#ifndef ADTSOLVER__HPP__
#define ADTSOLVER__HPP__
#include <assert.h>
#include <string.h>
#include <queue>

#include "ae/AeValSolver.hpp"
#include "ae/SMTUtils.hpp"
#include "ufo/Smt/EZ3.hh"

using namespace std;
using namespace boost;
namespace ufo
{
  class ADTSolver
  {
    private:

    Expr goal;
    ExprVector& assumptions;
    ExprVector& constructors;

    map<Expr, Expr> baseConstructors;
    map<Expr, Expr> indConstructors;

    ExprFactory &efac;
    SMTUtils u;

    // DS for lemma gen
    ExprVector baseconstrapps;
    ExprVector negativeLemmas;
    ExprVector positiveLemmas;

    ExprVector rewriteHistory;
    vector<int> rewriteSequence;
    queue<Expr> consecutives;
    int maxDepth;
    int maxGrow;
    int mergingIts;
    int earlySplit;
    bool verbose;
    int sp = 2;
    int glob_ind = 0;
    int lev = 0;
    bool useZ3 = false;
    bool useKS = false;
    unsigned to;
    ExprVector blockedAssms;
    int nestedLevel;

    public:

    ADTSolver(Expr _goal, ExprVector& _assumptions, ExprVector& _constructors,
      int _glob_ind = 0, int _lev = 0, int _maxDepth = 5, int _maxGrow = 3,
      int _mergingIts = 3, int _earlySplit = 1, bool _verbose = false,
      bool _useZ3 = true, bool _useKS = true, unsigned _to = 1000, unsigned _l = 0) :
        goal(_goal), assumptions(_assumptions), constructors(_constructors),
        glob_ind(_glob_ind), lev(_lev), efac(_goal->getFactory()),
        u(_goal->getFactory(), _to), maxDepth(_maxDepth), maxGrow(_maxGrow),
        mergingIts(_mergingIts), earlySplit(_earlySplit), verbose(_verbose),
        useZ3(_useZ3), useKS(_useKS), to (_to), nestedLevel(_l)
    {
      // for convenience, rename assumptions (to have unique quantified variables)
      renameAssumptions();
    }

    void renameAssumptions()
    {
      int c = 0;
      ExprSet allVars;
      filter(conjoin(assumptions, efac), bind::IsConst (), inserter(allVars, allVars.begin()));

      for (int i = 0; i < assumptions.size(); i++)
      {
        map<Expr, ExprVector> vars;
        getQVars(assumptions[i], vars);
        ExprMap replFls;
        for (auto & e : vars)
        {
          ExprMap repls;
          for (int j = 0; j < e.first->arity() - 1; j++)
          {
            Expr v = bind::fapp(e.first->arg(j));
            Expr newVar;
            while (true)
            {
              newVar = cloneVar(v, mkTerm<string> ("_qv_" + to_string(++c), efac));
              if (find(allVars.begin(), allVars.end(), newVar) == allVars.end()) break;
            }
            repls[v->left()->left()] = newVar->left()->left();
          }
          Expr newFla = replaceAll(e.first, replFls);
          replFls[e.first] = replaceAll(newFla, repls);
        }
        assumptions[i] = replaceAll(assumptions[i], replFls);
      }
    }

    bool simplifyGoal()
    {
      Expr goalQF = goal->last();
      if (containsOp<ITE>(goalQF)) // TODO: support IMPL/IFF
      {
        ExprVector disjs, vars;
        u.flatten(goalQF, disjs, false, vars, [](Expr a, ExprVector& b){return a;});
        goalQF = simplifyBool(disjoin(disjs, efac));
      }
      if (u.isEquiv(goalQF, mk<TRUE>(efac))) return true;

      ExprVector args;
      for (int i = 0; i < goal->arity() - 1; i++)
      {
        if (contains(goal->last(), goal->arg(i))) args.push_back(goal->arg(i));
      }
      if (args.size() == 0) goal = goalQF;
      else
      {
        args.push_back(goalQF);
        goal = mknary<FORALL>(args);
      }
      rewriteHistory.push_back(goal);
      return false;
    }

    bool findAssmOccurs(Expr goal, Expr e, Expr eq)
    {
      for (auto a : assumptions)
      {
        if (a == eq) continue;
        if (contains(a, e)) return true;
      }
      return (contains(goal, e));
    }

    void eliminateEqualities(Expr& goal)
    {
      ExprMap allrepls;
      for (auto it = assumptions.begin(); it != assumptions.end();)
      {
        Expr &a = *it;
        if (isOpX<EQ>(a))
        {
          ExprMap repls;
          if (findAssmOccurs(goal, a->left(), a) > 0 && a->left()->arity() == 1
              && !contains (a->right(), a->left()))
            repls[a->left()] = a->right();
          else if (findAssmOccurs(goal, a->right(), a) > 0 && a->right()->arity() == 1
              && !contains (a->left(), a->right()))
            repls[a->right()] = a->left();

          if (repls.empty()) ++it;
          else
          {
            it = assumptions.erase(it);
            for (int i = 0; i < assumptions.size(); i++)
              assumptions[i] = replaceAll(assumptions[i], repls);
            goal = replaceAll(goal, repls);
          }
        }
        else ++it;
      }
    }

    bool mergeAssumptions(int bnd = -1)
    {
      // simplify them first
      int sz = assumptions.size();
      for (int i = 0; i < sz; i++) // TODO: add mores simplifications
      {
        Expr &a = assumptions[i];
        a = simplifyBool(a);
      }
      if (bnd == -1) bnd = mergingIts; // default val
      for (int i = 0; i < bnd; i++)
      {
        ExprSet newAssms;
        for (auto a : assumptions)
        {
          // todo: figure out why there could be NULLs
          if (a == NULL) continue;

          if (isOpX<ITE>(a))
          {
            newAssms.insert(a);
            continue; // GF: could be useful in principle
          }

          if (!isOpX<FORALL>(a) && simplifyAssm(a, newAssms))
          {
            return true;
          }
          if (isOpX<NEG>(a))
          {
            getConj(mkNeg(a->left()), newAssms);
          }
          else
          {
            newAssms.insert(a);
          }
        }
        assumptions.clear();
        for (auto & a : newAssms)
        {
          // some blocking heurisitcs here (TODO: try to block them in early stages, i.e., don't even compute)
          if (isOpX<EQ>(a) && isOpX<AND>(a->left()) /*&& isOpX<AND>(a->right())*/) continue;

          if (find (blockedAssms.begin(), blockedAssms.end(), a) == blockedAssms.end())
            unique_push_back(a, assumptions);
        }
      }
      return false;
    }

    void splitAssumptions()
    {
      ExprSet newAssms;
      for (auto & a : assumptions)
      {
        if (a != NULL) getConj(a, newAssms);
      }
      assumptions.clear();
      for (auto & a : newAssms) assumptions.push_back(a);
    }

    bool simplifyAssm(Expr assm, ExprSet& newAssms)
    {
      for (auto a : assumptions)
      {
        if (a == assm || a == NULL) continue;
        if (isOpX<FORALL>(assm) && !isOpX<FORALL>(a)) continue;

        ExprVector result;
        if (useAssumption(assm, a, result, true)) {
          for (auto & it : result) {
            if (it == NULL) continue;

            Expr tmp = it;
            if (!u.isTrue(tmp))
              {
              if (u.isFalse(tmp))
              {
                if (verbose) outs () << string(sp, ' ')
                  << "inconsistent assumptions: " << *assm << " and " << *a << "\n";
                return true;
              }

              tmp = simplifyArithm(tmp);
              ExprSet tmps;
              getConj(simplifyBool(tmp), tmps);
              getConj(simplifyBool(simplifyArr(tmp)), tmps); // duplicate for the case of arrays
              for (auto & t : tmps)
              {
                if (find(assumptions.begin(), assumptions.end(), t) == assumptions.end())
                {
                  newAssms.insert(t);
                }
              }
            }
          }
        }
      }
      return false;
    }

    // main method to do rewriting
    // TODO: separate the logic for fwd, otherwise the code gets messy
    bool useAssumption(Expr subgoal, Expr assm, ExprVector& result, bool fwd = false)
    {
      if (isOpX<FORALL>(assm))
      {
        ExprMap matching;
        ExprVector args;
        for (int i = 0; i < assm->arity() - 1; i++) args.push_back(bind::fapp(assm->arg(i)));

        Expr assmQF = assm->last();
        Expr repl = assmQF;

        bool isImpl = false;
        if (isOpX<IMPL>(assmQF))
        {
          if (fwd) assmQF = assmQF->left();
          else assmQF = assmQF->right();
          isImpl = true;
        }

        if (isOpX<ITE>(assmQF))
        {
          int res = -1;
          if (fwd)
          {
            if (findMatching (assmQF->left(), subgoal, args, matching))
            {
              res = 1;
            }
            else
            {
              matching.clear();
              if (findMatching (mkNeg(assmQF->left()), subgoal, args, matching))
              {
                res = 2;
              }
            }
            if (res > 0)
            {
              repl = replaceAll(assmQF->arg(res), matching);

              // sanity removal
              for (auto it = args.begin(); it != args.end();)
              {
                if (contains (repl, *it)) ++it;
                else it = args.erase(it);
              }

              if (!args.empty())
              {
                repl = createQuantifiedFormulaRestr(repl, args);
              }

              result.push_back(repl);
              return true;
            }
          }
          else
          {
            // !fwd

            if (findMatching (assmQF->right(), subgoal, args, matching))
            {
              res = 1;
            }
            else
            {
              matching.clear();
              if (findMatching (assmQF->last(), subgoal, args, matching))
              {
                res = 2;
              }
            }
            if (res > 0)
            {
              if (res == 1) repl = assmQF->left();
              else repl = mkNeg(assmQF->left());
              repl = replaceAll(repl, matching);

              ExprSet vars;
              filter(assmQF->left(), bind::IsConst (), inserter(vars, vars.begin()));

              for (auto it = args.begin(); it != args.end();)
              {
                if (find(vars.begin(), vars.end(), *it) != vars.end())
                {
                  it = args.erase(it);
                }
                else
                {
                  ++it;
                }
              }
              if (!args.empty()) repl = createQuantifiedFormulaRestr(repl, args, false);

              result.push_back(repl);
              return true;
            }
          }
        }

        std::set<ExprMap> matchingSet;
        // we first search for a matching of the entire assumption (usually some inequality)
        if (findMatchingSubexpr (assmQF, subgoal, args, matchingSet))
        {
          for (auto matching : matchingSet) {
            Expr auxRepl = repl;
            auxRepl = replaceAll(auxRepl, matching);
            Expr replaced;
            if (isImpl)
            {
              if (fwd) // used in simplifyAssm
              {
                if (!isOpX<FORALL>(subgoal) && u.implies(subgoal, auxRepl->left()))
                {
                  ExprSet vars;
                  filter (assmQF, bind::IsConst (), inserter(vars, vars.begin()));
                  for (auto it = args.begin(); it != args.end();)
                  {
                    bool found = false;
                    if (find(vars.begin(), vars.end(), *it) != vars.end())
                    {
                      found = true;
                      it = args.erase(it);
                    }
                    if (!found)
                    {
                      ++it;
                    }
                  }

                  // sanity removal
                  for (auto it = args.begin(); it != args.end();)
                  {
                    if (contains (auxRepl->right(), *it)) ++it;
                    else it = args.erase(it);
                  }

                  if (args.empty())
                  {
                    replaced = auxRepl->right();
                  }
                  else
                  {
                    replaced = createQuantifiedFormulaRestr(auxRepl->right(), args);
                  }
                }
              }
              else
              {
                ExprSet vars;
                filter(assmQF, bind::IsConst (), inserter(vars, vars.begin()));
                replaced = replaceAll(subgoal, auxRepl->right(), auxRepl->left());

                for (auto it = args.begin(); it != args.end();)
                {
                  if (find(vars.begin(), vars.end(), *it) != vars.end())
                  {
                    it = args.erase(it);
                  }
                  else
                  {
                    ++it;
                  }
                }
                if (!args.empty())
                  replaced = createQuantifiedFormulaRestr(replaced, args, false);
              }
            }
            else
            {
              replaced = replaceAll(subgoal, auxRepl, mk<TRUE>(efac));
            }

            if (subgoal != replaced)
            {
              result.push_back(replaced);
              return true;
            }
          }
        }

        if (isImpl) return false;

        if (isOpX<EQ>(assmQF))
        {
          matchingSet.clear();
          // if the assumption is equality, the we search for a matching of its LHS
          // (we can try matching the RHS as well, but it will likely give us infinite loops)
          if (findMatchingSubexpr (assmQF->left(), subgoal, args, matchingSet))
          {
            for (auto matching : matchingSet) {
              Expr auxRepl = repl;
              auxRepl = replaceAll(auxRepl, matching);
              result.push_back(replaceAll(subgoal, auxRepl->left(), auxRepl->right()));
            }
            return true;
          }
          // try vice versa (dangerous since it will introduce repeated rewriting)
          // matchingSet.clear();
          // if (!fwd && findMatchingSubexpr (assmQF->right(), subgoal, args, matchingSet))
          // {
          //   for (auto matching : matchingSet) {
          //     Expr auxRepl = repl;
          //     auxRepl = replaceAll(auxRepl, matching);
          //     result.push_back(replaceAll(subgoal, auxRepl->right(), auxRepl->left()));
          //   }
          //   return true;
          // }
        }

        if (isOp<ComparissonOp>(assmQF) && isOp<ComparissonOp>(subgoal))
        {
          Expr assmQFtmp = assmQF;
          Expr subgoalTmp = subgoal;
          assmQF = normalizeArithm(assmQF);
          subgoal = normalizeArithm(subgoal);

          if (findMatching (assmQF->left(), subgoal->left(), args, matching))
          {
            repl = replaceAll(assmQF, matching);
            if (fwd && !u.isSat(repl, subgoal))
            {
              result.push_back(mk<FALSE>(efac));
              return true;
            }
            if (fwd)
            {
              if (((isOpX<LEQ>(repl) && isOpX<GEQ>(subgoal)) || (isOpX<GEQ>(repl) && isOpX<LEQ>(subgoal))) &&
                  (repl->left() == subgoal->left()) && (repl->right() == subgoal->right()))
                {
                  result.push_back(mk<EQ>(repl->left(), subgoal->right()));
                  return true;
                }
            }
            if (!fwd && u.implies(repl, subgoal))
            {
              result.push_back(mk<TRUE>(efac));
              return true;
            }
          }
          matching.clear();
          assmQF = assmQFtmp;
          subgoal = subgoalTmp;
        }

        if (isOpX<ITE>(subgoal))
        {
          matchingSet.clear();
          if (findMatchingSubexpr (assmQF, subgoal->left(), args, matchingSet))
          {
            for (auto matching : matchingSet) {
              Expr auxRepl = repl;
              for (auto & a : matching) auxRepl = replaceAll(auxRepl, a.first, a.second);
              if (u.implies(auxRepl, subgoal->left())) result.push_back(subgoal->right());
              else if (u.implies(auxRepl, mkNeg(subgoal->left()))) result.push_back(subgoal->last());
            }
            return (result.size() > 0);
          }
        }

        // try finding inconsistencies
        if (fwd && !containsOp<FORALL>(assmQF))
        {
          std::set<ExprMap> matchingSet1;
          ExprVector args1;
          filter(subgoal, bind::IsConst (), inserter(args1, args1.begin()));
          if (findMatchingSubexpr (subgoal, assmQF, args1, matchingSet1))
          {
            for (auto matching1 : matchingSet1) {
              Expr auxRepl = assmQF;
              for (auto & m : matching1){
                auto it = find(args.begin(), args.end(), m.second);
                if (it != args.end())
                {
                  auxRepl = replaceAll(auxRepl, m.second, m.first);
                  args.erase(it);
                }
                else
                {
                  if (m.second != m.first) break;
                }
              }
              if (args.empty())
              {
                if (!u.isSat(subgoal, auxRepl)) result.push_back(mk<FALSE>(efac));
                else result.push_back(auxRepl);
                return true;
              }
            }
          }
        }
      }
      else
      {
        // for a quantifier-free assumption (e.g., inductive hypotheses),
        // we create an SMT query and check with Z3
        // TODO: we can do so for ALL constistent quantifier-free assumptions at once

        if (isOpX<EQ>(assm)) // simple (SMT-free) checks first
        {
          Expr res = replaceAll(subgoal, assm->left(), assm->right());
          if (res != subgoal)
          {
            result.push_back(res);
            return true;
          }
        }

        if (!fwd && u.implies(assm, subgoal))
        {
          result.push_back(mk<TRUE>(efac));
          return true;
        }
        if (fwd && !u.isSat(assm, subgoal)) {
          result.push_back(mk<FALSE>(efac));
          return true;
        }

        if (!fwd && isOp<ComparissonOp>(subgoal) && isOp<ComparissonOp>(assm) &&
            isNumeric(subgoal->left()) && isNumeric(assm->left()))
        {
          Expr tryAbd = abduce(subgoal, assm);
          if (tryAbd != NULL && tryAbd != subgoal)
          {
            result.push_back(tryAbd);
            return true;
          }
        }

        // TODO: proper matching
        if (isOpX<IMPL>(subgoal))
        {
          if (u.implies(subgoal->left(), assm))
          {
            result.push_back(subgoal->right());
            return true;
          }
        }
        if (isOpX<ITE>(subgoal))
        {
          if (u.implies(assm, subgoal->left()))
          {
            result.push_back(subgoal->right());
            return true;
          }
          if (u.implies(assm, mk<NEG>(subgoal->left())))
          {
            result.push_back(subgoal->last());
            return true;
          }
        }

        if (isOpX<OR>(assm) && fwd)
        {
          ExprSet dsjs;
          getDisj(assm, dsjs);
          bool rem = false;
          for (auto it = dsjs.begin(); it != dsjs.end();)
          {
            if (!u.isSat(*it, subgoal))
            {
              rem = true;
              it = dsjs.erase(it);
            }
            else ++it;
          }
          if (rem)
          {
            Expr res = disjoin(dsjs, efac);
            result.push_back(res);
            return true;
          }
        }
        if (isOp<ComparissonOp>(assm))
        {
          Expr res = replaceAll(subgoal, assm, mk<TRUE>(efac));
          res = replaceAll(res, mkNeg(assm), mk<FALSE>(efac));
          Expr tmp = reBuildCmpSym(assm, assm->left(), assm->right());
          assert((bool)u.isEquiv(assm, tmp));
          res = replaceAll(res, tmp, mk<TRUE>(efac));
          res = replaceAll(res, mkNeg(tmp), mk<FALSE>(efac));
          if (res != subgoal)
          {
            result.push_back(simplifyBool(res));
            return true;
          }
        }

        ExprSet stores;
        ExprSet selects;
        getStores(subgoal, stores);
        getSelects(subgoal, selects);

        if (stores.size() > 0)
        {
          if (isOpX<NEQ>(assm) && contains(subgoal, assm->left()) && contains(subgoal, assm->right()))
          {
            for (auto & a : stores)
            {
              if (isOpX<STORE>(a->left()) &&
                  ((a->right() == assm->right() && a->left()->right() == assm->left()) ||
                   (a->right() == assm->left() && a->left()->right() == assm->right())))
              {
                ExprMap substs;
                substs[assm->right()] = assm->left();
                substs[assm->left()] = assm->right();
                Expr tmp = replaceAll(a, substs, false);

                if (u.implies(assm, mk<EQ>(tmp, a)))
                {
                  result.push_back(replaceAll(subgoal, a, tmp));   // very specific heuristic; works for multisets
                  return true;
                }

                if (a->last() != a->left()->last())
                {
                  substs[a->last()] = a->left()->last();
                  substs[a->left()->last()] = a->last();
                }
                result.push_back(replaceAll(subgoal, a, replaceAll(a, substs, false)));
                return true;
              }
            }
            for (auto & a : selects)
            {
              if (isOpX<STORE>(a->left()) && !isOpX<STORE>(a->left()->left()) &&
                  ((a->right() == assm->right() && a->left()->right() == assm->left()) ||
                   (a->right() == assm->left() && a->left()->right() == assm->right())))
              {
                result.push_back(replaceAll(subgoal, a, mk<SELECT>(a->left()->left(), a->right())));
                return true;
              }
            }
          }

          if (isOpX<SELECT>(assm))
          {

            for (auto & a : stores)
            {
              if (assm->left() == a->left() &&
                  assm->right() == a->right() &&
                  isOpX<TRUE>(a->last()))
              {
                result.push_back(replaceAll(subgoal, a, a->left()));
                return true;
              }
            }
          }

          if (isOpX<NEG>(assm) && isOpX<SELECT>(assm->left()))
          {
            for (auto & a : stores)
            {
              if (assm->left()->left() == a->left() &&
                  assm->left()->right() == a->right() &&
                  isOpX<FALSE>(a->last()))
              {
                result.push_back(replaceAll(subgoal, a, a->left()));
                return true;
              }
            }
          }
        }
      }
      return false;
    }

    bool handleExists(Expr subgoal)
    {
      if (verbose) outs () << string(sp, ' ')  << "existential quantifies are currently not supported\n";
      return false;
      // to be done
    }

    // this recursive method performs a naive search for a strategy
    bool rewriteAssumptions(Expr subgoal)
    {
      if (u.isEquiv(subgoal, mk<TRUE>(efac)))
      {
        if (verbose) outs () << string(sp, ' ') << "rewriting done\n";
        return true;
      }

      // check recursion depth
      if (rewriteSequence.size() >= maxDepth)
      {
        if (verbose) outs() << string(sp, ' ') << "Maximum recursion depth reached\n";
        return false;
      }

      // check consecutive applications of the same assumption
      /*if (rewriteSequence.size() > maxGrow)
      {
        bool incr = true;
        for (int i = 1; i < maxGrow + 1; i++)
        {
          if (treeSize(rewriteHistory[rewriteHistory.size() - i]) < treeSize(rewriteHistory[rewriteHistory.size() - i - 1]))
          {
            incr = false;
            break;
          }
        }

        if (incr)
        {
          if (verbose) outs() << string(sp, ' ') << "sequence of rewrites only grows\n";
          return false;
        }
      }*/

      //look for assumption that was used two times in a row
      //

      /* test site 1 */

      auto assumptionsTmp = assumptions;
      bool toRem = false;
      if (isOpX<IMPL>(subgoal))
      {
        uniquePushConj(subgoal->left(), assumptions);
        if (assumptions.size() != assumptionsTmp.size())
        {
          eliminateEqualities(subgoal);
          toRem = true;
          if (mergeAssumptions())
          {
            assumptions = assumptionsTmp;
            if (verbose) outs() << string(sp, ' ') << "proven (merge assms after impl)\n";
            return true;
          }
          printAssumptions();
        }
        subgoal = subgoal->right();
        if (verbose) outs() << string(sp, ' ') << "current subgoal: " << *subgoal << "\n";
      }

      if (isOpX<EXISTS>(subgoal))
      {
        return handleExists(subgoal);
      }

      subgoal = simplifyExists(subgoal);
      subgoal = simplifyArr(subgoal);
      subgoal = simplifyArithm(subgoal);
      subgoal = simplifyBool(subgoal);

      ExprSet subgoals;
      if (isOpX<ITE>(subgoal))
      {
        subgoals.insert(mk<IMPL>(subgoal->left(), subgoal->right()));
        subgoals.insert(mk<IMPL>(mkNeg(subgoal->left()), subgoal->last()));
      }
      else
      {
        getConj(subgoal, subgoals);
      }

      if (subgoals.size() > 1)
      {
        while (subgoals.size() > 0)
        {
          int subgoalsSize = subgoals.size();
          int part = 1;
          for (auto it = subgoals.begin(); it != subgoals.end();)
          {
            Expr s = *it;
            if (verbose)
            {
              outs () << string(sp, ' ') << "proceed with (part " << part << "/" << subgoalsSize << "): " << *s << "\n";
              part++;
            }

            tribool tmpres = simpleSMTcheck(s);
            if (tmpres)
            {
              if (verbose) outs() << string(sp, ' ') << "{\n" << string(sp+2, ' ') <<
                "  proven trivially (with Z3)\n" << string(sp, ' ') << "}\n";
            }
            else
            {
              auto rewriteHistoryTmp = rewriteHistory;
              auto rewriteSequenceTmp = rewriteSequence;
              auto assumptionsTmp = assumptions;

              if (verbose) outs() << string(sp, ' ') << "{\n";
              sp += 2;
              tmpres = rewriteAssumptions(s);   // recursive call
              sp -= 2;
              if (verbose) outs() << string(sp, ' ') << "}\n";

              rewriteHistory = rewriteHistoryTmp;
              rewriteSequence = rewriteSequenceTmp;
              assumptions = assumptionsTmp;
            }
            if (tmpres)
            {
              if (verbose) outs () << string(sp, ' ') << "adding " << *s << " to assumptions\n";
              assumptions.push_back(s);
              it = subgoals.erase(it);
            }
            else
            {
              ++it;
            }
          }
          if (subgoals.size() == subgoalsSize)
          {
            if (verbose) outs() << string(sp, ' ') << "cannot prove " << subgoalsSize << " of the subgoals\n";
            return false;
          }
          else if (verbose && subgoals.size() > 0) outs () << string(sp, ' ') << "will try subgoals again\n";
        }
        if (verbose) outs () << string(sp, ' ')  << "all subgoals are proven\n";
        return true;
      }

      // here, assume subgoals.size() == 1
      // thus, subgoal == *subgoals.begin()

      // quick syntactic check first:
      for (int i = 0; i < assumptions.size(); i++)
      {
        if (assumptions[i] == subgoal)
        {
          if (toRem) assumptions = assumptionsTmp;
          if (verbose) outs () << string(sp, ' ') << "rewriting [" << i << "] done\n";
          return true;
        }
      }

      map<int, ExprVector> allAttempts;

      /* test site 3 */
      /*bool resKS = false;
      if (useKS) resKS = useKnowledgeScheme(subgoal);
      if (resKS) {
	  outs() << "  applying lemma from knowledge scheme\n";
          Expr a = assumptions.back();
	  int i = assumptions.size() - 1;
          ExprVector result;
          if (useAssumption(subgoal, a, result)) {
            for (auto & it : result) {
              if (u.isTrue(it))
              {
                if (verbose) outs () << string(sp, ' ') << "applied [" <<  i << "]\n";
                return true;
              }
            }
            for (auto & it : result)
              if (find (rewriteHistory.begin(), rewriteHistory.end(), it) == rewriteHistory.end())
                allAttempts[i].push_back(it);
          }
        }
      if (tryRewriting(allAttempts, subgoal))
      {
        if (toRem) assumptions = assumptionsTmp;
        return true;
      }

      allAttempts.clear();*/
      ExprVector defered;
      //write function that scans list of assumptions and returns index
      //make vector for indices assumptions already scanned
      //push index to scanned list
      //in the next iteration, return new index
      //(think about what it means for an assumption to be best)
      for (int i = 0; i < assumptions.size(); i++)
      {
        /*if (!rewriteSequence.empty()) {
	   outs() << string(sp, ' ') << " i is " << i << "  rewrite sequence: " << rewriteSequence.back() << '\n';
	   if (i == rewriteSequence.back()) continue;
	}*/
	Expr a = assumptions[i];
        ExprVector result;
        if (useAssumption(subgoal, a, result)) {
          if (verbose) outs () << string(sp, ' ') << "found " << result.size() << " substitution(s) for assumption " << i << "\n";
          for (auto & it : result) {
            if (u.isTrue(it))
            {
              if (verbose) outs () << string(sp, ' ') << "applied [" << i << "]\n";
              return true;
            }
          }
          for (auto & it : result)
            if (find (rewriteHistory.begin(), rewriteHistory.end(), it) == rewriteHistory.end())
              allAttempts[i].push_back(it);
        }
      }
      if (tryRewriting(allAttempts, subgoal))
      {
        if (toRem) assumptions = assumptionsTmp;
        return true;
      }

      {
      // vector<int> orderedAttempts1;
      // vector<int> orderedAttempts2;

      // identifying an order for rewrites
      // for (auto & a : allAttempts)
      // {
      //   bool placed = false;

      //   bool sw;
      //   if (earlySplit == 1) sw = treeSize(subgoal) >= treeSize(a.second);
      //   else sw = true;

      //   if (sw)
      //   {
      //     for (int i = 0; i < orderedAttempts1.size(); i++)
      //     {
      //       if (treeSize(allAttempts[orderedAttempts1[i]]) > treeSize(a.second))
      //       {
      //         orderedAttempts1.insert(orderedAttempts1.begin() + i, a.first);
      //         placed = true;
      //         break;
      //       }
      //     }
      //     if (!placed) orderedAttempts1.push_back(a.first);
      //   }
      //   else
      //   {
      //     for (int i = 0; i < orderedAttempts2.size(); i++)
      //     {
      //       if (treeSize(allAttempts[orderedAttempts2[i]]) > treeSize(a.second))
      //       {
      //         orderedAttempts2.insert(orderedAttempts2.begin() + i, a.first);
      //         placed = true;
      //         break;
      //       }
      //     }
      //     if (!placed) orderedAttempts2.push_back(a.first);
      //   }
      // }
      }

      //look at where this code goes in depth

      /* test site 2 */
      //keep track of finished lemmas
      Expr resKS = NULL;
      if (useKS) {
         resKS = useKnowledgeScheme(subgoal); 
	 assumptionsTmp = assumptions; 
	 allAttempts.clear();
      if (resKS != NULL) {
	  outs() << "  applying lemma from knowledge scheme to subgoal " << subgoal << "\n";
          Expr a = resKS;
	  int i = -1;
          ExprVector result;
          if (useAssumption(subgoal, a, result)) {
            for (auto & it : result) {
              if (u.isTrue(it))
              {
                if (verbose) outs () << string(sp, ' ') << "applied [" <<  i << "]\n";
                return true;
              }
            }
            for (auto & it : result)
              if (find (rewriteHistory.begin(), rewriteHistory.end(), it) == rewriteHistory.end())
                allAttempts[i].push_back(it);
          }
        }
      if (tryRewriting(allAttempts, subgoal))
      {
        if (toRem) assumptions = assumptionsTmp;
        return true;
      }
      }

      if (splitDisjAssumptions(subgoal)) return true;

      bool res = false;

      if (isOpX<OR>(subgoal)) res = splitByGoal(subgoal);
      if (!res) res = proveByContradiction(subgoal);
      if (!res) res = similarityHeuristic(subgoal);
      if (toRem) assumptions = assumptionsTmp;
      if (res) return true;

      if (lemmaGen(subgoal)) return true;

      //apply knowledge scheme heuristic
      /*res = false;
      if (useKS) res = useKnowledgeScheme(subgoal);
      if (res) {
        for (int i = assumptions.size()-1; i >= 0; i--)
        {
          Expr a = assumptions[i];
          ExprVector result;
          if (useAssumption(subgoal, a, result)) {
            for (auto & it : result) {
              if (u.isTrue(it))
              {
                if (verbose) outs () << string(sp, ' ') << "applied [" << i << "]\n";
                return true;
              }
            }
            for (auto & it : result)
              if (find (rewriteHistory.begin(), rewriteHistory.end(), it) == rewriteHistory.end())
                allAttempts[i].push_back(it);
          }
        }
      }*/

      // backtrack:
      if (verbose) outs () << string(sp, ' ') << "backtrack to: " << *subgoal << "\n";
      return res;
    }

    bool lemmaGen(Expr subgoal)
    {
      if (lev < 1 /* max meta-induction level, hardcoded for now */)
      {
        map<Expr, int> occs;
        getCommonSubterms(subgoal, occs);   // get common subterms in `exp` to further replace by fresh symbols
        auto it = occs.begin();
        for (int i = 0; i < occs.size() + 1; i++)
        {
          Expr expGen = subgoal;
          if (it != occs.end()) // try generalizing based on the current subterm from occs
          {
            expGen = generalizeGoal(subgoal, it->first, it->second);
            ++it;
            if (expGen == NULL) continue;
          }
          else
          {
            // if nothing worked, try to prove it as is (exactly once, but if not very large)
            if (getMonotDegree(expGen) > 2 || countFuns(expGen) > 3) //  hand-selected heuristics
              continue;
          }

          ExprVector vars;
          filter (expGen, IsConst (), inserter(vars, vars.begin()));
          for (auto it = vars.begin(); it != vars.end();)
            if (find(baseconstrapps.begin(), baseconstrapps.end(), *it) == baseconstrapps.end()) ++it;
              else it = vars.erase(it);

          bool toCont = false;
          for (auto & l : negativeLemmas)
          {
            ExprMap matching;
            if (findMatching(expGen, l, vars, matching))
            {
              toCont = true;
              break;
            }
          }
          if (toCont) continue;

          for (auto & l : positiveLemmas)
          {
            ExprMap matching;
            if (findMatching(expGen, l, vars, matching))
            {
              toCont = true;
              break;
            }
          }

          if (!toCont)
          {
            auto assumptionsNst = assumptions;
            for (auto it = assumptionsNst.begin(); it != assumptionsNst.end();)
              if (hasOnlyVars(*it, baseconstrapps)) ++it;
                else it = assumptionsNst.erase(it);

            ADTSolver sol (mkQFla(expGen, vars), assumptionsNst, constructors, glob_ind, lev + 1,
                           maxDepth, maxGrow, mergingIts, earlySplit, false, useZ3, useKS, to);

            toCont = bool(sol.solve());
          }
          if (toCont)
          {
            if (verbose) outs () << string(sp, ' ')  << "proven by induction: " << *expGen << "\n";
            positiveLemmas.push_back(expGen);
            return true;
          }
          else
          {
            if (verbose) outs () << string(sp, ' ')  << "nested induction failed\n";
            negativeLemmas.push_back(expGen);
          }
        }
      }
      return false;
    }

    //TRY TO MAKE BENCHMARK GOAL INCORRECT AND SEE WHAT HAPPENS

    // try rewriting in a particular order
    bool tryRewriting(map<int, ExprVector>& allAttempts, Expr subgoal)
    {
      for (auto & a : allAttempts) {
        int i = a.first;
        for (auto & exp : a.second) {
          if (verbose) outs() << string(sp, ' ') << "rewritten [" << i << "]: " << *exp << "\n";

          // save history
          rewriteHistory.push_back(exp);
	  if (!rewriteSequence.empty()) {
	     if (rewriteSequence.back() == i) {
	        consecutives.push(exp);
	     }
	  }
	  else {
            queue<Expr> emptyTemp;
	    swap(consecutives, emptyTemp);
	  }
          rewriteSequence.push_back(i);

          if (rewriteAssumptions(exp))
          {
            if (verbose) if (exp) outs () << string(sp, ' ')  << "rewriting done\n";
            return true;
          }
          else
          {
            // failed attempt, remove history
            rewriteHistory.pop_back();
            rewriteSequence.pop_back();
          }
        }
      }
      return false;
    }

    // a particular heuristic, to be extended
    Expr generalizeGoal(Expr e, Expr subterm, int occs /* how often `subterm` occurs in `e` */)
    {
      if (occs < 1) return NULL;
      if (subterm->arity() == 0 && !isOpX<MPZ>(subterm))
        return NULL;                                      // it should not be a (non-integer) constant
      if (isOpX<FAPP>(subterm) &&
          subterm->left()->arity() == 2) return NULL;     // it should not be a variable
      Expr expGen = e;
      Expr s = bind::mkConst(mkTerm<string> ("_w_" + to_string(glob_ind), efac), typeOf(subterm));
      glob_ind++;                                         // create a fresh symmbol
      expGen = replaceAll(expGen, subterm, s);
      if (isOpX<MPZ>(subterm))                            // replace negative consts
        expGen = replaceAll(expGen, mkMPZ(-lexical_cast<cpp_int>(subterm), efac),
                                    mk<UN_MINUS>(s));;
      if (!emptyIntersect(expGen, subterm)) return NULL;  // there should not be any leftovers after replacement
      int cnt = countFuns(expGen);                        // check the result
      if (cnt == 0 || cnt > 3) return NULL;
      if (getMonotDegree(expGen) > 2) return NULL;        // if it is still "too complex", scratch it
      return expGen;
    }

    bool classifyRewrite(Expr assm) {
       Expr newExpr;
       if (isOpX<FORALL>(assm) || isOpX<EXISTS>(assm)) newExpr = assm->last();
       if (isOpX<EQ>(newExpr)) {
          if (treeSize(newExpr->left()) < treeSize(newExpr->right())) return false;
	  return true;
       }
       else {return true;}
    }

    Expr useKnowledgeScheme(Expr subgoal) {
	//not null
        if (subgoal == NULL) return NULL;
	/*if (consecutives.empty()) {outs() << "  no consecutive rewrites found\n";}
	else if (!consecutives.empty()) {outs() << "  new subgoal will be " << consecutives.front() << '\n';}
	subgoal = consecutives.front();*/
	ExprSet knowledgeScheme;
        buildKnowledgeScheme(subgoal, knowledgeScheme);
        printKnowledgeScheme(knowledgeScheme);
        ExprVector res;
        for (auto is = knowledgeScheme.begin(); is != knowledgeScheme.end(); is++) {
          //outs() << "  Current subgoal is: " << subgoal << "\n";
          //outs() << "  Current lemma is: " << (*is) << "\n\n";
          useAssumption(subgoal, (*is), res);
          if (!res.empty()) {
	    /*outs() << "RESULTS FROM USEASSUMPTIONS\n";
	    for (auto temp = res.begin(); temp != res.end(); temp++) {
                outs() << "\t" << *temp << "\n";
	    }*/
            //test if (*is) is in assumptions
	    for (auto ba = assumptions.begin(); ba != assumptions.end(); ba++) {
               if (testIsomorphism((*ba), (*is))) return NULL;
	       if (testIsomorphism(mirrorLemma(*ba), (*is))) return NULL;
	    }
            //printKnowledgeScheme();
	    //add disproof code here
            if (disproof(*is)) continue;
            outs() << "  Attempting to prove " << (*is) << "\n";
            ADTSolver sol ((*is), assumptions, constructors, glob_ind, lev+1,
                           maxDepth, maxGrow, mergingIts, earlySplit, false, useZ3, false, to);
            if (sol.solve()) {
	      outs() << "  Using " << (*is) << "\n";
              return (*is);
            }
          }
	  else {
             useAssumption(subgoal, mirrorLemma((*is)), res);
	     if (!res.empty()) {
		//test if (*is) is in assumptions
	        for (auto ba = assumptions.begin(); ba != assumptions.end(); ba++) {
                  if (testIsomorphism((*ba), (*is))) return NULL;
		  if (testIsomorphism(mirrorLemma(*ba), (*is))) return NULL;
	        }
            	//printKnowledgeScheme();
		if (disproof(*is)) continue;
            	outs() << "  Attempting to prove " << (*is) << "\n";
            	ADTSolver sol ((*is), assumptions, constructors, glob_ind, lev+1,
                              maxDepth, maxGrow, mergingIts, earlySplit, false, useZ3, false, to);
            	if (sol.solve()) {
	           outs() << "  Using " << (*is) << "\n";
              	   return (*is);
            	}
	     }
	  }
       }
       knowledgeScheme.clear();
       return NULL;
    }

    bool testIsomorphism(Expr exp1, Expr exp2) {
       ExprVector vars;
       ExprMap matching;
       filter(exp1, bind::IsConst(), inserter(vars, vars.begin()));
       if (findMatching(exp1, exp2, vars, matching)) {
          outs() << "  expressions are isomorphic\n";
	  return true;
       }
       return false;
    }

    bool disproof(Expr exp) {
       outs() << "  Attempting to disprove: " << exp << '\n';
       outs() << "  {\n";
       ExprVector vars;
       Expr newExpr;
       //remove quantifier
       if (isOpX<FORALL>(exp) || isOpX<EXISTS>(exp)) {newExpr = exp->last();}
       else {newExpr = exp;}
       //newExpr = mk<NEG>(newExpr);
       //newExpr = mk<NEQ>(newExpr->left(), newExpr->right());
       //collect variables and remove constants
       filter(newExpr, bind::IsConst(), inserter(vars, vars.begin()));
       Expr base =  mk<FAPP>(*find_if(constructors.begin(), constructors.end(), [](Expr x){return x->arity() == 2;}));
       for (auto it = vars.begin(); it != vars.end(); ) {
         if (*it == base) {vars.erase(it);}
	 else it++;
       }
       //collect finalTerms
       ExprSet finalTerms = generateTerms(newExpr, vars, 3);
       outs() << "    generated " << finalTerms.size() << " terms\n";
       outs() << "    unrolling terms\n";
       int counter = 0;
       for (auto it = finalTerms.begin(); it != finalTerms.end(); it++) {
	  Expr temp = *it;
	  Expr old = temp;
          while (true) {
             ExprVector results;
             for (auto is = assumptions.begin(); is != assumptions.end(); is++) {
		//locate specific function definitions
		//when reading file, extract definitions
		//pattern match for two assumptions, one will have base cons the other will be ind
		//
                useAssumption(temp, *is, results);
                if (!results.empty()) {
		   temp = results[0];
		   //outs() << "  temp is: " << temp << '\n';
		   //outs() << "  old is: " << old << '\n';
		}
	     }
	     if (old == temp) {break;}
	     else {old = temp;}
	     //if (isOpX<TRUE>(temp)) break;
	  }
          //outs() << "    unrolled term: " << temp << '\n';
	  //outs() << "    counter: " << counter << '\n';
	  counter++;
	  auto res = u.isTrue(temp);
	  if (!res) {
	    outs() << "    Disproven with Z3.\n";
	    outs() << "  }\n";
	    return true;
	  }
	  if (counter == 50 || counter == finalTerms.size() - 1) {
	    outs() << "    Tested maximum number of terms\n";
            outs() << "  }\n";
            return false;	    
	  };
       }
       outs() << "    Disproof failed.\n";
       outs() << "  }\n";
       //experiment here with useAssumption, run on an infinite loop that replaces each rev2 instance one at a time
       return false;
    }
    
    //extend this for arbitrary combinations using dynamic programming
    /*ExprSet generateTerms(Expr exp, ExprVector vars, int length) {
       ExprSet ret;
       ExprVector args;
       Expr base = mk<FAPP>(*find_if(constructors.begin(), constructors.end(), [](Expr x){return x->arity() == 2;}));
       Expr cons = *find_if(constructors.begin(), constructors.end(), [](Expr x){return x->arity() != 2;});
       Expr type = cons->arg(1);
       Expr temp = base;
       Expr newExpr = exp;
       int counter = 0;
       //handle base case
       for (int i = 0; i < vars.size(); i++) newExpr = replaceAll(newExpr, vars[i], base);
       ret.insert(newExpr);
       for (int i = 0; i < length; i++) {
          //loop over variables
          ret.insert(newExpr);
	  newExpr = exp;
	  for (int j = 0; j < vars.size(); j++) {
             //generate list of length i
	     for (int k = 0; k < i; k++) {
                Expr var = bind::mkConst(mkTerm<string>("_t_" + to_string(counter), efac), type);
		counter++;
		args.insert(args.end(), {cons, var, temp});
		temp = mknary<FAPP>(args);
		args.clear();
	     }
	     newExpr = replaceAll(newExpr, vars[j], temp);
	     temp = base;
	  }
       }
       //print
       for (auto it = ret.begin(); it != ret.end(); it++) {
          outs() << "    generated term is: " << *it << '\n';
       }
       return ret;
    }*/


    ExprSet generateTerms(Expr exp, ExprVector vars, int length) {
       ExprSet result;
       ExprSet startSet;
       startSet.insert(exp);
       ExprSet generatedTerms = generateLists(vars.size(), length);
       //for (auto it = generatedTerms.begin(); it != generatedTerms.end(); it++) {outs() << "  generated list: " << *it << '\n';}
       generateTermsMemoize(startSet, vars, generatedTerms, result);
       return result;
    }

    void generateTermsMemoize(ExprSet start, ExprVector vars, ExprSet newTerms, ExprSet & result) {
       if (vars.empty()) {
	 result = start;      
         return;
       }
       ExprSet newSet;
       Expr curVar = vars.back();
       vars.pop_back();
       for (auto it = start.begin(); it != start.end(); it++) {
          for (auto is = newTerms.begin(); is != newTerms.end(); is++) {
             Expr temp = replaceAll(*it, curVar, *is);
             newSet.insert(temp);
	  }
       }
       generateTermsMemoize(newSet, vars, newTerms, result);  
    }

    ExprSet generateLists(int numCopies, int length) {
       ExprSet retVal;
       ExprVector args;
       Expr cons = *find_if(constructors.begin(), constructors.end(), [](Expr x){return x->arity() != 2;});
       Expr base = mk<FAPP>(*find_if(constructors.begin(), constructors.end(), [](Expr x){return x->arity() == 2;}));
       Expr temp = base;
       Expr type = cons->arg(1);
       int counter = 0;
          for (int j = 0; j < length; j++) {
             for (int k = 0; k < j; k++) {
                Expr var = bind::mkConst(mkTerm<string>("_t_" + to_string(counter), efac), type);
		counter++;
		args.insert(args.end(), {cons, var, temp});
		temp = mknary<FAPP>(args);
		args.clear();
	     }
	     retVal.insert(temp);
	     temp = base;
	  }
       return retVal;
    }

    Expr mirrorLemma(Expr origin) {
        Expr expGen;
        if (isOpX<FORALL>(origin)) {
           ExprVector vars;
           filter (origin->last(), IsConst (), inserter(vars, vars.begin()));
           if (isOpX<LT>(origin->last())) {
              expGen = mkQFla(mk<GT>(origin->last()->right(), origin->last()->left()), vars);
              return expGen;
           }
           if (isOpX<GT>(origin->last())) {
              expGen = mkQFla(mk<LT>(origin->last()->right(), origin->last()->left()), vars);
              return expGen;
           }
           if (isOpX<LEQ>(origin->last())) {
              expGen = mkQFla(mk<GEQ>(origin->last()->right(), origin->last()->left()), vars);
              return expGen;
           }
           if (isOpX<GEQ>(origin->last())) {
              expGen = mkQFla(mk<LEQ>(origin->last()->right(), origin->last()->left()), vars);
              return expGen;
           }
           if (isOpX<EQ>(origin->last())) {
              expGen = mkQFla(mk<EQ>(origin->last()->right(), origin->last()->left()), vars);
              return expGen;
           }
           if (isOpX<NEQ>(origin->last())) {
              expGen = mkQFla(mk<NEQ>(origin->last()->right(), origin->last()->left()), vars);
              return expGen;
           }
        }
        return origin;
    }

    /*
     * use the findMatching function to implement alpha-conversion
     */
    void buildKnowledgeScheme(Expr subgoal, ExprSet & knowledgeScheme) {
      if (subgoal == NULL) return;
      ExprMap matching;
      ExprVector vars;
      ExprVector catas;  // catamorphism: ADT -> primitive type
      ExprVector anas;   // anamorphism: primitive type -> ADT
      ExprVector travs;  // ADT -> ADT
      //build vector of catamorphisms
      filter(subgoal, 
             [](Expr x) {
	             bool y = isOpX<FDECL>(x) && (isOpX<INT_TY>(x->last()) || isOpX<BOOL_TY>(x->last())) && x->arity() >= 3;
		     if (y == false) return false;
		     for (int i = 0; i < x->arity() - 1; i++) {
                        y =  (!isOpX<INT_TY>(x->arg(i))) && (!isOpX<BOOL_TY>(x->arg(i))) && (!isOpX<ARRAY_TY>(x->arg(i)));
		     }
		     return y;
	          },
                  inserter(catas, catas.begin()));
      //build vector of anamorphisms
      filter(subgoal, 
             [](Expr x){ 
		     bool y = isOpX<FDECL>(x) && (isOpX<INT_TY>(x->arg(1)) || isOpX<BOOL_TY>(x->arg(1))) && x->arity() == 3;
                     return y;
                  },
                  inserter(anas, anas.begin()));
      //build vector of traversals, must have at least arity 1
      filter(subgoal, 
             [](Expr x){
		     bool y = isOpX<FDECL>(x) && x->arity() >= 3;
		     if (y == false) return false;
	             for (int i = 1; i < x->arity(); i++) {
                        y = y && (!isOpX<INT_TY>(x->arg(i)) && !isOpX<BOOL_TY>(x->arg(i)) && !isOpX<ARRAY_TY>(x->arg(i)));
	             }
		     return (y && isOpX<FDECL>(x) && x->arity() >= 3);
	          },
	          inserter(travs, travs.begin()));
      /*outs() << "catamorphisms: \n";
      for (auto it = catas.begin(); it != catas.end(); it++) {outs() << "\t" << (*it) << "\n";}
      outs() << "anamorphisms: \n";
      for (auto it = anas.begin(); it != anas.end(); it++) {outs() << "\t" << (*it) << "\n";}
      outs() << "traversals: \n";
      for (auto it = travs.begin(); it != travs.end(); it++) {outs() << "\t" << (*it) << "\n";}*/
      Expr expGen;
      //catamorphic lemmas
      for (auto it = catas.begin(); it != catas.end(); it++) {
         //positive definiteness property
         if (subgoal->arity() == 3 && isOpX<INT_TY>(subgoal->last())) {
            Expr var = bind::mkConst(mkTerm<string>("_ks_qv_" + to_string(glob_ind), efac), subgoal->arg(1));
            glob_ind++;
            vars.push_back(var);
            expGen = mkQFla(mk<LEQ>(mkMPZ(0,efac), mk<FAPP>(subgoal, var)), vars);
            knowledgeScheme.insert(expGen);
	    vars.clear();
         }
      }
      //traversal lemmas
      for (auto it = travs.begin(); it != travs.end(); it++) {
       	 if ((*it)->arity() == 4) {
            //associativity property
            Expr var1 = bind::mkConst(mkTerm<string>("_ks_qv_" + to_string(glob_ind), efac), (*it)->arg(1));
            glob_ind++;
            vars.push_back(var1);
            Expr var2 = bind::mkConst(mkTerm<string>("_ks_qv_" + to_string(glob_ind), efac), (*it)->arg(1));
            glob_ind++;
            vars.push_back(var2);
            Expr var3 = bind::mkConst(mkTerm<string>("_ks_qv_" + to_string(glob_ind), efac), (*it)->arg(1));
            glob_ind++;
            vars.push_back(var3);
            expGen = mkQFla(mk<EQ>(mk<FAPP>((*it), mk<FAPP>((*it), var1, var2), var3), mk<FAPP>((*it), var1, mk<FAPP>((*it), var2, var3))),vars);
            knowledgeScheme.insert(expGen);
            vars.clear();
            //distributive property
            //trav1 = is
            //trav2 = it
            //trav1(trav2(x, y)) = trav2(trav1(x), trav1(y))
            for (auto is = travs.begin(); is != travs.end(); is++) {
               if ((*is)->arity() == 3 && (*it)->arity() == 4) {
                  Expr var4 = bind::mkConst(mkTerm<string>("_ks_qv_" + to_string(glob_ind), efac), (*it)->arg(1));
                  glob_ind++;
                  vars.push_back(var4);
                  Expr var5 = bind::mkConst(mkTerm<string>("_ks_qv_" + to_string(glob_ind), efac), (*it)->arg(1));
                  glob_ind++;
                  vars.push_back(var5);
                  expGen = mkQFla(mk<EQ>(mk<FAPP>((*is), mk<FAPP>((*it), var4, var5)), mk<FAPP>((*it), mk<FAPP>((*is), var4), mk<FAPP>((*is), var5))), vars);
                  Expr expGen1 =  mkQFla(mk<EQ>(mk<FAPP>((*is), mk<FAPP>((*it), var4, var5)), mk<FAPP>((*it), mk<FAPP>((*is), var5), mk<FAPP>((*is), var4))), vars);
                  //knowledgeScheme.insert(expGen);
                  knowledgeScheme.insert(expGen1);
                  vars.clear();
               }
            }
	    //nilpotent expansion property
	    //trav1 = is
	    //trav2 = it
	    //trav2(x,y) = trav1(trav2(x,nil),y)
	    for (auto is = travs.begin(); is != travs.end(); is++) {
               if ((*is)->arity() == 4 && (*it)->arity() == 4) {
                  Expr var6 = bind::mkConst(mkTerm<string>("_ks_qv_" + to_string(glob_ind), efac), (*it)->arg(1));
                  glob_ind++;
                  vars.push_back(var6);
                  Expr var7 = bind::mkConst(mkTerm<string>("_ks_qv_" + to_string(glob_ind), efac), (*it)->arg(1));
                  glob_ind++;
                  vars.push_back(var7);
		  auto nil = find_if(constructors.begin(), constructors.end(), [](Expr x){ return x->arity() == 2; }); 
		  expGen = mkQFla(mk<EQ>(mk<FAPP>((*is), var6, var7), mk<FAPP>((*it), mk<FAPP>((*is), var6, mk<FAPP>((*nil))), var7)), vars);
		  knowledgeScheme.insert(expGen);
		  vars.clear();
	       }
	    }
         }
      }
      //lemmas involving catamorphisms and traversals
      for (auto it = travs.begin(); it != travs.end(); it++) {
         if ((*it)->arity() == 4) {
            for (auto is = catas.begin(); is != catas.end(); is++) {
               if ((*is)->arity() == 3 && isOpX<INT_TY>((*is)->last())) {
                  //cata(trav(x, y)) = cata(x) +  cata(y)
                  Expr var1 = bind::mkConst(mkTerm<string>("_ks_qv_" + to_string(glob_ind), efac), (*it)->arg(1));
                  glob_ind++;
                  vars.push_back(var1);
                  Expr var2 = bind::mkConst(mkTerm<string>("_ks_qv_" + to_string(glob_ind), efac), (*it)->arg(1));
                  glob_ind++;
                  vars.push_back(var2);
                  expGen = mkQFla(mk<EQ>(mk<FAPP>((*is), mk<FAPP>((*it), var1, var2)), mk<PLUS>(mk<FAPP>((*is), var1), mk<FAPP>((*is), var2))), vars);
                  knowledgeScheme.insert(expGen);
		  vars.clear();
               }
            }
         }
      }
    }

    void printKnowledgeScheme(ExprSet & knowledgeScheme) {
      outs() << "  Knowledge scheme contains:\n";
      outs() << "  {\n";
      outs() << "    ==============\n";
      int i = 0;
      for (auto it = knowledgeScheme.begin(); it != knowledgeScheme.end(); it++) {
        outs() << "    | Entry [" << i << "]: " << (*it) << "\n";
	i++;
      }
      outs() << "    ==============\n";
      outs() << "  }\n";
    }

    bool proveByContradiction (Expr subgoal)
    {
      auto assumptionsTmp = assumptions;
      uniquePushConj(mkNeg(subgoal), assumptions);
      bool res = false;
      eliminateEqualities(subgoal);
      if (mergeAssumptions(1))
      {
        res = true;
        if (verbose) outs () << string(sp, ' ') << "proven by contradiction\n";
      }
      assumptions = assumptionsTmp;
      return res;
    }

    bool splitByGoal (Expr subgoal)
    {
      // heuristically pick a split (currently, one predicate)
      ExprSet dsjs;
      getDisj(subgoal, dsjs);
      if (dsjs.size() < 2) return false;

      auto spl = dsjs.end();
      for (auto it = dsjs.begin(); it != dsjs.end(); ++it)
      {
        for (auto & a : assumptions)
        {
          if (contains (a, *it))
          {
            if (isOp<ComparissonOp>(*it)) spl = it;  // try to find a comparisson
            if (*spl == NULL) spl = it;              // if none, find any
          }
        }
      }
      if (spl == dsjs.end()) spl = dsjs.begin();
      if (verbose) outs() << string(sp, ' ') << "deciding: " << **spl << "\n";

      auto rewriteHistoryTmp = rewriteHistory;
      auto rewriteSequenceTmp = rewriteSequence;
      auto assumptionsTmp = assumptions;

      uniquePushConj(mkNeg(*spl), assumptions);
      eliminateEqualities(subgoal);
      if (mergeAssumptions())
      {
        assumptions = assumptionsTmp;
        return true;
      }
      printAssumptions();

      dsjs.erase(spl);
      subgoal = disjoin(dsjs, efac);
      if (verbose) outs() << string(sp, ' ') << "current subgoal: " << *subgoal << "\n";

      if (verbose) outs () << string(sp, ' ') << "{\n";
      sp += 2;
      bool res = rewriteAssumptions(subgoal);
      sp -= 2;
      if (verbose) outs () << string(sp, ' ') << "}\n";

      rewriteHistory = rewriteHistoryTmp;
      rewriteSequence = rewriteSequenceTmp;
      assumptions = assumptionsTmp;
      if (res)
      {
        if (verbose) outs () << string(sp, ' ') << "succeeded\n";
        return true;
      }

      return false;
    }

    // potentially useful heuristic
    bool similarityHeuristic (Expr subgoal)
    {
      // heuristically pick a split: first, using disjunctions
      ExprSet cands;
      for (auto & a : assumptions)
      {
        if (isOpX<OR>(a))
        {
          ExprSet dsjs;
          getDisj(a, dsjs);
          if (dsjs.size() < 2) continue;
          auto it = dsjs.begin();
          for (; it != dsjs.end(); ++it)
          {
            if (*it == subgoal)
            {
              it = dsjs.erase(it);
              cands.insert(disjoin(dsjs, efac));
              break;
            }
          }
        }
      }
      if (cands.empty())      // then, based on matching
      {
        ExprVector args;
        filter(subgoal, bind::IsConst (), inserter(args, args.begin()));
        for (auto & a : assumptions)
        {
          if (isOpX<FORALL>(a)) continue;

          ExprMap matching;
          if (findMatching (subgoal, a, args, matching))
          {
            ExprSet eqs;
            for (auto & m : matching)
              if (m.first != m.second)
                eqs.insert(mk<EQ>(m.first, m.second));
            cands.insert(mkNeg(conjoin(eqs, efac)));
          }
        }
        if (cands.empty()) return false;
      }

      bool changed = false;
      for (auto & c : cands)
      {
        bool redund = false;
        for (auto & a : assumptions)
        {
          if (isOpX<FORALL>(a)) continue;
          if (u.implies(a, c))
          {
            redund = true;
            break;
          }
        }
        if (redund) continue;
        uniquePushConj(c, assumptions);
        changed = true;
      }
      if (!changed) return false;

      if (mergeAssumptions())
      {
        return true;
      }
      printAssumptions();

      if (verbose) outs () << string(sp, ' ') << "current subgoal: " << *subgoal << "\n";
      if (verbose) outs () << string(sp, ' ') << "{\n";
      sp += 2;
      bool res = rewriteAssumptions(subgoal);
      sp -= 2;
      if (verbose) outs () << string(sp, ' ') << "}\n";

      return res;
    }

    bool splitDisjAssumptions (Expr subgoal)
    {
      // more like a brute force splitting
      set<ExprSet> cands;
      map<ExprSet, Expr> origAssms;
      for (auto it = assumptions.begin(); it != assumptions.end(); )
      {
        Expr a = *it;
        if (find (blockedAssms.begin(), blockedAssms.end(), *it) != blockedAssms.end())
        {
          it = assumptions.erase(it);
          continue;
        }
        if (isOpX<ITE>(a))
        {
          a = mk<OR>(mk<AND>(a->left(), a->right()),
                     mk<AND>(mkNeg(a->left()), a->last()));
        }
        a = simplifyBool(simplifyArr(a));
        if (isOpX<OR>(a))
        {
          ExprSet dsjs;
          getDisj(a, dsjs);
          if (dsjs.size() < 2) continue;
          cands.insert(dsjs);
          origAssms[dsjs] = *it;
        }
        ++it;
      }

      if (cands.empty()) return false;
      ExprSet spl = *cands.begin();

      if (spl.empty()) return false;

      blockedAssms.push_back(origAssms[spl]);

      int part = 1;
      bool res = true;

      auto subgoalTmp = subgoal;
      auto assumptionsTmp = assumptions;
      auto rewriteHistoryTmp = rewriteHistory;
      auto rewriteSequenceTmp = rewriteSequence;

      for (auto & s : spl)
      {
        if (verbose) outs () << string(sp, ' ') << "split for (part " << part << "/"
            << spl.size()<< "): " << *s << "\n" << string(sp, ' ') << "{\n";
        sp += 2;
        part++;

        uniquePushConj(s, assumptions);
        eliminateEqualities(subgoal);
        if (mergeAssumptions())
        {
          assumptions = assumptionsTmp;
          sp -= 2;
          if (verbose) outs () << string(sp, ' ') << "}\n";
          continue;
        }
        for (auto it = assumptions.begin(); it != assumptions.end(); ++it)
        {
          if (origAssms[spl] == *it)
          {
            assumptions.erase(it);
            break;
          }
        }
        printAssumptions();

        res = rewriteAssumptions(subgoal);
        sp -= 2;
        if (verbose) outs () << string(sp, ' ') << "}\n";

        rewriteHistory = rewriteHistoryTmp;
        rewriteSequence = rewriteSequenceTmp;
        assumptions = assumptionsTmp;
        subgoal = subgoalTmp;
        if (!res) break;
      }

      blockedAssms.pop_back();
      if (res)
      {
        if (verbose) outs () << string(sp, ' ') << "splitting succeeded\n";
        return true;
      }
      else
      {
        if (verbose) outs () << string(sp, ' ') << "unable to succeed\n";
        return false;
      }
    }

    // preprocessing of the main goal
    void unfoldGoal()
    {
      ExprVector goalArgs;
      Expr unfoldedGoalQF = goal->last();
      bool toRebuild = false;
      for (int i = 0; i < goal->arity() - 1; i++)
      {
        //   - classify constructors for all ADTs that appear in the goal
        Expr type = goal->arg(i)->last();
        for (auto & a : constructors)
        {
          if (a->last() == type)
          {
            bool ind = false;
            for (int i = 0; i < a->arity() - 1; i++)
            {
              if (a->last() == a->arg(i))
              {
                ind = true;
                if (indConstructors[type] != NULL && indConstructors[type] != a)
                {
                  outs () << "Several inductive constructors are not supported\n";
                  exit(1);
                }
                indConstructors[type] = a;
              }
            }
            if (!ind)
            {
              if (baseConstructors[type] != NULL && baseConstructors[type] != a)
              {
                outs () << "Several base constructors are not supported\n";
                exit(1);
              }
              baseConstructors[type] = a;
              baseconstrapps.push_back(fapp(a));
            }
          }
        }

        //   - replace all non-inductive ADTs
        if (baseConstructors[type] != NULL && indConstructors[type] == NULL)
        {
          toRebuild = true;
          ExprVector args;
          args.push_back(baseConstructors[type]);
          for (int i = 1; i < baseConstructors[type]->arity() - 1; i++)
          {
            // TODO: make sure the name is unique
            Expr s = bind::mkConst(mkTerm<string>
                         ("_b_" + to_string(glob_ind++), efac),
                         baseConstructors[type]->arg(i));
            goalArgs.push_back(s->last());
            args.push_back(s);
          }
          Expr newApp = mknary<FAPP>(args);
          unfoldedGoalQF = replaceAll(unfoldedGoalQF, bind::fapp(goal->arg(i)), newApp);
        }
        else
        {
          goalArgs.push_back(goal->arg(i));
        }
      }

      // classify functions; TODO: avoid repetitions

      map<Expr, int> occs;
      getCommonSubterms(conjoin(assumptions, efac), occs);
      ExprSet funs;
      for (auto & m : occs)
        if (isOpX<FAPP>(m.first) && m.first->left()->arity() > 2 &&
          find(constructors.begin(), constructors.end(), m.first->left()) == constructors.end())
            funs.insert(m.first->left());

      for (auto & f : funs)
      {
        ExprVector assmsWith;
        for (auto & a : assumptions)
          if (contains(a, f))
            assmsWith.push_back(a);

        if (assmsWith.size() != 1) continue;
        // replace all non-recursive functions

        ExprVector result;
        if (useAssumption(unfoldedGoalQF, assmsWith[0], result, true))
        {
          unfoldedGoalQF = result[0];
          toRebuild = true;
        }
      }

      if (toRebuild)
      {
        goalArgs.push_back(unfoldedGoalQF);
        goal = mknary<FORALL>(goalArgs);

        // continue recursively, because newly introduced vars/funs may again need unfolding
        unfoldGoal();
      }
    }

    // and to enable searching for RHS of assumptions
    void insertSymmetricAssumption(Expr assm)
    {
      if (isOpX<EQ>(assm))
      {
        assumptions.push_back(mk<EQ>(assm->right(), assm->left()));
      }
      else if (isOpX<FORALL>(assm) && isOpX<EQ>(assm->last()))
      {
        ExprVector args;
        for (int i = 0; i < assm->arity() - 1; i++) args.push_back(assm->arg(i));
        args.push_back(mk<EQ>(assm->last()->right(), assm->last()->left()));
        assumptions.push_back(mknary<FORALL>(args));
      }
    }

    void printAssumptions()
    {
      if (!verbose) return;
      outs () << string(sp, ' ') << "{\n";
      outs () << string(sp+2, ' ') << string(20, '=') << "\n";
      for (int i = 0; i < assumptions.size(); i++)
      {
        outs () << string(sp+2, ' ') << "| Assumptions [" << i << "]: ";
        pprint(assumptions[i]);
      }
      outs () << string(sp+2, ' ') << string(20, '=') << "\n";
      outs () << string(sp, ' ') << "}\n";
    }

    bool induction(int num)
    {
      assert(num < goal->arity() - 1);
      Expr typeDecl = goal->arg(num);
      Expr type = goal->arg(num)->last();

      Expr baseConstructor = baseConstructors[type];
      Expr indConstructor = indConstructors[type];

      // instantiate every quantified variable (except the inductive one) in the goal
      Expr goalQF = goal->last();
      for (int i = 0; i < goal->arity() - 1; i++)
      {
        if (i == num) continue;
        // TODO: make sure the name is unique
        Expr s = bind::mkConst(mkTerm<string> ("_v_" + to_string(glob_ind), efac), goal->arg(i)->last());
        glob_ind++;
        goalQF = replaceAll(goalQF, bind::fapp(goal->arg(i)), s);
      }

      // prove the base case
      Expr baseSubgoal = replaceAll(goalQF, typeDecl, baseConstructor);
      ExprVector assumptionsTmp = assumptions;
      if (isOpX<IMPL>(baseSubgoal))
      {
        assumptions.push_back(baseSubgoal->left());
        baseSubgoal = baseSubgoal->right();
      }

      if (verbose)
      {
        outs() << "\nBase case:       ";
        pprint(baseSubgoal);
        outs() << "\n{\n";
      }

      tribool baseres = simpleSMTcheck(baseSubgoal);
      if (baseres)
      {
        if (verbose) outs() << "  proven trivially\n";
      }
      else
      {
        eliminateEqualities(baseSubgoal);
        if (mergeAssumptions())
        {
          if (verbose) outs() << "  proven trivially\n";
          baseres = true;
          assumptions = assumptionsTmp;
        }
        else
        {
          splitAssumptions();
          printAssumptions();

          rewriteHistory.clear();
          rewriteSequence.clear();

          baseres = rewriteAssumptions(baseSubgoal);
        }
      }

      if (verbose) outs () << "}\n";
      if (!baseres) baseres = doCaseSplitting(baseSubgoal);
      if (!baseres) return false;

      if (!assumptionsTmp.empty()) assumptions = assumptionsTmp;

      // generate inductive hypotheses
      ExprVector args;
      ExprVector indHypotheses;
      bool allQF = true;
      for (int i = 1; i < indConstructor->arity() - 1; i++)
      {
        // TODO: make sure the name is unique
        Expr s;
        Expr singleCons = NULL;
        for (auto & a : constructors)
        {
          if (a->last() == indConstructor->arg(i))
          {
            if (singleCons != NULL)
            {
              singleCons = NULL;
              break;
            }
            singleCons = a;
          }
        }
        if (singleCons != NULL)
        {
          // unfold definitions, if possible
          ExprVector argsCons;
          for (int j = 1; j < singleCons->arity() - 1; j++)
          {
            argsCons.push_back(bind::mkConst(mkTerm<string> ("_t_" + to_string(glob_ind), efac), singleCons->arg(j)));
            glob_ind++;
          }
          s = bind::fapp (singleCons, argsCons);
        }
        else
        {
          s = bind::mkConst(mkTerm<string> ("_t_" + to_string(glob_ind), efac), indConstructor->arg(i));
          glob_ind++;
        }

        args.push_back(s);

        if (type == indConstructor->arg(i)) // type check
        {
          ExprVector argsIH;
          for (int j = 0; j < goal->arity() - 1; j++)
          {
            if (j != num) argsIH.push_back(goal->arg(j));
          }
          argsIH.push_back(replaceAll(goal->last(), bind::fapp(typeDecl), s));
          if (argsIH.size() == 1)
          {
            indHypotheses.push_back(argsIH.back());
          }
          else
          {
            allQF = false;
            indHypotheses.push_back(mknary<FORALL>(argsIH));
          }
        }
      }
      for (auto & a : indHypotheses)
      {
        assumptions.push_back(a);
        // always add symmetric IH?
        insertSymmetricAssumption(a);
      }
      // prove the inductive step
      Expr indConsApp = bind::fapp(indConstructor, args);
      Expr indSubgoal = replaceAll(goalQF, bind::fapp(typeDecl), indConsApp);

      if (isOpX<IMPL>(indSubgoal))
      {
        assumptions.push_back(indSubgoal->left());
        indSubgoal = indSubgoal->right();
      }

      eliminateEqualities(indSubgoal);
      if (mergeAssumptions()) return true;
      splitAssumptions();
      if (verbose)
      {
        outs() << "\nInductive step:       ";
        pprint(indSubgoal);
        outs() << "\n{\n";
      }

      rewriteHistory.clear();
      rewriteSequence.clear();

      tribool indres = simpleSMTcheck(indSubgoal);
      if (indres)
      {
        if (verbose) outs() << "  proven trivially\n}\n";
        return true;
      }
      else
      {
        printAssumptions();
        indres = rewriteAssumptions(indSubgoal);
        if (indres)
        {
          if (verbose) outs () << "}\n";
          return true;
        }
      }
      // last resort so far
      return doCaseSplitting(indSubgoal);
    }

    bool doCaseSplitting(Expr goal)
    {
      for (int i = 0; i < assumptions.size(); i++)
      {
        Expr pre;
        auto a = assumptions[i];
        if (isOpX<FORALL>(a) && isOpX<IMPL>(a->last()))
        {
          ExprSet pres;
          getConj(a->last()->left(), pres);

          ExprVector varz;
          for (int i = 0; i < a->arity() - 1; i++) varz.push_back(bind::fapp(a->arg(i)));

          for (auto & p : pres)
          {
            if (emptyIntersect(p, varz))
            {
              pre = p;
              break;
            }
          }
        }

        if (isOpX<IMPL>(a)) pre = a->left();

        if (pre != NULL)
        {
          // GF: to support if isOpX<EQ>(pre) = true.
          Expr d = destructDiseq(pre);
          if (d != NULL)
          {
            assert(isOpX<EQ>(d));
            if (verbose) outs () << string(sp, ' ') << "case splitting for " << *d->left() << ":\n";
            if (verbose) outs () << string(sp, ' ') << "case " << *d << "\n" << string(sp, ' ') << "{\n";
            auto assumptionsTmp = assumptions;
            auto rewriteHistoryTmp = rewriteHistory;
            auto rewriteSequenceTmp = rewriteSequence;
            auto goalTmp = goal;

            goal = replaceAll(goal, d->left(), d->right());
            for (int j = 0; j < assumptions.size(); j++)
            {
              assumptions[j] = simplifyBool(replaceAll(assumptions[j], pre, mk<TRUE>(efac)));
              assumptions[j] = replaceAll(assumptions[j], d->left(), d->right());
            }

            eliminateEqualities(goal);
            mergeAssumptions(1);
            sp += 2;
            printAssumptions();
            if (verbose) outs () << string(sp, ' ') << "current subgoal: " << *goal << "\n";
            bool partiallyDone = rewriteAssumptions(goal);
            sp -= 2;

            assumptions = assumptionsTmp;
            rewriteHistory = rewriteHistoryTmp;
            rewriteSequence = rewriteSequenceTmp;
            goal = goalTmp;

            if (!partiallyDone) continue;
            if (verbose) outs() << string(sp, ' ') << "}\n";

            pre = mkNeg(pre);
            assert(isOpX<EQ>(pre) && pre->left() == d->left());
            if (verbose) outs () << string(sp, ' ') << "case " << *pre << "\n" << string(sp, ' ') << "{\n";

            goal = replaceAll(goal, pre->left(), pre->right());
            for (int j = 0; j < assumptions.size(); j++)
            {
              assumptions[j] = simplifyBool(replaceAll(assumptions[j], pre, mk<TRUE>(efac)));
              assumptions[j] = replaceAll(assumptions[j], pre->left(), pre->right());
            }
            eliminateEqualities(goal);
            mergeAssumptions(1);
            sp += 2;
            printAssumptions();
            if (verbose) outs () << string(sp, ' ') << "current subgoal: " << *goal << "\n";
            bool done = rewriteAssumptions(goal);
            sp -= 2;

            assumptions = assumptionsTmp;
            rewriteHistory = rewriteHistoryTmp;
            rewriteSequence = rewriteSequenceTmp;

            if (done)
            {
              if (verbose) outs() << string(sp, ' ') << "\n}\n";
              return true;
            }
          }
        }
      }
      return false;
    }

    Expr destructDiseq(Expr e)
    {
      if (isOpX<NEG>(e))
      {
        e = mkNeg(e->left());
      }
      if (isOp<NEQ>(e))
      {
        Expr ty;
        if (bind::isAdtConst(e->left()))
        {
          ty = e->left()->last()->last();
        }
        else if (bind::isAdtConst(e->right()))
        {
          ty = e->right()->last()->last();
        }

        if (ty == NULL) return NULL;

        Expr t;
        if (e->right()->last() == baseConstructors[ty])
        {
          t = e->left();
        }
        else if (e->left()->last() == baseConstructors[ty])
        {
          t = e->right();
        }

        Expr indConstructor = indConstructors[ty];
        ExprVector args;
        for (int i = 1; i < indConstructor->arity() - 1; i++)
        {
          // TODO: make sure the name is unique
          Expr s = bind::mkConst(mkTerm<string> ("_t_" + to_string(glob_ind), efac), indConstructor->arg(i));
          glob_ind++;
          args.push_back(s);
        }
        Expr indConsApp = bind::fapp(indConstructor, args);
        return mk<EQ>(t, indConsApp);
      }

      return NULL;
    }

    tribool solveNoind(int do_rewrite = true, int rounds = 2)
    {
      if (do_rewrite)
      {
        if (simpleSMTcheck(goal))
        {
          if (verbose) outs () << "Proved (with Z3)\n";
          return true;
        }
        splitAssumptions();
        eliminateEqualities(goal);
        auto assumptionsTmp = assumptions;
        mergeAssumptions(rounds);
        eliminateEqualities(goal);
        printAssumptions();
        if (verbose) outs () << "=====\n" << *goal << "\n\n\n";
        if (rewriteAssumptions(goal))
        {
          if (verbose) outs () << "\nProved\n";
          return true;
        }
        // revert and try induction:
        assumptions = assumptionsTmp;
      }

      ExprSet qFreeAssms;
      for (auto it = assumptions.begin(); it != assumptions.end(); )
      {
        if (!isOpX<FORALL>(*it))
        {
          if (isOpX<EQ>(*it) || isOpX<NEQ>(*it) || isOpX<FAPP>(*it) || isOpX<NEG>(*it) || isOpX<SELECT>(*it)) // super big hack
            qFreeAssms.insert(*it);

          it = assumptions.erase(it);
        }
        else ++it;
      }

      if (verbose) outs () << "\nProving by induction\n";
      goal = createQuantifiedFormula(mk<IMPL>(conjoin(qFreeAssms, efac), goal), constructors);
      if (isOpX<FORALL>(goal)) return solve();
      else return false;
    }

    tribool solve()
    {
      Expr goalPre = goal;
      for (int i = 0; i < 5; i++)
      {
        unfoldGoal();
        if (simplifyGoal())
        {
          if (verbose) outs () << "Trivially Proved\n";
          return true;
        }
        if (goalPre == goal) break;
        goalPre = goal;
      }
      rewriteHistory.push_back(goal);

      if (verbose)
      {
        outs () << "Simplified goal: ";
        pprint(goal);
      }

      for (int i = 0; i < goal->arity() - 1; i++)
      {
        Expr type = goal->arg(i)->last();
        if (baseConstructors[type] != NULL && indConstructors[type] != NULL)
        {
          if (induction(i))
          {
            if (verbose) outs () << "\nProved\n";
            return true;
          }
        }
      }
      tribool res = simpleSMTcheck(goal);
      if (verbose)
      {
        if (res) outs () << "Proved (with Z3)\n";
        else return indeterminate;
      }
      return res;
    }

    tribool simpleSMTcheck(Expr goal)
    {
      if (!useZ3) return false;
      return u.implies(conjoin(assumptions, efac), goal);
    }
  };

  //s is the content of the file
  void adtSolve(EZ3& z3, Expr s, int maxDepth,
                int maxGrow, int mergingIts, int earlySplit, bool verbose, int useZ3, bool useKS, int to)
  {
    ExprVector constructors;
    for (auto & a : z3.getAdtConstructors()) constructors.push_back(regularizeQF(a));

    ExprVector assumptions;
    Expr goal;
    //s is split into its conjuncts
    ExprSet cnjs;
    getConj(s, cnjs);
    for (auto c : cnjs)
    {
      bool possibleGoal = false;
      if (isOpX<NEG>(c) || isOpX<EXISTS>(c))
        possibleGoal = true;

      if (possibleGoal)
      {
        if (goal != NULL)
        {
          errs() << "WARNING: two (or more) asserts that qualify to be a goal."
                 << "\nUsing one of those.\n";
          if (isOpX<FORALL>(goal)) possibleGoal = false;
        }
      }

      if (possibleGoal)
        goal = regularizeQF(mkNeg(c));
      else
        assumptions.push_back(regularizeQF(c));
    }

    if (goal == NULL)
    {
      outs () << "Unable to detect the goal\n";
      return;
    }
    //assumptions here contain only data from file
    ADTSolver sol (goal, assumptions, constructors, 0, 0, maxDepth, maxGrow, mergingIts, earlySplit, verbose, useZ3, useKS, to);
    tribool res = isOpX<FORALL>(goal) ? sol.solve() : sol.solveNoind();
    /*outs () << "Final list of assumptions is\n";
    sol.printAssumptions();*/
    outs () << (res ? "unsat\n" : (!res ? "sat\n" : "unknown\n"));
  }
}

//read SMTlib docs about define-fun-rec
//definition/lemma annotations can workaround z3's failure

#endif
