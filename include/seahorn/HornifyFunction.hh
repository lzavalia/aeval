#ifndef __HORNIFY_FUNCTION__HH_
#define __HORNIFY_FUNCTION__HH_

#include "seahorn/HornifyModule.hh"
#include "llvm/IR/Function.h"

#include "ufo/Expr.hpp"
#include "ufo/Smt/EZ3.hh"
#include "seahorn/UfoSymExec.hh"
#include "seahorn/LiveSymbols.hh"

/// Constructs Horn clauses for a single function

namespace{

    inline const llvm::BasicBlock* findErrorBlock (const llvm::Function &F)
    {
      for (const llvm::BasicBlock& bb : F)
        if (llvm::isa<llvm::ReturnInst> (bb.getTerminator ())) return &bb;
      return NULL;
    }

}

namespace seahorn
{
  using namespace expr;
  using namespace llvm;
  using namespace ufo;

  class HornifyFunction
  {
  protected:
    HornifyModule &m_parent;
    
    SmallStepSymExec &m_sem;
    ZFixedPoint<EZ3> &m_fp;
    EZ3 &m_zctx;
    ExprFactory &m_efac;
    
    /// whether encoding is inter-procedural (i.e., with summaries)
    bool m_interproc;
    

    void extractFunctionInfo (const BasicBlock &BB);
  public:
    HornifyFunction (HornifyModule &parent, bool interproc = false) :
      m_parent (parent), m_sem (m_parent.symExec ()), 
      m_fp (m_parent.getZFixedPoint ()), m_zctx (m_fp.getContext ()),
      m_efac (m_zctx.getExprFactory ()), m_interproc (interproc) {}

    virtual ~HornifyFunction () {}
    ZFixedPoint<EZ3> &getZFixedPoint () {return m_fp;}
    virtual void runOnFunction (Function &F) = 0;
    bool checkProperty(ExprVector prop, Expr &inv);
  };

  class SmallHornifyFunction : public HornifyFunction
  {


  public:
    SmallHornifyFunction (HornifyModule &parent, 
                          bool interproc = false) : 
      HornifyFunction (parent, interproc) {}
    
    virtual void runOnFunction (Function &F);
  } ;
  

  class LargeHornifyFunction : public HornifyFunction
  {
  public:
    LargeHornifyFunction (HornifyModule &parent, 
                          bool interproc = false) : 
      HornifyFunction (parent, interproc) {}
    
    virtual void runOnFunction (Function &F);
  };

}



#endif
