#include "seahorn/Transforms/PromoteVerifierCalls.hh"
#include "llvm/Support/CallSite.h"
#include "llvm/Support/InstIterator.h"

#include "llvm/IR/IRBuilder.h"

#include "boost/range.hpp"
#include "llvm/Support/raw_ostream.h"

#include "avy/AvyDebug.h"

#include "llvm/Analysis/CallGraph.h"
using namespace llvm;

namespace seahorn
{
  char PromoteVerifierCalls::ID = 0;
  
  bool PromoteVerifierCalls::runOnModule (Module &M)
  {
    LOG ("pvc", errs () << "Running promote-verifier-calls pass\n";);
    
    
    
    LLVMContext &Context = M.getContext ();
    
    AttrBuilder B;
    
    AttributeSet as = AttributeSet::get (Context, 
                                        AttributeSet::FunctionIndex,
                                        B);
    
    m_assumeFn = dyn_cast<Function>
      (M.getOrInsertFunction ("verifier.assume", 
                              as,
                              Type::getVoidTy (Context),
                              Type::getInt1Ty (Context),
                              NULL));
    
    m_assertFn = dyn_cast<Function> 
      (M.getOrInsertFunction ("verifier.assert",
                              as,
                              Type::getVoidTy (Context),
                              Type::getInt1Ty (Context),
                              NULL));
   
    B.addAttribute (Attribute::NoReturn);
    B.addAttribute (Attribute::ReadNone);
    
    as = AttributeSet::get (Context, 
                           AttributeSet::FunctionIndex, B);
    m_errorFn = dyn_cast<Function>
      (M.getOrInsertFunction ("verifier.error",
                              as,
                              Type::getVoidTy (Context), NULL));
    
    CallGraph *cg = getAnalysisIfAvailable<CallGraph> ();
    if (cg)
    {
      cg->getOrInsertFunction (m_assumeFn);
      cg->getOrInsertFunction (m_assertFn);
      cg->getOrInsertFunction (m_errorFn);
    }
    
    for (auto &F : M) runOnFunction (F);
    return true;
  }
  
  bool PromoteVerifierCalls::runOnFunction (Function &F)
  {
    CallGraph* cg = getAnalysisIfAvailable<CallGraph> ();
    
    SmallVector<Instruction*, 16> toKill;
    
    bool Changed = false;
    for (auto &I : boost::make_iterator_range (inst_begin(F), inst_end (F)))
    {
      if (!isa<CallInst> (&I)) continue;
      CallSite CS (&I);
      
      const Function *fn = CS.getCalledFunction ();
      if (fn && (fn->getName ().equals ("__VERIFIER_assume") || 
                 fn->getName ().equals ("DISABLED__VERIFIER_assert")))
      {
        Function *nfn;
        if (fn->getName ().equals ("__VERIFIER_assume")) nfn = m_assumeFn;
        else if (fn->getName().equals ("__VERIFIER_assert")) nfn = m_assertFn;
        else continue;
        
        Value *cond = CS.getArgument (0);
        
        // strip zext if there is one
        if (const ZExtInst *ze = dyn_cast<const ZExtInst> (cond))
          cond = ze->getOperand (0);
        
        IRBuilder<> Builder (F.getContext ());
        Builder.SetInsertPoint (&I);
        
        // -- convert to Boolean if needed
        if (!cond->getType ()->isIntegerTy (1))
          cond = Builder.CreateICmpNE (cond,
                                       ConstantInt::get (cond->getType (), 0));
        
        CallInst *ci = Builder.CreateCall (nfn, cond);
        if (cg)
          (*cg)[&F]->addCalledFunction (CallSite (ci),
                                        (*cg)[ci->getCalledFunction ()]);
        
        toKill.push_back (&I);
      }
      else if (fn && fn->getName ().equals ("__VERIFIER_error"))
      {
        IRBuilder<> Builder (F.getContext ());
        Builder.SetInsertPoint (&I);
        CallInst *ci = Builder.CreateCall (m_errorFn);
        if (cg)
          (*cg)[&F]->addCalledFunction (CallSite (ci),
                                        (*cg)[ci->getCalledFunction ()]);
        
        toKill.push_back (&I);
      }
    }
    
    for (auto *I : toKill) I->eraseFromParent ();
    
    return Changed;
  }
  
  void PromoteVerifierCalls::getAnalysisUsage (AnalysisUsage &AU) const 
  {AU.setPreservesAll ();}
  
}

static llvm::RegisterPass<seahorn::PromoteVerifierCalls> 
X ("promote-verifier", "Promote all verifier related function");

