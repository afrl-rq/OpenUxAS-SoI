//===- Hello.cpp - Example code from "Writing an LLVM Pass" ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements two versions of the LLVM "Hello World" pass described
// in docs/WritingAnLLVMPass.html
//
//===----------------------------------------------------------------------===//

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
using namespace llvm;

#define DEBUG_TYPE "uxas"

STATISTIC(UxasCounter, "Counts number of functions greeted");

namespace {
  // Uxas - The first implementation, without getAnalysisUsage.
  struct Uxas : public FunctionPass {
    static char ID; // Pass identification, replacement for typeid
    Uxas() : FunctionPass(ID) {}

    bool runOnFunction(Function &F) override {
      ++UxasCounter;

      //-- ignore non-configure
      if(!F.getName().contains("configure")) return false;
      
      errs() << "Uxas: ";
      errs().write_escaped(F.getName()) << '\n';

      errs() << "============ SUBSCRIBES TO ============\n";
      
      //-- iterate over all basic blocks
      for(const auto &bb : F.getBasicBlockList()) {
        //-- iterate over statements
        for(const auto &ins : bb.getInstList()) {
          if(auto *II = dyn_cast<const InvokeInst>(&ins)) {
            const Function *cf = II->getCalledFunction();
            if(!cf->getName().contains("addSubscriptionAddress")) continue;            
            //errs() << F.getName() << " === invokes ==> " << cf->getName() << '\n';
            errs() << F.getName() << " === subscribes ==> " << II->getArgOperand(1)->getName() << '\n';
          }          
        }
      }
      
      return false;
    }
  };
}

char Uxas::ID = 0;
static RegisterPass<Uxas> X("uxas", "Uxas Pass");
