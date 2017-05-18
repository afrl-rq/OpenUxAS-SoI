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

#include <cxxabi.h>
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

    //-- return the class name given a method of the class
    StringRef getClassName(Function &F)
    {
      auto pt = dyn_cast<PointerType>(F.getFunctionType()->getParamType(0));
      assert(pt);
      auto st = dyn_cast<StructType>(pt->getElementType());
      assert(st);
      //-- the name always starts with "class.", so get rid of that
      return st->getName().substr(6);
    }

    //-- return demangled name
    std::string demangle(const StringRef &mangled)
    {
      int status = 0;
      std::string res(abi::__cxa_demangle(mangled.data(), 0, 0, &status));
      return res.substr(0, res.find('['));
    }

    bool runOnFunction(Function &F) override {
      ++UxasCounter;

      //-- ignore non-configure
      if(!F.getName().contains("configure")) return false;
      
      //errs() << "Uxas: ";
      //errs().write_escaped(F.getName()) << '\n';

      errs() << "---------------------------------------------------------------------------------\n";
      errs() << "service : " << getClassName(F);
      
      errs() << " === SUBSCRIBES TO ===>\n";
      
      //-- iterate over all basic blocks
      for(const auto &bb : F.getBasicBlockList()) {
        //-- iterate over statements
        for(const auto &ins : bb.getInstList()) {
          if(auto *II = dyn_cast<const InvokeInst>(&ins)) {
            const Function *cf = II->getCalledFunction();
            if(!cf->getName().contains("addSubscriptionAddress")) continue;            

            //-- the first argument to a method call is always the
            //-- this pointer. so get the second argument.
            auto *arg = II->getArgOperand(1);

            if(auto *Const = dyn_cast<Constant>(arg))            
              errs() << '\t' << demangle(Const->getName()) << '\n';
            else if(auto *II = dyn_cast<InvokeInst>(arg)) {
              errs() << '\t' << demangle(II->getCalledFunction()->getName()) << "()\n";
            } else assert(0);
          }          
        }
      }
      
      return false;
    }
  };
}

char Uxas::ID = 0;
static RegisterPass<Uxas> X("uxas", "Uxas Pass");
