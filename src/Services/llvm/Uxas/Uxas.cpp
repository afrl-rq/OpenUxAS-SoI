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

#include <set>
#include <cxxabi.h>
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
using namespace llvm;

#define DEBUG_TYPE "uxas"

//STATISTIC(UxasCounter, "Counts number of functions greeted");

namespace {
  // Uxas - The first implementation, without getAnalysisUsage.
  struct Uxas : public ModulePass {
    static char ID; // Pass identification, replacement for typeid
    Uxas() : ModulePass(ID) {}

    //-- name of the service class being analyzed
    StringRef serviceName;

    //-- set of pubs extracted
    std::set<std::string> allPubs;
    
    //-- set of subs extracted
    std::set<std::string> allSubs;
    
    /*****************************************************************/
    //-- return the class name given a method of the class. if F does
    //-- not belong to a class return an empty string as name.
    /*****************************************************************/
    StringRef getClassName(Function &F)
    {
      if(F.getFunctionType()->getNumParams()) {
        if(auto pt = dyn_cast<PointerType>(F.getFunctionType()->getParamType(0))) {
          if(auto *st = dyn_cast<StructType>(pt->getElementType()))
            //-- the name always starts with "class.", so get rid of that
            return st->getName().substr(6);
        }
      }

      return "";
    }

    /*****************************************************************/
    //-- return demangled name
    /*****************************************************************/
    std::string demangle(const StringRef &mangled)
    {
      int status = 0;
      std::string res(abi::__cxa_demangle(mangled.data(), 0, 0, &status));
      return res.substr(0, res.find('['));
    }

    /*****************************************************************/
    //-- extract all messages that function F subscribes to
    /*****************************************************************/
    void extractSubs(Function &F)
    {
      StringRef className = getClassName(F);
      if(className == "") return;
      
      //-- iterate over all basic blocks
      for(const auto &bb : F.getBasicBlockList()) {
        //-- iterate over statements
        for(const auto &ins : bb.getInstList()) {
          Function *cf = NULL;
          Value *arg = NULL;
          
          //-- extract called function and argument. the first
          //-- argument to a method call is always the this
          //-- pointer. so get the second argument.
          if(auto *II = dyn_cast<const InvokeInst>(&ins)) {
            cf = II->getCalledFunction();
            if(II->getNumArgOperands() > 1) arg = II->getArgOperand(1);
          } else if(auto *CI = dyn_cast<const CallInst>(&ins)) {
            cf = CI->getCalledFunction();
            if(CI->getNumArgOperands() > 1) arg = CI->getArgOperand(1);
          }
          
          if(cf == NULL || !cf->getName().contains("addSubscriptionAddress")) continue;
          assert(arg);

          //errs() << "found potential sub: " << ins << '\n';
          
          if(auto *Const = dyn_cast<Constant>(arg))
            allSubs.insert(demangle(Const->getName()));
          else if(auto *II = dyn_cast<InvokeInst>(arg)) {
            allSubs.insert(demangle(II->getCalledFunction()->getName()) + "()");
          }
        }
      }
    }

    /*****************************************************************/
    //-- find all users of a value recursively
    /*****************************************************************/
    std::set<Value*> allUsers(Value *v)
    {
      std::set<Value*> res;
      bool repeat = true;
      while(repeat) {
        repeat = false;
        for(auto u : v->users()) {
          if(Value *v = dyn_cast<Value>(u))
            if(res.insert(v).second) repeat = true;
        }
      }
      return res;
    }
    
    /*****************************************************************/
    //-- extract all messages that function F publishes
    /*****************************************************************/
    void extractPubs(Function &F)
    {
      StringRef className = getClassName(F);
      if(className != serviceName) return;

      //-- iterate over all basic blocks
      for(const auto &bb : F.getBasicBlockList()) {
        //-- iterate over statements
        for(const auto &ins : bb.getInstList()) {
          if(auto *II = dyn_cast<const InvokeInst>(&ins)) {
            const Function *cf = II->getCalledFunction();
            if(cf == NULL) continue;

            //-- get the argument that corresponds to the message
            //-- being sent
            Value *arg = NULL;
            if(cf->getName().contains("sendSharedLmcpObjectBroadcastMessage"))
              arg = II->getArgOperand(1);
            else if(cf->getName().contains("sendSharedLmcpObjectLimitedCastMessage"))
              arg = II->getArgOperand(2);
            if(!arg) continue;

            //errs() << "found potential pub: " << *II << '\n';

            //-- the first argument to a method call is always the
            //-- this pointer. so get the second argument.
            for(auto u : allUsers(arg)) {
              //errs() << "user " << *u << '\n';
              if(auto *CI = dyn_cast<CallInst>(u)) {
                if(Function *CF = CI->getCalledFunction()) {
                  if(CF->getName().contains("static_pointer_cast")) {
                    std::string dn = demangle(CF->getName());
                    size_t pos1 = dn.find(',');
                    if(pos1 == std::string::npos) continue;
                    size_t pos2 = dn.find('>', pos1);
                    if(pos2 == std::string::npos) continue;
                    allPubs.insert(dn.substr(pos1+2, pos2-pos1-2));
                  }
                  else if(CF->getName().contains("shared_ptr")) {
                    std::string dn = demangle(CF->getName());
                    size_t pos1 = dn.find("shared_ptr<");
                    if(pos1 == std::string::npos) continue;

                    pos1 = dn.find("shared_ptr<", pos1+1);
                    if(pos1 == std::string::npos) continue;

                    pos1 = dn.find("shared_ptr<", pos1+1);
                    if(pos1 == std::string::npos) continue;

                    size_t pos2 = dn.find('>', pos1);
                    if(pos2 == std::string::npos) continue;
                    allPubs.insert(dn.substr(pos1+11, pos2-pos1-11));
                  }
                }
              }
            }
            
            /*
            assert(isa<AllocaInst>(arg));
            auto *ai = dyn_cast<AllocaInst>(arg);
            errs() << *(ai->getAllocatedType()) << '\n';

            
            auto *type = arg->getType();
            assert(type);            
            errs() << *type << '\n';
            auto *pt = dyn_cast<PointerType>(type);
            assert(pt);
            auto *et = pt->getElementType();
            errs() << *et << '\n';
            assert(isa<StructType>(et));
            auto *st = dyn_cast<StructType>(et);
            for(auto *t : st->elements()) {
              errs() << *t << '\n';
            }
            */
          }          
        }
      }
    }

    /*****************************************************************/
    //-- the top level method
    /*****************************************************************/
    bool runOnModule(Module &M) override
    {
      //-- first get the name of the service class by looking for the
      //-- configure method and seeing which class it belongs to. also
      //-- process the configure method to extract the sub
      //-- information.
      for(Function &F : M.getFunctionList()) {
        if(!F.getName().contains("configure")) continue;
        StringRef className = getClassName(F);
        if(className == "") continue;
        serviceName = className;
        errs() << "got service name " << serviceName << '\n';
        extractSubs(F);
        break;
      }
      
      //-- now extract the pub information
      for(Function &F : M.getFunctionList()) {
        if(!F.getName().contains("configure")) extractPubs(F);
      }

      //-- print sub information
      errs() << "---------------------------------------------------------------------------------\n";
      errs() << "service : " << serviceName << " === SUBSCRIBES TO ===>\n";
      for(const auto &s : allSubs) errs() << '\t' << s << '\n';
      
      //-- print pub information
      errs() << "---------------------------------------------------------------------------------\n";
      errs() << "service : " << serviceName << " === PUBLISHES TO ===>\n";
      for(const auto &p : allPubs) errs() << '\t' << p << '\n';      
      
      return false;
    }
  };
}

char Uxas::ID = 0;
static RegisterPass<Uxas> X("uxas", "Uxas Pass");
