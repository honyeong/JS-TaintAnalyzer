/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "hermes/Optimizer/Scalar/CustomCallGraphProvider.h"

#include "hermes/IR/IR.h"
#include "hermes/IR/Instrs.h"
#include "hermes/Optimizer/Scalar/Utils.h"

using namespace hermes;

/// Auxiliary method to figure out the Functions that a given CallInst may
/// be calling. Returns true if we have a complete set, false if there are
/// unknown callees.
static bool CustomidentifyCallees(CallInst *CI, llvh::DenseSet<Function *> &callees) {
  Value *callee = CI->getCallee();
  switch (callee->getKind()) {
    case ValueKind::FunctionKind: {
      auto *F = cast<Function>(callee);
      callees.insert(F);
      return true;
    }
    case ValueKind::CreateFunctionInstKind: {
      auto *CFI = cast<CreateFunctionInst>(callee);
      callees.insert(CFI->getFunctionCode());
      return true;
    }
    case ValueKind::LoadFrameInstKind: {
      auto *LFI = cast<LoadFrameInst>(callee);
      Variable *V = LFI->getLoadVariable();
      if (V->getParent()->isGlobalScope()) {
        return false;
      }
      for (auto *U : V->getUsers()) {
        if (llvh::isa<LoadFrameInst>(U)) {
          // Skip over a load frame using that address
          continue;
        }
        auto *SF = llvh::dyn_cast<StoreFrameInst>(U);
        if (!SF) {
          // Unknown inst using that address ... bail out.
          return false;
        }
        auto *CFI = llvh::dyn_cast<CreateFunctionInst>(SF->getValue());
        if (!CFI) {
          // Currently look only direct stores of created functions.
          return false;
        }
        callees.insert(CFI->getFunctionCode());
      }
      return true;
    }
    default: {
      // If callee is any other ValueKind, we don't know.
      return false;
    }
  }
}

/// Auxiliary method to figure out the call sites at which F may be
/// invoked.  Returns true if the complete set of call sites is known.
static bool CustomidentifyCallsites(
    Function *F,
    llvh::DenseSet<CallInst *> &callSites) {
  for (auto *CU : F->getUsers()) {
    if (auto *CI = llvh::dyn_cast<CallInst>(CU)) {
      if (!isDirectCallee(F, CI))
        return false;
      callSites.insert(CI);
    } else if (auto *CFI = llvh::dyn_cast<CreateFunctionInst>(CU)) {
      for (auto *CL : CFI->getUsers()) {
        auto *CI = llvh::dyn_cast<CallInst>(CL);
        if (!CI)
          return false;

        if (!isDirectCallee(CFI, CI))
          return false;
        callSites.insert(CI);
      }
    } else {
      return false;
    }
  }
  return true;
}

/// The main function that computes caller-callee relationships.
void CustomCallGraphProvider::initCallRelationships(Function *F) {
  // (a) Initialize the callsites map.
  llvh::DenseSet<CallInst *> callSites;
  if (CustomidentifyCallsites(F, callSites)) {
    callsites_.insert(std::make_pair(F, callSites));
    //llvh::outs() << "Debug1 : " << F -> getInternalNameStr() << "\n";
  }

  // (b) Initialize the callees map.
  for (auto &bbit : *F) {
    for (auto &it : bbit) {
      Instruction *I = &it;

      auto *CI = llvh::dyn_cast<CallInst>(I);
      if (!CI)
        continue;

      //llvh::outs() << "Debug2 : " << I -> getOperand(0) -> getKindStr() << "\n";
      //llvh::outs() << "I : " << I -> getKindStr() << "\n";
      //llvh::outs() << "I-Callee : " << CI -> getCallee() -> getKindStr() << "\n";
      for(auto &it2 : bbit)
      {
          Instruction *tmp = &it2;
          if(tmp == CI -> getCallee())
          {
              //llvh::outs() << "Test Debug : " << tmp -> getOperand(1) << "\n";
              auto* tmp2 = llvh::dyn_cast<LiteralString>(tmp->getOperand(1));
              llvh::outs() << "Callee Name : " << tmp2 -> getValue() << "\n";
              llvh::outs() << "Callee Instruction : " << CI -> getName() << "\n";
              llvh::outs() << "Callee Addr(Debug) : " << tmp2 << "\n";
              //llvh::outs() << "Debug get type : " << tmp -> getOperand(0) -> getType() << "\n";
              //llvh::outs() << "Debug get type : " << tmp -> getOperand(1) -> getType() << "\n";
              //llvh::outs() << "Test Debug2 : " << tmp2 -> getName() << "\n";
          }
      }
      //llvh::outs() << "Debug5 : " << CI -> getArgument(0) -> getKindStr() << "\n";

      llvh::DenseSet<Function *> funcs;
      if (CustomidentifyCallees(CI, funcs)) {
        callees_.insert(std::make_pair(CI, funcs));
      }
    }
  }
}
