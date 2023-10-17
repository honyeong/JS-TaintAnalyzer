/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "hermes/Optimizer/PassManager/Pipeline.h"
#include "hermes/Optimizer/PassManager/PassManager.h"
#include "hermes/Optimizer/Scalar/Auditor.h"
#include "hermes/Optimizer/Scalar/DCE.h"
#include "hermes/Optimizer/Scalar/SimplifyCFG.h"
#include "hermes/Optimizer/Scalar/StackPromotion.h"
#include "hermes/Optimizer/Scalar/TypeInference.h"
#include "hermes/Optimizer/Scalar/CustomCallGraphProvider.h"
#include "hermes/Optimizer/Scalar/SimpleCallGraphProvider.h"
#include "hermes/Optimizer/Scalar/TaintAnalysis.h"

#include "llvh/Support/Debug.h"
#include "llvh/Support/raw_ostream.h"

#include "hermes/IR/CFG.h"

#include <map>
#include <string>
#include <queue>
#include <vector>
#include <iostream>

#define DEBUG_TYPE "pipeline"

using llvh::dbgs;

bool hermes::runCustomOptimizationPasses(
    Module &M,
    const std::vector<std::string> &Opts) {
  LLVM_DEBUG(dbgs() << "Optimizing with custom pipeline...\n");
  PassManager PM{M.getContext().getCodeGenerationSettings()};

  // Add the optimization passes.
  for (auto P : Opts) {
    if (!PM.addPassForName(P)) {
      return false;
    }
  }
  // Run the optimizations.
  PM.run(&M);
  return true;
}

void hermes::runFullOptimizationPasses(Module &M) {
  auto start = std::chrono::high_resolution_clock::now();
  LLVM_DEBUG(dbgs() << "Running -O optimizations...\n");
  PassManager PM{M.getContext().getCodeGenerationSettings()};
  PM.addInstSimplify();
  PM.addResolveStaticRequire();
  PM.addDCE();
  PM.addTypeInference();
  PM.addSimplifyCFG();
  PM.addStackPromotion();
  PM.addMem2Reg();
  PM.addStackPromotion();
  PM.addInlining();
  PM.addStackPromotion();
  PM.addInstSimplify();
  PM.addDCE();

#ifdef HERMES_RUN_WASM
  if (M.getContext().getUseUnsafeIntrinsics()) {
    PM.addTypeInference();
    PM.addPass(new WasmSimplify());
  }
#endif // HERMES_RUN_WASM

  PM.addTypeInference();
  PM.addCSE();
  PM.addTDZDedup();
  PM.addSimplifyCFG();
  PM.addInstSimplify();
  PM.addFuncSigOpts();
  PM.addDCE();
  PM.addSimplifyCFG();
  PM.addMem2Reg();
  PM.addAuditor();
  PM.addTypeInference();
  PM.addHoistStartGenerator();

#ifdef HERMES_RUN_WASM
    // Emit Asm.js/Wasm unsafe compiler intrinsics, if enabled.
    if (M.getContext().getUseUnsafeIntrinsics()) {
    PM.addPass(new EmitWasmIntrinsics());
    }
#endif // HERMES_RUN_WASM
  PM.run(&M);

  llvh::outs() << "JavaScript Taint Analyzer\n";
  /// Initial Settings
  for(Module::iterator ModIter = M.begin(); ModIter != M.end(); ModIter++)
  {
    Function* Func = llvh::cast<Function>(ModIter);
    TaintAnalyzer::setFunction(Func);
    TaintAnalyzer::numOfFunc++;
  }
  ///

  // Inst 자체에 taint : 해당 inst를 참조할 경우 taint value 확인 가능
  // Inst의 operand에 taint : stringRef의 경우 해당 stringRef가 taint되어 다른 곳에서도 참조 가능
  /// Taint Analysis Stuff
  for(Module::iterator ModIter = M.begin(); ModIter != M.end(); ModIter++)
  {
    Function* Func = llvh::cast<Function>(ModIter);
    for(Function::iterator FuncIter = Func -> begin(); FuncIter != Func -> end(); FuncIter++)
    {
        BasicBlock* BB = llvh::cast<BasicBlock>(FuncIter);
        for(BasicBlock::iterator BBIter = BB -> begin(); BBIter != BB -> end(); BBIter++)
        {
            Instruction* Inst = llvh::cast<Instruction>(BBIter);
            if(auto* CI = llvh::dyn_cast<CallInst>(Inst)) // 메서드에 대해 오염 확인하기
            {
                auto* callee = CI->getCallee(); // 함수 callee
                if(callee->isFunction() && callee->getFunction() != nullptr)
                {
                    std::vector<std::pair<bool, Value*>> parameters;
                    if(CI->getNumOperands()-2 != 0) // check parameter
                    {
                        for(unsigned int i = 1 ; i < CI->getNumArguments() ; i++) 
                        {
                            Value* param =  CI->getArgument(i);
                            if(param->isTainted() == true || param->isTaintSource() == true)
                            {
                                parameters.push_back(std::make_pair(true,param));
                            }    
                            else
                            {
                                parameters.push_back(std::make_pair(false,param));
                            }
                        }
                    }
                    std::pair<bool, std::list<std::string>> isTaintedFunction = TaintAnalyzer::runFunction(callee->getFunction(), parameters);
                    if(isTaintedFunction.first == true) // Instruction에 따라 각 Operand 마다 taint 및 list 전달
                    {
                        Inst->setTaint(); // CallInst
                        callee->setTaint(); // CallInst %0 -> callee(LoadPropertyInst)
                        if(auto* LPI = llvh::dyn_cast<LoadPropertyInst>(callee))
                        {
                            LPI->getProperty()->setTaint();
                            LPI->getProperty()->taintList.insert(LPI->getProperty()->taintList.end(), isTaintedFunction.second.begin(), isTaintedFunction.second.end());
                            LPI->getProperty()->taintList.sort();
                            LPI->getProperty()->taintList.unique();
                        }
                        Inst->taintList.insert(Inst->taintList.end(), isTaintedFunction.second.begin(), isTaintedFunction.second.end());
                        callee->taintList.insert(callee->taintList.end(), isTaintedFunction.second.begin(), isTaintedFunction.second.end());
                        
                        Inst->taintList.sort();
                        callee->taintList.sort();

                        Inst->taintList.unique();
                        callee->taintList.unique();
                    }
                }
                else if(auto* LPI = llvh::dyn_cast<LoadPropertyInst>(callee)) // check if taint to sink
                {
                    Value* value = LPI->getProperty();
                    if(value->isTainted() == true || value->isTaintSource() == true)
                    {
                        if(auto* prop = llvh::dyn_cast<LiteralString>(value))
                        {
                            llvh::StringRef propStr = prop->getValue().str();
                            CI->setJSProperty(propStr);
                            CI->setJSObject(value->getJSObject());
                            CI->taintList.insert(CI->taintList.end(), value->taintList.begin(), value->taintList.end());
                            CI->taintList.sort();
                            CI->taintList.unique();
                        }
                    }
                    else if(auto* prop = llvh::dyn_cast<LiteralString>(value))
                    {
                        llvh::StringRef propStr = prop->getValue().str(); // 함수 이름 추출
                        if(TaintAnalyzer::taintSinkMap.count(propStr) != 0 || value->isTaintSink() == true)
                        {
                            if(propStr.str() == "fetch" || propStr.str() == "get" || propStr.str() == "post" || propStr.str() == "put" || propStr.str() == "sendBeacon")
                            {
                                if(CI->getNumOperands()-2 != 0) // check parameter
                                {
                                    std::string urlStr;
                                    std::string apiStr;
                                    std::list<std::string> taintList;

                                    for(unsigned int i = 1 ; i < CI->getNumArguments() ; i++) 
                                    {
                                        Value* value =  CI->getArgument(i);

                                        if(value->isTainted() == true || value->isTaintSource() == true)
                                        {
                                            taintList = value->taintList;
                                        }
                                        else if(auto* obj = llvh::dyn_cast<AllocObjectLiteralInst>(value))
                                        {
                                            unsigned int opSize = obj->getNumOperands();
                                            for(unsigned int i = 0; i < opSize; i++)
                                            {
                                                unsigned int idx = (i*2)+1;
                                                if(opSize <= idx)
                                                    break;
                                                if(obj->getOperand(idx)->isTainted() || obj->getOperand(idx)->isTaintSource())
                                                    taintList = obj->taintList;
                                                if(obj->getOperand(idx)->isURL())
                                                    urlStr = obj->getOperand(idx)->getURL().str();
                                            }
                                        }

                                        else if(auto* LS = llvh::dyn_cast<LiteralString>(value))
                                        {
                                            llvh::StringRef str = LS->getValue().str();
                                            if(TaintAnalyzer::isURL(str))
                                                urlStr = str.str();
                                        }
                                        else if(value->isURL()) // 여기서 매칭이 안되는듯.. url propagation 다시 확인 ㄱㄱ
                                        {
                                            urlStr = value->getURL().str();
                                        }
                                    }

                                    if(propStr.str() == "get" || propStr.str() == "post" || propStr.str() == "put")
                                        apiStr = "axios." + propStr.str();
                                    else if(propStr.str() == "sendBeacon")
                                        apiStr = "navigator." + propStr.str();
                                    else apiStr = propStr.str();

                                    TaintAnalyzer::SinkPair leakValue = TaintAnalyzer::SinkPair(urlStr, apiStr, taintList);
                                    TaintAnalyzer::leakList.push_back(leakValue); 
                                    TaintAnalyzer::leakCnt++;
                                }
                            }
                            else if(propStr.str() == "open") // XMLHttpRequest.open("GET", "/server", true)
                            {
                                if(CI->getThis()->isTaintSink() && CI->getNumOperands()-2 != 0) // XMLHttpRequest
                                {
                                    CI->setURL(CI->getArgument(2)->getURL());
                                    CI->getThis()->setURL(CI->getArgument(2)->getURL());
                                }
                            }
                            else if(propStr.str() == "send") // XMLHttpRequest.send(), WebSocket.send()
                            {
                                auto* obj = CI->getThis();
                                std::string objStr = obj->getJSProperty().str();
                                if((objStr == "XMLHttpRequest" || obj->getJSProperty().str() == "XMLHttpRequest") && CI->getNumOperands()-2 != 0)
                                {
                                    obj->taintList = CI->getArgument(1)->taintList;
                                    TaintAnalyzer::SinkPair leakValue = TaintAnalyzer::SinkPair(obj->getURL(), "XMLHttpRequest.send", obj->taintList);
                                    TaintAnalyzer::leakList.push_back(leakValue); 
                                    TaintAnalyzer::leakCnt++;
                                }
                                else if((objStr == "WebSocket" || obj->getJSProperty().str() == "WebSocket") && CI->getNumOperands()-2 != 0)
                                {
                                    Value* value = CI->getArgument(1);
                                    if(auto* LPIvalue = llvh::dyn_cast<LoadPropertyInst>(value))
                                    {
                                        TaintAnalyzer::SinkPair leakValue = TaintAnalyzer::SinkPair(CI->getThis()->getURL(), "WebSocket.send", LPIvalue->getProperty()->taintList);
                                        TaintAnalyzer::leakList.push_back(leakValue); 
                                        TaintAnalyzer::leakCnt++;
                                    }
                                }
                            }
                        }
                        std::list<llvh::StringRef>::iterator it = std::find(TaintAnalyzer::taintObjectMap.begin(), TaintAnalyzer::taintObjectMap.end(), propStr);
                        if(it != TaintAnalyzer::taintObjectMap.end())
                        { // taint property를 포함하는 object에 대해 value set
                            value->setJSObject(propStr);
                            LPI->setJSObject(propStr);
                        }
                    }
                }
            }
            else if(auto* LPI = llvh::dyn_cast<LoadPropertyInst>(Inst)) // 요소(property)에 대해 taint 또는 object set
            {
                Value* value = LPI->getProperty();
                if(auto* prop = llvh::dyn_cast<LiteralString>(value))
                {
                    llvh::StringRef propStr = prop->getValue().str();
                    if(TaintAnalyzer::taintSourceMap.count(propStr) != 0) // Set taint source
                    {
                        Value* object = LPI->getObject();
                        if(auto* objLPI = llvh::dyn_cast<LoadPropertyInst>(object))
                        {
                            if(objLPI->getProperty()->isJSObject())
                            {
                                Inst->setJSObject(objLPI->getProperty()->getJSObject());
                                Inst->setAsTaintSource();
                                Inst->setJSProperty(propStr);

                                value->setJSObject(objLPI->getProperty()->getJSObject());
                                value->setAsTaintSource();
                                value->setJSProperty(propStr);

                                std::string obj = objLPI->getProperty()->getJSObject().str();
                                std::string source = propStr.str();
                                std::string api = obj + "." + source;

                                std::list<llvh::StringRef>::iterator it = std::find(TaintAnalyzer::taintObjectMap.begin(), TaintAnalyzer::taintObjectMap.end(), obj);
                                if(it != TaintAnalyzer::taintObjectMap.end())
                                {
                                    if(source != "width" && source != "height")
                                    {
                                        auto it = TaintAnalyzer::taintSourceMap.find(source);
                                        if(it != TaintAnalyzer::taintSourceMap.end()) 
                                        {
                                            api = it->second.str() + "." + source;
                                        }
                                    }
                                    if(source != "Date")
                                    {
                                        value->taintList.push_back(api);
                                        Inst->taintList.push_back(api);
                                        TaintAnalyzer::sourceCnt++;
                                        TaintAnalyzer::sourceList.push_back(api);
                                    }
                                }
                            }
                        }
                        else if(auto* objConI = llvh::dyn_cast<ConstructInst>(object)) // new Date() ~
                        {
                            Value* constructor = objConI->getConstructor();
                            if(auto* conLPI = llvh::dyn_cast<LoadPropertyInst>(constructor))
                            {
                                if(conLPI->getProperty()->isJSObject()) // constructor object일 시
                                {
                                    Inst->setJSObject(conLPI->getProperty()->getJSObject());
                                    Inst->setAsTaintSource();
                                    Inst->setJSProperty(propStr);

                                    value->setJSObject(conLPI->getProperty()->getJSObject());
                                    value->setAsTaintSource();
                                    value->setJSProperty(propStr);

                                    std::string obj = conLPI->getProperty()->getJSObject().str();
                                    std::string source = propStr.str();
                                    std::string api = obj+ "." +source;

                                    std::list<llvh::StringRef>::iterator it = std::find(TaintAnalyzer::taintObjectMap.begin(), TaintAnalyzer::taintObjectMap.end(), obj);
                                    if(it != TaintAnalyzer::taintObjectMap.end())
                                    {
                                        if(source != "width" && source != "height")
                                        {
                                            auto it = TaintAnalyzer::taintSourceMap.find(source);
                                            if(it != TaintAnalyzer::taintSourceMap.end()) 
                                            {
                                                api = it->second.str() + "." + source;
                                            }
                                        }
                                        if(source != "Date")
                                        {
                                            value->taintList.push_back(api);
                                            Inst->taintList.push_back(api);
                                            TaintAnalyzer::sourceCnt++;
                                            TaintAnalyzer::sourceList.push_back(api);
                                        }
                                    }
                                }
                            }
                        }
                        else if(auto* objCI = llvh::dyn_cast<CallInst>(object))
                        { //abc().df;
                            Value* callee = objCI->getCallee();
                            if(auto* callLPI = llvh::dyn_cast<LoadPropertyInst>(callee))
                            {
                                if(callLPI->getProperty()->isJSObject())
                                {
                                    Inst->setJSObject(callLPI->getProperty()->getJSObject());
                                    Inst->setAsTaintSource();
                                    Inst->setJSProperty(propStr);

                                    value->setJSObject(callLPI->getProperty()->getJSObject());
                                    value->setAsTaintSource();
                                    value->setJSProperty(propStr);

                                    std::string obj = callLPI->getProperty()->getJSObject().str();
                                    std::string source = propStr.str();
                                    std::string api = obj+ "." +source;

                                    std::list<llvh::StringRef>::iterator it = std::find(TaintAnalyzer::taintObjectMap.begin(), TaintAnalyzer::taintObjectMap.end(), obj);
                                    if(it != TaintAnalyzer::taintObjectMap.end())
                                    {
                                        if(source != "width" && source != "height")
                                        {
                                            auto it = TaintAnalyzer::taintSourceMap.find(source);
                                            if(it != TaintAnalyzer::taintSourceMap.end()) 
                                            {
                                                api = it->second.str() + "." + source;
                                            }
                                        }
                                        if(source != "Date")
                                        {
                                            value->taintList.push_back(api);
                                            Inst->taintList.push_back(api);
                                            TaintAnalyzer::sourceCnt++;
                                            TaintAnalyzer::sourceList.push_back(api);
                                        }
                                    }
                                }
                            }
                        }
                    }
                    else if(TaintAnalyzer::taintSinkMap.count(propStr) != 0) // Set taint sink
                    {
                        Value* object = LPI->getObject();
                        Inst->setAsTaintSink();
                        Inst->setJSProperty(propStr);
                        value->setAsTaintSink();
                        value->setJSProperty(propStr);
                        if(auto* objLPI = llvh::dyn_cast<LoadPropertyInst>(object))
                        {
                            if(objLPI->getProperty()->isJSObject())
                            {
                                Inst->setJSObject(objLPI->getProperty()->getJSObject());
                                value->setJSObject(objLPI->getProperty()->getJSObject());
                            }

                            std::string obj = objLPI->getProperty()->getJSObject().str();
                            if(propStr.str() != "open")
                            {
                                std::list<llvh::StringRef>::iterator it = std::find(TaintAnalyzer::taintObjectMap.begin(), TaintAnalyzer::taintObjectMap.end(), obj);
                                if(it != TaintAnalyzer::taintObjectMap.end())
                                {
                                    std::string source = propStr.str();
                                    std::string api = obj + "." + source;
                                    TaintAnalyzer::sinkList.push_back(api);
                                    TaintAnalyzer::sinkCnt++;
                                }
                            }
                        }
                    }
                    std::list<llvh::StringRef>::iterator it = std::find(TaintAnalyzer::taintObjectMap.begin(), TaintAnalyzer::taintObjectMap.end(), propStr);
                    if(it != TaintAnalyzer::taintObjectMap.end())
                    { // taint property를 포함하는 object에 대해 value set
                        value->setJSObject(propStr);
                        LPI->setJSObject(propStr);
                    }
                    if(TaintAnalyzer::isURL(propStr))
                    {
                        value->setURL(propStr);
                        LPI->setURL(propStr);
                    }
                }
            }
            if(auto* ConI = llvh::dyn_cast<ConstructInst>(Inst))
            {
                Value* constructor = ConI->getConstructor();
                if(auto* conLPI = llvh::dyn_cast<LoadPropertyInst>(constructor))
                {
                    Value* value = conLPI->getProperty();
                    if(auto* prop = llvh::dyn_cast<LiteralString>(value))
                    {
                        llvh::StringRef propStr = prop->getValue().str();
                        if(propStr.str() == "OfflineAudioContext" || propStr.str() == "Function")
                        {
                            Inst->setTaint();
                            Inst->setAsTaintSource();
                            Inst->setJSProperty(propStr);

                            constructor->setTaint();
                            constructor->setAsTaintSource();
                            constructor->setJSProperty(propStr);

                            value->setTaint();
                            value->setAsTaintSource();
                            value->setJSProperty(propStr);

                            std::string conStr = propStr.str();
                            Inst->taintList.push_back(conStr);
                            constructor->taintList.push_back(conStr);
                            value->taintList.push_back(conStr);
                            TaintAnalyzer::sourceCnt++;
                        }
                        if(propStr.str() == "WebSocket" || propStr.str() == "XMLHttpRequest") // Sink
                        {
                            Inst->setAsTaintSink();
                            Inst->setJSProperty(propStr);
                            constructor->setAsTaintSink();
                            constructor->setJSProperty(propStr);

                            if(propStr.str() == "WebSocket") // websocket
                            {
                                for(unsigned int i = 1 ; i < ConI->getNumArguments() ; i++) 
                                {
                                    Value* value =  ConI->getArgument(i);
                                    if(TaintAnalyzer::isURL(value->getURL()))
                                    {
                                        Inst->setURL(value->getURL());
                                        constructor->setURL(value->getURL());
                                    }
                                }
                            }
                        }
                        std::list<llvh::StringRef>::iterator it = std::find(TaintAnalyzer::taintObjectMap.begin(), TaintAnalyzer::taintObjectMap.end(), propStr);
                        if(it != TaintAnalyzer::taintObjectMap.end()) 
                        {
                            Inst->setTaint();
                            Inst->setAsTaintSource();
                            Inst->setJSProperty(propStr);                 

                            constructor->setTaint();
                            constructor->setAsTaintSource();
                            constructor->setJSProperty(propStr);

                            value->setTaint();
                            value->setAsTaintSource();
                            value->setJSProperty(propStr);    

                            std::string obj = conLPI->getProperty()->getJSObject().str();
                            std::string source = propStr.str();
                            std::string api = obj+ "." +source;

                            std::list<llvh::StringRef>::iterator it = std::find(TaintAnalyzer::taintObjectMap.begin(), TaintAnalyzer::taintObjectMap.end(), obj);
                            if(it != TaintAnalyzer::taintObjectMap.end())
                            {
                                if(source != "width" && source != "height")
                                {
                                    auto it = TaintAnalyzer::taintSourceMap.find(source);
                                    if(it != TaintAnalyzer::taintSourceMap.end()) 
                                    {
                                        api = it->second.str() + "." + source;
                                    }
                                }
                                if(source != "Date")
                                {
                                    value->taintList.push_back(api);
                                    Inst->taintList.push_back(api);
                                    constructor->taintList.push_back(api);
                                    TaintAnalyzer::sourceCnt++;
                                    TaintAnalyzer::sourceList.push_back(api);
                                }
                            }
                        }
                    }
                }
            }
            else if(auto* RI = llvh::dyn_cast<ReturnInst>(Inst))
            {
                if(RI->getNumOperands() == 1)
                {
                    Value* value = RI->getOperand(0);
                    if(value->isTainted() == true || value->isTaintSource() == true)
                    {
                        if(TaintAnalyzer::taintedFunctionMap.find(Func->getInternalNameStr()) == TaintAnalyzer::taintedFunctionMap.end())
                        {
                            TaintAnalyzer::taintedFunctionMap.insert(std::make_pair(Func->getInternalNameStr(), true));
                        }
                    }
                }
            }
            TaintAnalyzer::propagate(Inst);
        }
    }
  }
  auto end = std::chrono::high_resolution_clock::now();
  std::chrono::duration<double> duration = end - start;
  std::cout << "Execution time : " << duration.count() << " 초" << "\n";
  std::cout << "Function : " << TaintAnalyzer::numOfFunc << "\n";
  std::cout << "Function that returns tainted value : " << TaintAnalyzer::taintedFunctionMap.size() << "\n";
  std::cout << "Sink Count : " << TaintAnalyzer::sinkCnt << "\n";
  std::cout << "Source Count : " << TaintAnalyzer::sourceCnt << "\n";
  TaintAnalyzer::sourceList.sort();
  TaintAnalyzer::sourceList.unique();
  TaintAnalyzer::sinkList.sort();
  TaintAnalyzer::sinkList.unique();
  std::cout << "<-- Source List -->\n";
  for(auto i = TaintAnalyzer::sourceList.begin(); i != TaintAnalyzer::sourceList.end(); i++)
  {
    std::cout << *i << "\n";
  }
  std::cout << "<-- Sink List -->\n";
  for(auto i = TaintAnalyzer::sinkList.begin(); i != TaintAnalyzer::sinkList.end(); i++)
  {
    std::cout << *i << "\n";
  }
  if(TaintAnalyzer::leakCnt != 0)
  {
    std::cout << "External Leak Count : " << TaintAnalyzer::leakCnt << "\n";
    int i = 1;
    for(const TaintAnalyzer::SinkPair &pair : TaintAnalyzer::leakList)
    {
        std::cout << "<- Leak " << i << " ->\n";
        std::cout << "Leaked API : " << pair.sink << "\n";
        std::cout << "Leaked URL : " << pair.url << "\n";
        std::cout << "-- Source API --" << "\n";
        for(const std::string& api : pair.taintList) 
        {
            std::cout << api << "\n";
        }
        std::cout << "----------------\n"; 
        i++;
    }
  }
  else std::cout << "Leak not found \n"; 
}

void hermes::runDebugOptimizationPasses(Module &M) {
  LLVM_DEBUG(dbgs() << "Running -Og optimizations...\n");
  PassManager PM{M.getContext().getCodeGenerationSettings()};

  PM.addInstSimplify();
  PM.addResolveStaticRequire();

  // Move StartGenerator instructions to the start of functions.
  PM.addHoistStartGenerator();

#ifdef HERMES_RUN_WASM
  // Emit Asm.js/Wasm unsafe compiler intrinsics, if enabled.
  if (M.getContext().getUseUnsafeIntrinsics()) {
    PM.addPass(new EmitWasmIntrinsics());
  }
#endif // HERMES_RUN_WASM

  // Run the optimizations.
  PM.run(&M);
}

#ifdef HERMES_RUN_WASM
void hermes::runNoOptimizationPasses(Module &M) {
  LLVM_DEBUG(dbgs() << "Running -O0 optimizations...\n");

  // Emit Asm.js/Wasm unsafe compiler intrinsics, if enabled.
  if (M.getContext().getUseUnsafeIntrinsics()) {
    PassManager PM;
    PM.addPass(new EmitWasmIntrinsics());
    PM.run(&M);
  }
}
#else
void hermes::runNoOptimizationPasses(Module &M) { // M : Full IR code
  LLVM_DEBUG(dbgs() << "Running -O0 optimizations...\n");
}

void hermes::runTestOptimizationPasses(Module &M) {
}

#endif // HERMES_RUN_WASM

#undef DEBUG_TYPE
