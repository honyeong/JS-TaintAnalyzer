#include "hermes/Optimizer/Scalar/TaintAnalysis.h"

namespace TaintAnalyzer {
using namespace hermes;
#define MAX_RECURSIVE 100

bool isURL(llvh::StringRef input) {
    // URL을 판별할 정규 표현식 패턴
    std::regex urlPattern("(https?|ftp|file|ws)://[-A-Za-z0-9+&@#/%?=~_|!:,.;]*[-A-Za-z0-9+&@#/%=~_|]");

    // 입력 문자열과 패턴을 비교하여 일치 여부 확인
    return std::regex_match(input.str(), urlPattern);
}

void setFunction(Function* Func)
{
    for(Function::iterator FuncIter = Func -> begin(); FuncIter != Func -> end(); FuncIter++)
    {
        BasicBlock* BB = llvh::cast<BasicBlock>(FuncIter);
        for(BasicBlock::iterator BBIter = BB -> begin(); BBIter != BB -> end(); BBIter++)
        {
            Instruction* Inst = llvh::cast<Instruction>(BBIter);
            if(auto* CFI = llvh::dyn_cast<CreateFunctionInst>(Inst))
            {
                CFI->setFunction(CFI->getFunctionCode());
            }
        }
    }
}

void propagate(Instruction* Inst)
{
    unsigned int opSize = Inst->getNumOperands();
    if(auto* SPI = llvh::dyn_cast<StorePropertyInst>(Inst))
    {
        if(SPI->getOperand(0)->isTainted() || SPI->getOperand(0)->isTaintSource()) 
        {
            Inst->setTaint();
            Inst->setJSProperty(SPI->getOperand(0)->getJSProperty());
            Inst->setJSObject(SPI->getOperand(0)->getJSObject());
            Inst->taintList.insert(Inst->taintList.end(), SPI->getOperand(0)->taintList.begin(), SPI->getOperand(0)->taintList.end());
            Inst->taintList.sort();
            Inst->taintList.unique();

            SPI->getOperand(2)->setTaint();
            SPI->getOperand(2)->setJSProperty(SPI->getOperand(0)->getJSProperty());
            SPI->getOperand(2)->setJSObject(SPI->getOperand(0)->getJSObject());
            SPI->getOperand(2)->taintList.insert(SPI->getOperand(2)->taintList.end(), Inst->taintList.begin(), Inst->taintList.end());
            SPI->getOperand(2)->taintList.sort();
            SPI->getOperand(2)->taintList.unique();
        }
        else if(SPI->getOperand(0)->isTaintSink())
        {
            Inst->setAsTaintSink();
            Inst->setJSProperty(SPI->getOperand(0)->getJSProperty());
            Inst->setJSObject(SPI->getOperand(0)->getJSObject());
            Inst->setURL(SPI->getOperand(0)->getURL());

            SPI->getOperand(2)->setAsTaintSink();
            SPI->getOperand(2)->setJSProperty(SPI->getOperand(0)->getJSProperty());
            SPI->getOperand(2)->setJSObject(SPI->getOperand(0)->getJSObject());
            SPI->getOperand(2)->setURL(SPI->getOperand(0)->getURL());
        }
        else if(auto* LS = llvh::dyn_cast<LiteralString>(SPI->getOperand(0)))
        {
            llvh::StringRef str = LS->getValue().str();
            if(TaintAnalyzer::isURL(str))
            {
                Inst->setURL(str);
                SPI->getOperand(2)->setURL(str);
            }
        }
        else if(auto* LPI = llvh::dyn_cast<LoadPropertyInst>(SPI->getOperand(0))) // Taint property를 포함하는 Object propagate
        {
            if(LPI->getOperand(1)->isJSObject())
            {
                Inst->setJSObject(LPI->getOperand(1)->getJSObject());
                SPI->getOperand(2)->setJSObject(LPI->getOperand(1)->getJSObject());
            }
            else if(LPI->getOperand(1)->isURL())
            {
                Inst->setURL(LPI->getOperand(1)->getURL());
                SPI->getOperand(2)->setURL(LPI->getOperand(1)->getURL());
            }
        } 
        else if(auto* CFI = llvh::dyn_cast<CreateFunctionInst>(SPI->getOperand(0))) // Function
        {
            SPI->getOperand(2)->setFunction(CFI->getFunction());
        }
    }
    else if(auto* SFI = llvh::dyn_cast<StoreFrameInst>(Inst))
    {
        if(SFI->getOperand(0)->isTainted() || SFI->getOperand(0)->isTaintSource()) 
        {
            Inst->setTaint();
            Inst->setJSProperty(SFI->getOperand(0)->getJSProperty());
            Inst->setJSObject(SFI->getOperand(0)->getJSObject());
            Inst->taintList.insert(Inst->taintList.end(), SFI->getOperand(0)->taintList.begin(), SFI->getOperand(0)->taintList.end());
            Inst->taintList.unique();

            SFI->getOperand(1)->setTaint();
            SFI->getOperand(1)->setJSProperty(SFI->getOperand(0)->getJSProperty());
            SFI->getOperand(1)->setJSObject(SFI->getOperand(0)->getJSObject());
            SFI->getOperand(1)->taintList.insert(SFI->getOperand(1)->taintList.end(), SFI->getOperand(0)->taintList.begin(), SFI->getOperand(0)->taintList.end());
            SFI->getOperand(1)->taintList.sort();
            SFI->getOperand(1)->taintList.unique();
        }
        if(SFI->getOperand(0)->isTaintSink())
        {
            Inst->setAsTaintSink();
            Inst->setJSProperty(SFI->getOperand(0)->getJSProperty());
            Inst->setJSObject(SFI->getOperand(0)->getJSObject());
            Inst->setURL(SFI->getOperand(0)->getURL());

            SFI->getOperand(1)->setAsTaintSink();
            SFI->getOperand(1)->setJSProperty(SFI->getOperand(0)->getJSProperty());
            SFI->getOperand(1)->setJSObject(SFI->getOperand(0)->getJSObject());
            SFI->getOperand(1)->setURL(SFI->getOperand(0)->getURL());
        }
        else if(auto* LS = llvh::dyn_cast<LiteralString>(SFI->getOperand(0)))
        {
            llvh::StringRef str = LS->getValue().str();
            if(TaintAnalyzer::isURL(str))
            {
                Inst->setURL(str);
                SFI->getOperand(1)->setURL(str);
            }
        }
        else if(auto* LPI = llvh::dyn_cast<LoadPropertyInst>(SFI->getOperand(0))) // Taint property를 포함하는 Object propagate
        {
            if(LPI->getOperand(1)->isJSObject())
            {
                Inst->setJSObject(LPI->getOperand(1)->getJSObject());
                SFI->getOperand(1)->setJSObject(LPI->getOperand(1)->getJSObject());
            }
            else if(LPI->getOperand(1)->isURL())
            {
                Inst->setURL(LPI->getOperand(1)->getURL());
                SFI->getOperand(1)->setURL(LPI->getOperand(1)->getURL());
            }
        }
        else if(auto* CFI = llvh::dyn_cast<CreateFunctionInst>(SFI->getOperand(0)))
        {
            SFI->getOperand(1)->setFunction(CFI->getFunction());
        }
    }
    else if(auto* TSGPI = llvh::dyn_cast<TryStoreGlobalPropertyInst>(Inst))
    {
        if(TSGPI->getOperand(0)->isTainted() || TSGPI->getOperand(0)->isTaintSource()) 
        {
            Inst->setTaint();
            Inst->setJSProperty(TSGPI->getOperand(0)->getJSProperty());
            Inst->setJSObject(TSGPI->getOperand(0)->getJSObject());
            Inst->taintList.insert(Inst->taintList.end(), TSGPI->getOperand(0)->taintList.begin(), TSGPI->getOperand(0)->taintList.end());
            Inst->taintList.sort();
            Inst->taintList.unique();

            TSGPI->getOperand(1)->setTaint();
            TSGPI->getOperand(1)->setJSProperty(TSGPI->getOperand(0)->getJSProperty());
            TSGPI->getOperand(1)->setJSObject(TSGPI->getOperand(0)->getJSObject());
            TSGPI->getOperand(1)->taintList.insert(TSGPI->getOperand(1)->taintList.end(), TSGPI->getOperand(0)->taintList.begin(), TSGPI->getOperand(0)->taintList.end());
            TSGPI->getOperand(1)->taintList.sort();
            TSGPI->getOperand(1)->taintList.unique();
        }
        if(TSGPI->getOperand(0)->isTaintSink())
        {
            Inst->setAsTaintSink();
            Inst->setJSProperty(TSGPI->getOperand(0)->getJSProperty());
            Inst->setJSObject(TSGPI->getOperand(0)->getJSObject());
            Inst->setURL(TSGPI->getOperand(0)->getURL());

            TSGPI->getOperand(1)->setAsTaintSink();
            TSGPI->getOperand(1)->setJSProperty(TSGPI->getOperand(0)->getJSProperty());
            TSGPI->getOperand(1)->setJSObject(TSGPI->getOperand(0)->getJSObject());
            TSGPI->getOperand(1)->setURL(TSGPI->getOperand(0)->getURL());
        }
        else if(auto* LS = llvh::dyn_cast<LiteralString>(TSGPI->getOperand(0)))
        {
            llvh::StringRef str = LS->getValue().str();
            if(TaintAnalyzer::isURL(str))
            {
                Inst->setURL(str);
                TSGPI->getOperand(1)->setURL(str);
            }
        }
        else if(auto* LPI = llvh::dyn_cast<LoadPropertyInst>(TSGPI->getOperand(0))) // Taint property를 포함하는 Object propagate
        {
            if(LPI->getOperand(1)->isJSObject())
            {
                Inst->setJSObject(LPI->getOperand(1)->getJSObject());
                TSGPI->getOperand(1)->setJSObject(LPI->getOperand(1)->getJSObject());
            }
            else if(LPI->getOperand(1)->isURL())
            {
                Inst->setURL(LPI->getOperand(1)->getURL());
                TSGPI->getOperand(1)->setURL(LPI->getOperand(1)->getURL());
            }
        }
        else if(auto* CFI = llvh::dyn_cast<CreateFunctionInst>(TSGPI->getOperand(0)))
        {
            TSGPI->getOperand(1)->setFunction(CFI->getFunction());
        }
    }
    else if(auto* SOPI = llvh::dyn_cast<StoreOwnPropertyInst>(Inst))
    {
        if(SOPI->getOperand(0)->isTainted() || SOPI->getOperand(0)->isTaintSource()) 
        {
            Inst->setTaint();
            Inst->setJSProperty(SOPI->getOperand(0)->getJSProperty());
            Inst->setJSObject(SOPI->getOperand(0)->getJSObject());
            Inst->taintList.insert(Inst->taintList.end(), SOPI->getOperand(0)->taintList.begin(), SOPI->getOperand(0)->taintList.end());
            Inst->taintList.sort();
            Inst->taintList.unique();
            
            SOPI->getOperand(1)->setTaint();
            SOPI->getOperand(1)->setJSProperty(SOPI->getOperand(0)->getJSProperty());
            SOPI->getOperand(1)->setJSObject(SOPI->getOperand(0)->getJSObject());
            SOPI->getOperand(1)->taintList.insert(SOPI->getOperand(1)->taintList.end(), SOPI->getOperand(0)->taintList.begin(), SOPI->getOperand(0)->taintList.end());
            SOPI->getOperand(1)->taintList.sort();
            SOPI->getOperand(1)->taintList.unique();

            SOPI->getOperand(2)->setTaint();
            SOPI->getOperand(2)->setJSProperty(SOPI->getOperand(0)->getJSProperty());
            SOPI->getOperand(2)->setJSObject(SOPI->getOperand(0)->getJSObject());
            SOPI->getOperand(2)->taintList.insert(SOPI->getOperand(2)->taintList.end(), SOPI->getOperand(0)->taintList.begin(), SOPI->getOperand(0)->taintList.end());
            SOPI->getOperand(2)->taintList.sort();
            SOPI->getOperand(2)->taintList.unique();
        }
        if(SOPI->getOperand(0)->isTaintSink())
        {
            Inst->setAsTaintSink();
            Inst->setJSProperty(SOPI->getOperand(0)->getJSProperty());
            Inst->setJSObject(SOPI->getOperand(0)->getJSObject());
            Inst->setURL(SOPI->getOperand(0)->getURL());

            SOPI->getOperand(1)->setAsTaintSink();
            SOPI->getOperand(1)->setJSProperty(SOPI->getOperand(0)->getJSProperty());
            SOPI->getOperand(1)->setJSObject(SOPI->getOperand(0)->getJSObject());
            SOPI->getOperand(1)->setURL(SOPI->getOperand(0)->getURL());

            SOPI->getOperand(2)->setAsTaintSink();
            SOPI->getOperand(2)->setJSProperty(SOPI->getOperand(0)->getJSProperty());
            SOPI->getOperand(2)->setJSObject(SOPI->getOperand(0)->getJSObject());
            SOPI->getOperand(2)->setURL(SOPI->getOperand(0)->getURL());
        }
        else if(auto* LS = llvh::dyn_cast<LiteralString>(SOPI->getOperand(0)))
        {
            llvh::StringRef str = LS->getValue().str();
            if(TaintAnalyzer::isURL(str))
            {
                Inst->setURL(str);
                SOPI->getOperand(1)->setURL(str);
                SOPI->getOperand(2)->setURL(str);
            }
        }
        else if(auto* LPI = llvh::dyn_cast<LoadPropertyInst>(SOPI->getOperand(0))) // Taint property를 포함하는 Object propagate
        {
            if(LPI->getOperand(1)->isJSObject())
            {
                Inst->setJSObject(LPI->getOperand(1)->getJSObject());
                SOPI->getOperand(2)->setJSObject(LPI->getOperand(1)->getJSObject());
            }
            else if(LPI->getOperand(1)->isURL())
            {
                Inst->setURL(LPI->getOperand(1)->getURL());
                SOPI->getOperand(2)->setURL(LPI->getOperand(1)->getURL());
            }
        }
        else if(auto* CFI = llvh::dyn_cast<CreateFunctionInst>(SOPI->getOperand(0)))
        {
            SOPI->getOperand(2)->setFunction(CFI->getFunction());
        }
    }
    else if(auto* SNOPI = llvh::dyn_cast<StoreNewOwnPropertyInst>(Inst))
    {
        if(SNOPI->getOperand(0)->isTainted() || SNOPI->getOperand(0)->isTaintSource()) 
        {
            Inst->setTaint();
            Inst->setJSProperty(SNOPI->getOperand(0)->getJSProperty());
            Inst->setJSObject(SNOPI->getOperand(0)->getJSObject());
            Inst->taintList.insert(Inst->taintList.end(), SNOPI->getOperand(0)->taintList.begin(), SNOPI->getOperand(0)->taintList.end());
            Inst->taintList.sort();
            Inst->taintList.unique();
            
            SNOPI->getOperand(2)->setTaint();
            SNOPI->getOperand(2)->setJSProperty(SNOPI->getOperand(0)->getJSProperty());
            SNOPI->getOperand(2)->setJSObject(SNOPI->getOperand(0)->getJSObject());
            SNOPI->getOperand(2)->taintList.insert(SNOPI->getOperand(2)->taintList.end(), SNOPI->getOperand(0)->taintList.begin(), SNOPI->getOperand(0)->taintList.end());
            SNOPI->getOperand(2)->taintList.sort();
            SNOPI->getOperand(2)->taintList.unique();
        }
        if(SNOPI->getOperand(0)->isTaintSink())
        {
            Inst->setAsTaintSink();
            Inst->setJSProperty(SNOPI->getOperand(0)->getJSProperty());
            Inst->setJSObject(SNOPI->getOperand(0)->getJSObject());
            Inst->setURL(SNOPI->getOperand(0)->getURL());

            SNOPI->getOperand(2)->setAsTaintSink();
            SNOPI->getOperand(2)->setJSProperty(SNOPI->getOperand(0)->getJSProperty());
            SNOPI->getOperand(2)->setJSObject(SNOPI->getOperand(0)->getJSObject());
            SNOPI->getOperand(2)->setURL(SNOPI->getOperand(0)->getURL());
        }
        else if(auto* LS = llvh::dyn_cast<LiteralString>(SNOPI->getOperand(0)))
        {
            llvh::StringRef str = LS->getValue().str();
            if(TaintAnalyzer::isURL(str))
            {
                Inst->setURL(str);
                SNOPI->getOperand(2)->setURL(str);
            }
        }
        else if(auto* LPI = llvh::dyn_cast<LoadPropertyInst>(SNOPI->getOperand(0))) // Taint property를 포함하는 Object propagate
        {
            if(LPI->getOperand(1)->isJSObject())
            {
                Inst->setJSObject(LPI->getOperand(1)->getJSObject());
                SNOPI->getOperand(2)->setJSObject(LPI->getOperand(1)->getJSObject());
            }
            else if(LPI->getOperand(1)->isURL())
            {
                Inst->setURL(LPI->getOperand(1)->getURL());
                SNOPI->getOperand(2)->setURL(LPI->getOperand(1)->getURL());
            }
        }
        else if(auto* CFI = llvh::dyn_cast<CreateFunctionInst>(SNOPI->getOperand(0)))
        {
            SNOPI->getOperand(2)->setFunction(CFI->getFunction());
        }  
    }
    else if(auto* SGSI = llvh::dyn_cast<StoreGetterSetterInst>(Inst))
    {
        if(SGSI->getOperand(0)->isTainted() || SGSI->getOperand(0)->isTaintSource())
        {
            Inst->setTaint();
            Inst->setJSProperty(SGSI->getOperand(0)->getJSProperty());
            Inst->setJSObject(SGSI->getOperand(0)->getJSObject());
            Inst->taintList.insert(Inst->taintList.end(), SGSI->getOperand(0)->taintList.begin(), SGSI->getOperand(0)->taintList.end());
            Inst->taintList.sort();
            Inst->taintList.unique();
            
            SGSI->getOperand(2)->setTaint();
            SGSI->getOperand(2)->setJSProperty(SGSI->getOperand(0)->getJSProperty());
            SGSI->getOperand(2)->setJSObject(SGSI->getOperand(0)->getJSObject());
            SGSI->getOperand(2)->taintList.insert(SGSI->getOperand(2)->taintList.end(), SGSI->getOperand(0)->taintList.begin(), SGSI->getOperand(0)->taintList.end());       
            SGSI->getOperand(2)->taintList.sort();
            SGSI->getOperand(2)->taintList.unique();
        }
        if(SGSI->getOperand(0)->isTaintSink())
        {
            Inst->setAsTaintSink();
            Inst->setJSProperty(SGSI->getOperand(0)->getJSProperty());
            Inst->setJSObject(SGSI->getOperand(0)->getJSObject());
            Inst->setURL(SGSI->getOperand(0)->getURL());

            SGSI->getOperand(2)->setAsTaintSink();
            SGSI->getOperand(2)->setJSProperty(SGSI->getOperand(0)->getJSProperty());
            SGSI->getOperand(2)->setJSObject(SGSI->getOperand(0)->getJSObject());
            SGSI->getOperand(2)->setURL(SGSI->getOperand(0)->getURL());
        }
        if(SGSI->getOperand(1)->isTainted() || SGSI->getOperand(1)->isTaintSource())
        {
            Inst->setTaint();
            Inst->setJSProperty(SGSI->getOperand(1)->getJSProperty());
            Inst->setJSObject(SGSI->getOperand(1)->getJSObject());
            Inst->taintList.insert(Inst->taintList.end(), SGSI->getOperand(1)->taintList.begin(), SGSI->getOperand(1)->taintList.end());
            Inst->taintList.sort();
            Inst->taintList.unique();
            
            SGSI->getOperand(2)->setTaint();
            SGSI->getOperand(2)->setJSProperty(SGSI->getOperand(1)->getJSProperty());
            SGSI->getOperand(2)->setJSObject(SGSI->getOperand(1)->getJSObject());
            SGSI->getOperand(2)->taintList.insert(SGSI->getOperand(2)->taintList.end(), SGSI->getOperand(1)->taintList.begin(), SGSI->getOperand(1)->taintList.end());
            SGSI->getOperand(2)->taintList.sort();
            SGSI->getOperand(2)->taintList.unique();
        }
        if(SGSI->getOperand(1)->isTaintSink())
        {
            Inst->setAsTaintSink();
            Inst->setJSProperty(SGSI->getOperand(1)->getJSProperty());
            Inst->setJSObject(SGSI->getOperand(1)->getJSObject());
            Inst->setURL(SGSI->getOperand(1)->getURL());

            SGSI->getOperand(2)->setAsTaintSink();
            SGSI->getOperand(2)->setJSProperty(SGSI->getOperand(0)->getJSProperty());
            SGSI->getOperand(2)->setJSObject(SGSI->getOperand(0)->getJSObject());
            SGSI->getOperand(2)->setURL(SGSI->getOperand(0)->getURL());
        }
        else if(auto* LS = llvh::dyn_cast<LiteralString>(SGSI->getOperand(0)))
        {
            llvh::StringRef str = LS->getValue().str();
            if(TaintAnalyzer::isURL(str))
            {
                Inst->setURL(str);
                SGSI->getOperand(2)->setURL(str);
            }
        }
        else if(auto* LS = llvh::dyn_cast<LiteralString>(SGSI->getOperand(1)))
        {
            llvh::StringRef str = LS->getValue().str();
            if(TaintAnalyzer::isURL(str))
            {
                Inst->setURL(str);
                SGSI->getOperand(2)->setURL(str);
            }
        }        
        else if(auto* LPI = llvh::dyn_cast<LoadPropertyInst>(SGSI->getOperand(0))) // Taint property를 포함하는 Object propagate
        {
            if(LPI->getOperand(1)->isJSObject())
            {
                Inst->setJSObject(LPI->getOperand(1)->getJSObject());
                SGSI->getOperand(2)->setJSObject(LPI->getOperand(1)->getJSObject());
            }
            else if(LPI->getOperand(1)->isURL())
            {
                Inst->setURL(LPI->getOperand(1)->getURL());
                SGSI->getOperand(2)->setURL(LPI->getOperand(1)->getURL());
            }
        }
        else if(auto* LPI = llvh::dyn_cast<LoadPropertyInst>(SGSI->getOperand(1))) // Taint property를 포함하는 Object propagate
        {
            if(LPI->getOperand(1)->isJSObject())
            {
                Inst->setJSObject(LPI->getOperand(1)->getJSObject());
                SGSI->getOperand(2)->setJSObject(LPI->getOperand(1)->getJSObject());
            }
            else if(LPI->getOperand(1)->isURL())
            {
                Inst->setURL(LPI->getOperand(1)->getURL());
                SGSI->getOperand(2)->setURL(LPI->getOperand(1)->getURL());
            }
        }
        else if(auto* CFI = llvh::dyn_cast<CreateFunctionInst>(SGSI->getOperand(0)))
        {
            SGSI->getOperand(2)->setFunction(CFI->getFunction());
        }
        else if(auto* CFI = llvh::dyn_cast<CreateFunctionInst>(SGSI->getOperand(1)))
        {
            SGSI->getOperand(2)->setFunction(CFI->getFunction());
        }
    }
    else if(auto* AOLI = llvh::dyn_cast<AllocObjectLiteralInst>(Inst))
    {
        unsigned int AOLIOpSize = AOLI->getNumOperands();
        for(unsigned int i = 0; i < AOLIOpSize; i++)
        {
            unsigned int idx = (i*2)+1;
            if(AOLIOpSize <= idx)
                break;
            if(AOLI->getOperand(idx)->isTainted() || AOLI->getOperand(idx)->isTaintSource())
            {
                Inst->setTaint();
                Inst->setJSObject(AOLI->getOperand(idx)->getJSObject());
                Inst->setJSProperty(AOLI->getOperand(idx)->getJSProperty());
                Inst->taintList.insert(Inst->taintList.end(), AOLI->getOperand(idx)->taintList.begin(), AOLI->getOperand(idx)->taintList.end());                    
                Inst->taintList.sort();
                Inst->taintList.unique();
                
                AOLI->getOperand(idx-1)->setTaint();
                AOLI->getOperand(idx-1)->setJSObject(AOLI->getOperand(idx)->getJSObject());
                AOLI->getOperand(idx-1)->setJSProperty(AOLI->getOperand(idx)->getJSProperty());
                AOLI->getOperand(idx-1)->taintList.insert(AOLI->getOperand(idx-1)->taintList.end(), AOLI->getOperand(idx)->taintList.begin(), AOLI->getOperand(idx)->taintList.end());
                AOLI->getOperand(idx-1)->taintList.sort();
                AOLI->getOperand(idx-1)->taintList.unique();
            }
            else if(AOLI->getOperand(idx)->isTaintSink())
            {
                Inst->setAsTaintSink();
                Inst->setJSProperty(AOLI->getOperand(idx)->getJSProperty());
                Inst->setJSObject(AOLI->getOperand(idx)->getJSObject());
                Inst->setURL(AOLI->getOperand(idx)->getURL());

                AOLI->getOperand(idx-1)->setAsTaintSink();
                AOLI->getOperand(idx-1)->setJSProperty(AOLI->getOperand(idx-1)->getJSProperty());
                AOLI->getOperand(idx-1)->setJSObject(AOLI->getOperand(idx-1)->getJSObject());
                AOLI->getOperand(idx-1)->setURL(AOLI->getOperand(idx-1)->getURL());
            }
            else if(AOLI->getOperand(idx)->isJSObject())
            {
                AOLI->getOperand(idx-1)->setJSObject(AOLI->getOperand(idx)->getJSObject());
            }
            else if(AOLI->getOperand(idx)->isURL())
            {
                AOLI->getOperand(idx-1)->setURL(AOLI->getOperand(idx)->getURL());
            }
            else if(auto* CFI = llvh::dyn_cast<CreateFunctionInst>(AOLI->getOperand(idx)))
            {
                AOLI->getOperand(idx-1)->setFunction(CFI->getFunction());
            }
        }        
    }
    else if(auto* DEI = llvh::dyn_cast<DirectEvalInst>(Inst))
    {
        Inst->setTaint();
        Inst->setJSProperty("eval");
        DEI->getOperand(0)->setTaint();
        DEI->getOperand(0)->setJSProperty("eval");
    }
    else 
    {
        for(unsigned int i = 0; i < opSize; i++)
        {
            Value* operand = Inst->getOperand(i);
            if(operand->isTainted() || operand->isTaintSource())
            {
                Inst->setTaint();
                Inst->setJSProperty(operand->getJSProperty());
                Inst->setJSObject(operand->getJSObject());
                Inst->taintList.insert(Inst->taintList.end(), operand->taintList.begin(), operand->taintList.end());
                Inst->taintList.sort();
                Inst->taintList.unique();
            }
            if(operand->isJSObject())
            {
                Inst->setJSObject(operand->getJSObject());
            }
            if(operand->isFunction())
            {
                Inst->setFunction(operand->getFunction());
            }
            if(operand->isURL())
            {
                Inst->setURL(operand->getURL());
            }
            if(operand->isTaintSink())
            {
                Inst->setAsTaintSink();
                Inst->setJSProperty(operand->getJSProperty());
            }
        }
    }
}

std::pair<bool, std::list<std::string>> runFunction(Function* Func, std::vector<std::pair<bool,Value*>> params)
{
    Func->recursiveCnt++;
    std::list<std::string> list;
    if(Func->recursiveCnt >= MAX_RECURSIVE || Func == nullptr)
        return std::make_pair(false, list);
    if(Func->getParameters().size() == params.size())
    {
        int i = 0;
        for(Parameter* P : Func->getParameters()) // 파라미터 오염 셋팅
        {
            if(params[i].first == true)
            {
                P->setTaint();
                P->taintList.insert(P->taintList.end(), params[i].second->taintList.begin(), params[i].second->taintList.begin());
            }
            P->setJSObject(params[i].second->getJSObject());
            P->setJSProperty(params[i].second->getJSProperty());
            P->setURL(params[i].second->getURL());
            i++;
        }
    }
    for(Function::iterator FuncIter = Func->begin(); FuncIter != Func->end(); FuncIter++) // 함수 내 코드 실행
    {
        BasicBlock* BB = llvh::cast<BasicBlock>(FuncIter);
        for(BasicBlock::iterator BBIter = BB -> begin(); BBIter != BB -> end(); BBIter++)
        {
            Instruction* subInst = llvh::cast<Instruction>(BBIter);
            if(auto* CI = llvh::dyn_cast<CallInst>(subInst)) // 함수 호출 명령
            {
                auto* callee = CI->getCallee();
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
                    std::pair<bool, std::list<std::string>> isTaintedFunction = runFunction(callee->getFunction(), parameters);
                    if(isTaintedFunction.first == true) // Instruction에 따라 각 Operand 마다 taint 및 list 전달 필요
                    {
                        subInst->setTaint(); // CallInst
                        callee->setTaint(); // CallInst %0 -> callee(LoadPropertyInst)
                        if(auto* LPI = llvh::dyn_cast<LoadPropertyInst>(callee))
                        {
                            LPI->getProperty()->setTaint();
                            LPI->getProperty()->taintList.insert(LPI->getProperty()->taintList.end(), isTaintedFunction.second.begin(), isTaintedFunction.second.end());
                            LPI->getProperty()->taintList.sort();
                            LPI->getProperty()->taintList.unique();
                        }
                        subInst->taintList.insert(subInst->taintList.end(), isTaintedFunction.second.begin(), isTaintedFunction.second.end());
                        callee->taintList.insert(callee->taintList.end(), isTaintedFunction.second.begin(), isTaintedFunction.second.end());
                        
                        subInst->taintList.sort();
                        callee->taintList.sort();
                        
                        subInst->taintList.unique();
                        callee->taintList.unique();
                    }
                }
                else if(auto* LPI = llvh::dyn_cast<LoadPropertyInst>(callee)) // 오염이 싱크로 빠지는지 확인
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
                    
                    else if(auto* LPIprop = llvh::dyn_cast<LiteralString>(value))
                    {
                        llvh::StringRef propStr = LPIprop->getValue().str();
                        if(taintSinkMap.count(propStr) != 0 || value->isTaintSink() == true)
                        {
                            if(propStr.str() == "fetch" || propStr.str() == "get" || propStr.str() == "post" || propStr.str() == "sendBeacon")
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
                        std::list<llvh::StringRef>::iterator it = std::find(taintObjectMap.begin(), taintObjectMap.end(), propStr);
                        if(it != taintObjectMap.end())
                        { // taint property를 포함하는 object에 대해 value set
                            value->setJSObject(propStr);
                            LPI->setJSObject(propStr);
                        }                 
                    }
                }
            }
            else if(auto* LPI = llvh::dyn_cast<LoadPropertyInst>(subInst)) // 요소(property)에 대해 taint 또는 object set
            {
                Value* value = LPI->getProperty();
                if(auto* LPIProp = llvh::dyn_cast<LiteralString>(value))
                {
                    llvh::StringRef propStr = LPIProp->getValue().str();
                    if(taintSourceMap.count(propStr) != 0) // set taint source
                    {
                        Value* object = LPI->getObject();
                        if(auto* objLPI = llvh::dyn_cast<LoadPropertyInst>(object))
                        {
                            if(objLPI->getProperty()->isJSObject())
                            {
                                subInst->setJSObject(objLPI->getProperty()->getJSObject());
                                subInst->setAsTaintSource();
                                subInst->setJSProperty(propStr);

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
                                        subInst->taintList.push_back(api);
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
                                    subInst->setJSObject(conLPI->getProperty()->getJSObject());
                                    subInst->setAsTaintSource();
                                    subInst->setJSProperty(propStr);

                                    value->setJSObject(conLPI->getProperty()->getJSObject());
                                    value->setAsTaintSource();
                                    value->setJSProperty(propStr);

                                    std::string obj = conLPI->getProperty()->getJSObject().str();
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
                                            subInst->taintList.push_back(api);
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
                                    subInst->setJSObject(callLPI->getProperty()->getJSObject());
                                    subInst->setAsTaintSource();
                                    subInst->setJSProperty(propStr);

                                    value->setJSObject(callLPI->getProperty()->getJSObject());
                                    value->setAsTaintSource();
                                    value->setJSProperty(propStr);

                                    std::string obj = callLPI->getProperty()->getJSObject().str();
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
                                            subInst->taintList.push_back(api);
                                            TaintAnalyzer::sourceCnt++;
                                            TaintAnalyzer::sourceList.push_back(api);
                                        }
                                    }
                                }
                            }
                        }                                                
                    }
                    else if(taintSinkMap.count(propStr) != 0) // set taint sink
                    {   
                        Value* object = LPI->getObject();
                        subInst->setAsTaintSink();
                        subInst->setJSProperty(propStr);                                
                        value->setAsTaintSink();
                        value->setJSProperty(propStr);
                        if(auto* objLPI = llvh::dyn_cast<LoadPropertyInst>(object))
                        {
                            if(objLPI->getProperty()->isJSObject())
                            {
                                subInst->setJSObject(objLPI->getProperty()->getJSObject());
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
                    std::list<llvh::StringRef>::iterator it = std::find(taintObjectMap.begin(), taintObjectMap.end(), propStr);
                    if(it != taintObjectMap.end()) { // taint property를 포함하는 object에 대해 value set
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
            if(auto* ConI = llvh::dyn_cast<ConstructInst>(subInst)) // Construct 선언만으로 taint setting 이 가능한 경우 확인
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
                            subInst->setTaint();
                            subInst->setAsTaintSource();
                            subInst->setJSProperty(propStr);      

                            constructor->setTaint();
                            constructor->setAsTaintSource();
                            constructor->setJSProperty(propStr);

                            value->setTaint();
                            value->setAsTaintSource();
                            value->setJSProperty(propStr);         

                            std::string conStr = propStr.str();
                            subInst->taintList.push_back(conStr);
                            constructor->taintList.push_back(conStr);
                            value->taintList.push_back(conStr);
                            sourceCnt++;
                        }
                        if(propStr.str() == "WebSocket" || propStr.str() == "XMLHttpRequest") // Sink
                        {
                            subInst->setAsTaintSink();
                            subInst->setJSProperty(propStr);
                            constructor->setAsTaintSink();
                            constructor->setJSProperty(propStr);

                            if(propStr.str() == "WebSocket") // websocket
                            {
                                for(unsigned int i = 1 ; i < ConI->getNumArguments() ; i++) 
                                {
                                    Value* value =  ConI->getArgument(i);
                                    if(TaintAnalyzer::isURL(value->getURL()))
                                    {
                                        subInst->setURL(value->getURL());
                                        constructor->setURL(value->getURL());
                                    }
                                }
                            }
                        }
                        std::list<llvh::StringRef>::iterator it = std::find(taintObjectMap.begin(), taintObjectMap.end(), propStr);
                        if(it != taintObjectMap.end()) 
                        {
                            subInst->setTaint();
                            subInst->setAsTaintSource();
                            subInst->setJSProperty(propStr);       

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
                                    subInst->taintList.push_back(api);
                                    constructor->taintList.push_back(api);
                                    TaintAnalyzer::sourceCnt++;
                                    TaintAnalyzer::sourceList.push_back(api);
                                }
                            }
                        }
                    }
                }
            }
            else if(auto* RI = llvh::dyn_cast<ReturnInst>(subInst))
            {
                if(RI->getNumOperands() == 1)
                {
                    Value* value = RI->getOperand(0);
                    Func->recursiveCnt--;
                    if(value->isTainted() || value->isTaintSource())
                    {
                        return std::make_pair(true, subInst->taintList);
                    }
                    else return std::make_pair(false, list);
                }
            }
            propagate(subInst);
        }
    }
    return std::make_pair(false, list);
}
}