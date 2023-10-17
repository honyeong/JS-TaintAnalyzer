#include "hermes/Optimizer/PassManager/Pipeline.h"
#include "hermes/Optimizer/PassManager/PassManager.h"
#include "hermes/Optimizer/Scalar/Auditor.h"
#include "hermes/Optimizer/Scalar/DCE.h"
#include "hermes/Optimizer/Scalar/SimplifyCFG.h"
#include "hermes/Optimizer/Scalar/StackPromotion.h"
#include "hermes/Optimizer/Scalar/TypeInference.h"
#include "hermes/Optimizer/Scalar/CustomCallGraphProvider.h"
#include "hermes/Optimizer/Scalar/SimpleCallGraphProvider.h"

#include "llvh/Support/Debug.h"
#include "llvh/Support/raw_ostream.h"

#include "hermes/IR/CFG.h"

#include <map>
#include <string>
#include <queue>
#include <vector>
#include <list>
#include <chrono>
#include <set>
#include <regex>

namespace TaintAnalyzer {
using namespace hermes;

/*
// <- Class -> //
class Node 
{
private:
    std::string name;
    Function* func;
    std::vector<Function*> subFunctions;

public:
    Node(){};
    void setName(std::string name);
    void setFunction(Function* func);
    void setSubFunction(Function* func);
    std::string getName();
    Function* getFunction();
    std::vector<Function*> getSubFunctions();
};

class Graph 
{
private:
    std::vector<Node*> nodes;
public:
    Graph(){};
    void setNode(Node* n);
    std::vector<Node*> getNodes();
    void printNode();
};
*/

class SinkPair {
public:
    std::string url;
    std::string sink;
    std::list<std::string> taintList;

    SinkPair(std::string urlStr, std::string sinkStr, std::list<std::string> list) : url(urlStr), sink(sinkStr), taintList(list) {}
};

// <- Variables -> //
static std::multimap<std::string, std::pair<Instruction*, Function*>> functionMap; // key = 함수가 저장된 변수, 객체명, value = 함수 주소
static std::map<std::string, Function*> functionMap2;
static std::map<llvh::StringRef, bool> taintedFunctionMap;
//static std::map<Function*, std::map<std::string>> taintedFunctionList;
//static Graph functionGraph;
//static int recursiveCnt;

static std::list<llvh::StringRef> taintObjectMap = {
    
    // LoadPropertyInst -> LoadPropertyInst로 접근 가능한 Object
    llvh::StringRef("navigator"),
    llvh::StringRef("document"),
    llvh::StringRef("cookieStore"),
    llvh::StringRef("screen"),
    llvh::StringRef("window"),
    llvh::StringRef("visualViewport"),
    llvh::StringRef("userAgentData"),
    llvh::StringRef("performance"),
    llvh::StringRef("history"),
    llvh::StringRef("locationbar"),
    llvh::StringRef("mediaDevices"),
    llvh::StringRef("MediaSource"),
    llvh::StringRef("speechSynthesis"),
    llvh::StringRef("URL"),
    llvh::StringRef("Notification"),
    llvh::StringRef("location"),
    llvh::StringRef("console"),
    
    // LoadPropertyInst -> CallInst로 접근 가능한 Inst
    llvh::StringRef("getElementById"),
    llvh::StringRef("createElement"),
    llvh::StringRef("getContext"),
    llvh::StringRef("getShaderPrecisionFormat"),
    llvh::StringRef("animate"),
    llvh::StringRef("AudioBuffer"),

    // LoadPropertyInst -> ConstructInst로 접근 가능한 Inst
    llvh::StringRef("Date"),
    llvh::StringRef("WheelEvent"),
    llvh::StringRef("Gyroscope"),
    llvh::StringRef("AbsoluteOrientationSensor"),
    llvh::StringRef("DateTimeFormat"),
    

    // Sink Object
    //llvh::StringRef("WebSocket"),
    //llvh::StringRef("axios"),
    //llvh::StringRef("XMLHttpRequest")
};

static std::multimap<llvh::StringRef, llvh::StringRef> taintSourceMap = {
    {"userAgent", "navigator"},
    {"appVersion", "navigator"},
    {"platform", "navigator"},
    {"language", "navigator"},
    {"languages", "navigator"},
    {"cookieEnabled", "navigator"},
    {"doNotTrack", "navigator"},
    {"mimeTypes", "navigator"},
    {"vendor", "navigator"},
    {"webdriver", "navigator"},
    {"deviceMemory", "navigator"},
    {"maxTouchPoints", "navigator"},
    {"appName", "navigator"},
    {"hardwareConcurrency", "navigator"},
    {"product", "navigator"},
    {"productSub", "navigator"},
    {"appCodeName", "navigator"},
    {"vendorSub", "navigator"},
    {"plugins", "navigator"},
    {"mediaDevices", "navigator"},
    {"mediaCapabilities", "navigator"},
    {"connection", "navigator"},
    {"onLine", "navigator"},
    {"keyboard", "navigator"},
    {"permissions", "navigator"},
    {"storage", "navigator"},
    {"getBattery", "navigator"},
    {"javaEnabled", "navigator"},
    {"requestMediaKeySystemAccess", "navigator"},
    
    {"cookie", "document"},
    {"referrer", "document"},
    {"fonts", "document"},
    {"visibilityState", "document"},
    
    {"width", "screen"},
    {"height", "screen"},
    {"colorDepth", "screen"},
    {"availWidth", "screen"},
    {"availHeight", "screen"},
    {"availTop", "screen"},
    {"availLeft", "screen"},
    {"pixelDepth", "screen"},
    {"orientation", "screen"},

    {"innerWidth", "window"},
    {"innerHeight", "window"},
    {"outerWidth", "window"},
    {"outerHeight", "window"},
    {"pageXOffset", "window"},
    {"pageYOffset", "window"},
    {"devicePixelRatio", "window"},
    {"screenX", "window"},
    {"screenY", "window"},
    {"scrollX", "window"},
    {"scrollY", "window"},
    {"screenLeft", "window"},
    {"toolbar", "window"},
    {"locationbar", "window"},
    {"personalbar", "window"},
    {"menubar", "window"},
    {"statusbar", "window"},
    {"screenTop", "window"},
    {"scrollbars", "window"},
    {"top", "window"},
    {"localStorage", "window"},
    {"sessionStorage", "window"},
    {"name", "window"},
    {"indexedDB", "window"},
    {"matchMedia", "window"},
    {"openDatabase", "window"},

    {"height", "visualViewport"},
    {"width", "visualViewport"},
    {"pageLeft", "visualViewport"},
    {"scale", "visualViewport"},
    {"offsetLeft", "visualViewport"},
    {"offsetTop", "visualViewport"},
    {"pageTop", "visualViewport"},

    {"brands", "userAgentData"},
    {"getHighEntropyValues", "userAgentData"},

    {"memory", "performance"},
    {"now", "performance"},

    {"length", "history"},
    {"visible", "locationbar"},
    {"enumerateDevices", "mediaDevices"},
    {"isTypeSupported", "MediaSource"},
    {"getVoices", "speechSynthesis"},
    {"createObjectURL", "URL"},
    {"permission", "Notification"},
    {"href", "location"},
    {"memory", "console"},
    // CallInst Object
    /*
    const canvas = document.getElementById("canvas");
    const dataURL = canvas.toDataURL();
    const toBlob = canvas.toBlob();
    console.log(dataURL);
    */
    /*
    const canvas = document.getElementById("canvas");
    const ctx = canvas.getContext("2d");

    let text = ctx.measureText("Hello world");
    console.log(text.width); // 56;
    */
    {"toDataURL", "createElement"},
    {"toBlob", "createElement"},
    {"canPlayType", "createElement"},

    {"measureText", "getContext"},
    {"getImageData", "getContext"},
    {"isPointInPath", "getContext"},

    {"getSupportedExtensions", "getContext"},
    {"getParameter", "getContext"},
    {"getShaderPrecisionFormat", "getContext"},
    {"getContextAttributes", "getContext"},
    {"readPixels", "getContext"},
    /*
    const canvas = document.getElementById("canvas");
    const gl = canvas.getContext("webgl");

    gl.getShaderPrecisionFormat(gl.VERTEX_SHADER, gl.MEDIUM_FLOAT).precision; // 23
    gl.getShaderPrecisionFormat(gl.FRAGMENT_SHADER, gl.LOW_INT).precision; // 0
    */
    {"precision", "getShaderPrecisionFormat"},
    {"rangeMin", "getShaderPrecisionFormat"},
    {"rangeMax", "getShaderPrecisionFormat"},
    /*
    const canvas = document.getElementById("canvas");
    const gl = canvas.getContext("webgl");
    const pixels = new Uint8Array( gl.drawingBufferWidth * gl.drawingBufferHeight * 4, );
    gl.readPixels(0, 0, gl.drawingBufferWidth, gl.drawingBufferHeight, gl.RGBA, gl.UNSIGNED_BYTE, pixels,);
    console.log(pixels); // Uint8Array
    */
    {"getChannelData", "AudioBuffer"},

    {"currentTime", "Animation"},
    {"startTime", "Animation"},
   
    // ConstructInst Object
    {"getTime", "Date"},
    {"getTimezoneOffset", "Date"},
    
    {"deltaX", "WheelEvent"},
    {"deltaY", "WheelEvent"},
    {"deltaZ", "WheelEvent"},

    {"x", "Gyroscope"},
    {"y", "Gyroscope"},
    {"z", "Gyroscope"},

    {"start", "AbsoluteOrientationSensor"},
    {"resolvedOptions", "DateTimeFormat"},

    // Construct only
    {"OfflineAudioContext", "constructor"},
    {"Function", "constructor"},
};

static std::multimap<llvh::StringRef, llvh::StringRef> taintSinkMap = {
    // 아래 명령은 LoadProperty 하나로 처리해도 될 것 같다
    {"fetch", "method"}, // %0 : url, %1 : data
    {"get", "axios"}, // %0 : url, %1 : data
    {"post", "axios"}, // %0 : url, %1 : data

    {"open", "XMLHttpRequest"},
    {"send", "XMLHttpRequest"},
    {"send", "WebSocket"},
    {"sendBeacon", "navigator"}    
};

// <- Methods -> //
//template <typename T>
/*static constexpr inline auto ptrToAddr(T *pointer);

void printFunctionMap();
void printFunctionMap2();

void setFunctionMap(Function* Func);
void setFunctionMap2(Function* Func);
void setGraph(Graph* functionGraph, Function* Func);
void setParamsFunc(Node* n, Instruction* I);

std::string getCallInstStr(CallInst* CI);
Function* findFuncFromStr(std::string varName, Instruction* I);
*/

bool isURL(llvh::StringRef input);
void setFunction(Function* func);
void setAsTaintSource();
void setTaint();
void printTaintSinkDetails();
void isTainted();


std::pair<bool, std::list<std::string>> runFunction(Function* Func, std::vector<std::pair<bool,Value*>> params);
void propagate(Instruction* Inst);


// <- Output ->
static int numOfFunc;
static int numOfTaintedFunc;
static int sourceCnt;
static int sinkCnt;
static int leakCnt;
static std::list<std::string> sourceList;
static std::list<std::string> sinkList;
static std::list<SinkPair> leakList;
}
