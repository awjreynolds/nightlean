#include "../include/noctium_control.h"
#include <cassert>
#include <cstdint>
#include <fstream>
#include <functional>
#include <iostream>
#include <map>
#include <sstream>
#include <string>
#include <vector>

static std::string take(uint64_t token, bool secret=false) {
  size_t length=0,written=99;
  if(secret){assert(noctium_control_result_length(token,&length)==NOCTIUM_CONTROL_INVALID_HANDLE);assert(noctium_control_private_length(token,&length)==NOCTIUM_CONTROL_OK);}
  else assert(noctium_control_result_length(token,&length)==NOCTIUM_CONTROL_OK);
  std::string bytes(length,'\0');
  const auto copied=secret?noctium_control_private_copy(token,reinterpret_cast<uint8_t*>(bytes.data()),length,&written):noctium_control_result_copy(token,reinterpret_cast<uint8_t*>(bytes.data()),length,&written);
  assert(copied==NOCTIUM_CONTROL_OK&&written==length);
  assert((secret?noctium_control_private_free(token):noctium_control_result_free(token))==NOCTIUM_CONTROL_OK);
  return bytes;
}
static std::string field(const std::string &json,const std::string &name) {
  const auto prefix="\""+name+"\":\"";const auto found=json.find(prefix);assert(found!=std::string::npos);
  const auto start=found+prefix.size(),end=json.find('"',start);assert(end!=std::string::npos);return json.substr(start,end-start);
}
static std::string request_id(const std::string &json) {
  const auto prefix=std::string("\"id\":");const auto found=json.find(prefix);assert(found!=std::string::npos);
  const auto start=found+prefix.size(),end=json.find_first_not_of("0123456789",start);return json.substr(start,end-start);
}
static std::string context(bool providers=true) {
  const auto grants="[\"witness.bool.v1\",\"witness.native.v1\",\"private_state.stage.v1\",\"private_state.compare_exchange.v1\"]";
  return "{\"protocolVersion\":1,\"namespace\":\"test\",\"baseRevision\":\"r0\",\"attemptId\":\""+std::string(64,'a')+"\",\"capabilities\":[{\"id\":\"store\",\"namespace\":\"test\",\"keyPrefix\":\"counter/\",\"operations\":"+grants+"}],\"operations\":[{\"operation\":\"witness.bool.v1\",\"argumentSchema\":{},\"resultSchema\":\"Bool\"},{\"operation\":\"witness.native.v1\",\"argumentSchema\":{},\"resultSchema\":\"Native\"}],\"providers\":"+(providers?"[{\"input\":\"flag\",\"operation\":\"witness.bool.v1\",\"capability\":\"store\",\"arguments\":{}},{\"input\":\"left\",\"operation\":\"witness.native.v1\",\"capability\":\"store\",\"arguments\":{}},{\"input\":\"right\",\"operation\":\"witness.native.v1\",\"capability\":\"store\",\"arguments\":{}}]":"[]")+",\"commitCapability\":\"store\",\"limits\":{\"requests\":64,\"writes\":64,\"privateBytes\":65536}}";
}
static uint64_t begin(const std::string &plan,bool active,bool providers=true) {
  const auto inputs=providers?(active?"{\"active\":true}":"{\"active\":false}"):"{}";
  const auto envelope="{\"abiVersion\":1,\"plan\":"+plan+",\"inputs\":"+inputs+",\"hostContext\":"+context(providers)+"}";
  uint64_t session=0;assert(noctium_control_begin(reinterpret_cast<const uint8_t*>(envelope.data()),envelope.size(),&session)==NOCTIUM_CONTROL_OK);return session;
}
struct Outcome {std::string status,trace;std::vector<std::string> calls;};
static Outcome run(const std::string &plan,bool active,bool providers=true) {
  const auto session=begin(plan,active,providers);
  std::map<std::string,std::function<std::string(const std::string&)>> callbacks{{"flag",[](const std::string&){return "true";}},{"left",[](const std::string&){return "\"11\"";}},{"right",[](const std::string& private_request){assert(private_request.find("\"counter/value\":{\"type\":\"Native\",\"value\":\"1\"}")!=std::string::npos);return "\"22\"";}}};
  Outcome output;
  for(;;){uint64_t result=0;assert(noctium_control_advance(session,&result)==NOCTIUM_CONTROL_OK);const auto status=take(result);assert(status.find("trace")==std::string::npos);if(status.find("\"status\":\"need_host\"")==std::string::npos){output.status=status;break;}
    uint64_t repeated=0;assert(noctium_control_advance(session,&repeated)==NOCTIUM_CONTROL_OK);assert(take(repeated)==status);
    const auto name=field(status,"name");assert(callbacks.count(name));output.calls.push_back(name);
    uint64_t private_args=0;assert(noctium_control_private_request(session,&private_args)==NOCTIUM_CONTROL_OK);const auto private_request=take(private_args,true);
    const auto reply="{\"abiVersion\":1,\"requestId\":"+request_id(status)+",\"operation\":\""+field(status,"operation")+"\",\"capability\":\""+field(status,"capability")+"\",\"schema\":\""+field(status,"schema")+"\",\"value\":"+callbacks.at(name)(private_request)+"}";
    assert(noctium_control_resume(session,reinterpret_cast<const uint8_t*>(reply.data()),reply.size(),&result)==NOCTIUM_CONTROL_OK);take(result);
  }
  uint64_t trace=0;assert(noctium_control_private_trace(session,&trace)==NOCTIUM_CONTROL_OK);output.trace=take(trace,true);assert(noctium_control_free(session)==NOCTIUM_CONTROL_OK);return output;
}
int main(int argc,char **argv) {
  assert(argc>=2&&argc<=6);std::ifstream stream(argv[1]);assert(stream.good());std::stringstream buffer;buffer<<stream.rdbuf();const auto plan=buffer.str();
  const auto inactive=run(plan,false);assert(field(inactive.status,"status")=="completed");assert(field(inactive.status,"result")=="7");assert(inactive.calls.empty());assert(inactive.trace=="{\"events\":[],\"protocolVersion\":1}");
  const auto active=run(plan,true);assert(field(active.status,"status")=="completed");assert(field(active.status,"result")=="22");assert((active.calls==std::vector<std::string>{"flag","left","right"}));assert(active.trace=="{\"events\":[\"witness:flag\",\"witness:left\",\"stage\",\"witness:right\"],\"protocolVersion\":1}");
  const std::string failed="{\"schemaVersion\":1,\"kind\":\"host-control\",\"name\":\"failure\",\"inputs\":[],\"witnesses\":[],\"functions\":[{\"id\":\"s0d0\",\"name\":\"main\",\"parameters\":[],\"resultType\":\"Native\",\"body\":[{\"tag\":\"assert\",\"condition\":{\"tag\":\"bool\",\"value\":false}},{\"tag\":\"return\",\"value\":{\"tag\":\"constant\",\"value\":\"0\"}}]}],\"entry\":\"s0d0\",\"limits\":{\"maxSteps\":131072}}";
  std::string failure_source=failed;
  if(argc>=3){std::ifstream source(argv[2]);assert(source.good());std::stringstream bytes;bytes<<source.rdbuf();failure_source=bytes.str();}
  const auto failure=run(failure_source,false,false);assert(field(failure.status,"status")=="failed");assert(failure.status.find("execution_rejected")!=std::string::npos);assert(failure.calls.empty());assert(failure.trace=="{\"events\":[],\"protocolVersion\":1}");
  const auto cancelled=begin(plan,true);uint64_t result=0;assert(noctium_control_advance(cancelled,&result)==NOCTIUM_CONTROL_OK);take(result);assert(noctium_control_cancel(cancelled,&result)==NOCTIUM_CONTROL_OK);take(result);assert(noctium_control_private_request(cancelled,&result)==NOCTIUM_CONTROL_INVALID_STATE);assert(noctium_control_free(cancelled)==NOCTIUM_CONTROL_OK);
  for(int index=3;index<argc;++index){
    std::ifstream fixture(argv[index]);assert(fixture.good());std::stringstream content;content<<fixture.rdbuf();
    for(const bool flag:std::vector<bool>{false,true}){
      const auto inputs=index==3?std::string("{}"):std::string("{\"flag\":")+(flag?"true":"false")+"}";
      const auto envelope="{\"abiVersion\":1,\"plan\":"+content.str()+",\"inputs\":"+inputs+",\"hostContext\":"+context(false)+"}";
      uint64_t session=0;assert(noctium_control_begin(reinterpret_cast<const uint8_t*>(envelope.data()),envelope.size(),&session)==NOCTIUM_CONTROL_OK);
      uint64_t token=0;assert(noctium_control_advance(session,&token)==NOCTIUM_CONTROL_OK);const auto status=take(token);assert(field(status,"status")=="completed");
      if(index==5)assert(field(status,"result")=="2");else assert(status.find("\"result\":null")!=std::string::npos);
      assert(noctium_control_private_trace(session,&token)==NOCTIUM_CONTROL_OK);assert(take(token,true)=="{\"events\":[],\"protocolVersion\":1}");assert(noctium_control_free(session)==NOCTIUM_CONTROL_OK);
    }
  }
  std::cout<<"{\"adapter\":\"C++ C ABI\",\"activeResult\":\"22\",\"activeCallbacks\":3,\"activeStages\":1,\"inactiveResult\":\"7\",\"inactiveCallbacks\":0,\"inactiveStages\":0,\"failureRejected\":true,\"cancelled\":true,\"unitConditional\":"<<(argc>=4?"true":"false")<<",\"unitPrivateBranches\":"<<(argc>=5?"true":"false")<<",\"constantInactiveReturn\":"<<(argc>=6?"true":"false")<<",\"nativeGuardQualified\":false}\n";
}
