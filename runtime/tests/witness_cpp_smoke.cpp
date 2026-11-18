#include "../include/noctium_control.h"
#include "../include/noctium_native.h"
#include <cassert>
#include <cctype>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
#include <algorithm>
#include <chrono>
#include <thread>
#include <fcntl.h>
#include <unistd.h>
#include <sys/random.h>

static std::string take(uint64_t token, bool secret=false) {
  size_t length=0, written=99;
  if (secret) {
    assert(noctium_control_result_length(token,&length)==NOCTIUM_CONTROL_INVALID_HANDLE);
    assert(noctium_control_private_length(token,&length)==NOCTIUM_CONTROL_OK);
  } else {
    assert(noctium_control_result_length(token,&length)==NOCTIUM_CONTROL_OK);
  }
  std::string bytes(length,'\0');
  const auto copied=secret
      ? noctium_control_private_copy(token,reinterpret_cast<uint8_t*>(bytes.data()),length,&written)
      : noctium_control_result_copy(token,reinterpret_cast<uint8_t*>(bytes.data()),length,&written);
  assert(copied==NOCTIUM_CONTROL_OK&&written==length);
  assert((secret?noctium_control_private_free(token):noctium_control_result_free(token))==NOCTIUM_CONTROL_OK);
  return bytes;
}

static std::string field(const std::string &json,const std::string &name) {
  static size_t lookup=0;
  ++lookup;
  const auto prefix="\""+name+"\":\"";
  const auto found=json.find(prefix);
  if(found==std::string::npos){
    std::cerr<<"missing JSON string field: "<<name<<" (lookup "<<lookup<<")"<<std::endl;
    assert(false&&"required JSON string field is missing");
  }
  const auto start=found+prefix.size(),end=json.find('"',start);
  assert(end!=std::string::npos);
  return json.substr(start,end-start);
}
static std::string last_field(const std::string &json,const std::string &name) {
  const auto prefix="\""+name+"\":\"";
  const auto found=json.rfind(prefix);
  assert(found!=std::string::npos);
  const auto start=found+prefix.size(),end=json.find('"',start);
  assert(end!=std::string::npos);
  return json.substr(start,end-start);
}
static std::string numeric_field(const std::string &json,const std::string &name) {
  const auto prefix="\""+name+"\":";
  const auto found=json.find(prefix);
  assert(found!=std::string::npos);
  auto start=found+prefix.size();
  while(start<json.size()&&json[start]==' ')++start;
  const auto end=json.find_first_not_of("0123456789",start);
  assert(end!=std::string::npos&&end>start);
  return json.substr(start,end-start);
}

static std::string object_field(const std::string& json,const std::string& name) {
  const auto key=json.find("\""+name+"\":");
  assert(key!=std::string::npos);
  const auto start=json.find('{',key);
  assert(start!=std::string::npos);
  unsigned depth=0;
  bool quoted=false,escaped=false;
  for(auto end=start;end<json.size();++end){
    const char byte=json[end];
    if(quoted){
      if(escaped)escaped=false;
      else if(byte=='\\')escaped=true;
      else if(byte=='"')quoted=false;
      continue;
    }
    if(byte=='"'){quoted=true;continue;}
    if(byte=='{')++depth;
    else if(byte=='}'&&--depth==0)return json.substr(start,end-start+1);
  }
  assert(false&&"unterminated JSON object field");
  return {};
}

static void persist_public_evidence(const std::string& path,const std::string& profile,
  const std::string& address,const std::string& deployment_receipt,
  const std::string& call_receipt,size_t provider_calls,bool source_state_matched) {
  std::ofstream output(path,std::ios::binary|std::ios::trunc);
  assert(output.good());
  output<<"{\"abiVersion\":1,\"profile\":\""<<profile
    <<"\",\"contractAddress\":\""<<address<<"\",\"deployment\":"
    <<(deployment_receipt.empty()?"null":deployment_receipt)<<",\"call\":"
    <<(call_receipt.empty()?"null":call_receipt)<<",\"providerCallCount\":"
    <<provider_calls<<",\"sourcePrivateValueMatched\":"
    <<(source_state_matched?"true":"false")<<"}\n";
  output.flush();
  assert(output.good());
}

static std::string read_file(const char *path) {
  std::ifstream stream(path);
  assert(stream.good());
  std::stringstream bytes;
  bytes << stream.rdbuf();
  return bytes.str();
}

static std::string take_native(uint64_t token,bool secret=false) {
  size_t length=0,written=99;
  if(secret){
    assert(noctium_native_result_length(token,&length)==NOCTIUM_NATIVE_INVALID_HANDLE);
    assert(noctium_native_private_length(token,&length)==NOCTIUM_NATIVE_OK);
  } else {
    assert(noctium_native_result_length(token,&length)==NOCTIUM_NATIVE_OK);
  }
  std::string bytes(length,'\0');
  const auto copied=secret
      ?noctium_native_private_copy(token,reinterpret_cast<uint8_t*>(bytes.data()),length,&written)
      :noctium_native_result_copy(token,reinterpret_cast<uint8_t*>(bytes.data()),length,&written);
  assert(copied==NOCTIUM_NATIVE_OK&&written==length);
  assert((secret?noctium_native_private_free(token):noctium_native_result_free(token))==NOCTIUM_NATIVE_OK);
  return bytes;
}

static std::string fresh_attempt() {
  std::string value(32,'\0');
  assert(getentropy(value.data(),value.size())==0);
  static const char* digits="0123456789abcdef";
  std::string encoded;
  encoded.reserve(64);
  for(unsigned char byte:value){encoded+=digits[byte>>4];encoded+=digits[byte&15];}
  for(volatile char& byte:value)byte=0;
  return encoded;
}

static uint64_t open_localnet(const std::string& config) {
  std::vector<uint8_t> seed(32,0);
  seed[31]=1;
  uint64_t adapter=0;
  const auto status=noctium_localnet_open(
    reinterpret_cast<const uint8_t*>(config.data()),config.size(),seed.data(),seed.size(),&adapter
  );
  if(status!=NOCTIUM_NATIVE_OK){
    std::cerr<<"localnet open failed with status "<<status<<std::endl;
    assert(false&&"localnet adapter did not open");
  }
  for(volatile uint8_t& byte:seed)byte=0;
  return adapter;
}

static std::string replace_number(std::string json,const std::string& name,const std::string& value) {
  const auto key=json.find("\""+name+"\"");
  assert(key!=std::string::npos);
  auto start=json.find(':',key);
  assert(start!=std::string::npos);
  ++start;
  while(start<json.size()&&std::isspace(static_cast<unsigned char>(json[start])))++start;
  auto end=start;
  while(end<json.size()&&std::isdigit(static_cast<unsigned char>(json[end])))++end;
  assert(end>start);
  json.replace(start,end-start,value);
  return json;
}

static std::string replace_string(std::string json,const std::string& name,const std::string& value) {
  const auto key=json.find("\""+name+"\"");
  assert(key!=std::string::npos);
  auto start=json.find(':',key);
  assert(start!=std::string::npos);
  ++start;
  while(start<json.size()&&std::isspace(static_cast<unsigned char>(json[start])))++start;
  assert(start<json.size()&&json[start]=='\"');
  auto end=start+1;
  bool escaped=false;
  for(;end<json.size();++end){
    if(escaped){escaped=false;continue;}
    if(json[end]=='\\'){escaped=true;continue;}
    if(json[end]=='\"')break;
  }
  assert(end<json.size());
  json.replace(start,end-start+1,"\""+value+"\"");
  return json;
}

static std::string client_metadata(const std::string& json) {
  return "{\"abiVersion\":1,\"requestId\":\""+field(json,"requestId")+
    "\",\"operation\":\""+field(json,"operation")+"\",\"capability\":\""+
    field(json,"capability")+"\",\"schema\":\""+field(json,"schema")+
    "\",\"profile\":\""+field(json,"profile")+"\"}";
}

static std::string drive_client(uint64_t client,uint64_t adapter,std::string status={}) {
  for(unsigned step=0;step<2048;++step){
    if(status.empty()){
      uint64_t result=0;
      assert(noctium_client_advance(client,&result)==NOCTIUM_NATIVE_OK);
      status=take_native(result);
    }
    if(field(status,"status")!="need_host")return status;
    uint64_t request=0;
    assert(noctium_client_request(client,&request)==NOCTIUM_NATIVE_OK);
    if(status.find("\"hasPrivateArguments\":true")!=std::string::npos){
      uint64_t private_token=0;
      assert(noctium_client_private_request(request,&private_token)==NOCTIUM_NATIVE_OK);
      auto private_bytes=take_native(private_token,true);
      assert(!private_bytes.empty());
      for(volatile char& byte:private_bytes)byte=0;
    }
    auto entropy=std::string(32,'\0');
    assert(getentropy(entropy.data(),entropy.size())==0);
    uint64_t reply=0;
    const auto resolved=noctium_localnet_resolve(
      adapter,request,1,reinterpret_cast<const uint8_t*>(entropy.data()),entropy.size(),&reply
    );
    for(volatile char& byte:entropy)byte=0;
    assert(resolved==NOCTIUM_NATIVE_OK);
    const auto metadata=client_metadata(status);
    uint64_t result=0;
    assert(noctium_client_resume(client,
      reinterpret_cast<const uint8_t*>(metadata.data()),metadata.size(),reply,&result)==NOCTIUM_NATIVE_OK);
    status=take_native(result);
  }
  assert(false&&"native client exceeded the smoke-test step bound");
  return {};
}

static std::string client_command(uint64_t client,uint64_t adapter,const std::string& command) {
  uint64_t result=0;
  assert(noctium_client_command(client,
    reinterpret_cast<const uint8_t*>(command.data()),command.size(),&result)==NOCTIUM_NATIVE_OK);
  return drive_client(client,adapter,take_native(result));
}

static std::string observe_client(uint64_t client,uint64_t adapter) {
  for(unsigned retry=0;retry<180;++retry){
    const auto status=client_command(client,adapter,"observe");
    if(status.find("\"receipt\":")!=std::string::npos)return status;
    assert(field(status,"status")=="step_done");
    std::this_thread::sleep_for(std::chrono::milliseconds(500));
  }
  assert(false&&"native client did not observe finality");
  return {};
}

static std::string deployment_context(const std::string& attempt,const std::string& name_space) {
  return "{\"protocolVersion\":1,\"namespace\":\""+name_space+
    "\",\"baseRevision\":\"r0\",\"attemptId\":\""+attempt+
    "\",\"capabilities\":[{\"id\":\"store\",\"namespace\":\""+name_space+
    "\",\"keyPrefix\":\"claims/\",\"operations\":[\"private_state.stage.v1\","
    "\"private_state.compare_exchange.v1\"]}],\"operations\":[],\"providers\":[],"
    "\"commitCapability\":\"store\"}";
}

static std::string read_local_private_value(uint64_t adapter,const std::string& name_space,const std::string& key) {
  const auto query="{\"namespace\":\""+name_space+"\",\"key\":\""+key+"\"}";
  uint64_t token=0;
  assert(noctium_localnet_private_value(adapter,
    reinterpret_cast<const uint8_t*>(query.data()),query.size(),&token)==NOCTIUM_NATIVE_OK);
  return take_native(token,true);
}

static std::string witness_host_context(const std::string& attempt,const std::string& name_space) {
  return "{\"protocolVersion\":1,\"namespace\":\""+name_space+"\",\"baseRevision\":\"r0\","
    "\"attemptId\":\""+attempt+"\",\"capabilities\":["
    "{\"id\":\"private\",\"namespace\":\""+name_space+"\",\"keyPrefix\":\"cache/\","
    "\"operations\":[\"private_state.read.v1\",\"private_state.stage.v1\",\"private_state.compare_exchange.v1\"]},"
    "{\"id\":\"lookup\",\"namespace\":\""+name_space+"\",\"keyPrefix\":\"lookup/\","
    "\"operations\":[\"noctium.lookup.v1\"]}],\"operations\":["
    "{\"operation\":\"private_state.read.v1\",\"argumentSchema\":{\"key\":\"Key\"},"
    "\"resultSchema\":\"UIntRange<256>\"},"
    "{\"operation\":\"noctium.lookup.v1\",\"argumentSchema\":{\"seed\":\"UIntRange<256>\"},"
    "\"resultSchema\":\"UIntRange<256>\"}],\"providers\":["
    "{\"input\":\"cache\",\"operation\":\"private_state.read.v1\","
    "\"capability\":\"private\",\"arguments\":{\"key\":\"cache/last\"}},"
    "{\"input\":\"lookup\",\"operation\":\"noctium.lookup.v1\","
    "\"capability\":\"lookup\",\"arguments\":{}}],\"commitCapability\":\"private\","
    "\"limits\":{\"requests\":64,\"writes\":64,\"privateBytes\":65536}}";
}

static int run_native_witness(int argc,char** argv) {
  assert(argc==11);
  auto target_descriptor=read_file(argv[2]);
  const auto state_config=read_file(argv[3]);
  const auto parameters=read_file(argv[4]);
  const auto plan=read_file(argv[5]);
  const auto client_descriptor=read_file(argv[6]);
  auto localnet_config=read_file(argv[7]);
  const std::string evidence_path=argv[8];
  const auto alternate_parameters=read_file(argv[9]);
  const std::string alternate_parameter_hash=argv[10];
  const auto run_id=fresh_attempt();
  const auto journal_directory="/private/tmp/noctium-witness62-cpp-"+run_id.substr(0,16)+"/journal";
  localnet_config=replace_string(localnet_config,"journalDirectory",journal_directory);
  const auto adapter=open_localnet(localnet_config);
  uint64_t result=0;
  assert(noctium_localnet_context(adapter,&result)==NOCTIUM_NATIVE_OK);
  const auto chain_context=take_native(result);
  const auto future_ttl=std::to_string(std::stoull(field(chain_context,"blockTime"))+1800);
  target_descriptor=replace_number(target_descriptor,"ttl",future_ttl);
  const auto profile=field(target_descriptor,"profile");
  const auto manifest=field(target_descriptor,"trustedManifestSha256");
  const auto parameter_hash=field(target_descriptor,"proofParametersSha256");
  const auto k=numeric_field(target_descriptor,"k");
  const auto ttl=numeric_field(target_descriptor,"ttl");
  const auto proof_descriptor=
    "{\"abiVersion\":1,\"profile\":\""+profile+"\",\"trustedManifestSha256\":\""+manifest+
    "\",\"proofParametersSha256\":\""+parameter_hash+"\",\"k\":"+k+",\"ttl\":"+ttl+
    ",\"proofServiceCapability\":\"host.prover\",\"maxResponseBytes\":1048576}";
  auto target_coins=std::string(32,'\0');
  assert(getentropy(target_coins.data(),target_coins.size())==0);
  uint64_t target=0;
  assert(noctium_native_witness_target_begin(
    reinterpret_cast<const uint8_t*>(target_descriptor.data()),target_descriptor.size(),
    reinterpret_cast<const uint8_t*>(state_config.data()),state_config.size(),
    reinterpret_cast<const uint8_t*>(parameters.data()),parameters.size(),
    reinterpret_cast<const uint8_t*>(target_coins.data()),target_coins.size(),&target,&result
  )==NOCTIUM_NATIVE_OK);
  for(volatile char& byte:target_coins)byte=0;
  const auto prepared_target=take_native(result);
  assert(field(prepared_target,"status")=="target_ready");
  assert(field(prepared_target,"entrypoint")=="claim");
  const auto contract_address=field(prepared_target,"contractAddress");

  const auto incomplete_attempt=fresh_attempt();
  const auto incomplete_context=witness_host_context(incomplete_attempt,"noctium-witness62-incomplete-"+incomplete_attempt.substr(0,12));
  const auto incomplete_begin="{\"abiVersion\":1,\"inputs\":{\"expected\":\"14\",\"seed\":\"7\"},\"hostContext\":"+incomplete_context+"}";
  uint64_t incomplete_control=0;
  assert(noctium_control_begin_from_native_target(
    target,reinterpret_cast<const uint8_t*>(plan.data()),plan.size(),
    reinterpret_cast<const uint8_t*>(incomplete_begin.data()),incomplete_begin.size(),&incomplete_control
  )==NOCTIUM_CONTROL_OK);
  auto incomplete_coins=std::string(32,'\0');
  assert(getentropy(incomplete_coins.data(),incomplete_coins.size())==0);
  uint64_t rejected_proof=99;
  assert(noctium_native_begin_from_witness(
    reinterpret_cast<const uint8_t*>(proof_descriptor.data()),proof_descriptor.size(),target,incomplete_control,
    reinterpret_cast<const uint8_t*>(parameters.data()),parameters.size(),
    reinterpret_cast<const uint8_t*>(incomplete_coins.data()),incomplete_coins.size(),&rejected_proof
  )==NOCTIUM_NATIVE_INVALID_STATE&&rejected_proof==0);
  for(volatile char& byte:incomplete_coins)byte=0;
  assert(noctium_control_advance(incomplete_control,&result)==NOCTIUM_CONTROL_OK);
  assert(take(result).find("\"status\":\"need_host\"")!=std::string::npos);
  assert(noctium_control_cancel(incomplete_control,&result)==NOCTIUM_CONTROL_OK);
  assert(take(result).find("\"status\":\"cancelled\"")!=std::string::npos);
  auto cancelled_coins=std::string(32,'\0');
  assert(getentropy(cancelled_coins.data(),cancelled_coins.size())==0);
  assert(noctium_native_begin_from_witness(
    reinterpret_cast<const uint8_t*>(proof_descriptor.data()),proof_descriptor.size(),target,incomplete_control,
    reinterpret_cast<const uint8_t*>(parameters.data()),parameters.size(),
    reinterpret_cast<const uint8_t*>(cancelled_coins.data()),cancelled_coins.size(),&rejected_proof
  )==NOCTIUM_NATIVE_INVALID_STATE&&rejected_proof==0);
  for(volatile char& byte:cancelled_coins)byte=0;
  assert(noctium_control_free(incomplete_control)==NOCTIUM_CONTROL_OK);

  const auto attempt=fresh_attempt();
  const auto source_namespace="noctium-witness62-source-"+attempt.substr(0,16);
  const auto host_context=witness_host_context(attempt,source_namespace);
  const auto begin="{\"abiVersion\":1,\"inputs\":{\"expected\":\"14\",\"seed\":\"7\"},\"hostContext\":"+host_context+"}";
  uint64_t control=0;
  assert(noctium_control_begin_from_native_target(
    target,reinterpret_cast<const uint8_t*>(plan.data()),plan.size(),
    reinterpret_cast<const uint8_t*>(begin.data()),begin.size(),&control
  )==NOCTIUM_CONTROL_OK);
  const std::string forged_source_stage=
    "{\"abiVersion\":2,\"operation\":\"private_state.stage.v1\","
    "\"capability\":\"private\",\"key\":\"cache/forged\","
    "\"type\":\"UIntRange<256>\",\"value\":\"999\"}";
  uint64_t denied_source_stage=99;
  assert(noctium_control_stage(control,
    reinterpret_cast<const uint8_t*>(forged_source_stage.data()),forged_source_stage.size(),
    &denied_source_stage)==NOCTIUM_CONTROL_INVALID_RESPONSE&&denied_source_stage==0);
  std::vector<std::string> calls;
  bool completed=false;
  for(unsigned step=0;step<64;++step){
    uint64_t token=0;
    assert(noctium_control_advance(control,&token)==NOCTIUM_CONTROL_OK);
    const auto pending=take(token);
    if(pending.find("\"status\":\"completed\"")!=std::string::npos){completed=true;break;}
    assert(pending.find("\"status\":\"need_host\"")!=std::string::npos);
    const auto name=last_field(pending,"name");
    calls.push_back(name);
    std::string private_request;
    for(unsigned export_count=0;export_count<1024;++export_count){
      uint64_t private_token=0;
      assert(noctium_control_private_request(control,&private_token)==NOCTIUM_CONTROL_OK);
      const auto exported=take(private_token,true);
      if(export_count==0)private_request=exported;
      else assert(exported==private_request);
    }
    std::string value;
    if(name=="cache"){
      assert(private_request.find("\"key\":\"cache/last\"")!=std::string::npos);
      assert(private_request.find("\"cache/last\":{\"type\":\"UIntRange<256>\",\"value\":\"1\"}")!=std::string::npos);
      value="\"1\"";
    } else {
      assert(name=="lookup");
      assert(private_request.find("\"seed\":\"7\"")!=std::string::npos);
      value="\"14\"";
    }
    const auto response="{\"protocolVersion\":2,\"requestId\":\""+field(pending,"requestId")+
      "\",\"attemptId\":\""+attempt+"\",\"outcome\":\"value\",\"operation\":\""+
      field(pending,"operation")+"\",\"capability\":\""+field(pending,"capability")+
      "\",\"schema\":\""+field(pending,"schema")+"\",\"value\":"+value+"}";
    assert(noctium_control_resume_typed(control,
      reinterpret_cast<const uint8_t*>(response.data()),response.size(),&token)==NOCTIUM_CONTROL_OK);
    take(token);
  }
  assert(completed);
  assert((calls==std::vector<std::string>{"cache","cache","lookup","cache","lookup"}));

  auto proof_coins=std::string(32,'\0');
  assert(getentropy(proof_coins.data(),proof_coins.size())==0);
  auto mismatched_coins=std::string(32,'\0');
  assert(getentropy(mismatched_coins.data(),mismatched_coins.size())==0);
  const auto mismatched_descriptor=replace_string(
    proof_descriptor,"proofParametersSha256",alternate_parameter_hash);
  uint64_t mismatched_proof=99;
  assert(noctium_native_begin_from_witness(
    reinterpret_cast<const uint8_t*>(mismatched_descriptor.data()),mismatched_descriptor.size(),
    target,control,
    reinterpret_cast<const uint8_t*>(alternate_parameters.data()),alternate_parameters.size(),
    reinterpret_cast<const uint8_t*>(mismatched_coins.data()),mismatched_coins.size(),
    &mismatched_proof
  )==NOCTIUM_NATIVE_INVALID_ARGUMENT&&mismatched_proof==0);
  for(volatile char& byte:mismatched_coins)byte=0;
  assert(noctium_control_advance(control,&result)==NOCTIUM_CONTROL_OK);
  assert(take(result).find("\"status\":\"completed\"")!=std::string::npos);
  uint64_t proof=0;
  assert(noctium_native_begin_from_witness(
    reinterpret_cast<const uint8_t*>(proof_descriptor.data()),proof_descriptor.size(),target,control,
    reinterpret_cast<const uint8_t*>(parameters.data()),parameters.size(),
    reinterpret_cast<const uint8_t*>(proof_coins.data()),proof_coins.size(),&proof
  )==NOCTIUM_NATIVE_OK);
  for(volatile char& byte:proof_coins)byte=0;
  assert(noctium_native_advance(proof,&result)==NOCTIUM_NATIVE_OK);
  const auto proof_request=take_native(result);
  assert(field(proof_request,"status")=="need_proof");
  uint64_t request=0;
  assert(noctium_native_private_request(proof,&request)==NOCTIUM_NATIVE_OK);
  auto prove_coins=std::string(32,'\0');
  assert(getentropy(prove_coins.data(),prove_coins.size())==0);
  assert(noctium_native_local_prove(request,
    reinterpret_cast<const uint8_t*>(prove_coins.data()),prove_coins.size(),&result)==NOCTIUM_NATIVE_OK);
  for(volatile char& byte:prove_coins)byte=0;
  const auto proof_response=take_native(result);
  const auto proof_reply="{\"abiVersion\":1,\"requestId\":"+numeric_field(proof_request,"requestId")+
    ",\"operation\":\"native.prove.v1\",\"capability\":\""+field(proof_request,"capability")+
    "\",\"profile\":\""+field(proof_request,"profile")+"\"}";
  assert(noctium_native_resume(proof,
    reinterpret_cast<const uint8_t*>(proof_reply.data()),proof_reply.size(),
    reinterpret_cast<const uint8_t*>(proof_response.data()),proof_response.size(),&result)==NOCTIUM_NATIVE_OK);
  const auto proved=take_native(result);
  assert(field(proved,"status")=="proved");

  const auto deploy_attempt=fresh_attempt();
  const auto deploy_namespace="noctium-witness62-deploy-"+deploy_attempt.substr(0,16);
  const auto deploy_context=deployment_context(deploy_attempt,deploy_namespace);
  const auto deploy_setup="{\"hostContext\":"+deploy_context+",\"stages\":[]}";
  uint64_t deployment_client=0;
  assert(noctium_client_start(proof,0,
    reinterpret_cast<const uint8_t*>(client_descriptor.data()),client_descriptor.size(),
    reinterpret_cast<const uint8_t*>(deploy_setup.data()),deploy_setup.size(),&deployment_client)==NOCTIUM_NATIVE_OK);
  const auto deployment_prepared=client_command(deployment_client,adapter,"prepare");
  if(field(deployment_prepared,"status")!="step_done"){
    std::cerr<<deployment_prepared<<std::endl;
    assert(false&&"typed witness deployment prepare failed");
  }
  assert(field(deployment_prepared,"contractAddress")==contract_address);
  const auto deployment_submitted=client_command(deployment_client,adapter,"submit");
  if(field(deployment_submitted,"status")!="step_done"){
    std::cerr<<deployment_submitted<<std::endl;
    assert(false&&"typed witness deployment submit failed");
  }
  const auto deployment_receipt=observe_client(deployment_client,adapter);
  assert(field(deployment_receipt,"contractAddress")==contract_address);
  const auto deployment_receipt_json=object_field(deployment_receipt,"receipt");
  persist_public_evidence(evidence_path,profile,contract_address,deployment_receipt_json,{},calls.size(),false);
  const auto deployment_committed=client_command(deployment_client,adapter,"commit");
  if(field(deployment_committed,"phase")!="Committed"){
    std::cerr<<deployment_committed<<std::endl;
    assert(false&&"typed witness deployment commit failed");
  }
  assert(field(deployment_committed,"contractAddress")==contract_address);
  persist_public_evidence(evidence_path,profile,contract_address,
    object_field(deployment_committed,"receipt"),{},calls.size(),false);
  assert(noctium_client_detach(deployment_client)==NOCTIUM_NATIVE_OK);

  uint64_t client=0;
  assert(noctium_client_start_from_witness(proof,
    reinterpret_cast<const uint8_t*>(client_descriptor.data()),client_descriptor.size(),&client)==NOCTIUM_NATIVE_OK);
  uint64_t duplicate=99;
  assert(noctium_client_start_from_witness(proof,
    reinterpret_cast<const uint8_t*>(client_descriptor.data()),client_descriptor.size(),&duplicate)==NOCTIUM_NATIVE_INVALID_STATE&&duplicate==0);
  const auto call_prepared=client_command(client,adapter,"prepare");
  if(field(call_prepared,"status")!="step_done"){
    std::cerr<<call_prepared<<std::endl;
    assert(false&&"typed witness call prepare failed");
  }
  const auto call_submitted=client_command(client,adapter,"submit");
  if(field(call_submitted,"status")!="step_done"){
    std::cerr<<call_submitted<<std::endl;
    assert(false&&"typed witness call submit failed");
  }
  const auto call_receipt=observe_client(client,adapter);
  assert(field(call_receipt,"contractAddress")==contract_address);
  const auto call_receipt_json=object_field(call_receipt,"receipt");
  persist_public_evidence(evidence_path,profile,contract_address,
    deployment_receipt_json,call_receipt_json,calls.size(),false);
  const auto call_committed=client_command(client,adapter,"commit");
  if(field(call_committed,"phase")!="Committed"){
    std::cerr<<call_committed<<std::endl;
    assert(false&&"typed witness call commit failed");
  }
  assert(field(call_committed,"contractAddress")==contract_address);
  assert(call_committed.find("\"privateCommitted\":true")!=std::string::npos);
  const auto private_value=read_local_private_value(adapter,source_namespace,"cache/last");
  const bool source_state_matched=private_value.find("\"value\":\"14\"")!=std::string::npos;
  assert(source_state_matched);
  persist_public_evidence(evidence_path,profile,contract_address,
    object_field(deployment_committed,"receipt"),object_field(call_committed,"receipt"),
    calls.size(),source_state_matched);
  assert(noctium_client_detach(client)==NOCTIUM_NATIVE_OK);
  assert(noctium_native_free(proof)==NOCTIUM_NATIVE_OK);
  assert(noctium_native_target_context_free(target)==NOCTIUM_NATIVE_INVALID_HANDLE);
  assert(noctium_localnet_free(adapter)==NOCTIUM_NATIVE_OK);
  std::cout<<"typed source localnet C ABI passed, provider calls="<<calls.size()
    <<", contract address="<<contract_address<<"\n";
  return 0;
}

int main(int argc,char **argv) {
  if(argc>1&&std::string(argv[1])=="native")return run_native_witness(argc,argv);
  assert(argc==2);
  const auto plan=read_file(argv[1]);
  const std::string attempt(64,'b');
  const std::string context=
    "{\"protocolVersion\":1,\"namespace\":\"noctium\",\"baseRevision\":\"fixture-r0\","
    "\"attemptId\":\""+attempt+"\",\"capabilities\":["
    "{\"id\":\"private\",\"namespace\":\"noctium\",\"keyPrefix\":\"cache/\","
    "\"operations\":[\"private_state.read.v1\",\"private_state.stage.v1\",\"private_state.compare_exchange.v1\"]},"
    "{\"id\":\"lookup\",\"namespace\":\"noctium\",\"keyPrefix\":\"lookup/\","
    "\"operations\":[\"noctium.lookup.v1\"]}],\"operations\":["
    "{\"operation\":\"private_state.read.v1\",\"argumentSchema\":{\"key\":\"Key\"},"
    "\"resultSchema\":\"UIntRange<256>\"},"
    "{\"operation\":\"noctium.lookup.v1\",\"argumentSchema\":{\"seed\":\"UIntRange<256>\"},"
    "\"resultSchema\":\"UIntRange<256>\"}],\"providers\":["
    "{\"input\":\"cache\",\"operation\":\"private_state.read.v1\","
    "\"capability\":\"private\",\"arguments\":{\"key\":\"cache/last\"}},"
    "{\"input\":\"lookup\",\"operation\":\"noctium.lookup.v1\","
    "\"capability\":\"lookup\",\"arguments\":{}}],"
    "\"commitCapability\":\"private\",\"limits\":{\"requests\":64,"
    "\"writes\":64,\"privateBytes\":65536}}";
  const auto begin="{\"abiVersion\":1,\"plan\":"+plan+
    ",\"inputs\":{\"expected\":\"14\",\"seed\":\"7\"},\"hostContext\":"+context+"}";
  uint64_t session=0;
  assert(noctium_control_begin(reinterpret_cast<const uint8_t*>(begin.data()),begin.size(),&session)==NOCTIUM_CONTROL_OK);
  const std::string forged_stage=
    "{\"abiVersion\":2,\"operation\":\"private_state.stage.v1\","
    "\"capability\":\"private\",\"key\":\"cache/forged\","
    "\"type\":\"UIntRange<256>\",\"value\":\"999\"}";
  uint64_t denied_stage=99;
  assert(noctium_control_stage(session,
    reinterpret_cast<const uint8_t*>(forged_stage.data()),forged_stage.size(),&denied_stage)
    ==NOCTIUM_CONTROL_INVALID_RESPONSE&&denied_stage==0);

  std::vector<std::string> calls;
  std::string complete;
  for (;;) {
    uint64_t result=0;
    assert(noctium_control_advance(session,&result)==NOCTIUM_CONTROL_OK);
    const auto pending=take(result);
    if (pending.find("\"status\":\"need_host\"")==std::string::npos) {
      complete=pending;
      break;
    }
    uint64_t repeated=0;
    assert(noctium_control_advance(session,&repeated)==NOCTIUM_CONTROL_OK);
    assert(take(repeated)==pending);
    assert(pending.find("cache/last")==std::string::npos);
    const auto name=last_field(pending,"name");
    calls.push_back(name);
    std::string private_request;
    for(unsigned export_count=0;export_count<4;++export_count){
      uint64_t private_token=0;
      assert(noctium_control_private_request(session,&private_token)==NOCTIUM_CONTROL_OK);
      const auto exported=take(private_token,true);
      if(export_count==0)private_request=exported;
      else assert(exported==private_request);
    }
    std::string value;
    if (name=="cache") {
      assert(private_request.find("\"key\":\"cache/last\"")!=std::string::npos);
      assert(private_request.find("\"cache/last\":{\"type\":\"UIntRange<256>\",\"value\":\"1\"}")!=std::string::npos);
      value="\"1\"";
    } else {
      assert(name=="lookup");
      assert(private_request.find("\"seed\":\"7\"")!=std::string::npos);
      value="\"14\"";
    }
    const auto response="{\"protocolVersion\":2,\"requestId\":\""+field(pending,"requestId")+
      "\",\"attemptId\":\""+attempt+"\",\"outcome\":\"value\","
      "\"operation\":\""+field(pending,"operation")+"\",\"capability\":\""+
      field(pending,"capability")+"\",\"schema\":\""+field(pending,"schema")+
      "\",\"value\":"+value+"}";
    auto crossed=response;
    const auto attempt_position=crossed.find(attempt);
    assert(attempt_position!=std::string::npos);
    crossed.replace(attempt_position,attempt.size(),std::string(64,'c'));
    uint64_t denied=99;
    assert(noctium_control_resume_typed(session,reinterpret_cast<const uint8_t*>(crossed.data()),crossed.size(),&denied)==NOCTIUM_CONTROL_INVALID_RESPONSE&&denied==0);
    assert(noctium_control_advance(session,&repeated)==NOCTIUM_CONTROL_OK);
    assert(take(repeated)==pending);
    assert(noctium_control_resume_typed(session,reinterpret_cast<const uint8_t*>(response.data()),response.size(),&result)==NOCTIUM_CONTROL_OK);
    take(result);
  }
  assert(complete.find("\"status\":\"completed\"")!=std::string::npos);
  assert(complete.find("\"result\":\"14\"")!=std::string::npos);
  assert((calls==std::vector<std::string>{"cache","cache","lookup","cache","lookup"}));
  assert(noctium_control_free(session)==NOCTIUM_CONTROL_OK);
  std::cout<<"typed source fixture C ABI passed, provider calls="<<calls.size()<<"\n";
}
