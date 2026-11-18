#include "../include/noctium_native.h"
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
#include <unistd.h>
#include <sys/random.h>
#ifdef NDEBUG
#error "Qualification requires assertions"
#endif
using Bytes = std::vector<uint8_t>;
static Bytes read(const char* path) { std::ifstream f(path,std::ios::binary);assert(f.good());return Bytes(std::istreambuf_iterator<char>(f),{}); }
static void wipe(Bytes& bytes) { for(volatile auto& byte:bytes)byte=0; }
static Bytes coins() { Bytes bytes(32);assert(getentropy(bytes.data(),bytes.size())==0);return bytes; }
static std::string text(const Bytes& bytes) { return std::string(bytes.begin(),bytes.end()); }
static std::string field(const std::string& json,const std::string& name) {
  auto start=json.find("\""+name+"\":\"");assert(start!=std::string::npos);start+=name.size()+4;
  auto end=json.find('"',start);assert(end!=std::string::npos);return json.substr(start,end-start);
}
static std::string number(const std::string& json,const std::string& name) {
  auto start=json.find("\""+name+"\":");assert(start!=std::string::npos);start+=name.size()+3;
  auto end=json.find_first_not_of("0123456789",start);assert(end>start);return json.substr(start,end-start);
}
static Bytes take(uint64_t token,bool secret=false,bool release=true) {
  size_t n=0,w=99;
  assert((secret?noctium_native_private_length(token,&n):noctium_native_result_length(token,&n))==NOCTIUM_NATIVE_OK);
  Bytes bytes(n);assert((secret?noctium_native_private_copy(token,bytes.data(),n,&w):noctium_native_result_copy(token,bytes.data(),n,&w))==NOCTIUM_NATIVE_OK);assert(w==n);
  if(release)assert((secret?noctium_native_private_free(token):noctium_native_result_free(token))==NOCTIUM_NATIVE_OK);
  return bytes;
}
static uint64_t begin(const Bytes& descriptor,const Bytes& config,const Bytes& params) {
  auto entropy=coins();uint64_t session=99;
  assert(noctium_native_begin(descriptor.data(),descriptor.size(),config.data(),config.size(),params.data(),params.size(),entropy.data(),entropy.size(),&session)==NOCTIUM_NATIVE_OK);
  wipe(entropy);assert(session);return session;
}
static std::string advance(uint64_t session) {uint64_t t=0;assert(noctium_native_advance(session,&t)==NOCTIUM_NATIVE_OK);return text(take(t));}
static std::string metadata(const std::string& req,const std::string& id="",const std::string& operation="",const std::string& capability="",const std::string& profile="") {
  return "{\"abiVersion\":1,\"requestId\":"+(id.empty()?number(req,"requestId"):id)+",\"operation\":\""+(operation.empty()?field(req,"operation"):operation)+"\",\"capability\":\""+(capability.empty()?field(req,"capability"):capability)+"\",\"profile\":\""+(profile.empty()?field(req,"profile"):profile)+"\"}";
}
static int32_t resume(uint64_t session,const std::string& meta,const Bytes& proof,uint64_t& out) {
  out=99;return noctium_native_resume(session,reinterpret_cast<const uint8_t*>(meta.data()),meta.size(),proof.data(),proof.size(),&out);
}
int main(int argc,char** argv) {
  assert(argc==4);auto descriptor=read(argv[1]),config=read(argv[2]),params=read(argv[3]);
  uint64_t out=99;assert(noctium_native_advance(42,&out)==NOCTIUM_NATIVE_INVALID_HANDLE&&out==0);
  const auto a=begin(descriptor,config,params),b=begin(descriptor,config,params);
  const auto req=advance(a),other=advance(b);assert(req==advance(a));assert(number(req,"requestId")!=number(other,"requestId"));assert(field(req,"operation")=="native.prove.v1");
  uint64_t payload=0;assert(noctium_native_private_request(a,&payload)==NOCTIUM_NATIVE_OK);
  size_t n=99,w=99;assert(noctium_native_result_length(payload,&n)==NOCTIUM_NATIVE_INVALID_HANDLE&&n==0);
  auto private_payload=take(payload,true,false);assert(private_payload.size()>400000&&private_payload.size()<1048576);
  uint8_t small=7;assert(noctium_native_private_copy(payload,&small,1,&w)==NOCTIUM_NATIVE_BUFFER_TOO_SMALL&&w==0&&small==7);
  auto entropy=coins();uint64_t response_token=0;
  assert(noctium_native_local_prove(payload,entropy.data(),entropy.size(),&response_token)==NOCTIUM_NATIVE_OK);wipe(entropy);
  auto proof=take(response_token);assert(noctium_native_result_free(response_token)==NOCTIUM_NATIVE_INVALID_HANDLE);
  entropy=coins();assert(noctium_native_local_prove(payload,entropy.data(),entropy.size(),&out)==NOCTIUM_NATIVE_INVALID_STATE&&out==0);wipe(entropy);
  const auto meta=metadata(req);
  for(const auto& wrong:std::vector<std::string>{metadata(req,number(other,"requestId")),metadata(req,"","wrong"),metadata(req,"","","wrong"),metadata(req,"","","","wrong"),"{",meta.substr(0,meta.size()-1)+",\"unexpected\":true}"}) {
    assert(resume(a,wrong,proof,out)==NOCTIUM_NATIVE_INVALID_RESPONSE&&out==0);assert(advance(a)==req);
  }
  assert(resume(b,meta,proof,out)==NOCTIUM_NATIVE_INVALID_RESPONSE&&out==0);
  assert(resume(b,metadata(other),proof,out)==NOCTIUM_NATIVE_INVALID_RESPONSE&&out==0);
  auto bad=proof;bad.back()^=1;assert(resume(a,meta,bad,out)==NOCTIUM_NATIVE_INVALID_RESPONSE&&out==0);
  bad.resize(1048577);assert(resume(a,meta,bad,out)==NOCTIUM_NATIVE_LIMIT&&out==0);
  assert(resume(a,meta,proof,out)==NOCTIUM_NATIVE_OK);const auto result=text(take(out));
  assert(field(result,"status")=="proved");assert(result.find("\"funded\":false")!=std::string::npos&&result.find("\"submitted\":false")!=std::string::npos);assert(field(result,"publicIntentSha256").size()==64);assert(advance(a)==result);
  assert(resume(a,meta,proof,out)==NOCTIUM_NATIVE_INVALID_STATE&&out==0);assert(noctium_native_cancel(a)==NOCTIUM_NATIVE_INVALID_STATE);
  assert(noctium_native_private_length(payload,&n)==NOCTIUM_NATIVE_INVALID_HANDLE);assert(noctium_native_private_free(payload)==NOCTIUM_NATIVE_INVALID_HANDLE);
  uint64_t revoked=0;assert(noctium_native_private_request(b,&revoked)==NOCTIUM_NATIVE_OK);assert(noctium_native_cancel(b)==NOCTIUM_NATIVE_OK);assert(noctium_native_private_length(revoked,&n)==NOCTIUM_NATIVE_INVALID_HANDLE);assert(resume(b,metadata(other),proof,out)==NOCTIUM_NATIVE_INVALID_STATE&&out==0);assert(noctium_native_cancel(b)==NOCTIUM_NATIVE_INVALID_STATE);
  const auto c=begin(descriptor,config,params);assert(noctium_native_cancel(c)==NOCTIUM_NATIVE_OK);assert(noctium_native_private_request(c,&out)==NOCTIUM_NATIVE_INVALID_STATE&&out==0);assert(noctium_native_free(c)==NOCTIUM_NATIVE_OK);
  assert(noctium_native_free(a)==NOCTIUM_NATIVE_OK);assert(noctium_native_free(a)==NOCTIUM_NATIVE_INVALID_HANDLE);assert(noctium_native_free(b)==NOCTIUM_NATIVE_OK);
  std::cout<<"{\"adapter\":\"linked C++ native proof ABI phase A\",\"profile\":\""<<field(req,"profile")<<"\",\"privatePayloadBytes\":"<<private_payload.size()<<",\"responseBytes\":"<<proof.size()<<",\"publicIntentSha256\":\""<<field(result,"publicIntentSha256")<<"\",\"positiveAndAdversarialReplies\":true,\"fundingSubmissionJournalAbiDelivered\":false}"<<std::endl;
  wipe(private_payload);wipe(config);wipe(descriptor);return 0;
}
