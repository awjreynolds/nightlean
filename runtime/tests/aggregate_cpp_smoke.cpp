#include "noctium_runtime.h"
#include "noctium_aggregate.h"
#include <cassert>
#include <cctype>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <iterator>
#include <string>
#include <vector>

using Bytes=std::vector<uint8_t>;
static std::string read(const char *path){
  std::ifstream file(path,std::ios::binary);assert(file.good());
  return std::string(std::istreambuf_iterator<char>(file),std::istreambuf_iterator<char>());
}
static Bytes hex(const std::string &source){
  std::string text;for(unsigned char c:source)if(!std::isspace(c))text.push_back(static_cast<char>(c));
  assert(text.size()%2==0);Bytes out;
  auto digit=[](char c)->uint8_t{if(c>='0'&&c<='9')return static_cast<uint8_t>(c-'0');if(c>='a'&&c<='f')return static_cast<uint8_t>(c-'a'+10);assert(false);return 0;};
  for(size_t i=0;i<text.size();i+=2)out.push_back(static_cast<uint8_t>(digit(text[i])*16+digit(text[i+1])));
  return out;
}
static Bytes take(uint64_t token){
  size_t length=0,written=99;
  assert(noctium_aggregate_buffer_length(token,&length)==NOCTIUM_OK);
  assert(length>0);Bytes output(length,0xa5);
  assert(noctium_aggregate_buffer_copy(token,output.data(),length-1,&written)==NOCTIUM_BUFFER_TOO_SMALL);
  assert(written==0&&output[0]==0xa5);
  assert(noctium_aggregate_buffer_copy(token,output.data(),output.size(),&written)==NOCTIUM_OK);
  assert(written==output.size());
  assert(noctium_aggregate_buffer_free(token)==NOCTIUM_OK);
  assert(noctium_aggregate_buffer_free(token)==NOCTIUM_INVALID_HANDLE);
  assert(noctium_aggregate_buffer_length(token,&length)==NOCTIUM_INVALID_HANDLE&&length==0);
  return output;
}
static Bytes encode(const std::string &schema,const std::string &value){
  uint64_t token=99;
  assert(noctium_aggregate_encode(reinterpret_cast<const uint8_t*>(schema.data()),schema.size(),
    reinterpret_cast<const uint8_t*>(value.data()),value.size(),&token)==NOCTIUM_OK);
  assert(token!=0);return take(token);
}
static std::string decode(const std::string &schema,const Bytes &wire){
  uint64_t token=99;
  assert(noctium_aggregate_decode(reinterpret_cast<const uint8_t*>(schema.data()),schema.size(),
    wire.data(),wire.size(),&token)==NOCTIUM_OK);
  Bytes result=take(token);return std::string(result.begin(),result.end());
}
static void reject_wire(const std::string &schema,const Bytes &wire){
  uint64_t token=99;
  assert(noctium_aggregate_decode(reinterpret_cast<const uint8_t*>(schema.data()),schema.size(),
    wire.data(),wire.size(),&token)==NOCTIUM_INVALID_ARGUMENT);
  assert(token==0);
}
static void reject_value(const std::string &schema,const std::string &value){
  uint64_t token=99;
  assert(noctium_aggregate_encode(reinterpret_cast<const uint8_t*>(schema.data()),schema.size(),
    reinterpret_cast<const uint8_t*>(value.data()),value.size(),&token)==NOCTIUM_INVALID_ARGUMENT);
  assert(token==0);
}
static size_t leaves_offset(const Bytes &wire){
  constexpr size_t magic=sizeof("noctium:aggregate:value:v1:")-1;
  assert(wire.size()>magic+8);
  uint32_t n=static_cast<uint32_t>(wire[magic])|static_cast<uint32_t>(wire[magic+1])<<8|
    static_cast<uint32_t>(wire[magic+2])<<16|static_cast<uint32_t>(wire[magic+3])<<24;
  return magic+4+static_cast<size_t>(n)+4;
}
int main(int argc,char **argv){
  assert(argc==4);
  assert(noctium_aggregate_abi_version()==NOCTIUM_AGGREGATE_ABI_VERSION);
  const std::string schema=read(argv[1]),value=read(argv[2]);
  const Bytes expected=hex(read(argv[3]));
  const Bytes encoded=encode(schema,value);
  assert(encoded==expected);
  assert(encode(schema,decode(schema,encoded))==encoded);
  Bytes changed=encoded;changed.push_back(0);reject_wire(schema,changed);
  changed=encoded;changed.pop_back();reject_wire(schema,changed);
  changed=encoded;changed[sizeof("noctium:aggregate:value:v1:")-1+4]^=1;reject_wire(schema,changed);
  std::string unknown=value;const size_t final=unknown.find_last_of('}');assert(final!=std::string::npos);
  unknown.insert(final,",\"unknown\":null");reject_value(schema,unknown);
  uint64_t cleared=99;
  assert(noctium_aggregate_encode(nullptr,1,nullptr,1,&cleared)==NOCTIUM_INVALID_ARGUMENT&&cleared==0);
  assert(noctium_aggregate_encode(nullptr,1,nullptr,1,nullptr)==NOCTIUM_INVALID_ARGUMENT);
  const std::string enum_schema=R"({"schemaVersion":1,"typeFingerprint":"NoctiumCompositeTypeV1;e11:Host.ChoiceNoctiumCompositeLayoutV1;0;1;E11:Host.Choice2;V4:None0;V4:Some1;f5:valuesU255;","layout":{"kind":"enum","id":"Host.Choice","variants":[{"name":"None","fields":[]},{"name":"Some","fields":[{"name":"value","layout":{"kind":"scalar","leaf":{"kind":"uint","maximum":"255"}}}]}]},"counts":{"leaves":2,"expandedNodes":4,"layoutNodes":4}})";
  const std::string none=R"({"kind":"enum","id":"Host.Choice","variant":"None","fields":[]})";
  const Bytes empty=encode(enum_schema,none);
  assert(encode(enum_schema,decode(enum_schema,empty))==empty);
  changed=empty;changed[leaves_offset(empty)]=2;reject_wire(enum_schema,changed);
  changed=empty;changed[leaves_offset(empty)+32]=1;reject_wire(enum_schema,changed);
  reject_value(enum_schema,R"({"kind":"enum","id":"Host.Other","variant":"None","fields":[]})");
  reject_value(enum_schema,R"({"kind":"enum","id":"Host.Choice","variant":"Some","fields":[{"name":"value","value":{"kind":"uint","maximum":"255","value":"256"}}]})");
  std::cout<<"Aggregate C++ host roundtrip, nominal, malformed, tag, padding and ownership checks passed\n";
}
