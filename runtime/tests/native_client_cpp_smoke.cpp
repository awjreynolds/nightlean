#include "../include/noctium_native.h"
#include <cassert>
#include <cctype>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <utility>
#include <vector>
#include <algorithm>
#include <chrono>
#include <thread>
#include <sys/random.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <filesystem>
#include <unistd.h>
#ifdef NDEBUG
#error "Qualification requires assertions"
#endif
using Bytes=std::vector<uint8_t>;
static Bytes read(const char* p){std::ifstream f(p,std::ios::binary);assert(f.good());return Bytes(std::istreambuf_iterator<char>(f),{});}
static std::string text(const Bytes& b){return std::string(b.begin(),b.end());}
static void wipe(Bytes& b){for(volatile auto& v:b)v=0;}
static Bytes coins(){Bytes b(32);assert(getentropy(b.data(),32)==0);return b;}
static std::string hex(const Bytes& b){static const char* digits="0123456789abcdef";std::string s;for(auto v:b){s+=digits[v>>4];s+=digits[v&15];}return s;}
static size_t value_start(const std::string& s,const std::string& k){auto p=s.find("\""+k+"\"");assert(p!=std::string::npos);p=s.find(':',p)+1;while(p<s.size()&&std::isspace(static_cast<unsigned char>(s[p])))++p;return p;}
static std::string field(const std::string& s,const std::string& k){auto p=value_start(s,k);assert(s[p]=='"');auto end=s.find('"',++p);assert(end!=std::string::npos);return s.substr(p,end-p);}
static std::string number(const std::string& s,const std::string& k){auto p=value_start(s,k);auto e=s.find_first_not_of("0123456789",p);assert(e>p);return s.substr(p,e-p);}
static std::string object(const std::string& s,const std::string& k){auto p=value_start(s,k),i=p;assert(s[p]=='{');size_t depth=0;bool quoted=false,escaped=false;for(;i<s.size();++i){char c=s[i];if(quoted){if(escaped)escaped=false;else if(c=='\\')escaped=true;else if(c=='"')quoted=false;}else if(c=='"')quoted=true;else if(c=='{')++depth;else if(c=='}'&&--depth==0)return s.substr(p,i-p+1);}assert(false);return{};}
static Bytes take(uint64_t t,bool secret=false){size_t n=0,w=99;assert((secret?noctium_native_private_length(t,&n):noctium_native_result_length(t,&n))==NOCTIUM_NATIVE_OK);Bytes b(n);assert((secret?noctium_native_private_copy(t,b.data(),n,&w):noctium_native_result_copy(t,b.data(),n,&w))==NOCTIUM_NATIVE_OK&&n==w);assert((secret?noctium_native_private_free(t):noctium_native_result_free(t))==NOCTIUM_NATIVE_OK);return b;}
static void write(const char* path,const std::string& bytes,bool secret=false){int fd=open(path,O_WRONLY|O_CREAT|O_EXCL|O_NOFOLLOW,secret?0600:0644);assert(fd>=0);size_t done=0;while(done<bytes.size()){auto n=::write(fd,bytes.data()+done,bytes.size()-done);assert(n>0);done+=static_cast<size_t>(n);}assert(fsync(fd)==0);assert(close(fd)==0);auto parent=std::filesystem::path(path).parent_path();if(parent.empty())parent=".";int directory=open(parent.c_str(),O_RDONLY|O_DIRECTORY|O_NOFOLLOW);assert(directory>=0);assert(fsync(directory)==0);assert(close(directory)==0);}

static std::string context(const std::string& id,const std::string& ns,bool stale=false){return "{\"protocolVersion\":1,\"namespace\":\""+ns+"\",\"baseRevision\":\""+(stale?"stale":"r0")+"\",\"attemptId\":\""+id+"\",\"capabilities\":[{\"id\":\"store\",\"namespace\":\""+ns+"\",\"keyPrefix\":\"claims/\",\"operations\":[\"private_state.stage.v1\",\"private_state.compare_exchange.v1\"]}],\"operations\":[],\"providers\":[],\"commitCapability\":\"store\"}";}
static std::string setup(const std::string& ctx){return "{\"hostContext\":"+ctx+",\"stages\":[{\"abiVersion\":1,\"operation\":\"private_state.stage.v1\",\"capability\":\"store\",\"key\":\"claims/accepted\",\"type\":\"Bool\",\"value\":true}]}";}
static std::string metadata(const std::string& s){return "{\"abiVersion\":1,\"requestId\":\""+field(s,"requestId")+"\",\"operation\":\""+field(s,"operation")+"\",\"capability\":\""+field(s,"capability")+"\",\"schema\":\""+field(s,"schema")+"\",\"profile\":\""+field(s,"profile")+"\"}";}
static uint64_t open_adapter(const Bytes& config,bool wallet){Bytes seed(32);seed[31]=1;uint64_t a=0;assert(noctium_localnet_open(config.data(),config.size(),wallet?seed.data():nullptr,wallet?seed.size():0,&a)==NOCTIUM_NATIVE_OK);wipe(seed);return a;}
struct Host{explicit Host(uint64_t a):adapter(a){} uint64_t adapter;bool lose_submit_ack=false,adversarial=true;std::vector<std::string> operations;size_t largest_private=0;};
static std::string drive(uint64_t c,Host& h,std::string status={}){
  for(unsigned steps=0;steps<2048;++steps){
    if(status.empty()){uint64_t token=0;assert(noctium_client_advance(c,&token)==NOCTIUM_NATIVE_OK);status=text(take(token));}
    if(field(status,"status")!="need_host")return status;
    const auto op=field(status,"operation");h.operations.push_back(op);uint64_t request=0;assert(noctium_client_request(c,&request)==NOCTIUM_NATIVE_OK);
    if(status.find("\"hasPrivateArguments\":true")!=std::string::npos){uint64_t p=0;if(noctium_client_private_request(request,&p)==NOCTIUM_NATIVE_OK){size_t n=0;assert(noctium_native_result_length(p,&n)==NOCTIUM_NATIVE_INVALID_HANDLE);assert(noctium_native_private_length(p,&n)==NOCTIUM_NATIVE_OK);h.largest_private=std::max(h.largest_private,n);assert(noctium_native_private_free(p)==NOCTIUM_NATIVE_OK);}}
    auto entropy=coins();uint64_t reply=0;const auto result=noctium_localnet_resolve(h.adapter,request,1,entropy.data(),entropy.size(),&reply);wipe(entropy);if(result!=NOCTIUM_NATIVE_OK){std::cerr<<"native host service failed op="<<op<<" code="<<result<<std::endl;assert(false);}
    if(h.lose_submit_ack&&op=="chain.submit.v1"){assert(noctium_client_service_free(reply)==NOCTIUM_NATIVE_OK);assert(noctium_client_service_failure(request,&reply)==NOCTIUM_NATIVE_OK);h.lose_submit_ack=false;}
    const auto meta=metadata(status);
    if(h.adversarial){uint64_t out=99;auto wrong=meta;auto p=wrong.find("\"capability\":\"")+14;wrong.insert(p,"wrong.");assert(noctium_client_resume(c,reinterpret_cast<const uint8_t*>(wrong.data()),wrong.size(),reply,&out)==NOCTIUM_NATIVE_INVALID_RESPONSE&&out==0);uint64_t ordinary=0;assert(noctium_client_advance(c,&ordinary)==NOCTIUM_NATIVE_OK);assert(noctium_client_resume(c,reinterpret_cast<const uint8_t*>(meta.data()),meta.size(),ordinary,&out)==NOCTIUM_NATIVE_INVALID_HANDLE&&out==0);take(ordinary);}
    uint64_t out=0;assert(noctium_client_resume(c,reinterpret_cast<const uint8_t*>(meta.data()),meta.size(),reply,&out)==NOCTIUM_NATIVE_OK);auto next=text(take(out));
    if(h.adversarial){out=99;assert(noctium_client_resume(c,reinterpret_cast<const uint8_t*>(meta.data()),meta.size(),reply,&out)!=NOCTIUM_NATIVE_OK&&out==0);}
    status=next;
  }assert(false);return{};
}
static std::string command(uint64_t c,const char* op,Host& host){uint64_t out=0;assert(noctium_client_command(c,reinterpret_cast<const uint8_t*>(op),std::char_traits<char>::length(op),&out)==NOCTIUM_NATIVE_OK);return drive(c,host,text(take(out)));}
static std::string observe(uint64_t c,Host& h){for(unsigned i=0;i<180;++i){auto s=command(c,"observe",h);if(s.find("\"receipt\":")!=std::string::npos)return s;assert(field(s,"status")=="step_done");std::this_thread::sleep_for(std::chrono::milliseconds(500));}assert(false);return{};}
static Bytes transaction(uint64_t c){uint64_t t=0;assert(noctium_client_transaction(c,&t)==NOCTIUM_NATIVE_OK);return take(t);}
static Bytes state(uint64_t c){uint64_t t=0;assert(noctium_client_receipt_state(c,&t)==NOCTIUM_NATIVE_OK);return take(t);}
static std::string private_value(Host& host, const std::string& name_space,
                                 const std::string& key = "claims/accepted") {
  const auto request = "{\"namespace\":\"" + name_space + "\",\"key\":\"" + key + "\"}";
  uint64_t token = 0;
  assert(noctium_localnet_private_value(host.adapter,
      reinterpret_cast<const uint8_t*>(request.data()), request.size(), &token) == NOCTIUM_NATIVE_OK);
  auto data = take(token, true);
  const auto value = text(data);
  wipe(data);
  return value;
}
static uint64_t recover(const Bytes& descriptor,const std::string& ctx){uint64_t c=0;assert(noctium_client_recover(descriptor.data(),descriptor.size(),reinterpret_cast<const uint8_t*>(ctx.data()),ctx.size(),&c)==NOCTIUM_NATIVE_OK);return c;}
static uint64_t prove_source(const Bytes& descriptor,const Bytes& config,const Bytes& parameters){
  auto entropy=coins();uint64_t source=0,t=0,request=0;assert(noctium_native_begin(descriptor.data(),descriptor.size(),config.data(),config.size(),parameters.data(),parameters.size(),entropy.data(),entropy.size(),&source)==NOCTIUM_NATIVE_OK);wipe(entropy);
  assert(noctium_native_advance(source,&t)==NOCTIUM_NATIVE_OK);const auto pending=text(take(t));assert(noctium_native_private_request(source,&request)==NOCTIUM_NATIVE_OK);entropy=coins();assert(noctium_native_local_prove(request,entropy.data(),entropy.size(),&t)==NOCTIUM_NATIVE_OK);wipe(entropy);const auto response=take(t);
  const auto meta="{\"abiVersion\":1,\"requestId\":"+number(pending,"requestId")+",\"operation\":\"native.prove.v1\",\"capability\":\""+field(pending,"capability")+"\",\"profile\":\""+field(pending,"profile")+"\"}";
  assert(noctium_native_resume(source,reinterpret_cast<const uint8_t*>(meta.data()),meta.size(),response.data(),response.size(),&t)==NOCTIUM_NATIVE_OK);take(t);return source;
}
static const uint8_t* bytes(const std::string& value) {
  return reinterpret_cast<const uint8_t*>(value.data());
}

static std::string attempt_id() {
  auto entropy = coins();
  const auto id = hex(entropy);
  wipe(entropy);
  return id;
}

static void require_ok(int32_t status, const char* operation) {
  if (status != NOCTIUM_NATIVE_OK) std::cerr << operation << " returned " << status << '\n';
  assert(status == NOCTIUM_NATIVE_OK);
}

static uint64_t chain_ttl(Host& host) {
  uint64_t token = 0;
  require_ok(noctium_localnet_context(host.adapter, &token), "read localnet context");
  return std::stoull(field(text(take(token)), "blockTime")) + 1800;
}

static uint64_t finalize_module_call(uint64_t client, const std::string& operation,
                                    Host& host, bool recovery, std::string* revision = nullptr) {
  if (!recovery) {
    assert(field(command(client, "prepare", host), "phase") == "Prepared");
    assert(field(command(client, "submit", host), "status") == "step_done");
  }
  uint64_t next = 99;
  assert(noctium_native_contract_state_take(client, &next) == NOCTIUM_NATIVE_INVALID_STATE);
  assert(next == 0);
  const auto observed = observe(client, host);
  const auto accepted = command(client, "commit", host);
  assert(field(accepted, "phase") == "Committed");
  assert(accepted.find("\"privateCommitted\":true") != std::string::npos);
  if (revision) *revision = field(accepted, "privateRevision");
  require_ok(noctium_native_contract_state_take(client, &next), "take committed state");
  uint64_t duplicate = 99;
  assert(noctium_native_contract_state_take(client, &duplicate) == NOCTIUM_NATIVE_INVALID_STATE);
  assert(duplicate == 0);
  std::cout << "{\"operation\":\"" << operation << "\",\"receipt\":" << object(observed, "receipt")
            << ",\"stateHex\":\"" << hex(state(client)) << "\"}" << std::endl;
  require_ok(noctium_client_detach(client), "detach committed client");
  return next;
}

static std::string module_namespace(const std::string& id) {
  return "cpp67-" + id.substr(0, 24);
}

static constexpr auto wallet_key = "noctium/NoctiumExamples.Wallet/saved";
static constexpr auto wallet_capability = "private_state:NoctiumExamples.Wallet";
static constexpr auto uint8_schema = "UIntRange<256>";

static std::string typed_context(const std::string& attempt, const std::string& name_space,
                                 const std::string& revision, const std::string& provider) {
  const auto operation = "noctium.witness." + provider + ".v1";
  return "{\"protocolVersion\":1,\"namespace\":\"" + name_space
      + "\",\"baseRevision\":\"" + revision + "\",\"attemptId\":\"" + attempt
      + "\",\"commitCapability\":\"" + wallet_capability + "\",\"capabilities\":["
      + "{\"id\":\"" + wallet_capability + "\",\"namespace\":\"" + name_space
      + "\",\"keyPrefix\":\"noctium/NoctiumExamples.Wallet/\",\"operations\":["
      + "\"private_state.read.v1\",\"private_state.stage.v1\",\"private_state.compare_exchange.v1\"]},"
      + "{\"id\":\"" + provider + "\",\"namespace\":\"" + name_space
      + "\",\"keyPrefix\":\"callbacks/\",\"operations\":[\"" + operation + "\"]}],"
      + "\"operations\":[{\"operation\":\"private_state.read.v1\",\"argumentSchema\":{\"key\":\"Key\"},"
      + "\"resultSchema\":\"" + uint8_schema + "\"},{\"operation\":\"" + operation
      + "\",\"argumentSchema\":{\"previous\":\"" + uint8_schema + "\"},\"resultSchema\":\""
      + uint8_schema + "\"}],\"providers\":[{\"input\":\"private_state.read.NoctiumExamples.Wallet.saved.v1\","
      + "\"operation\":\"private_state.read.v1\",\"capability\":\"" + wallet_capability
      + "\",\"arguments\":{\"key\":\"" + wallet_key + "\"}},{\"input\":\"" + provider
      + "\",\"operation\":\"" + operation + "\",\"capability\":\"" + provider
      + "\",\"arguments\":{}}]}";
}

static std::string typed_reply(const std::string& request, const std::string& attempt,
                               const std::string& decimal) {
  return "{\"protocolVersion\":2,\"requestId\":\"" + field(request, "requestId")
      + "\",\"attemptId\":\"" + attempt + "\",\"outcome\":\"value\",\"operation\":\""
      + field(request, "operation") + "\",\"capability\":\"" + field(request, "capability")
      + "\",\"schema\":\"" + field(request, "schema") + "\",\"value\":\"" + decimal + "\"}";
}

static uint64_t start_typed_module_call(uint64_t target, uint64_t& current,
    const std::string& selection, const std::string& operation, const std::string& attempt,
    const std::string& name_space, const std::string& revision, const Bytes& descriptor,
    const Bytes& srs, Host& host) {
  const bool first = operation == "advance";
  assert(first || operation == "advanceAgain");
  const std::string provider = first ? "NoctiumExamples.nextValue"
                                     : "NoctiumExamples.nextValueAfterCheckpoint";
  const std::string prior = first ? "6" : "7";
  const std::string next = first ? "7" : "9";
  const auto inputs = "{\"expected\":\"" + next + "\"}";
  auto begin = [&](const std::string& id) {
    const auto source_context = typed_context(id, name_space, revision, provider);
    auto entropy = coins();
    uint64_t witness = 0;
    require_ok(noctium_native_contract_witness_begin(
        target, current, bytes(selection), selection.size(), bytes(inputs), inputs.size(),
        bytes(source_context), source_context.size(), srs.data(), srs.size(),
        entropy.data(), entropy.size(), &witness), "begin bound typed witness");
    wipe(entropy);
    assert(noctium_native_contract_state_free(current) == NOCTIUM_NATIVE_INVALID_HANDLE);
    current = 0;
    return witness;
  };
  if (first) {
    const auto cancelled = begin(attempt_id());
    uint64_t status = 0, private_request = 0;
    require_ok(noctium_native_contract_witness_advance(cancelled, &status), "advance before cancel");
    assert(field(text(take(status)), "status") == "need_host");
    require_ok(noctium_native_contract_witness_private_request(cancelled, &private_request), "get request before cancel");
    require_ok(noctium_native_contract_witness_cancel(cancelled, &current), "cancel bound typed witness");
    size_t size = 99;
    assert(noctium_native_private_length(private_request, &size) == NOCTIUM_NATIVE_INVALID_HANDLE);
    assert(size == 0 && current != 0);
  }
  const auto witness = begin(attempt);
  unsigned requests = 0;
  for (; requests < 3; ++requests) {
    uint64_t status = 0;
    require_ok(noctium_native_contract_witness_advance(witness, &status), "advance bound typed witness");
    const auto pending = text(take(status));
    assert(pending.find("\"arguments\":") == std::string::npos);
    if (field(pending, "status") == "completed") break;
    assert(field(pending, "status") == "need_host");
    uint64_t token = 0;
    require_ok(noctium_native_contract_witness_private_request(witness, &token), "read private typed request");
    size_t size = 99;
    assert(noctium_native_result_length(token, &size) == NOCTIUM_NATIVE_INVALID_HANDLE && size == 0);
    auto private_bytes = take(token, true);
    auto request = text(private_bytes);
    wipe(private_bytes);
    assert(field(pending, "schema") == uint8_schema);
    assert(field(request, "requestId") == field(pending, "requestId"));
    std::string answer;
    if (requests == 0) {
      assert(field(request, "operation") == "private_state.read.v1");
      assert(field(request, "key") == wallet_key);
      const auto saved = private_value(host, name_space, wallet_key);
      if (first) {
        assert(saved == "null");
        answer = "6";
      } else {
        assert(field(saved, "value") == "7");
        answer = field(saved, "value");
      }
    } else {
      assert(requests == 1 && field(request, "operation") == "noctium.witness." + provider + ".v1");
      assert(field(request, "previous") == prior);
      answer = std::to_string(std::stoul(field(request, "previous")) + (first ? 1 : 2));
      assert(answer == next);
    }
    auto response = typed_reply(pending, attempt, answer);
    if (first && requests == 0) {
      const auto crossed = typed_reply(pending, std::string(64, 'f'), answer);
      status = 99;
      assert(noctium_native_contract_witness_resume(witness, bytes(crossed), crossed.size(), &status)
             == NOCTIUM_NATIVE_INVALID_RESPONSE && status == 0);
      std::vector<uint64_t> retained(64);
      for (auto& token : retained) {
        require_ok(noctium_native_contract_witness_advance(witness, &token), "retain callback status");
      }
      status = 99;
      assert(noctium_native_contract_witness_resume(witness, bytes(response), response.size(), &status)
             == NOCTIUM_NATIVE_LIMIT && status == 0);
      for (auto token : retained) require_ok(noctium_native_result_free(token), "release callback status");
    }
    require_ok(noctium_native_contract_witness_resume(witness, bytes(response), response.size(), &status),
               "resume bound typed witness");
    take(status);
    for (volatile auto& byte : response) byte = 0;
    for (volatile auto& byte : request) byte = 0;
  }
  assert(requests == 2);
  auto entropy = coins();
  uint64_t client = 0;
  require_ok(noctium_client_contract_witness_start(
      witness, descriptor.data(), descriptor.size(), entropy.data(), entropy.size(), &client),
      "prove and start bound typed call");
  wipe(entropy);
  assert(noctium_native_contract_witness_free(witness) == NOCTIUM_NATIVE_INVALID_HANDLE);
  return client;
}

static int modules(int argc, char** argv, bool recovery, bool typed = false) {
  assert(argc == 9);
  const auto descriptor = read(argv[2]);
  Host host{open_adapter(read(argv[3]), true)};
  host.adversarial = false;
  auto target_descriptor = text(read(argv[4]));
  auto state_config = read(argv[5]);
  const auto srs = read(argv[6]);
  const std::string srs_sha = argv[7];
  target_descriptor.replace(value_start(target_descriptor, "ttl"), number(target_descriptor, "ttl").size(),
                            std::to_string(chain_ttl(host)));
  uint64_t target = 0, metadata_token = 0;
  auto entropy = coins();
  std::string reference;
  if (recovery) {
    auto private_reference = read(argv[8]);
    reference = text(private_reference);
    wipe(private_reference);
    const auto deploy_id = field(reference, "deploymentAttempt");
    require_ok(noctium_native_contract_target_restore(
        bytes(target_descriptor), target_descriptor.size(), state_config.data(), state_config.size(),
        entropy.data(), entropy.size(), bytes(deploy_id), deploy_id.size(),
        &target, &metadata_token), "restore module target");
  } else {
    require_ok(noctium_native_contract_target_begin(
        bytes(target_descriptor), target_descriptor.size(), state_config.data(), state_config.size(),
        entropy.data(), entropy.size(), &target, &metadata_token), "begin module target");
  }
  wipe(entropy);
  wipe(state_config);
  const auto address = field(text(take(metadata_token)), "contractAddress");
  const std::string first_operation = typed ? "advance" : "firstUpdate";
  const auto witness_namespace = "cpp67-typed-" + address.substr(0, 24);
  std::string private_revision = "r0";
  uint64_t current = 0;
  auto start = [&](const std::string& operation, const std::string& value,
                   const std::string& id, int32_t expected = NOCTIUM_NATIVE_OK) {
    const auto selection = "{\"abiVersion\":1,\"operation\":\"" + operation
                         + "\",\"k\":" + (typed ? "7" : "6") + ",\"ttl\":" + std::to_string(chain_ttl(host))
                         + ",\"proofParametersSha256\":\"" + srs_sha + "\"}";
    if (typed) {
      assert(expected == NOCTIUM_NATIVE_OK);
      return start_typed_module_call(target, current, selection, operation, id, witness_namespace,
                                     private_revision, descriptor, srs, host);
    }
    const auto inputs = "{\"value\":\"" + value + "\"}";
    const auto setup_json = setup(context(id, module_namespace(id)));
    uint64_t client = 99;
    auto coins_input = coins();
    const auto result = noctium_client_contract_call_start(
        target, current, bytes(selection), selection.size(), bytes(inputs), inputs.size(),
        srs.data(), srs.size(), coins_input.data(), coins_input.size(),
        descriptor.data(), descriptor.size(), bytes(setup_json), setup_json.size(), &client);
    wipe(coins_input);
    if (result != expected) std::cerr << operation << " returned " << result << '\n';
    assert(result == expected);
    if (expected == NOCTIUM_NATIVE_OK) {
      assert(noctium_native_contract_state_free(current) == NOCTIUM_NATIVE_INVALID_HANDLE);
      current = 0;
    } else {
      assert(client == 0);
    }
    return client;
  };

  if (!recovery) {
    const auto deploy_id = attempt_id();
    const auto setup_json = setup(context(deploy_id, module_namespace(deploy_id)));
    uint64_t deployment = 0;
    require_ok(noctium_client_contract_deployment_start(
        target, bytes(first_operation), first_operation.size(), descriptor.data(), descriptor.size(),
        bytes(setup_json), setup_json.size(), &deployment), "start module deployment");
    current = finalize_module_call(deployment, "deploy", host, false);
    const auto call_id = attempt_id();
    const auto first = start(first_operation, "11", call_id);
    assert(field(command(first, "prepare", host), "phase") == "Prepared");
    const auto sealed = transaction(first);
    host.lose_submit_ack = true;
    const auto uncertain = command(first, "submit", host);
    assert(field(uncertain, "phase") == "Uncertain");
    assert((typed ? private_value(host, witness_namespace, wallet_key)
                  : private_value(host, module_namespace(call_id))) == "null");
    std::string recovery_context;
    if (typed) {
      uint64_t token = 0;
      require_ok(noctium_client_recovery_context(first, &token), "take typed recovery context");
      auto private_data = take(token, true);
      recovery_context = text(private_data);
      wipe(private_data);
    }
    require_ok(noctium_client_detach(first), "detach uncertain client");
    write(argv[8], "{\"deploymentAttempt\":\"" + deploy_id + "\",\"callAttempt\":\"" + call_id
          + "\",\"transactionId\":\"" + field(uncertain, "transactionId")
          + "\",\"contractAddress\":\"" + address + "\",\"transactionHex\":\"" + hex(sealed)
          + "\"" + (typed ? ",\"typedContext\":" + recovery_context : "") + "}", true);
    for (volatile auto& byte : recovery_context) byte = 0;
  } else {
    assert(address == field(reference, "contractAddress"));
    const auto call_id = field(reference, "callAttempt");
    auto host_context = typed ? object(reference, "typedContext")
                              : context(call_id, module_namespace(call_id));
    const auto deploy_id = field(reference, "deploymentAttempt");
    const auto crossed_context = context(deploy_id, module_namespace(deploy_id));
    uint64_t denied = 99;
    const auto crossed = noctium_native_contract_call_recover(
        target, bytes(call_id), call_id.size(), descriptor.data(), descriptor.size(),
        bytes(crossed_context), crossed_context.size(), &denied);
    assert(crossed != NOCTIUM_NATIVE_OK && denied == 0);
    uint64_t first = 0;
    require_ok(noctium_native_contract_call_recover(
        target, bytes(call_id), call_id.size(), descriptor.data(), descriptor.size(),
        bytes(host_context), host_context.size(), &first), "recover module call");
    for (volatile auto& byte : host_context) byte = 0;
    drive(first, host);
    assert(hex(transaction(first)) == field(reference, "transactionHex"));
    current = finalize_module_call(first, first_operation, host, true, &private_revision);
    assert(std::count(host.operations.begin(), host.operations.end(),
                      "private_state.compare_exchange.v1") == 1);
    for (const auto& operation : host.operations) {
      assert(operation != "funding.native.v1" && operation != "approval.sign.v1");
    }
    if (typed) {
      assert(private_revision == "r1");
      assert(field(private_value(host, witness_namespace, wallet_key), "value") == "7");
      current = finalize_module_call(start("advanceAgain", "9", attempt_id()), "advanceAgain",
                                     host, false, &private_revision);
      assert(private_revision == "r2");
      assert(field(private_value(host, witness_namespace, wallet_key), "value") == "9");
    } else {
      assert(private_value(host, module_namespace(call_id)).find("\"value\":true") != std::string::npos);
      const std::pair<const char*, const char*> calls[] = {
          {"againRead", "11"}, {"againUpdate", "23"}, {"differentUpdate", "7"}
      };
      for (const auto& [operation, value] : calls) {
        current = finalize_module_call(start(operation, value, attempt_id()), operation, host, false);
      }
      start("againRead", "22", attempt_id(), NOCTIUM_NATIVE_INVALID_ARGUMENT);
    }
    require_ok(noctium_native_contract_state_free(current), "free final module state");
    std::cout << "{\"recoveredFirstCall\":true,\"crossedRecoveryRejected\":true,"
              << (typed ? "\"secondCallbackReadCommittedState\":true," : "\"staleReadRejected\":true,")
              << "\"contractAddress\":\""
              << address << "\"}" << std::endl;
    for (volatile auto& byte : reference) byte = 0;
  }
  require_ok(noctium_native_contract_target_free(target), "free module target");
  require_ok(noctium_localnet_free(host.adapter), "free localnet adapter");
  return 0;
}

int main(int argc,char** argv){
  assert(argc>=2);const std::string mode=argv[1];
  if (mode == "modules-run" || mode == "modules-recover") {
    return modules(argc, argv, mode == "modules-recover");
  }
  if (mode == "typed-modules-run" || mode == "typed-modules-recover") {
    return modules(argc, argv, mode == "typed-modules-recover", true);
  }
  if(mode=="run"){
    assert(argc==9);auto proof_descriptor=read(argv[2]),private_config=read(argv[3]),srs=read(argv[4]),descriptor=read(argv[5]),local=read(argv[6]);Host host{open_adapter(local,true)};
    uint64_t t=0;assert(noctium_localnet_context(host.adapter,&t)==NOCTIUM_NATIVE_OK);const auto public_context=text(take(t));auto proof_json=text(proof_descriptor);const auto p=value_start(proof_json,"ttl"),end=proof_json.find_first_not_of("0123456789",p);proof_json.replace(p,end-p,std::to_string(std::stoull(field(public_context,"blockTime"))+1800));proof_descriptor=Bytes(proof_json.begin(),proof_json.end());
    const auto cancelled_source=prove_source(proof_descriptor,private_config,srs);auto cancel_entropy=coins();const auto cancel_id=hex(cancel_entropy);wipe(cancel_entropy);const auto cancel_ns="cpp61-cancel-"+cancel_id.substr(0,16);const auto cancel_setup=setup(context(cancel_id,cancel_ns));uint64_t cancelled=0;assert(noctium_client_start(cancelled_source,0,descriptor.data(),descriptor.size(),reinterpret_cast<const uint8_t*>(cancel_setup.data()),cancel_setup.size(),&cancelled)==NOCTIUM_NATIVE_OK);
    const std::string prepare_command="prepare";assert(noctium_client_command(cancelled,reinterpret_cast<const uint8_t*>(prepare_command.data()),prepare_command.size(),&t)==NOCTIUM_NATIVE_OK);auto cancel_pending=text(take(t));
    for(unsigned step=0;step<2;++step){assert(field(cancel_pending,"operation")==std::string(step==0?"chain.snapshot.v1":"funding.native.v1"));uint64_t request=0,reply=0;assert(noctium_client_request(cancelled,&request)==NOCTIUM_NATIVE_OK);auto entropy=coins();assert(noctium_localnet_resolve(host.adapter,request,1,entropy.data(),entropy.size(),&reply)==NOCTIUM_NATIVE_OK);wipe(entropy);const auto m=metadata(cancel_pending);assert(noctium_client_resume(cancelled,reinterpret_cast<const uint8_t*>(m.data()),m.size(),reply,&t)==NOCTIUM_NATIVE_OK);cancel_pending=text(take(t));}
    assert(field(cancel_pending,"operation")=="approval.sign.v1");uint64_t cancel_request=0,private_token=0;assert(noctium_client_request(cancelled,&cancel_request)==NOCTIUM_NATIVE_OK);assert(noctium_client_private_request(cancel_request,&private_token)==NOCTIUM_NATIVE_OK);assert(noctium_client_detach(cancelled)==NOCTIUM_NATIVE_INVALID_STATE);const auto cancel_done=command(cancelled,"cancel",host);assert(field(cancel_done,"phase")=="Cancelled");size_t revoked_length=99;assert(noctium_native_private_length(private_token,&revoked_length)==NOCTIUM_NATIVE_INVALID_HANDLE&&revoked_length==0);assert(noctium_client_service_failure(cancel_request,&t)==NOCTIUM_NATIVE_INVALID_HANDLE&&t==0);assert(private_value(host,cancel_ns)=="null");assert(noctium_client_detach(cancelled)==NOCTIUM_NATIVE_OK);assert(noctium_native_free(cancelled_source)==NOCTIUM_NATIVE_OK);
    for(const auto& initial_command:std::vector<std::string>{"cancel","deadline"}){
      const auto dry_source=prove_source(proof_descriptor,private_config,srs);auto dry_entropy=coins();const auto dry_id=hex(dry_entropy);wipe(dry_entropy);const auto dry_setup=setup(context(dry_id,"cpp61-dry-"+dry_id.substr(0,16)));uint64_t dry=0;assert(noctium_client_start(dry_source,0,descriptor.data(),descriptor.size(),reinterpret_cast<const uint8_t*>(dry_setup.data()),dry_setup.size(),&dry)==NOCTIUM_NATIVE_OK);assert(field(command(dry,"prepare",host),"phase")=="Prepared");
      assert(noctium_client_command(dry,reinterpret_cast<const uint8_t*>(initial_command.data()),initial_command.size(),&t)==NOCTIUM_NATIVE_OK);const auto pending_cancel=text(take(t));assert(field(pending_cancel,"operation")=="journal.persist.v1");uint64_t cancel_q=0,failure=0;assert(noctium_client_request(dry,&cancel_q)==NOCTIUM_NATIVE_OK);assert(noctium_client_service_failure(cancel_q,&failure)==NOCTIUM_NATIVE_OK);const auto m=metadata(pending_cancel);assert(noctium_client_resume(dry,reinterpret_cast<const uint8_t*>(m.data()),m.size(),failure,&t)==NOCTIUM_NATIVE_OK);const auto not_durable=text(take(t));assert(field(not_durable,"phase")=="Cancelled");assert(not_durable.find("\"durableAcknowledged\":false")!=std::string::npos);assert(noctium_client_detach(dry)==NOCTIUM_NATIVE_INVALID_STATE);
      const auto start_ops=host.operations.size();const auto durable_cancel=command(dry,initial_command.c_str(),host);assert(field(durable_cancel,"phase")=="Cancelled");assert(durable_cancel.find("\"durableAcknowledged\":true")!=std::string::npos);for(auto i=start_ops;i<host.operations.size();++i)assert(host.operations[i]=="journal.persist.v1");uint64_t denied=99;const std::string submit="submit";assert(noctium_client_command(dry,reinterpret_cast<const uint8_t*>(submit.data()),submit.size(),&denied)==NOCTIUM_NATIVE_INVALID_STATE&&denied==0);assert(noctium_client_detach(dry)==NOCTIUM_NATIVE_OK);assert(noctium_native_free(dry_source)==NOCTIUM_NATIVE_OK);
    }
    const auto source=prove_source(proof_descriptor,private_config,srs);wipe(private_config);
    auto id_entropy=coins();const auto deploy_id=hex(id_entropy);wipe(id_entropy);const auto deploy_ns="cpp61-deploy-"+deploy_id.substr(0,16);const auto deploy_context=context(deploy_id,deploy_ns,true);const auto deploy_setup=setup(deploy_context);uint64_t deployment=0;assert(noctium_client_start(source,0,descriptor.data(),descriptor.size(),reinterpret_cast<const uint8_t*>(deploy_setup.data()),deploy_setup.size(),&deployment)==NOCTIUM_NATIVE_OK);
    auto prepared=command(deployment,"prepare",host);if(field(prepared,"status")!="step_done"){std::cerr<<prepared<<std::endl;assert(false);}const auto deploy_tx=transaction(deployment);assert(field(command(deployment,"submit",host),"status")=="step_done");observe(deployment,host);const auto deployed=command(deployment,"commit",host);assert(field(deployed,"phase")=="Conflicted");assert(deployed.find("\"privateCommitted\":false")!=std::string::npos);assert(private_value(host,deploy_ns)=="null");const auto initial=state(deployment);assert(noctium_client_detach(deployment)==NOCTIUM_NATIVE_OK);
    id_entropy=coins();const auto call_id=hex(id_entropy);wipe(id_entropy);const auto call_ns="cpp61-call-"+call_id.substr(0,16);const auto call_context=context(call_id,call_ns);const auto call_setup=setup(call_context);uint64_t call=0;assert(noctium_client_start(source,1,descriptor.data(),descriptor.size(),reinterpret_cast<const uint8_t*>(call_setup.data()),call_setup.size(),&call)==NOCTIUM_NATIVE_OK);assert(noctium_client_start(source,1,descriptor.data(),descriptor.size(),reinterpret_cast<const uint8_t*>(call_setup.data()),call_setup.size(),&t)==NOCTIUM_NATIVE_INVALID_STATE&&t==0);
    prepared=command(call,"prepare",host);if(field(prepared,"status")!="step_done"){std::cerr<<prepared<<std::endl;assert(false);}const auto call_tx=transaction(call);host.lose_submit_ack=true;const auto uncertain=command(call,"submit",host);assert(field(uncertain,"phase")=="Uncertain");assert(private_value(host,call_ns)=="null");uint64_t out=99;const std::string cancel="cancel";assert(noctium_client_command(call,reinterpret_cast<const uint8_t*>(cancel.data()),cancel.size(),&out)==NOCTIUM_NATIVE_INVALID_STATE&&out==0);assert(noctium_client_detach(call)==NOCTIUM_NATIVE_OK);assert(noctium_native_free(source)==NOCTIUM_NATIVE_OK);
    write(argv[8],"{\"hostContext\":"+call_context+",\"expectedTransactionId\":\""+field(uncertain,"transactionId")+"\",\"namespace\":\""+call_ns+"\",\"sealedTransactionHex\":\""+hex(call_tx)+"\"}",true);
    const auto output="{\"adapter\":\"linked C++ native client phase B\",\"deployment\":"+deployed+",\"deploymentTransactionHex\":\""+hex(deploy_tx)+"\",\"initialStateHex\":\""+hex(initial)+"\",\"callUncertain\":"+uncertain+",\"callTransactionHex\":\""+hex(call_tx)+"\",\"largestPrivateServicePayload\":"+std::to_string(host.largest_private)+",\"lostSubmissionAcknowledgement\":true,\"deploymentCasConflict\":true,\"preBroadcastApprovalCancellation\":true,\"cancelledPrivatePayloadRevoked\":true,\"cancelAndDeadlinePersistenceRetry\":true,\"privateClaimCasBeforeFinality\":false}";write(argv[7],output);std::cout<<"{\"status\":\"recovery_required\",\"contractAddress\":\""+field(uncertain,"contractAddress")+"\",\"transactionId\":\""+field(uncertain,"transactionId")+"\"}"<<std::endl;assert(noctium_localnet_free(host.adapter)==NOCTIUM_NATIVE_OK);return 0;
  }
  assert(mode=="recover"&&argc==6);auto descriptor=read(argv[2]),local=read(argv[3]),private_reference=read(argv[4]);const auto reference=text(private_reference),ctx=object(reference,"hostContext"),expected=field(reference,"expectedTransactionId"),ns=field(reference,"namespace");Host host{open_adapter(local,false)};
  const auto a=recover(descriptor,ctx),b=recover(descriptor,ctx);uint64_t ta=0,tb=0;assert(noctium_client_advance(a,&ta)==NOCTIUM_NATIVE_OK);auto sa=text(take(ta));assert(noctium_client_advance(b,&tb)==NOCTIUM_NATIVE_OK);auto sb=text(take(tb));uint64_t qa=0,qb=0,reply=0;assert(noctium_client_request(a,&qa)==NOCTIUM_NATIVE_OK);assert(noctium_client_request(b,&qb)==NOCTIUM_NATIVE_OK);assert(noctium_localnet_resolve(host.adapter,qa,0,nullptr,0,&reply)==NOCTIUM_NATIVE_OK);const auto mb=metadata(sb);uint64_t out=99;assert(noctium_client_resume(b,reinterpret_cast<const uint8_t*>(mb.data()),mb.size(),reply,&out)==NOCTIUM_NATIVE_INVALID_RESPONSE&&out==0);const auto ma=metadata(sa);assert(noctium_client_resume(a,reinterpret_cast<const uint8_t*>(ma.data()),ma.size(),reply,&out)==NOCTIUM_NATIVE_OK);sa=drive(a,host,text(take(out)));sb=drive(b,host,sb);assert(field(sa,"transactionId")==expected&&field(sb,"transactionId")==expected);
  const auto original=transaction(a);assert(hex(original)==field(reference,"sealedTransactionHex"));assert(field(command(a,"submit",host),"status")=="step_done");observe(a,host);const auto accepted=command(a,"commit",host);if(field(accepted,"phase")!="Committed"){std::cerr<<accepted<<std::endl;assert(false);}assert(accepted.find("\"privateCommitted\":true")!=std::string::npos);assert(private_value(host,ns).find("\"value\":true")!=std::string::npos);const auto final_state=state(a);
  auto before=host.operations.size();const auto stale=command(b,"submit",host);assert(field(stale,"status")=="step_error");for(auto i=before;i<host.operations.size();++i)assert(host.operations[i]!="chain.submit.v1");assert(transaction(b)==original);assert(noctium_client_detach(b)==NOCTIUM_NATIVE_INVALID_STATE);assert(field(command(b,"reload",host),"phase")=="Committed");before=host.operations.size();assert(field(command(b,"commit",host),"status")=="step_error");assert(host.operations.size()==before);observe(b,host);before=host.operations.size();assert(field(command(b,"commit",host),"phase")=="Committed");for(auto i=before;i<host.operations.size();++i)assert(host.operations[i]!="private_state.compare_exchange.v1");assert(transaction(b)==original);
  for(const auto& op:host.operations)assert(op!="funding.native.v1"&&op!="approval.sign.v1");
  write(argv[5],"{\"adapter\":\"separate linked C++ recovery process\",\"result\":"+accepted+",\"transactionHex\":\""+hex(original)+"\",\"finalStateHex\":\""+hex(final_state)+"\",\"largestPrivateServicePayload\":"+std::to_string(host.largest_private)+",\"crossedReplyRejected\":true,\"staleWriterRejectedBeforeBroadcast\":true,\"terminalReplayHadNoSecondExternalCas\":true,\"witnessSeedFundingSigningNeeded\":false}");std::cout<<"{\"status\":\"committed\",\"transactionId\":\""+expected+"\",\"contractAddress\":\""+field(accepted,"contractAddress")+"\"}"<<std::endl;wipe(private_reference);assert(noctium_client_detach(a)==NOCTIUM_NATIVE_OK);assert(noctium_client_detach(b)==NOCTIUM_NATIVE_OK);assert(noctium_localnet_free(host.adapter)==NOCTIUM_NATIVE_OK);return 0;
}
