#include "smoke_helpers.hpp"
#include <map>
#include <tuple>

using JsonCall = int32_t (*)(uint64_t, const uint8_t *, size_t, uint64_t *);
static const std::string staged_value = "8675309";
static std::string checked_take(uint64_t token) {
  const auto result = take(token);
  assert(!contains(result, staged_value));
  assert(!contains(result, "claims/"));
  assert(!contains(result,"journalDigest"));
  assert(!contains(result,"8675310"));
  return result;
}
static std::string host_call(uint64_t session, const std::string &json, JsonCall function,
                             int32_t expected = NIGHTLEAN_OK) {
  uint64_t result = 99;
  assert(function(session, reinterpret_cast<const uint8_t *>(json.data()), json.size(), &result) == expected);
  if (expected != NIGHTLEAN_OK) { assert(result == 0); return {}; }
  return checked_take(result);
}
static std::string host_advance(uint64_t session) {
  uint64_t result = 0;
  assert(nightlean_session_advance(session, &result) == NIGHTLEAN_OK);
  return checked_take(result);
}
static std::string private_data(uint64_t session, uint32_t kind, int32_t expected = NIGHTLEAN_OK) {
  uint64_t token = 99;
  assert(nightlean_session_private_data(session, kind, &token) == expected);
  if (expected != NIGHTLEAN_OK) { assert(token == 0); return {}; }
  size_t length = 0, written = 99;
  assert(nightlean_result_length(token, &length) == NIGHTLEAN_INVALID_HANDLE);
  assert(nightlean_private_length(token, &length) == NIGHTLEAN_OK);
  std::string bytes(length, '\0');
  assert(nightlean_private_copy(token, reinterpret_cast<uint8_t *>(bytes.data()), length - 1, &written) == NIGHTLEAN_BUFFER_TOO_SMALL);
  assert(written == 0);
  assert(nightlean_private_copy(token, reinterpret_cast<uint8_t *>(bytes.data()), length, &written) == NIGHTLEAN_OK);
  assert(nightlean_private_free(token) == NIGHTLEAN_OK);
  assert(nightlean_private_free(token) == NIGHTLEAN_INVALID_HANDLE);
  return bytes;
}
static std::string notice(uint64_t session, char attempt, char transaction, const std::string &event,
                          int32_t expected = NIGHTLEAN_OK) {
  return host_call(session, "{\"abiVersion\":1,\"event\":\"" + event +
    "\",\"attemptId\":\"" + std::string(64, attempt) + "\",\"transactionId\":\"" +
    std::string(64, transaction) + "\"}", nightlean_session_notify, expected);
}
static std::string stage(uint64_t session, const std::string &key,
                         int32_t expected = NIGHTLEAN_OK,const std::string &value=staged_value) {
  return host_call(session, "{\"abiVersion\":1,\"operation\":\"private_state.stage.v1\",\"capability\":\"store\",\"key\":\"" +
    key + "\",\"type\":\"Native\",\"value\":\"" + value + "\"}", nightlean_session_stage_private, expected);
}
static std::string read_response(uint64_t session, const std::string &value, int32_t expected = NIGHTLEAN_OK,
                                 const std::string &op = "private_state.read.v1", const std::string &cap = "store",
                                 const std::string &schema = "UIntRange<256>", unsigned id = 1) {
  return host_call(session, "{\"abiVersion\":1,\"requestId\":" + std::to_string(id) +
    ",\"operation\":\"" + op + "\",\"capability\":\"" + cap + "\",\"schema\":\"" + schema +
    "\",\"value\":" + value + "}", nightlean_session_resume, expected);
}
static std::string field(const std::string &json,const std::string &key){
  const auto prefix="\""+key+"\":\"";const auto start=json.find(prefix);assert(start!=std::string::npos);
  const auto value=start+prefix.size();const auto end=json.find('"',value);assert(end!=std::string::npos);return json.substr(value,end-value);
}
static std::string cas_payload(uint64_t session,const std::string &outcome,const std::string &revision,const std::string &base="r0"){
  const auto journal=private_data(session,NIGHTLEAN_PRIVATE_JOURNAL);
  return "{\"abiVersion\":1,\"requestId\":3,\"operation\":\"private_state.compare_exchange.v1\",\"capability\":\"store\",\"schema\":\"PrivateStateCasResult/v1\",\"value\":{\"outcome\":\""+outcome+"\",\"baseRevision\":\""+base+"\",\"revision\":\""+revision+"\",\"attemptId\":\""+field(journal,"attemptId")+"\",\"transactionId\":\""+field(journal,"transactionId")+"\",\"journalDigest\":\""+field(journal,"journalDigest")+"\"}}";
}
static std::string commit_response(uint64_t session,const std::string &outcome,const std::string &revision,int32_t expected=NIGHTLEAN_OK,const std::string &base="r0"){
  const auto payload=expected==NIGHTLEAN_INVALID_STATE?"{\"abiVersion\":1,\"requestId\":3,\"value\":{}}":cas_payload(session,outcome,revision,base);
  return host_call(session,payload,nightlean_session_resume,expected);
}
static std::string read_file(const char *path) {
  std::ifstream file(path);
  return std::string((std::istreambuf_iterator<char>(file)), {});
}
static std::string configured(std::string envelope, std::string context, char attempt) {
  const auto marker = context.find(std::string(64, 'a')); assert(marker != std::string::npos);
  context.replace(marker, 64, std::string(64, attempt));
  const auto end = envelope.find_last_not_of(" \r\n\t"); assert(envelope[end] == '}');
  envelope.erase(end);
  return envelope + ",\"hostContext\":" + context + "}";
}
static uint64_t prepared(const std::string &envelope) {
  const auto session = start_session(envelope);
  private_data(session, NIGHTLEAN_PRIVATE_JOURNAL, NIGHTLEAN_INVALID_STATE);
  stage(session, "claims/used");
  const auto request = host_advance(session);
  assert(contains(request, "private_state.read.v1"));
  assert(contains(private_data(session, NIGHTLEAN_PRIVATE_REQUEST), "claims/secret"));
  read_response(session, "\"255\"");
  assert(contains(host_advance(session), "\"name\":\"right\""));
  resume(session, 2, "\"255\"", NIGHTLEAN_OK);
  assert(contains(host_advance(session), "\"status\":\"completed\""));
  private_data(session,NIGHTLEAN_PRIVATE_JOURNAL,NIGHTLEAN_INVALID_STATE);
  stage(session,"claims/used",NIGHTLEAN_INVALID_STATE);
  return session;
}
static std::string accepted(uint64_t session, char attempt, char transaction) {
  notice(session, attempt, transaction, "bind");
  const auto journal=private_data(session,NIGHTLEAN_PRIVATE_JOURNAL);
  assert(contains(journal,staged_value)||contains(journal,"8675310"));
  notice(session, attempt, transaction, "submitted", NIGHTLEAN_INVALID_STATE);
  notice(session, attempt, transaction, "persisted");
  notice(session, attempt, transaction, "persisted");
  notice(session, attempt, transaction, "submitted");
  notice(session, attempt, transaction, "submitted");
  const auto request = notice(session, attempt, transaction, "accepted");
  assert(contains(request, "private_state.compare_exchange.v1"));
  return request;
}
struct HostStore {
  unsigned revision = 0, applies = 0;
  struct Receipt {char transaction;unsigned revision;std::string digest;};
  std::map<char, Receipt> receipts;
  std::map<std::string,std::string> values;
  std::string reply(uint64_t session, char attempt, char transaction) {
    const auto journal = private_data(session, NIGHTLEAN_PRIVATE_REQUEST);
    assert(contains(journal, "\"attemptId\":\"" + std::string(64, attempt) + "\""));
    assert(contains(journal, "\"transactionId\":\"" + std::string(64, transaction) + "\""));
    assert(contains(journal, "\"namespace\":\"wallet_A\""));
    assert(contains(journal, "\"baseRevision\":\"r0\""));
    assert(contains(journal, "\"entrypoint\":\"apply\""));
    const auto digest=field(journal,"journalDigest");
    if (receipts.count(attempt)) {
      const auto old = receipts.at(attempt);
      const auto outcome=old.transaction==transaction && old.digest==digest?"committed":"conflict";
      return cas_payload(session,outcome,"r"+std::to_string(old.revision));
    }
    if (revision != 0) return cas_payload(session, "conflict", "r" + std::to_string(revision));
    values["claims/used"]=staged_value;
    ++revision; ++applies; receipts[attempt] = {transaction, revision,digest};
    return cas_payload(session, "committed", "r" + std::to_string(revision));
  }
  std::string apply(uint64_t session,char attempt,char transaction){return host_call(session,reply(session,attempt,transaction),nightlean_session_resume);}
};
int main(int argc, char **argv) {
  assert(argc == 3);
  const auto envelope = read_file(argv[1]), context = read_file(argv[2]);
  auto with = [&](char attempt) { return configured(envelope, context, attempt); };
  for(const auto &change:std::vector<std::tuple<std::string,std::string,int32_t>>{
      {"\"requests\":3","\"requests\":2",NIGHTLEAN_LIMIT},
      {"\"keyPrefix\":\"claims/\"","\"keyPrefix\":\"*\"",NIGHTLEAN_INVALID_ARGUMENT},
      {"\"keyPrefix\":\"claims/\"","\"keyPrefix\":\"claims//\"",NIGHTLEAN_INVALID_ARGUMENT},
      {"\"resultSchema\":\"UIntRange<256>\"","\"resultSchema\":\"Bool\"",NIGHTLEAN_INVALID_ARGUMENT},
      {"claims/secret","claims_evil/secret",NIGHTLEAN_INVALID_RESPONSE}}){
    auto invalid=context;const auto at=invalid.find(std::get<0>(change));assert(at!=std::string::npos);invalid.replace(at,std::get<0>(change).size(),std::get<1>(change));
    const auto body=configured(envelope,invalid,'6');uint64_t bad_session=99,bad_result=99;
    assert(nightlean_session_begin(reinterpret_cast<const uint8_t*>(body.data()),body.size(),&bad_session,&bad_result)==std::get<2>(change));assert(bad_session==0&&bad_result==0);
  }
  const auto first = start_session(with('a'));
  stage(first, "claims_evil/used", NIGHTLEAN_INVALID_RESPONSE);
  stage(first, "claims/used"); stage(first, "claims/other", NIGHTLEAN_LIMIT);
  const auto request = host_advance(first); assert(host_advance(first) == request);
  read_response(first, "\"255\"", NIGHTLEAN_INVALID_RESPONSE, "wrong.v1");
  read_response(first, "\"255\"", NIGHTLEAN_INVALID_RESPONSE, "private_state.read.v1", "other");
  read_response(first, "\"255\"", NIGHTLEAN_INVALID_RESPONSE, "private_state.read.v1", "store", "Bool");
  read_response(first, "\"255\"", NIGHTLEAN_INVALID_RESPONSE, "private_state.read.v1", "store", "UIntRange<256>", 9);
  read_response(first, "\"0255\"", NIGHTLEAN_INVALID_RESPONSE);
  read_response(first, "\"256\"", NIGHTLEAN_INVALID_RESPONSE);
  assert(host_advance(first) == request);
  read_response(first, "\"255\""); read_response(first, "\"255\"", NIGHTLEAN_INVALID_STATE);
  host_advance(first); resume(first, 2, "\"255\"", NIGHTLEAN_OK); host_advance(first);
  const auto pending = accepted(first, 'a', 'b'); assert(notice(first, 'a', 'b', "accepted") == pending);
  notice(first, 'a', 'c', "accepted", NIGHTLEAN_INVALID_STATE);
  commit_response(first, "committed", "r1", NIGHTLEAN_INVALID_RESPONSE, "wrong");
  commit_response(first, "committed", "r0", NIGHTLEAN_INVALID_RESPONSE);
  const auto concurrent = prepared(with('c')); accepted(concurrent, 'c', 'd');
  HostStore store; assert(store.applies == 0);
  const auto reply=store.reply(first,'a','b');
  host_call(concurrent,reply,nightlean_session_resume,NIGHTLEAN_INVALID_RESPONSE);
  auto wrong_digest=reply;const auto digest_marker=field(reply,"journalDigest");wrong_digest.replace(wrong_digest.find(digest_marker),digest_marker.size(),std::string(64,'0'));
  host_call(first,wrong_digest,nightlean_session_resume,NIGHTLEAN_INVALID_RESPONSE);
  auto wrong_transaction=reply;wrong_transaction.replace(wrong_transaction.find(std::string(64,'b')),64,std::string(64,'c'));
  host_call(first,wrong_transaction,nightlean_session_resume,NIGHTLEAN_INVALID_RESPONSE);
  assert(contains(host_call(first,reply,nightlean_session_resume), "\"phase\":\"committed\"")); assert(store.applies == 1);
  assert(contains(notice(first, 'a', 'b', "accepted"), "\"phase\":\"committed\""));
  private_data(first, NIGHTLEAN_PRIVATE_JOURNAL, NIGHTLEAN_INVALID_STATE);
  commit_response(first, "committed", "r1", NIGHTLEAN_INVALID_STATE);
  assert(nightlean_session_free(first) == NIGHTLEAN_OK);
  assert(contains(store.apply(concurrent, 'c', 'd'), "\"phase\":\"conflicted\"")); assert(store.applies == 1);
  assert(nightlean_session_free(concurrent) == NIGHTLEAN_OK);
  const auto retry = prepared(with('a')); accepted(retry, 'a', 'b');
  assert(contains(store.apply(retry, 'a', 'b'), "\"phase\":\"committed\"")); assert(store.applies == 1);
  assert(nightlean_session_free(retry) == NIGHTLEAN_OK);
  const auto altered=start_session(with('a'));stage(altered,"claims/used",NIGHTLEAN_OK,"8675310");
  host_advance(altered);read_response(altered,"\"255\"");host_advance(altered);resume(altered,2,"\"255\"",NIGHTLEAN_OK);host_advance(altered);accepted(altered,'a','b');
  assert(contains(store.apply(altered,'a','b'),"\"phase\":\"conflicted\""));assert(store.applies==1);assert(nightlean_session_free(altered)==NIGHTLEAN_OK);
  const auto uncertain = prepared(with('e')); notice(uncertain, 'e', 'f', "bind");
  notice(uncertain, 'e', 'f', "persisted"); notice(uncertain, 'e', 'f', "submitted");
  assert(contains(notice(uncertain, 'e', 'f', "uncertain"), "\"hostCasAcknowledged\":false"));
  private_data(uncertain, NIGHTLEAN_PRIVATE_REQUEST, NIGHTLEAN_INVALID_STATE);
  uint64_t result = 0; assert(nightlean_session_cancel(uncertain, &result) == NIGHTLEAN_INVALID_STATE);
  assert(contains(notice(uncertain, 'e', 'f', "rejected"), "\"phase\":\"rejected\""));
  private_data(uncertain, NIGHTLEAN_PRIVATE_JOURNAL, NIGHTLEAN_INVALID_STATE);
  assert(nightlean_session_free(uncertain) == NIGHTLEAN_OK);
  const auto cancelled = start_session(with('1')); stage(cancelled, "claims/used");
  assert(nightlean_session_cancel(cancelled, &result) == NIGHTLEAN_OK); checked_take(result);
  private_data(cancelled, NIGHTLEAN_PRIVATE_JOURNAL, NIGHTLEAN_INVALID_STATE);
  assert(nightlean_session_free(cancelled) == NIGHTLEAN_OK);
  auto bad = with('2'); const auto sum = bad.find("\"expected\":\"510\""); assert(sum != std::string::npos);
  bad.replace(sum, std::string("\"expected\":\"510\"").size(), "\"expected\":\"509\"");
  const auto failed = start_session(bad); stage(failed, "claims/used"); host_advance(failed); read_response(failed, "\"255\"");
  host_advance(failed); resume(failed, 2, "\"255\"", NIGHTLEAN_OK);
  assert(contains(host_advance(failed), "\"status\":\"failed\""));
  private_data(failed, NIGHTLEAN_PRIVATE_JOURNAL, NIGHTLEAN_INVALID_STATE);
  assert(nightlean_session_free(failed) == NIGHTLEAN_OK);
  assert(store.applies==1 && store.values.size()==1 && store.values.at("claims/used")==staged_value);
  // Exhausted private-buffer quota rejects without advancing lifecycle state.
  const auto limited=prepared(with('3'));notice(limited,'3','4',"bind");
  std::vector<uint64_t> tokens;
  for(unsigned i=0;i<NIGHTLEAN_MAX_PRIVATE_RESULTS;++i){uint64_t token=0;assert(nightlean_session_private_data(limited,NIGHTLEAN_PRIVATE_JOURNAL,&token)==NIGHTLEAN_OK);tokens.push_back(token);}
  uint64_t extra=99;assert(nightlean_session_private_data(limited,NIGHTLEAN_PRIVATE_JOURNAL,&extra)==NIGHTLEAN_LIMIT);assert(extra==0);
  for(auto token:tokens)assert(nightlean_private_free(token)==NIGHTLEAN_OK);
  assert(contains(private_data(limited,NIGHTLEAN_PRIVATE_JOURNAL),staged_value));
  assert(nightlean_session_cancel(limited,&result)==NIGHTLEAN_OK);checked_take(result);assert(nightlean_session_free(limited)==NIGHTLEAN_OK);
  auto small=context;auto at=small.find("\"privateBytes\":4096");assert(at!=std::string::npos);small.replace(at,std::string("\"privateBytes\":4096").size(),"\"privateBytes\":1024");
  at=small.find("\"writes\":1");assert(at!=std::string::npos);small.replace(at,std::string("\"writes\":1").size(),"\"writes\":64");
  const auto small_session=start_session(configured(envelope,small,'5'));bool limited_bytes=false;
  for(unsigned i=0;i<64;++i){const auto key="claims/"+std::string(100,'k')+std::to_string(i);const auto body="{\"abiVersion\":1,\"operation\":\"private_state.stage.v1\",\"capability\":\"store\",\"key\":\""+key+"\",\"type\":\"Native\",\"value\":\"8675309\"}";
    uint64_t out=99;const auto code=nightlean_session_stage_private(small_session,reinterpret_cast<const uint8_t*>(body.data()),body.size(),&out);
    if(code==NIGHTLEAN_LIMIT){assert(out==0);limited_bytes=true;break;}assert(code==NIGHTLEAN_OK);checked_take(out);
  }
  assert(limited_bytes);assert(nightlean_session_cancel(small_session,&result)==NIGHTLEAN_OK);checked_take(result);assert(nightlean_session_free(small_session)==NIGHTLEAN_OK);
  return 0;
}
