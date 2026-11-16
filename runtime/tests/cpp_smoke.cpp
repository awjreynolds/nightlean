#include "nightlean_runtime.h"
#include <cassert>
#include <fstream>
#include <iterator>
#include <string>
#include <vector>

static std::string take(uint64_t token) {
  size_t size = 0, written = 99;
  assert(nightlean_result_length(token, &size) == NIGHTLEAN_OK);
  assert(size > 0);
  std::string bytes(size, '\0');
  assert(nightlean_result_copy(token, reinterpret_cast<uint8_t *>(bytes.data()),
                               size - 1, &written) == NIGHTLEAN_BUFFER_TOO_SMALL);
  assert(written == 0);
  assert(nightlean_result_copy(token, reinterpret_cast<uint8_t *>(bytes.data()),
                               size, &written) == NIGHTLEAN_OK);
  assert(written == size);
  assert(nightlean_result_free(token) == NIGHTLEAN_OK);
  assert(nightlean_result_free(token) == NIGHTLEAN_INVALID_HANDLE);
  return bytes;
}
static bool contains(const std::string &s, const std::string &part) {
  return s.find(part) != std::string::npos;
}
static uint64_t start_session(const std::string &envelope) {
  uint64_t session = 0, result = 0;
  assert(nightlean_session_begin(reinterpret_cast<const uint8_t *>(envelope.data()),
                                envelope.size(), &session, &result) == NIGHTLEAN_OK);
  assert(session != 0 && contains(take(result), "\"status\":\"ready\""));
  return session;
}
static std::string advance(uint64_t session) {
  uint64_t result = 0;
  assert(nightlean_session_advance(session, &result) == NIGHTLEAN_OK);
  return take(result);
}
static void resume(uint64_t session, uint64_t id, const std::string &value,
                   int32_t expected) {
  const std::string response = "{\"abiVersion\":1,\"requestId\":" +
    std::to_string(id) + ",\"value\":" + value + "}";
  uint64_t result = 99;
  assert(nightlean_session_resume(session,
    reinterpret_cast<const uint8_t *>(response.data()), response.size(), &result) == expected);
  if (expected == NIGHTLEAN_OK) assert(contains(take(result), "\"status\":\"ready\""));
  else assert(result == 0);
}
int main(int argc, char **argv) {
  assert(argc == 2);
  std::ifstream file(argv[1]);
  std::string envelope((std::istreambuf_iterator<char>(file)), {});
  assert(!envelope.empty());
  const uint64_t session = start_session(envelope);
  resume(session, 1, "\"42\"", NIGHTLEAN_INVALID_STATE);
  const std::vector<std::string> names = {"secret", "sibling0", "sibling1", "direction0", "direction1"};
  const std::vector<std::string> values = {"\"42\"", "\"17\"", "\"23\"", "false", "true"};
  for (size_t i = 0; i < names.size(); ++i) {
    const auto request = advance(session);
    assert(contains(request, "\"status\":\"need_host\""));
    assert(contains(request, "\"name\":\"" + names[i] + "\""));
    assert(contains(request, "\"id\":" + std::to_string(i + 1)));
    assert(advance(session) == request);
    resume(session, i + 2, values[i], NIGHTLEAN_INVALID_RESPONSE);
    resume(session, i + 1, i < 3 ? "\"042\"" : "\"false\"", NIGHTLEAN_INVALID_RESPONSE);
    assert(advance(session) == request);
    resume(session, i + 1, values[i], NIGHTLEAN_OK);
    resume(session, i + 1, values[i], NIGHTLEAN_INVALID_STATE);
  }
  const auto completed = advance(session);
  assert(contains(completed, "\"status\":\"completed\""));
  assert(contains(completed, "\"officialCircuitChecked\":true"));
  assert(contains(completed, "\"operations\":21"));
  assert(contains(completed, "\"nullifier\":\"16533581147424469099777953019315187868248076859940057971562926865714239641352\""));
  assert(contains(completed, "\"proofGenerated\":false"));
  assert(!contains(completed, "\"42\""));
  assert(advance(session) == completed);
  assert(nightlean_session_free(session) == NIGHTLEAN_OK);
  uint64_t result = 99;
  assert(nightlean_session_advance(session, &result) == NIGHTLEAN_INVALID_HANDLE);
  assert(result == 0);
  const uint64_t rejected = start_session(envelope);
  for (size_t i = 0; i < values.size(); ++i) {
    advance(rejected);
    resume(rejected, i + 1, i == 0 ? "\"43\"" : values[i], NIGHTLEAN_OK);
  }
  const auto failed = advance(rejected);
  assert(contains(failed, "\"status\":\"failed\""));
  assert(contains(failed, "execution_rejected"));
  assert(!contains(failed, "43"));
  assert(nightlean_session_free(rejected) == NIGHTLEAN_OK);
  const uint64_t cancelled = start_session(envelope);
  advance(cancelled);
  assert(nightlean_session_cancel(cancelled, &result) == NIGHTLEAN_OK);
  assert(contains(take(result), "\"status\":\"cancelled\""));
  assert(contains(advance(cancelled), "\"status\":\"cancelled\""));
  resume(cancelled, 1, "\"42\"", NIGHTLEAN_INVALID_STATE);
  assert(nightlean_session_free(cancelled) == NIGHTLEAN_OK);
  assert(nightlean_session_free(cancelled) == NIGHTLEAN_INVALID_HANDLE);
  return 0;
}
