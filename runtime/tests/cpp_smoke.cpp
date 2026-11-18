#include "smoke_helpers.hpp"

int main(int argc, char **argv) {
  assert(argc == 2 || argc == 3);
  std::ifstream file(argv[1]);
  std::string envelope((std::istreambuf_iterator<char>(file)), {});
  assert(!envelope.empty());
  const uint64_t session = start_session(envelope);
  resume(session, 1, "\"42\"", NOCTIUM_INVALID_STATE);
  const std::vector<std::string> names = {"secret", "sibling0", "sibling1", "direction0", "direction1"};
  const std::vector<std::string> values = {"\"42\"", "\"17\"", "\"23\"", "false", "true"};
  for (size_t i = 0; i < names.size(); ++i) {
    const auto request = advance(session);
    assert(contains(request, "\"status\":\"need_host\""));
    assert(contains(request, "\"name\":\"" + names[i] + "\""));
    assert(contains(request, "\"id\":" + std::to_string(i + 1)));
    assert(advance(session) == request);
    resume(session, i + 2, values[i], NOCTIUM_INVALID_RESPONSE);
    resume(session, i + 1, i < 3 ? "\"042\"" : "\"false\"", NOCTIUM_INVALID_RESPONSE);
    assert(advance(session) == request);
    resume(session, i + 1, values[i], NOCTIUM_OK);
    resume(session, i + 1, values[i], NOCTIUM_INVALID_STATE);
  }
  const auto completed = advance(session);
  assert(contains(completed, "\"status\":\"completed\""));
  assert(contains(completed, "\"officialCircuitChecked\":true"));
  assert(contains(completed, "\"operations\":21"));
  assert(contains(completed, "\"nullifier\":\"16533581147424469099777953019315187868248076859940057971562926865714239641352\""));
  assert(contains(completed, "\"proofGenerated\":false"));
  assert(!contains(completed, "\"42\""));
  assert(advance(session) == completed);
  assert(noctium_session_free(session) == NOCTIUM_OK);
  uint64_t result = 99;
  assert(noctium_session_advance(session, &result) == NOCTIUM_INVALID_HANDLE);
  assert(result == 0);
  const uint64_t rejected = start_session(envelope);
  for (size_t i = 0; i < values.size(); ++i) {
    advance(rejected);
    resume(rejected, i + 1, i == 0 ? "\"43\"" : values[i], NOCTIUM_OK);
  }
  const auto failed = advance(rejected);
  assert(contains(failed, "\"status\":\"failed\""));
  assert(contains(failed, "execution_rejected"));
  assert(!contains(failed, "43"));
  assert(noctium_session_free(rejected) == NOCTIUM_OK);
  const uint64_t cancelled = start_session(envelope);
  advance(cancelled);
  assert(noctium_session_cancel(cancelled, &result) == NOCTIUM_OK);
  assert(contains(take(result), "\"status\":\"cancelled\""));
  assert(contains(advance(cancelled), "\"status\":\"cancelled\""));
  resume(cancelled, 1, "\"42\"", NOCTIUM_INVALID_STATE);
  assert(noctium_session_free(cancelled) == NOCTIUM_OK);
  assert(noctium_session_free(cancelled) == NOCTIUM_INVALID_HANDLE);
  if (argc == 3) {
    std::ifstream unsigned_file(argv[2]);
    const std::string unsigned_envelope((std::istreambuf_iterator<char>(unsigned_file)), {});
    const auto unsigned_session = start_session(unsigned_envelope);
    const auto request = advance(unsigned_session);
    assert(contains(request, "\"name\":\"left\""));
    assert(contains(request, "\"type\":\"UIntRange<256>\""));
    resume(unsigned_session, 1, "255", NOCTIUM_INVALID_RESPONSE);
    resume(unsigned_session, 1, "true", NOCTIUM_INVALID_RESPONSE);
    resume(unsigned_session, 1, "\"256\"", NOCTIUM_INVALID_RESPONSE);
    resume(unsigned_session, 1, "\"0255\"", NOCTIUM_INVALID_RESPONSE);
    assert(advance(unsigned_session) == request);
    resume(unsigned_session, 1, "\"255\"", NOCTIUM_OK);
    assert(contains(advance(unsigned_session), "\"name\":\"right\""));
    resume(unsigned_session, 2, "\"255\"", NOCTIUM_OK);
    const auto unsigned_completed = advance(unsigned_session);
    assert(contains(unsigned_completed, "\"status\":\"completed\""));
    assert(contains(unsigned_completed, "\"result\":\"510\""));
    assert(contains(unsigned_completed, "\"officialCircuitChecked\":true"));
    assert(noctium_session_free(unsigned_session) == NOCTIUM_OK);
  }
  return 0;
}
