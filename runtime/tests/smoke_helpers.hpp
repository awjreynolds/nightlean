#pragma once
#include "noctium_runtime.h"
#include <cassert>
#include <fstream>
#include <iterator>
#include <string>
#include <vector>

inline std::string take(uint64_t token) {
  size_t size = 0, written = 99;
  assert(noctium_result_length(token, &size) == NOCTIUM_OK);
  assert(size > 0);
  std::string bytes(size, '\0');
  assert(noctium_result_copy(token, reinterpret_cast<uint8_t *>(bytes.data()),
                               size - 1, &written) == NOCTIUM_BUFFER_TOO_SMALL);
  assert(written == 0);
  assert(noctium_result_copy(token, reinterpret_cast<uint8_t *>(bytes.data()),
                               size, &written) == NOCTIUM_OK);
  assert(written == size);
  assert(noctium_result_free(token) == NOCTIUM_OK);
  assert(noctium_result_free(token) == NOCTIUM_INVALID_HANDLE);
  return bytes;
}
inline bool contains(const std::string &s, const std::string &part) {
  return s.find(part) != std::string::npos;
}
inline uint64_t start_session(const std::string &envelope) {
  uint64_t session = 0, result = 0;
  assert(noctium_session_begin(reinterpret_cast<const uint8_t *>(envelope.data()),
                                envelope.size(), &session, &result) == NOCTIUM_OK);
  assert(session != 0 && contains(take(result), "\"status\":\"ready\""));
  return session;
}
inline std::string advance(uint64_t session) {
  uint64_t result = 0;
  assert(noctium_session_advance(session, &result) == NOCTIUM_OK);
  return take(result);
}
inline void resume(uint64_t session, uint64_t id, const std::string &value,
                   int32_t expected) {
  const std::string response = "{\"abiVersion\":1,\"requestId\":" +
    std::to_string(id) + ",\"value\":" + value + "}";
  uint64_t result = 99;
  assert(noctium_session_resume(session,
    reinterpret_cast<const uint8_t *>(response.data()), response.size(), &result) == expected);
  if (expected == NOCTIUM_OK) assert(contains(take(result), "\"status\":\"ready\""));
  else assert(result == 0);
}
