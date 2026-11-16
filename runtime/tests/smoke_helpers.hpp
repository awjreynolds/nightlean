#pragma once
#include "nightlean_runtime.h"
#include <cassert>
#include <fstream>
#include <iterator>
#include <string>
#include <vector>

inline std::string take(uint64_t token) {
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
inline bool contains(const std::string &s, const std::string &part) {
  return s.find(part) != std::string::npos;
}
inline uint64_t start_session(const std::string &envelope) {
  uint64_t session = 0, result = 0;
  assert(nightlean_session_begin(reinterpret_cast<const uint8_t *>(envelope.data()),
                                envelope.size(), &session, &result) == NIGHTLEAN_OK);
  assert(session != 0 && contains(take(result), "\"status\":\"ready\""));
  return session;
}
inline std::string advance(uint64_t session) {
  uint64_t result = 0;
  assert(nightlean_session_advance(session, &result) == NIGHTLEAN_OK);
  return take(result);
}
inline void resume(uint64_t session, uint64_t id, const std::string &value,
                   int32_t expected) {
  const std::string response = "{\"abiVersion\":1,\"requestId\":" +
    std::to_string(id) + ",\"value\":" + value + "}";
  uint64_t result = 99;
  assert(nightlean_session_resume(session,
    reinterpret_cast<const uint8_t *>(response.data()), response.size(), &result) == expected);
  if (expected == NIGHTLEAN_OK) assert(contains(take(result), "\"status\":\"ready\""));
  else assert(result == 0);
}
