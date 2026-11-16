#include "nightlean_runtime.h"
#include <assert.h>
#include <stdint.h>

int main(void) {
  uint64_t session = 99, result = 99;
  size_t length = 99;
  assert(nightlean_runtime_abi_version() == NIGHTLEAN_ABI_VERSION);
  assert(nightlean_session_begin(NULL, 1, &session, &result) == NIGHTLEAN_INVALID_ARGUMENT);
  assert(session == 0 && result == 0);
  result = 99;
  assert(nightlean_session_begin(NULL, 1, NULL, &result) == NIGHTLEAN_INVALID_ARGUMENT);
  assert(result == 0);
  session = 99;
  assert(nightlean_session_begin(NULL, 1, &session, NULL) == NIGHTLEAN_INVALID_ARGUMENT);
  assert(session == 0);
  assert(nightlean_session_begin(NULL, 1, NULL, NULL) == NIGHTLEAN_INVALID_ARGUMENT);
  assert(nightlean_session_advance(UINT64_MAX, &result) == NIGHTLEAN_INVALID_HANDLE);
  assert(result == 0);
  assert(nightlean_result_length(UINT64_MAX, &length) == NIGHTLEAN_INVALID_HANDLE);
  assert(length == 0);
  assert(nightlean_session_free(UINT64_MAX) == NIGHTLEAN_INVALID_HANDLE);
  assert(nightlean_result_free(UINT64_MAX) == NIGHTLEAN_INVALID_HANDLE);
  return 0;
}
