#include "noctium_runtime.h"
#include <assert.h>
#include <stdint.h>

int main(void) {
  uint64_t session = 99, result = 99;
  size_t length = 99;
  assert(noctium_runtime_abi_version() == NOCTIUM_ABI_VERSION);
  assert(noctium_session_begin(NULL, 1, &session, &result) == NOCTIUM_INVALID_ARGUMENT);
  assert(session == 0 && result == 0);
  result = 99;
  assert(noctium_session_begin(NULL, 1, NULL, &result) == NOCTIUM_INVALID_ARGUMENT);
  assert(result == 0);
  session = 99;
  assert(noctium_session_begin(NULL, 1, &session, NULL) == NOCTIUM_INVALID_ARGUMENT);
  assert(session == 0);
  assert(noctium_session_begin(NULL, 1, NULL, NULL) == NOCTIUM_INVALID_ARGUMENT);
  assert(noctium_session_advance(UINT64_MAX, &result) == NOCTIUM_INVALID_HANDLE);
  assert(result == 0);
  assert(noctium_result_length(UINT64_MAX, &length) == NOCTIUM_INVALID_HANDLE);
  assert(length == 0);
  assert(noctium_session_free(UINT64_MAX) == NOCTIUM_INVALID_HANDLE);
  assert(noctium_result_free(UINT64_MAX) == NOCTIUM_INVALID_HANDLE);
  return 0;
}
