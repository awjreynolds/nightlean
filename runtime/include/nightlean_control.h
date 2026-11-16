#ifndef NIGHTLEAN_CONTROL_H
#define NIGHTLEAN_CONTROL_H
#include <stddef.h>
#include <stdint.h>
#ifdef __cplusplus
extern "C" {
#endif
/* Separate source-only host execution. No native circuit, proof, transaction or
   persistent-commit operation is exposed. Handles are process-local and bounded.
   Inputs are UTF-8 JSON, at most 1MiB, and retained provider arguments are private.
   Result tokens retain bytes until result_free. Copies belong to the caller.
   No callback runs inside the ABI. Ordinary status/request transport is private
   host-execution data. Scheduling, failures and activity may depend on private
   guards. Never publish this transport as contract logs or observations. DF-00
   checks successful scalar return payloads, not host/provider activity or timing.
   The host registers providers through hostContext, dispatches need_host requests,
   and resumes with the bound request id, operation, capability, schema and value.
   Repeated advance while suspended returns the same request. Invalid responses
   retain suspension. cancel drops invocation-local state and denies later resume.
   Copies require caller-owned valid buffers. Null/invalid pointers are rejected
   where detectable. Memory validity and synchronization stay the caller's duty. */
enum { NIGHTLEAN_CONTROL_OK=0, NIGHTLEAN_CONTROL_INVALID_ARGUMENT=1,
  NIGHTLEAN_CONTROL_INVALID_HANDLE=2, NIGHTLEAN_CONTROL_INVALID_STATE=3,
  NIGHTLEAN_CONTROL_INVALID_RESPONSE=4, NIGHTLEAN_CONTROL_LIMIT=5,
  NIGHTLEAN_CONTROL_INTERNAL=6, NIGHTLEAN_CONTROL_BUFFER_TOO_SMALL=7 };
int32_t nightlean_control_begin(const uint8_t*,size_t,uint64_t*);
int32_t nightlean_control_advance(uint64_t,uint64_t*);
int32_t nightlean_control_resume(uint64_t,const uint8_t*,size_t,uint64_t*);
int32_t nightlean_control_stage(uint64_t,const uint8_t*,size_t,uint64_t*);
int32_t nightlean_control_cancel(uint64_t,uint64_t*);
int32_t nightlean_control_free(uint64_t);
int32_t nightlean_control_result_length(uint64_t,size_t*);
int32_t nightlean_control_result_copy(uint64_t,uint8_t*,size_t,size_t*);
int32_t nightlean_control_result_free(uint64_t);
/* Private request arguments and branch-effect traces use a separate token API.
   Ordinary result functions reject these tokens. Caller-owned copies stay private
   and require the host's own clearing policy. Traces contain no witness values.
   private_request includes invocationWrites, an overlay of validated local stages
   for the current callback. This overlay is cleared on failure/cancel/free. */
int32_t nightlean_control_private_request(uint64_t,uint64_t*);
int32_t nightlean_control_private_trace(uint64_t,uint64_t*);
int32_t nightlean_control_private_length(uint64_t,size_t*);
int32_t nightlean_control_private_copy(uint64_t,uint8_t*,size_t,size_t*);
int32_t nightlean_control_private_free(uint64_t);
#ifdef __cplusplus
}
#endif
#endif
