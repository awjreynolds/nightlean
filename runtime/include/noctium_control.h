#ifndef NOCTIUM_CONTROL_H
#define NOCTIUM_CONTROL_H
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
   A native v2 plan starts through begin_from_native_target. Its opaque target
   context binds the authenticated plan, witness binding, relation, contract
   address and entrypoint before any provider or stage runs. The Control session
   freezes this target. Native handoff checks the proof-prepared call against the
   same context before it consumes the session.
   Repeated advance while suspended returns the same request. Invalid responses
   retain suspension. cancel drops invocation-local state and denies later resume.
   Copies require caller-owned valid buffers. Null/invalid pointers are rejected
   where detectable. Memory validity and synchronization stay the caller's duty. */
enum { NOCTIUM_CONTROL_OK=0, NOCTIUM_CONTROL_INVALID_ARGUMENT=1,
  NOCTIUM_CONTROL_INVALID_HANDLE=2, NOCTIUM_CONTROL_INVALID_STATE=3,
  NOCTIUM_CONTROL_INVALID_RESPONSE=4, NOCTIUM_CONTROL_LIMIT=5,
  NOCTIUM_CONTROL_INTERNAL=6, NOCTIUM_CONTROL_BUFFER_TOO_SMALL=7 };
int32_t noctium_control_begin(const uint8_t*,size_t,uint64_t*);
/* Native v2 source programs start only from an opaque target context retained
   from an authenticated bundle and state configuration. Plan bytes must match
   the selected bundle artifact exactly. begin JSON is
   {"abiVersion":1,"inputs":{...},"hostContext":{...}}. The target token
   supplies the frozen contract address, entrypoint, binding and relation. */
int32_t noctium_control_begin_from_native_target(uint64_t,const uint8_t*,size_t,
  const uint8_t*,size_t,uint64_t*);
int32_t noctium_control_advance(uint64_t,uint64_t*);
int32_t noctium_control_resume(uint64_t,const uint8_t*,size_t,uint64_t*);
/* V2 typed witness replies use protocolVersion=2, canonical decimal requestId,
   exact operation/capability/schema and outcome=value with a canonical value,
   or outcome=error with error.code=provider_failed. */
int32_t noctium_control_resume_typed(uint64_t,const uint8_t*,size_t,uint64_t*);
/* External/manual staging is supported for legacy v1 plans only. V2 writes
   execute from their bound source plan through the interpreter. */
int32_t noctium_control_stage(uint64_t,const uint8_t*,size_t,uint64_t*);
int32_t noctium_control_cancel(uint64_t,uint64_t*);
int32_t noctium_control_free(uint64_t);
int32_t noctium_control_result_length(uint64_t,size_t*);
int32_t noctium_control_result_copy(uint64_t,uint8_t*,size_t,size_t*);
int32_t noctium_control_result_free(uint64_t);
/* Private request arguments and branch-effect traces use a separate token API.
   Ordinary result functions reject these tokens. Caller-owned copies stay private
   and require the host's own clearing policy. Traces contain no witness values.
   private_request includes invocationWrites, an overlay of validated local stages
   for the current callback. This overlay is cleared on failure/cancel/free. */
int32_t noctium_control_private_request(uint64_t,uint64_t*);
int32_t noctium_control_private_trace(uint64_t,uint64_t*);
/* V2 native-plan completion validates the exact actual relation and exports a
   private snapshot of the complete scalar circuit input map plus host writes.
   Bool leaves bound to native field inputs use canonical decimal strings "0"/"1". */
int32_t noctium_control_private_completion(uint64_t,const uint8_t*,size_t,uint64_t*);
int32_t noctium_control_private_length(uint64_t,size_t*);
int32_t noctium_control_private_copy(uint64_t,uint8_t*,size_t,size_t*);
int32_t noctium_control_private_free(uint64_t);
#ifdef __cplusplus
}
#endif
#endif
