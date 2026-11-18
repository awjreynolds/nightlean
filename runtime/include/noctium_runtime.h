#ifndef NOCTIUM_RUNTIME_H
#define NOCTIUM_RUNTIME_H
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

#define NOCTIUM_ABI_VERSION 1u
#define NOCTIUM_MAX_INPUT_BYTES 1048576u
#define NOCTIUM_MAX_SESSIONS 64u
#define NOCTIUM_MAX_RESULTS 256u
#define NOCTIUM_HOST_PROTOCOL_VERSION 1u
#define NOCTIUM_MAX_PRIVATE_RESULTS 64u
#define NOCTIUM_PRIVATE_REQUEST 1u
#define NOCTIUM_PRIVATE_JOURNAL 2u

enum noctium_status {
  NOCTIUM_OK = 0,
  NOCTIUM_INVALID_ARGUMENT = 1,
  NOCTIUM_INVALID_HANDLE = 2,
  NOCTIUM_INVALID_STATE = 3,
  NOCTIUM_INVALID_RESPONSE = 4,
  NOCTIUM_LIMIT = 5,
  NOCTIUM_INTERNAL = 6,
  NOCTIUM_BUFFER_TOO_SMALL = 7
};

/* Handles are process-local tokens. Zero, stale, and unallocated tokens reject. Tokens are not security capabilities.
 * Every returned session/result has one explicit free. Freeing a session
 * never frees its results. No Rust allocation or layout crosses this ABI.
 *
 * Input buffers are borrowed for the call. All non-null output pointers must
 * address correctly aligned, writable storage of the declared extent. Input
 * byte ranges must be readable and must not overlap output storage. Output
 * regions must not overlap one another. Invalid
 * memory addresses are a caller error, beyond Rust panic recovery.
 *
 * JSON is UTF-8 without a terminator. Native fields use canonical decimal
 * strings, Bool uses JSON true/false. UIntRange<N> uses canonical decimal
 * strings in [0,N), with 1 <= N <= 2^248. Calls return a numeric status and clear
 * output handles before validation. Errors never contain input values.
 * Begin/resume payloads are limited to NOCTIUM_MAX_INPUT_BYTES.
 *
 * begin accepts abiVersion, profile, plan, publicInputs, state,
 * ledgerParametersHex, address, and circuit. Profile v1 is
 * midnight-ledger-9-zkir-3.2.0. Private values arrive only through resume.
 * advance yields need_host with a typed witness.input request, or completed,
 * failed, or cancelled. Repeated advance preserves a pending request id.
 * resume accepts {"abiVersion":1,"requestId":N,"value":VALUE} and returns
 * ready on success. Invalid responses preserve the pending request.
 *
 * Hosts own asynchronous I/O. No callbacks execute inside this library.
 * Cancellation is cooperative between calls. Calls are thread safe and
 * serialized, including circuit checking. Free only after calls complete.
 */
uint32_t noctium_runtime_abi_version(void);
int32_t noctium_session_begin(const uint8_t *json, size_t length,
                               uint64_t *out_session, uint64_t *out_result);
int32_t noctium_session_advance(uint64_t session, uint64_t *out_result);
int32_t noctium_session_resume(uint64_t session, const uint8_t *json,
                                size_t length, uint64_t *out_result);
int32_t noctium_session_cancel(uint64_t session, uint64_t *out_result);
int32_t noctium_session_free(uint64_t session);
/* Optional hostContext grants versioned provider operations and scopes. Legacy
 * scalar input sessions need no hostContext. New private-state operations never
 * perform host I/O. Staged updates are application policy, outside circuit proof.
 *
 * stage_private takes abiVersion, operation=private_state.stage.v1, capability,
 * key, type, value. notify takes abiVersion, event, attemptId, transactionId.
 * Events are bind, persisted, submitted, accepted, rejected, uncertain.
 * Persist the private journal before reporting submitted. Accepted is HOST
 * evidence and yields a private_state.compare_exchange.v1 request. Only an
 * affirmative, matching host CAS response acknowledges commit. The reply echoes
 * attemptId, transactionId, private journalDigest, baseRevision and new revision.
 * Rejection and
 * uncertainty never imply commit. No cancellation after submission.
 *
 * private_data returns a PRIVATE token in a separate buffer namespace. Kind 1
 * retrieves pending request arguments, kind 2 a prepared transaction-bound
 * journal. Never log or publish these bytes. Public result APIs reject private
 * tokens, and private APIs reject public tokens. Each private token requires
 * private_free. Free wipes retained bytes best effort, not caller copies.
 */
int32_t noctium_session_stage_private(uint64_t session, const uint8_t *json,
                                       size_t length, uint64_t *out_result);
int32_t noctium_session_notify(uint64_t session, const uint8_t *json,
                                size_t length, uint64_t *out_result);
int32_t noctium_session_private_data(uint64_t session, uint32_t kind,
                                      uint64_t *out_private);
int32_t noctium_private_length(uint64_t token, size_t *out_length);
int32_t noctium_private_copy(uint64_t token, uint8_t *destination,
                               size_t capacity, size_t *out_written);
int32_t noctium_private_free(uint64_t token);
int32_t noctium_result_length(uint64_t result, size_t *out_length);
/* No partial copies. out_written is zero on failure. A successful copy
 * writes exactly result_length bytes, without a trailing NUL. */
int32_t noctium_result_copy(uint64_t result, uint8_t *destination,
                             size_t capacity, size_t *out_written);
int32_t noctium_result_free(uint64_t result);

#ifdef __cplusplus
}
#endif
#endif
