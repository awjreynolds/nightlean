#ifndef NIGHTLEAN_NATIVE_H
#define NIGHTLEAN_NATIVE_H
#include <stddef.h>
#include <stdint.h>
#ifdef __cplusplus
extern "C" {
#endif
/* Native proof API, phase A of the host binding. Funding, signing, submission and
   journal persistence are outside this API. Existing runtime/control ABIs are
   separate. Tokens belong to this ABI and this process only.

   begin receives separate public descriptor, private configuration and public SRS
   byte channels. Descriptor UTF-8 JSON (unknown fields reject):
     {"abiVersion":1,"profile":"<selected profile NAME>",
      "bundleDirectory":"<explicit host-authorized filesystem directory>",
      "trustedManifestSha256":"<independently supplied lowercase SHA256>",
      "proofParametersSha256":"<independently supplied SRS SHA256>",
      "k":9,"ttl":2000000000,"proofServiceCapability":"host.prover",
      "maxResponseBytes":1048576}
   Bundle authentication/key validation and SRS validation precede private parsing.
   A digest authenticates retained bytes. Source certificate authority, native
   implementation/keygen, SRS ceremony relations and service disclosure authority
   require the host's own policy. No network, provider credential or ambient RNG
   is selected by this API. Supply 32 fresh unpredictable secret entropy bytes to
   begin and separately to every local_prove call. Entropy quality stays external.

   advance returns need_proof metadata with requestId, operation native.prove.v1,
   capability, profile, encoding midnight-prove-v2, k, source/SRS identities and
   bounds. Repeated advance returns the same pending request. Scheduling and
   request transport are private host data, outside contract-observer guarantees.
   private_request grants a separate owned token for the witness-bearing official
   /prove payload. Ordinary result access rejects private tokens. The host alone
   authorizes external service transmission and enforces service deadlines.

   resume accepts separate JSON correlation metadata and raw versioned V2 proof:
     {"abiVersion":1,"requestId":<exact uint64>,"operation":"native.prove.v1",
      "capability":"host.prover","profile":"<selected profile NAME>"}
   Wrong/stale/crossed replies reject and retain pending state. Successful resume
   verifies the frozen statement/proof with the retained VK/SRS, attaches native
   ledger V3, rechecks binding and roundtrips serialization inside Rust. Exactly
   one response completes a session. Result JSON contains publicIntentHex and
   publicIntentSha256, with intentEncoding=public-pedersen-commitment, funded=false
   and submitted=false. This public native intent projection contains the binding
   commitment, never its private randomness. It is not a funded/sealed transaction.
   The bounded completed session retains its typed private unsealed ProvedIntent
   until free for a later phase-B integration. Phase A exposes no private-intent
   serialization or funding/sealing operation.

   Optional local_prove dispatches the private token to the linked Rust LocalProver
   synchronously, once per session, returning a raw V2 response result token. The
   host then calls resume. External service adapters instead read private bytes
   and supply their raw response to resume. No callback, foreign pointer, stack
   frame or asynchronous future survives an ABI call.

   cancel revokes pending payload tokens and rejects subsequent resume. Completion
   rejects later cancellation. Free revokes private tokens. Already copied host
   bytes stay under the host's clearing policy. Owned private payload buffers are
   zeroized on revocation/free. No blanket native-allocation wiping is promised.
   Calls running outside the registry lock retain owned Rust data until return.
   Cancellation discards their late completion but does not hard-stop CPU work.
   Hard stop/deadline enforcement requires a host worker policy. In-flight work
   still occupies its resource slot after cancel/free, until its call returns.

   Limits: 8 sessions, 2 live prepare/prove/verification calls, 64 ordinary result
   tokens, 16 private tokens, 1MiB private config/request/proof/result, 64KiB public
   descriptor/reply metadata, 16MiB declared bundle payload, 128MiB SRS. The
   bundle cap is this ABI host/resource policy, not a compiler capability ceiling
   or a change to other bundle consumers. Real claim
   qualification measured 456374 request / 3852 response / 4433 attached bytes.
   Reaching a bound rejects without an output token. Free tokens after use.

   Inputs must reference the declared readable bytes until return. Output pointers
   and copy buffers must be writable, correctly aligned and non-overlapping.
   Nulls, lengths and token classes are checked. Arbitrary invalid pointers or
   concurrent modification of borrowed foreign memory violate the caller contract.
   Caller-owned copies remain valid after token free. No Rust allocation is freed
   through a foreign allocator. */
enum { NIGHTLEAN_NATIVE_OK=0, NIGHTLEAN_NATIVE_INVALID_ARGUMENT=1,
  NIGHTLEAN_NATIVE_INVALID_HANDLE=2, NIGHTLEAN_NATIVE_INVALID_STATE=3,
  NIGHTLEAN_NATIVE_INVALID_RESPONSE=4, NIGHTLEAN_NATIVE_LIMIT=5,
  NIGHTLEAN_NATIVE_INTERNAL=6, NIGHTLEAN_NATIVE_BUFFER_TOO_SMALL=7 };
int32_t nightlean_native_begin(const uint8_t*,size_t,const uint8_t*,size_t,
  const uint8_t*,size_t,const uint8_t*,size_t,uint64_t*);
int32_t nightlean_native_advance(uint64_t,uint64_t*);
int32_t nightlean_native_private_request(uint64_t,uint64_t*);
int32_t nightlean_native_resume(uint64_t,const uint8_t*,size_t,const uint8_t*,size_t,uint64_t*);
int32_t nightlean_native_local_prove(uint64_t,const uint8_t*,size_t,uint64_t*);
int32_t nightlean_native_cancel(uint64_t);
int32_t nightlean_native_free(uint64_t);
int32_t nightlean_native_result_length(uint64_t,size_t*);
int32_t nightlean_native_result_copy(uint64_t,uint8_t*,size_t,size_t*);
int32_t nightlean_native_result_free(uint64_t);
int32_t nightlean_native_private_length(uint64_t,size_t*);
int32_t nightlean_native_private_copy(uint64_t,uint8_t*,size_t,size_t*);
int32_t nightlean_native_private_free(uint64_t);
#ifdef __cplusplus
}
#endif
#endif
