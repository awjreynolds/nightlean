# Typed source witnesses

The exact source revision and qualification scope are recorded in [typed-witness qualification](typed-witness-qualification.md), including bounded native evidence for profiles 3.2.0 and 3.2.1.

Noctium compiles finite Lean helper programs into a native circuit and an ordered private execution plan. Rust executes the plan. A C++ application drives the same interpreter through the C ABI. Neither path requires Node.

Witness providers supply untrusted values through explicit operation and capability declarations. A returned value grants no circuit truth, disclosure permission or ledger authority. Circuit constraints still check the resulting private inputs.

For straight-line scalar contracts, start with [the private state counter](../../examples/PrivateStateCounter.lean).
`noctium_private_state` declares wallet-owned typed cells. `noctium_witness` declares
an untrusted callback. A `noctium_witness_circuit ... where` body reads private
cells, states acceptance conditions with `prove`, and stages updates through the
same Rust execution plan described below. `prove` creates circuit constraints,
not Lean theorems. A private read or calculation needs no `disclose`. A public
result derived from either needs explicit release.

This source form supports Native, Bool and bounded UInt values, with Unit callback
results. Its `.observations.json` records authored proof conditions separately
from generated validity checks. The summary is source review material and is
not yet a verified bundle artifact. Composite and curve callback schemas and
structured source branches remain separate work.
Private reads within one plan currently share one scalar result type because
the host protocol declares one result schema per read operation. Mixed-type
private reads require a protocol extension, tracked with [the remaining type work](https://github.com/awjreynolds/noctium/issues/69).

Declarations describe access requests. The host still grants storage permissions.
Generated keys use `noctium/<qualified-schema>/<field>`. Grant a schema with
the slash-terminated prefix `noctium/<qualified-schema>/`, or selected exact keys.
The commit capability must cover every staged key. The example uses public writes
only. Combining source witnesses with ledger reads still needs the
[current-state witness integration](https://github.com/awjreynolds/noctium/issues/67).

[`tests/WitnessSource.lean`](../../tests/WitnessSource.lean) contains the source examples. They cover scalar calls, nominal composite arguments and results, repeated helpers, Unit and empty nominal results, private reads, staged writes and rejected disclosure. The scalar example stages `cache/last = 1`, reads the staged value, calls a helper twice, checks the replies against a public value and stages the final result.

[`tests/WitnessDisclosure.lean`](../../tests/WitnessDisclosure.lean) checks direct and helper-mediated leaks. Disclosing constants inside a branch does not disclose its private witness guard. The host plan requires explicit disclosure of the guard itself.

## Compile source

Declare `Helpers.WitnessSignature` values on `Helpers.Program.witnesses`. Each signature names its versioned operation, capability, typed parameters and result. Call a signature with `Term.witnessCall site name arguments`. Site names remain unique within each helper declaration.

Register a circuit with:

```lean
noctium_witness_circuit scalarRelation from scalarProgram entry "scalar"
```

The registered circuit also works inside the existing `noctium_contract` declaration. The source program stays available to the compiler for fresh type and disclosure checks.

```sh
lake exe noctium compile tests/WitnessSource.lean --output /tmp/noctium-witnesses
```

The selected ledger entrypoint emits:

| File | Purpose |
| --- | --- |
| `TypedWitness.ScalarWitness.claim.zkir` | Actual native CALL relation, including Impact operations and `Output []`. |
| `TypedWitness.ScalarWitness.claim.impact.json` | Ordered ledger plan and source circuit schema. |
| `TypedWitness.ScalarWitness.claim.witness.json` | Public signatures, schemas, source identity and exact private-input bindings. |
| `TypedWitness.ScalarWitness.claim.witness.control.json` | Typed private execution plan bound to the CALL relation. |

Standalone circuit bindings use a separate target identity. Their public-return convention does not replace the ledger CALL relation. Host-only plans use `mode: "host"` and have no native binding. Native guarded control remains gated by its own backend work.

The companion binding file has one trailing LF. Its embedded copy in the control plan preserves those exact bytes. Hash the retained raw file, rather than a parsed or reformatted JSON object.

## Public artifacts and private values

Public bindings record original input names and schemas, declaration paths, call sites, invocation ordinals and fresh circuit leaf names. Two executions of the same helper receive separate bindings. Unit and empty nominal results still receive invocation records.

The binding contains the actual emitted relation tree. Runtime checks require a complete correspondence between original inputs, witness result leaves and declared circuit inputs. Aggregate leaves use native field encodings. A flattened Boolean leaf becomes decimal `"0"` or `"1"`; a scalar `Bool` input keeps its Boolean JSON encoding.

Selected-entrypoint bundles retain optional `witnessBinding` and `witnessControl` roles together. The verifier rejects a missing member, unreferenced role, different entrypoint, changed relation, changed schema or incomplete input map. Existing bundles without witness roles keep their canonical format. An externally trusted manifest digest authenticates retained bytes. A self-hash alone supplies no source authority.

Invocation inputs, evaluated provider arguments, provider results and staged private writes travel through private channels. They do not enter the public artifact files. Host status and scheduling remain visible to the invocation controller. They are excluded from a contract-public privacy claim.

## Private state

A typed private read declares `operation := "private_state.read.v1"`, an explicit source `privateKey` and no dynamic arguments. Runtime checks the declared key, namespace, capability and key prefix. The request metadata excludes the private key value. The private argument channel carries the key and current invocation overlay.

Runtime already owns staged writes. A reply for an owned staged key must match its exact schema and newest canonical value. A wrong reply leaves the pending request and staged journal available for a valid retry. Reads of committed host storage still depend on the host storage service.

Source `Statement.stage` currently stages scalar values. Its writes remain tentative. The circuit translation retains evaluation of each stage value without treating the private write as a proved ledger transition. Staging and compare-and-exchange operations are reserved for the controlled journal lifecycle. They cannot be declared as ordinary typed witness providers. The host typed journal also supports nominal composite values; whole-composite source staging needs a separate source-language extension.

A source-bound execution accepts journal writes only from its compiled stage statements. The public manual-stage API remains available for legacy host-policy execution. It does not add writes to a source-qualified invocation.

## Owned native handoff

Prepare the native target before running source callbacks. The target context authenticates the bundle and proving parameters, retains the initial native contract state and creates the deployment nonce once. Its address and entrypoint stay fixed throughout private execution.

Rust applications use the opaque owners in [`witness_execution`](../../runtime/src/witness_execution.rs). Prepare a real `proof::WitnessTarget`, then pass it to `WitnessExecution::from_target`. The host has the frozen address before choosing its private-state namespace. `WitnessExecution::begin` combines those steps when a namespace is already available.

Drive `advance`, `private_request` and `resume_typed` until source execution completes. `prepare_proof` preserves the invocation on a rejected preparation, then transfers ownership to `WitnessProof`. After verified proving, `WitnessProvedCall` starts the separate deployment client and the source-bound CALL client through the existing driver. These types expose no mutable Runtime or replacement private-input map. The pinned proving-parameter digest also follows the invocation through proof preparation and verification.

[`runtime/tests/witness_execution_public.rs`](../../runtime/tests/witness_execution_public.rs) compiles against public crate APIs alone. Its integration test requires authenticated retained artifacts and public proving parameters, supplied through the environment. It covers source callbacks, corrected retries, invocation mismatch, changed SRS, local proving and the consuming client handoff.

The additive C entrypoints live in [`nightlean_native.h`](../../runtime/include/nightlean_native.h) and [`nightlean_control.h`](../../runtime/include/nightlean_control.h):

1. `nightlean_native_witness_target_begin` creates the bounded target context from authenticated artifacts, state-only configuration and explicit entropy.
2. `nightlean_control_begin_from_native_target` loads the retained plan and freezes the context identity, address and entrypoint before any provider call or stage.
3. Advance the Control session and answer typed requests. Replies carry protocol version, process-unique decimal request ID, attempt ID, operation, capability and schema. Invalid replies retain suspension. Explicit provider failure aborts the invocation.
4. `nightlean_native_begin_from_witness` obtains the complete canonical input map from the completed Control session. It accepts no caller-supplied replacement input map or arbitrary journal. Artifact, context, target and input checks precede consumption.
5. Verify and attach the proof through the existing native proof API. The completed proof session retains the actual source Runtime.
6. Deploy through the existing kind-0 client path using a separate deployment namespace. Deployment leaves source CALL writes untouched. `nightlean_client_start_from_witness` consumes the source Runtime for the proved CALL and follows the existing funding, approval, submission, finality and private CAS lifecycle.

A rejected handoff preserves a completed invocation for corrected retry. After successful consumption, cancellation belongs to the native proof or client owner. It discards that owned invocation. It does not restore the old Control session or interrupt arbitrary native CPU work.

Chain acceptance and private CAS are separate outcomes. A finalized call does not disappear when private storage reports a revision conflict. Recovery retains typed schemas and the exact source journal through the existing trusted-store protocol.

The qualified single-operation context covers deployment and its first call. [Existing-state calls and multi-entrypoint assembly](https://github.com/awjreynolds/noctium/issues/67) have a separate integration gate. Source execution does not require a fresh-deployment assumption inside the interpreter or provider protocol.

The Rust contract-set POC also supports corrected pre-proof retries at an
authenticated current-state checkpoint. `WitnessExecution::begin_contract_operation`
borrows a target and `&mut Option<CurrentStateContext>` and only takes the token
after source-session construction succeeds. `cancel_contract_operation` clears
the tentative session and returns that token. Successful preparation consumes
ownership. This path has one focused lifecycle test, with full multi-operation
ledger integration and process recovery still in issue 67.

## Assurance scope

The source model in [`Nightlean/Witness/Semantics.lean`](../../Nightlean/Witness/Semantics.lean) separates private source stages from the erased constraint computation. Its execution gate records a witness tape and replays frozen results rather than rerunning providers after erasing writes. Formal claims must identify their checked theorem, admitted source fragment and host assumptions.

`recordInvocation_replayInvocation_matches` connects the actual recording and replay entrypoints. For source runs admitted by the host-boundary trace, and successful compiler/input/tape validation, replay returns the same result or terminal error, ordered tape and cursor. Replay preserves its initial private store and leaves its journal empty. `validateCompleteInputMap_preserves_bindings` separately ties accepted canonical values to the exact original and fresh input names in circuit schema order. These facts do not prove general Helpers-to-circuit preservation.

The failure theorem uses a one-shot model of accepted execution. Its source-only diagnostic trace must stay empty. This excludes a rejected stage-value cast, a denied private write grant, a staged-read reply that contradicts the owned write, and a malformed typed callback. An accepted terminal provider failure stays in the recorded tape and replays with the same error and cursor. The native protocol separately retains a pending request after a malformed or mismatched reply, so a corrected reply retries that request. The theorem does not model those rejected callback attempts as accepted tape events. Diagnostic traces do not enter callback requests, public observations, artifacts or the native ABI.

Native checker, prover, C++ and ledger tests complement those source facts. They do not establish general Helpers lowering correctness, a verified Rust implementation or circuit-proved private storage. Full compiler assurance, native guarded execution and web/mobile packaging remain separate delivery goals.

[`runtime/tests/witness_checker.rs`](../../runtime/tests/witness_checker.rs) changes private witness leaves after host preparation, then invokes the upstream checker on the emitted CALL relation. The tests cover dishonest scalar replies, nominal result fields and noncanonical Boolean and bounded integer encodings. This separates native constraint rejection from provider validation and host assertions.
