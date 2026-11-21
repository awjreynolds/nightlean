# Shielded role authorization

The [Lean port](../../examples/openzeppelin/ShieldedRoleGate.lean) implements one protected action from OpenZeppelin's pinned ShieldedAccessControl. It derives an account ID and role commitment, binds a depth-20 Merkle path to the commitment, checks the ledger root and revocation set, then increments `protectedActions`. The caller supplies a typed path through the native witness session. [Pinned OpenZeppelin source](https://github.com/OpenZeppelin/compact-contracts/blob/f85f1a23685c6bbedfc8c2589ae3aa128aff7c46/contracts/src/access/ShieldedAccessControl.compact)

The private inputs are the secret and the path. Lean requires an explicit disclosure for the path direction when used to select the order of the hash inputs. The ledger receives the candidate root and nullifier for its checks. The entrypoint returns no value. Compact's source applies `disclose(path)` to the aggregate. The scoped comparison checks accepted state and rejected inputs in each runtime.

The Compact 0.36.1 comparator and Noctium's native witness and relation checker both accept the enrolled role at index 1 and advance the counter from zero to one. They reject a valid path for another leaf, a changed sibling that computes a different root, and a revoked role. These checks use in-memory ledger state and cover the authorization action. Grant administration, key generation, funded execution and a proof of non-disclosure remain open.

The compiler keeps mirrored conditional hashes compact in the symbolic checker and preserves the original instruction, input and depth budgets. The checker requires the same condition and exactly swapped arms. It also recognizes reconstruction from the low and high chunks of the same Bytes32 value. These changes preserve value comparisons and leave the original bounds in force.

With the same selected artifacts and range deduplication, sharing 124 bindings reduces this Impact plan from 4,715,622 to 142,072 bytes. It fits the bundler's 2 MiB JSON limit. Expanding the shared bindings reproduces the original plan, and the ZKIR and witness files match byte for byte. The native authorization cases still pass. [Impact artifact sharing](https://github.com/awjreynolds/noctium/issues/203)

Run the Compact oracle with the pinned compiler and runtime. Compile the Lean fixture for the 3.2.1 target, then point the focused native test at those artifacts.

```sh
node tests/compact/shielded-role-gate.mjs "$compactc" "$compact_runtime"
lake exe noctium compile examples/openzeppelin/ShieldedRoleGate.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --dedup-range-checks --emit ledger --emit witness --output build/experiments/role-gate
NOCTIUM_SHIELDED_ROLE_GATE_DIR="$PWD/build/experiments/role-gate" \
  cargo test --manifest-path runtime/Cargo.toml --locked --no-default-features \
  --features zkir-321 --test shielded_role_gate -- --ignored
```
