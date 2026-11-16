# 08: Run the first Lean-to-ZKIR vertical slice

Type: task

## Task

After the first contract workloads are selected, run one bounded vertical slice using a temporary Lean-owned circuit representation. Keep Nightlean's compiler code and primary lowering in Lean 4.

- Express the selected relation in Lean and lower it to the current ledger 9 ZKIR format.
- Validate the emitted IR with the exact pinned Midnight toolchain, generate keys, produce a proof, and verify it cryptographically.
- Determine which additional artifacts a deployable contract bundle needs. Exercise a Lean-generated Compact adapter only if it preserves Nightlean semantics.
- Deploy and call the generated contract on Preview after local output validation. Do not use Mainnet.
- Record tested commits, versions, commands, outputs, and the first failing stage if the path stops.

This spike qualifies one selected workload. It does not establish support for other circuit features.

## Blocked by

05: Choose the first contract workloads.
