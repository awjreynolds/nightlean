# Component-aware disclosure

The `noctium_component_circuit` command compiles an exported helper entry and checks disclosure for each public output component before the compiler writes circuit artifacts.

```lean
noctium_component_circuit componentRelease
  from componentDisclosureProgram entry "release"
```

Composite types use the checked layouts in `Types.CompositeEnv`. An export declares aggregate inputs with `Export.compositeInputs`. A declaration binds a formal parameter to its nominal composite type with `Declaration.compositeParameters`:

```lean
compositeInputs := [{name := "payload", type := payloadType, visibility := .private}]
compositeParameters := [("payload", payloadType)]
```

Nominal types are checked across helper calls before the compiler flattens aggregates into the scalar leaves used by the existing circuit backend. Structs, tuples, vectors, bytes and enum payloads use layout-derived component paths. Helper calls preserve each input's origin and add the helper path to diagnostics.

`disclose` clears origins from the selected payload only. Index, enum tag and runtime control origins stay separate. Dynamic vector indexing therefore retains the selector origin after disclosure of a selected field. Literal boolean conditions select their live branch at analysis time. Conditions with runtime values retain their control origins.

Private origins come from source visibility, provider witnesses and private-state effects. Provider witnesses lower to private circuit inputs and retain provider provenance. Private-state effects propagate origins through source analysis, but native compilation rejects them because no private-state read implementation exists. The effect form supports analysis of an existing source value, not access to persistent state.

The component checker derives visibility and provenance from the source program, helper bodies and checked composite layouts. It accepts no caller-declared public summaries. A missing origin rule or a nominal type mismatch fails closed. Unit outputs carry no payload leaves and follow the existing successful-unit policy.

## Focused checks

Run the focused source analysis tests and compiler fixtures with:

```sh
lake env lean tests/ComponentDisclosure.lean
bash tests/component-disclosure-cli.sh
```

The CLI fixture checks generated component inputs and outputs. It also confirms that unauthorized aggregate output and private-state effect fixtures fail before an artifact directory appears.

For native relation qualification, compile the authorized source into a persistent directory, generate keys for that exact relation with the retained 3.2.1 CLI, then run the checker fixture:

```sh
lake exe noctium compile tests/component-disclosure/authorized.lean --output "$ARTIFACTS"
MIDNIGHT_PP="$PARAMS" "$ZKIR" compile \
  "$ARTIFACTS/componentRelease.zkir" \
  "$ARTIFACTS/componentRelease.prover" \
  "$ARTIFACTS/componentRelease.verifier"
node tests/component-disclosure/qualify.mjs "$ARTIFACTS" \
  "$CHECKER" "$ARTIFACTS/componentRelease.prover" \
  "$ARTIFACTS/componentRelease.verifier" check
```

Use `prove` as the final argument to send the same relation and fresh keys to the configured loopback proof service. The qualification fixture checks valid inputs, rejects altered output leaves and provider witnesses, and records the relation hash.

## Retained qualification

[The qualification receipt](../../tests/component-disclosure-evidence.json) records the reviewed source hashes, an isolated build from public baseline `7198416`, the complete source/CLI checks and independent native checker results. The isolated build excludes the in-progress generic scalar compiler-proof changes. Both independently generated K4 keys match the native proving fixture.

The emitted JSON has SHA-256 `a7fd816122ba57b6036a48d0e65fd5000812e57e08aa802164fb58b7315e6ac8`. The native serialized relation has SHA-256 `7afcf57a6a3481448e663e9c6afd507b94e78d5501f8d2a8b11faadabba07010`. The retained native proof has 3,468 bytes and was self-verified by the native proof service. Correct inputs pass. Changed public result leaves and provider witnesses reject. This qualifies the selected circuit fixture, with no ledger acceptance or formal aggregate privacy claim.

Independent review also reproduced scalar widening into Native formals, explicit overloaded export selection and declared-type overload resolution. Private origins survive those conversions. Distinct nominal composites reject.

Unknown branches track reachable returns separately from paths which continue. The continuation restores the outer environment and retains conditional control dependencies. Regression cases cover private returns after a branch, mixed and nested early returns, and branch-local binding restoration. A well-typed private continuation reproduction now rejects during disclosure analysis, independently of the still-disabled native guard backend.
