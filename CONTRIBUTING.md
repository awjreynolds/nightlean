# Contributing to Noctium

Start with the [public issue map](https://github.com/awjreynolds/noctium/issues/1). GitHub Issues track decisions, research, implementation and dependencies. Open or join an issue before substantial work so the proposed scope and required evidence are clear.

## Development checks

Install [elan](https://github.com/leanprover/elan#installation), Git and Python 3. The repository pins Lean 4.35.0. From the repository root:

```sh
lake build
bash scripts/check-lean.sh
```

The compiler check script builds and checks the Lean modules and tests, checks and compiles the actual private claim, and runs its source-proof mutation regressions. This is the scope of the compiler CI job. Native Rust, prover and localnet qualification use separate workflows described in the [documentation index](docs/README.md).

For Rust changes, install Rust 1.100.0 and a native C build toolchain, then run the runtime tests with the pinned dependencies:

```sh
cargo +1.100.0 test --manifest-path runtime/Cargo.toml --locked
```

The [native client guide](docs/development/native-client.md#retained-qualification) adds the optional `localnet` feature, exclusive 3.2.1 profile and real-chain prerequisites. Do not interpret an ordinary test pass as a new proof or ledger qualification.

## What a useful change includes

- A bounded problem and an explanation of the resulting behavior.
- Tests at the affected boundary, including invalid inputs and failure behavior where relevant.
- For language or lowering changes, updated semantics, disclosure rules and preservation evidence, or an explicit unsupported gate.
- For proof changes, the exact statement, subject, assumptions and observer scope. Include a negative case which rejects the relevant source or artifact mutation.
- For native claims, the exact source revision, profile, toolchain and retained public evidence. Keep private witnesses, wallet seeds and private journals out of commits.

Keep source semantics, formal models and native implementation evidence distinguishable. A passing fixture does not establish generic compiler correctness. A functional theorem does not establish privacy.

Use the [glossary](GLOSSARY.md) and [architecture overview](docs/designs/architecture.md) for shared terminology. Report security issues through the [private reporting route](SECURITY.md).
