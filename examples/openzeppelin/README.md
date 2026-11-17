# OpenZeppelin port components

`PublicSupply.lean` rebuilds the pinned public-supply extension's 128-bit
increase/decrease accounting blocks. A narrowing cast rejects overflow and
unsigned subtraction rejects underflow. Writes explicitly disclose the updated
supply, so supply deltas reveal mint/burn amounts as in the reference.

These blocks are an ungated benchmark component. The completed token must pair
them atomically with encrypted mint/burn effects. This component does not yet
include encrypted balances, account authentication, a supply getter or the
complete token deployment.

The source includes small reference-evaluator checks. The focused
`runtime/tests/openzeppelin_supply.rs` test consumes the source-generated 3.2.1
artifacts, checks supply `0 → 5 → 3` against the native circuit, and rejects
overflow and underflow. It performs no key generation or deployment.

Reference: OpenZeppelin/compact-contracts at
`f85f1a23685c6bbedfc8c2589ae3aa128aff7c46`,
`contracts/src/token/extensions/ConfidentialFungibleTokenPublicSupply.compact`.
Adapted code retains the upstream MIT license in `LICENSE`.

See the [port requirements](../../docs/development/openzeppelin-port.md)
and [implementation ticket](https://github.com/awjreynolds/noctium/issues/68).
