# Noctium examples

Use the current authoring examples below. They import `Noctium.Frontend`, open
`Noctium`, and use `noctium_*` declarations.

| Example | What to read |
| --- | --- |
| [Bounded scalars](BoundedScalars.lean) | Private numeric inputs, inferred arithmetic bounds and a public ledger update. |
| [Disclosure](Disclosure.lean) | Explicit release of a private value or decision. |
| [Private claim](NoctiumPrivateClaim.lean) | Private witness inputs and calculations, approved public root/nullifier values, and a public replay-prevention map. |
| [Private state counter](PrivateStateCounter.lean) | A wallet-owned private cell, a typed untrusted callback, explicit proof conditions, a checked public ledger read and a staged private update. |
| [OpenZeppelin public supply](openzeppelin/PublicSupply.lean) | Checked 128-bit accounting. Public supply changes reveal the amount even when the input is marked private. |

A `private` circuit input is a witness value supplied by your application. It is
not a declaration of persisted private state. Contract ledger cells and maps are
public. Private application state and witness callbacks use the runtime's private
state lifecycle, described in the [typed witness guide](../docs/development/typed-witnesses.md).

Ordinary private calculations retain their private origin. `disclose(result)`
authorizes a public release of that result. An accepted proof reveals that its
declared relation holds. `assert` states a circuit constraint, so passing a
private assertion should not be described as revealing no information. The
readable witness source form uses `prove` for these acceptance conditions.

In the private state counter, `read private Wallet.saved as previous` accesses
wallet state. `stage Wallet.saved := next` records a pending update. Neither
operation publishes the value. An output derived from `next` requires
`disclose(next)`. The example instead returns an already-public expected value
and proves its relationship to the callback result. Acceptance reveals that
relationship. Here, `next = previous + 1` and `next = expected` reveal both
counter values from the public expected value. The example demonstrates private
storage and staged execution, with no counter-confidentiality claim. A private
cache does not authenticate a ledger balance or secret.

Compilation emits a source `.observations.json` alongside the circuit and witness
plan. It lists input visibility, private reads and stages, callback names,
authored proof conditions and explicit releases. It is a source review aid,
not a non-disclosure theorem or a verified bundle artifact. Contract ledger
activity, generated range checks, failures and timing require separate review.

## Historical qualified source

[PrivateClaim.lean](PrivateClaim.lean) retains its original technical spelling and
exact bytes because published proof and deployment records identify this source.
It is a historical qualification fixture. The current teaching copy above uses
Noctium names and explicit derived-value release, and does not inherit those
proof or deployment receipts. See the [actual-source proof guide](../docs/development/private-claim-proofs.md).
