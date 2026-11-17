# Noctium examples

Use the current authoring examples below. They import `Noctium.Frontend`, open
`Noctium`, and use `noctium_*` declarations.

| Example | What to read |
| --- | --- |
| [Bounded scalars](BoundedScalars.lean) | Private numeric inputs, inferred arithmetic bounds and a public ledger update. |
| [Disclosure](Disclosure.lean) | Explicit release of a private value or decision. |
| [Private claim](NoctiumPrivateClaim.lean) | Private witness inputs and calculations, approved public root/nullifier values, and a public replay-prevention map. |
| [OpenZeppelin public supply](openzeppelin/PublicSupply.lean) | Checked 128-bit accounting. Public supply changes reveal the amount even when the input is marked private. |

A `private` circuit input is a witness value supplied by your application. It is
not a declaration of persisted private state. Contract ledger cells and maps are
public. Private application state and witness callbacks use the runtime's private
state lifecycle, described in the [typed witness guide](../docs/development/typed-witnesses.md).

Ordinary private calculations retain their private origin. `disclose(result)`
authorizes a public release of that result. An accepted proof reveals that its
declared relation holds. `assert` states a circuit constraint, so passing a
private assertion should not be described as revealing no information.

## Historical qualified source

[PrivateClaim.lean](PrivateClaim.lean) retains its original technical spelling and
exact bytes because published proof and deployment records identify this source.
It is a historical qualification fixture. The current teaching copy above uses
Noctium names and explicit derived-value release, and does not inherit those
proof or deployment receipts. See the [actual-source proof guide](../docs/development/private-claim-proofs.md).
