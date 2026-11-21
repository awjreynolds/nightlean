import Noctium.IR

namespace Noctium

/-- Lean's scoped representation of Compact's `shieldedBurnAddress()` result.

Compact returns the left `Either` arm, which is the default
`ZswapCoinPublicKey`. The nominal marker keeps the recipient in Noctium's
existing wallet-key family, and the default key is the zero Bytes32 value.
This helper covers the canonical wallet burn address only. -/
inductive ShieldedBurnAddress where
  | wallet
  deriving Repr, BEq, DecidableEq

namespace ShieldedBurnAddress

/-- Compact's wallet arm is the left side of the returned Either. -/
def walletBranch (_ : ShieldedBurnAddress) : _root_.Bool := _root_.Bool.true

/-- The default `ZswapCoinPublicKey` payload is a zero Bytes32 value. -/
def recipient (_ : ShieldedBurnAddress) : Expr (.bytes 32) :=
  .bytes32Literal (List.replicate 32 0)

end ShieldedBurnAddress

/-- Canonical wallet recipient used by Compact's shielded burn helper. -/
def shieldedBurnAddress : ShieldedBurnAddress := .wallet

end Noctium
