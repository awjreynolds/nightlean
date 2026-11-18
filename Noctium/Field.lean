import Lean

namespace Noctium.Field

/-- BLS12-381 scalar modulus used by the ledger 9 ZKIR Native field. -/
def modulus : Nat :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513

/-- Canonical external field encoding: exactly 32 little-endian bytes. -/
def encode (n : Nat) : Except String ByteArray := do
  if n >= modulus then throw "noncanonical Native field value"
  let mut bytes := ByteArray.empty
  let mut value := n
  for _ in [0:32] do
    bytes := bytes.push (value % 256).toUInt8
    value := value / 256
  return bytes

def decode (bytes : ByteArray) : Except String Nat := do
  if bytes.size != 32 then throw "Native field encoding must contain exactly 32 bytes"
  let mut value := 0
  for byte in bytes.data.reverse do
    value := value * 256 + byte.toNat
  if value >= modulus then throw "noncanonical Native field encoding"
  return value

end Noctium.Field
