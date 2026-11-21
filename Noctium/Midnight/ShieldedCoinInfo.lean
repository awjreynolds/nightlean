import Noctium.Helpers.Wire

namespace Noctium.Midnight.ShieldedCoinInfo

open Noctium

/-- The canonical nominal identity for the unqualified Compact coin record. -/
def id : Types.DeclId := "Noctium.Midnight.ShieldedCoinInfo"

/-- The wire record follows Compact's `nonce`, `color`, `value` declaration
order. Qualification such as `mtIndex` belongs to the state container. -/
def fields : List (String × Ty) := [
  ("nonce", .bytes 32),
  ("color", .bytes 32),
  ("value", .uint (2 ^ 128 - 1))]

def type : Types.CompositeType := .structure id

def environment : Types.CompositeEnv := {
  structures := [{
    id
    fields := fields.map fun (name, fieldTy) => {
      name
      type := match fieldTy with
        | .bytes length => .bytes length
        | _ => .scalar fieldTy
    }
  }]
}

/-- Compact wire bytes concatenate two 32-byte fields and a 16-byte UInt128. -/
def frameBytes : Nat := 32 + 32 + 16

/-- Checked encoder/decoder shape for unqualified ShieldedCoinInfo values. -/
def codec : Helpers.Wire.Codec := {
  payload := type
  frameBytes
  composites := environment
}

/-- Canonical payload for the absent branch of `Maybe<ShieldedCoinInfo>`. -/
def zeroValue : Types.AggregateValue := .structure id [
  ("nonce", .bytes (List.replicate 32 0)),
  ("color", .bytes (List.replicate 32 0)),
  ("value", .scalar (.uint (2 ^ 128 - 1)) 0)]

end Noctium.Midnight.ShieldedCoinInfo
