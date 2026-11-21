import Noctium.Midnight.ShieldedCoinInfo

namespace Noctium.Midnight.ShieldedSendResult

open Noctium

/-- Compact orders the send result's `change` field before `sent`. -/
def id : Types.DeclId := "Noctium.Midnight.ShieldedSendResult"

def changeId : Types.DeclId := "Noctium.Midnight.MaybeShieldedCoinInfo"

def changeType : Types.CompositeType := .structure changeId

def changeFields : List Types.Field := [
  {name := "is_some", type := .scalar .bool},
  {name := "value", type := Noctium.Midnight.ShieldedCoinInfo.type}]

def changeEnvironment : Types.CompositeEnv := {
  structures := Noctium.Midnight.ShieldedCoinInfo.environment.structures ++ [{
    id := changeId
    fields := changeFields
  }]
}

def type : Types.CompositeType := .structure id

def fields : List Types.Field := [
  {name := "change", type := changeType},
  {name := "sent", type := Noctium.Midnight.ShieldedCoinInfo.type}]

def environment : Types.CompositeEnv := {
  structures := changeEnvironment.structures ++ [{id, fields}]
}

/-- The Noctium frame holds the change tag, change coin, and sent coin. -/
def frameBytes : Nat := 1 + Noctium.Midnight.ShieldedCoinInfo.frameBytes +
  Noctium.Midnight.ShieldedCoinInfo.frameBytes

def codec : Helpers.Wire.Codec := {
  payload := type
  frameBytes
  composites := environment
}

/-- Build a canonical optional coin. An absent value always carries a zero coin. -/
def changeValue (present : Bool) (payload : Types.AggregateValue) : Types.AggregateValue :=
  .structure changeId [
    ("is_some", .scalar .bool (if present then 1 else 0)),
    ("value", if present then payload else Noctium.Midnight.ShieldedCoinInfo.zeroValue)]

end Noctium.Midnight.ShieldedSendResult
