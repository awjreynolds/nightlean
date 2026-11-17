import Nightlean.Frontend
open Nightlean Nightlean.Helpers

def privateStatePayloadType : Types.CompositeType := Types.CompositeType.structure "Demo.Payload"
def privateStatePayloadParameter : Parameter := {name := "payload", ty := Ty.native}
def privateStateLeakExport : Export := {
  name := "leak", target := ⟨0, 0⟩,
  compositeInputs := [{name := "payload", type := privateStatePayloadType, visibility := Visibility.public}]
}
def privateStateEntry : Declaration := {
  id := ⟨0, 0⟩, name := "entry",
  parameters := [privateStatePayloadParameter],
  compositeParameters := [("payload", privateStatePayloadType)],
  result := .composite privateStatePayloadType,
  body := [.return (some (.effect .privateState "account.balance" (.ref "payload")))]
}
def privateStateProgram : Program := {
  composites := {structures := [{id := "Demo.Payload", fields := [
    ⟨"balance", .scalar .native, {}⟩,
    ⟨"nonce", .scalar .native, {}⟩]}]},
  declarations := [privateStateEntry],
  exports := [privateStateLeakExport]
}

open scoped Nightlean
nightlean_component_circuit privateStateLeak from privateStateProgram entry "leak"
