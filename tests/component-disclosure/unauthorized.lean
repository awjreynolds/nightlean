import Nightlean.Frontend
open Nightlean Nightlean.Helpers

def privatePayloadType : Types.CompositeType := Types.CompositeType.structure "Demo.Payload"
def privatePayloadParameter : Parameter := {name := "payload", ty := Ty.native}
def privateLeakExport : Export := {
  name := "leak", target := ⟨0, 0⟩,
  compositeInputs := [{name := "payload", type := privatePayloadType, visibility := Visibility.private}]
}
def privateEntryDeclaration : Declaration := {
  id := ⟨0, 0⟩, name := "entry",
  parameters := [privatePayloadParameter],
  compositeParameters := [("payload", privatePayloadType)],
  result := .composite privatePayloadType,
  body := [.return (some (.ref "payload"))]
}

def privateAggregateProgram : Program := {
  composites := {structures := [{id := "Demo.Payload", fields := [
    ⟨"balance", .scalar .native, {}⟩,
    ⟨"nonce", .scalar .native, {}⟩]}]},
  declarations := [privateEntryDeclaration],
  exports := [privateLeakExport]
}

open scoped Nightlean
nightlean_component_circuit privateAggregate from privateAggregateProgram entry "leak"
