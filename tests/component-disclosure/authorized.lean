import Nightlean.Frontend
open Nightlean Nightlean.Helpers

def componentPayloadType : Types.CompositeType := Types.CompositeType.structure "Demo.Payload"
def componentPayloadParameter : Parameter := {name := "payload", ty := Ty.native}
def componentReleaseExport : Export := {
  name := "release", target := ⟨0, 1⟩,
  compositeInputs := [{name := "payload", type := componentPayloadType, visibility := Visibility.private}]
}

def componentDisclosureProgram : Program := {
  composites := {structures := [{id := "Demo.Payload", fields := [
    ⟨"balance", .scalar .native, {}⟩,
    ⟨"nonce", .scalar .native, {}⟩]}]},
  declarations := [
    {id := ⟨0, 0⟩, name := "releasePayload",
      parameters := [componentPayloadParameter],
      compositeParameters := [("payload", componentPayloadType)],
      result := .composite componentPayloadType,
      body := [.return (some (.composite componentPayloadType [
        .disclose {} (.project (.ref "payload") (.field "balance")),
        .disclose {} (.witness "attestation" .native)]))]},
    {id := ⟨0, 1⟩, name := "entry",
      parameters := [componentPayloadParameter],
      compositeParameters := [("payload", componentPayloadType)],
      result := .composite componentPayloadType,
      body := [.return (some (.call "releasePayload" [.ref "payload"]))]}
  ],
  exports := [componentReleaseExport]
}

open scoped Nightlean
nightlean_component_circuit componentRelease from componentDisclosureProgram entry "release"
