import Noctium.Frontend

open scoped Noctium

namespace TypedWitnessResultCodec

def providerWire : Noctium.Helpers.Wire.Codec := {
  payload := .structure "ProviderPayload"
  frameBytes := 32
  composites := {
    structures := [{id := "ProviderPayload", fields := [
      {name := "leaf", type := .bytes 32}
    ]}]
  }
}

-- Same nominal structure, different frame ABI. The result declaration binds
-- to providerWire, so a caller cannot reinterpret its frame with this codec.
def conflictingWire : Noctium.Helpers.Wire.Codec := {
  payload := .structure "ProviderPayload"
  frameBytes := 33
  composites := {
    structures := [{id := "ProviderPayload", fields := [
      {name := "leaf", type := .bytes 32}
    ]}]
  }
}

noctium_witness providerResult() : Payload providerWire

noctium_witness_circuit typedProviderResult using providerWire where
  let result := witness providerResult()
  output leaf := disclose(field(result, leaf))
end

/-- error: witness result 'TypedWitnessResultCodec.providerResult' requires codec 'TypedWitnessResultCodec.providerWire' in this circuit's using clause -/
#guard_msgs in
noctium_witness_circuit missingProviderCodec using conflictingWire where
  output payload := disclose(witness providerResult())
end

/-- error: witness result 'TypedWitnessResultCodec.providerResult' has conflicting codecs 'TypedWitnessResultCodec.providerWire' and 'TypedWitnessResultCodec.conflictingWire' in this circuit's using clause -/
#guard_msgs in
noctium_witness_circuit ambiguousProviderCodec using conflictingWire, providerWire where
  output payload := disclose(witness providerResult())
end

end TypedWitnessResultCodec
