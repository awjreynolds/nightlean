import Noctium.Frontend

open scoped Noctium
open Noctium

namespace AggregateSerialization

private def paymentWire : Helpers.Wire.Codec := {
  payload := .structure "Payment"
  frameBytes := 10
  composites := {
    structures := [{id := "Payment", fields := [
      {name := "info", type := .tuple [.scalar (.uint 300), .scalar .bool]},
      {name := "flags", type := .vector 2 (.scalar .bool)},
      {name := "side", type := .enumeration "Side"},
      {name := "memo", type := .bytes 2}]}]
    enumerations := [{id := "Side", variants := [{name := "Pay"}, {name := "Cancel"}]}]
  }
}

noctium_witness_circuit transcode using paymentWire where
  private frame : Bytes 10
  output encoded : Bytes 10 :=
    let payment := decode(paymentWire, frame) in
    disclose(encode(paymentWire, payment))
end

noctium_contract Codec where
  entry transcode uses transcode where
    return encoding : Bytes 10 := encoded
  end
end

noctium_witness_circuit hosted where
  private frame : Bytes 34
  output encoded : Bytes 34 := disclose(serialize(deserialize(Native, frame), 34))
end

noctium_contract HostedCodec where
  entry decode uses hosted where
    return encoding : Bytes 34 := encoded
  end
end

end AggregateSerialization
