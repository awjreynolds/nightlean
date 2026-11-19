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

noctium_witness_circuit readPayment using paymentWire where
  private frame : Bytes 10
  output payment := disclose(decode(paymentWire, frame))
end

noctium_witness_circuit authorize using paymentWire where
  private frame : Bytes 10
  let payment := decode(paymentWire, frame)
  prove elementAt(field(payment, info), 1)
  prove elementAt(field(payment, flags), 1)
  prove eq(enumTag(field(payment, side)), 0)
  output code : UInt 8 := disclose(elementAt(field(payment, memo), 1))
end

private def optionsWire : Helpers.Wire.Codec := {
  payload := .vector 3 (.tuple [.scalar .bool, .bytes 1])
  frameBytes := 6
}

noctium_witness_circuit choose using optionsWire where
  public frame : Bytes 6
  private position : UInt 8
  let option := elementAt(decode(optionsWire, frame), disclose(position))
  prove elementAt(option, 0)
  output code : UInt 8 := disclose(elementAt(elementAt(option, 1), 0))
end

noctium_contract Codec where
  entry transcode uses transcode where
    return encoding : Bytes 10 := encoded
  end
  entry readPayment uses readPayment where
    return payment
  end
  entry authorize uses authorize where
    return approval : UInt 8 := code
  end
  entry choose uses choose where
    return choice : UInt 8 := code
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
