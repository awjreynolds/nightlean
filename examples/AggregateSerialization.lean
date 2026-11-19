import Noctium.Frontend
import Noctium.Helpers.Wire

open scoped Noctium
open Noctium Noctium.Helpers

namespace AggregateSerialization

private def payment : Types.CompositeType := .structure "Payment"

private def layouts : Types.CompositeEnv := {
  structures := [{id := "Payment", fields := [
    {name := "info", type := .tuple [.scalar (.uint 300), .scalar .bool]},
    {name := "flags", type := .vector 2 (.scalar .bool)},
    {name := "side", type := .enumeration "Side"},
    {name := "memo", type := .bytes 2}]}]
  enumerations := [{id := "Side", variants := [{name := "Pay"}, {name := "Cancel"}]}]
}

private def checkedProgram : Except String Program := do
  let layout ← (Types.compileType layouts payment).mapError (·.message)
  let codecs ← Noctium.Helpers.Wire.declarations layout "payment" 10 ⟨0, 0⟩ ⟨0, 1⟩
  pure {
    composites := layouts
    declarations := codecs ++ [{
      id := ⟨0, 2⟩, name := "transcode", parameters := [⟨"frame", .bytes 10⟩]
      result := .scalar (.bytes 10)
      body := [.return (some (.disclose {} (.call "paymentEncode" [
        .call "paymentDecode" [.ref "frame"]])))]}]
    exports := [{
      name := "transcode", target := ⟨0, 2⟩
      inputs := [{name := "frame", ty := .bytes 10, visibility := .private}]}]
  }

private def paymentProgram : Program := checkedProgram.toOption.getD {}

noctium_helper_circuit transcode from paymentProgram entry "transcode"

noctium_contract Codec where
  entry transcode uses transcode where
    return encoding : Bytes 10 := result
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
