import Noctium.Frontend

open scoped Noctium

noctium_witness iterationSeed() : Native
noctium_witness iterationBytes() : Bytes 2
noctium_witness iterationVisit(item : UInt 8) : Native

noctium_witness_circuit readableIteration where
  public offset : Native
  let sum : Native := fold(witness iterationSeed(),
    [map([witness iterationBytes()], fun item => witness iterationVisit(item))],
    fun acc value => add(add(acc, value), offset))
  output result : Native := disclose(sum)
end

#guard
  let compiled := Noctium.Witness.compile readableIteration.__program
    "noctium.witness-circuit.readableIteration.v1"
  (compiled.toOption.map (fun source => source.calls.map (·.name))) ==
    some ["iterationSeed", "iterationBytes", "iterationVisit", "iterationVisit"]

noctium_contract ReadableIteration where
  cell total : Native
  entry update uses readableIteration where
    write total := result
    return updated : Native := result
  end
end

/-- public output -/
#guard_msgs (substring := true) in
noctium_witness_circuit uncheckedIteration where
  private data : Bytes 2
  output leaked : Native := fold(0, [data], fun acc value => add(acc, value))
end

private def bytePair : Noctium.Helpers.Wire.Codec := {
  payload := .vector 2 (.scalar (.uint 255))
  frameBytes := 2
}

noctium_witness_circuit decodedIteration using bytePair where
  public frame : Bytes 2
  let values := decode(bytePair, frame)
  let bumped := let offset := 1 in map([values], fun value => add(value, offset))
  output mapped := bumped
  output sum : Native := fold(0, [bumped], fun acc value => add(acc, value))
end
