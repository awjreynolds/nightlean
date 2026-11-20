import Noctium.Frontend

open scoped Noctium

noctium_private_state ContainerWallet where
  cell last : Native
end

noctium_witness containerBytes() : Bytes 2
noctium_witness emptyContainer() : Bytes 0
noctium_witness containerStep(item : UInt 8, previous : Native) : Native

noctium_witness_circuit readableContainerLoop where
  public expected : Native
  for item in witness containerBytes() do
    read private ContainerWallet.last as previous
    let next : Native := witness containerStep(item, previous)
    prove eq(next, add(previous, item))
    stage ContainerWallet.last := next
  end
  for item in witness emptyContainer() do
    let next : Native := witness containerStep(item, 0)
    prove eq(next, item)
  end
  read private ContainerWallet.last as finalValue
  prove eq(finalValue, expected)
  output result : Native := expected
end

#guard
  let compiled := Noctium.Witness.compile readableContainerLoop.__program
    "noctium.witness-circuit.readableContainerLoop.v1"
  compiled.toOption.map (fun source => source.calls.map (·.name)) ==
    some ["containerBytes", "private_state.read.ContainerWallet.last.v1", "containerStep",
      "private_state.read.ContainerWallet.last.v1", "containerStep", "emptyContainer",
      "private_state.read.ContainerWallet.last.v1"]

noctium_control readableContainerLoopHost from readableContainerLoop.__program
  entry "noctium.witness-circuit.readableContainerLoop.v1"

noctium_contract ReadableContainerLoop where
  cell total : Native
  entry update uses readableContainerLoop where
    write total := result
    return updated : Native := result
  end
end

noctium_witness_circuit nestedOperatorReturn where
  public bytes : Bytes 1
  for item in bytes do
    let values := map([bytes], fun value => add(value, item))
    prove eq(elementAt(values, 0), add(item, item))
  end
end

private def emptyTupleWire : Noctium.Helpers.Wire.Codec := {
  payload := .tuple []
  frameBytes := 0
}

noctium_witness_circuit emptyTupleLoops using emptyTupleWire where
  let items := decode(emptyTupleWire, witness emptyContainer())
  for unused in items do
    prove false
  end
  for item : UInt 8 in items do
    let next : Native := witness containerStep(item, 0)
    prove eq(next, item)
  end
  for inferred in items do
    let next := witness containerStep(inferred, 0)
    let widened : Native := inferred
    prove eq(next, widened)
  end
  for inferred in items do
    let flag : Bool := inferred
    prove flag
  end
end

#guard
  let compiled := Noctium.Witness.compile emptyTupleLoops.__program
    "noctium.witness-circuit.emptyTupleLoops.v1"
  compiled.toOption.map (fun source => source.calls.map (·.name)) == some ["emptyContainer"]

noctium_witness emptyTupleSeed() : Native

noctium_witness_circuit emptyTupleOperators using emptyTupleWire where
  let items := decode(emptyTupleWire, witness emptyContainer())
  let mapped := map([items], fun item => witness containerStep(item, 0))
  let sum := fold(witness emptyTupleSeed(), [items, mapped],
    fun acc item value => add(value, witness containerStep(item, acc)))
  output result : Native := disclose(sum)
end

#guard
  let compiled := Noctium.Witness.compile emptyTupleOperators.__program
    "noctium.witness-circuit.emptyTupleOperators.v1"
  compiled.toOption.map (fun source => source.calls.map (·.name)) ==
    some ["emptyContainer", "emptyTupleSeed"]

noctium_control emptyTupleOperatorsHost from emptyTupleOperators.__program
  entry "noctium.witness-circuit.emptyTupleOperators.v1"

/-- error: empty tuple item 'item' has conflicting expected types -/
#guard_msgs in
noctium_witness_circuit conflictingEmptyItemTypes using emptyTupleWire where
  let items := decode(emptyTupleWire, witness emptyContainer())
  for item in items do
    let flag : Bool := item
    let byte : UInt 8 := item
    prove flag
  end
end

/-- error: unknown readable witness value 'item' -/
#guard_msgs in
noctium_witness_circuit escapedContainerItem where
  public bytes : Bytes 1
  for item in bytes do
    prove eq(item, item)
  end
  output escaped : UInt 8 := item
end
