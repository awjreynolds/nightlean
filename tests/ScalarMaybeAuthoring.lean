import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_witness_circuit scalarMaybeAuthoring where
  public amount : UInt 8
  let presentUInt := some(amount)
  let absentUInt := none(UInt 8)
  let presentBool := some(true)
  let absentBool := none(Bool)
  let presentNative := some(17)
  let absentNative := none(Native)
  let fallbackUInt := select(
    field(absentUInt, is_some), field(absentUInt, value), uint(9))
  prove eq(field(presentUInt, value), amount)
  prove eq(field(absentUInt, value), uint(0))
  prove eq(fallbackUInt, uint(9))
  prove eq(field(presentBool, value), true)
  prove eq(field(absentBool, value), false)
  prove eq(field(presentNative, value), 17)
  prove eq(field(absentNative, value), 0)
  output presentUIntOption := presentUInt
  output absentUIntOption := absentUInt
  output presentBoolOption := presentBool
  output absentBoolOption := absentBool
  output presentNativeOption := presentNative
  output absentNativeOption := absentNative
end

noctium_contract ScalarMaybeAuthoringNative where
  entry consume uses scalarMaybeAuthoring where
    return presentUIntOption
    return absentUIntOption
    return presentBoolOption
    return absentBoolOption
    return presentNativeOption
    return absentNativeOption
  end
end

private def scalarMaybeContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by scalar Maybe authoring fixture"
}

private def runScalarMaybe (amount : Nat) :=
  scalarMaybeAuthoring.run scalarMaybeContext [("amount", .uint 255 amount)]

#guard match runScalarMaybe 37 with
  | .ok outputs =>
      outputs.map (·.2) == [
        .native 1, .native 37, .native 0, .native 0,
        .native 1, .native 1, .native 0, .native 0,
        .native 1, .native 17, .native 0, .native 0]
  | .error _ => Bool.false

#guard match Witness.compile scalarMaybeAuthoring.__program
    "noctium.witness-circuit.scalarMaybeAuthoring.v1" with
  | .ok compiled =>
      compiled.circuit.outputs.length == 12 &&
      compiled.circuit.constraints.length > 0
  | .error _ => Bool.false

/-- undisclosed private parameter 'amount' -/
#guard_msgs (substring := true) in
noctium_witness_circuit scalarMaybeDisclosure where
  private amount : UInt 8
  output leaked := some(amount)
end
