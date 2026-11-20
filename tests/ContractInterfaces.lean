import Noctium.Frontend

open scoped Noctium

noctium_circuit updateInputs where
  private amount : UInt 8
  output provided : UInt 8 := disclose(amount)
end

noctium_contract ScalarTarget where
  cell total : UInt 8
  entry update uses updateInputs arguments [amount] where
    write total := provided
    return newTotal : UInt 8 := provided
  end
end

noctium_interface ScalarUpdate where
  entry update accepts [value : UInt 8] yields [stored : UInt 8]
end

noctium_implements ScalarTarget implements ScalarUpdate

noctium_circuit scalarInterfaceCaller where
  private opening : Native
  private payload : UInt 8
  private expected : UInt 8
  output binding : Native :=
    disclose(callCommitment(ScalarTarget, ScalarUpdate, "update", opening, [payload], [expected]))
end

/-- already implements -/
#guard_msgs (substring := true) in
noctium_implements ScalarTarget implements ScalarUpdate

/-- is not a declared Noctium contract -/
#guard_msgs (substring := true) in
noctium_implements updateInputs implements ScalarUpdate

noctium_interface MissingEntry where
  entry otherEntry accepts [] yields []
end

/-- has no entry 'otherEntry' -/
#guard_msgs (substring := true) in
noctium_implements ScalarTarget implements MissingEntry

noctium_interface WrongUint where
  entry update accepts [value : UInt 16] yields [stored : UInt 8]
end

/-- does not match interface -/
#guard_msgs (substring := true) in
noctium_implements ScalarTarget implements WrongUint

noctium_interface WrongGrouping where
  entry update accepts [payload := fields(value : UInt 8)] yields [stored : UInt 8]
end

/-- does not match interface -/
#guard_msgs (substring := true) in
noctium_implements ScalarTarget implements WrongGrouping

noctium_interface UnregisteredUpdate where
  entry update accepts [value : UInt 8] yields [stored : UInt 8]
end

/-- does not implement interface -/
#guard_msgs (substring := true) in
noctium_circuit unregisteredCaller where
  private opening : Native
  output binding : Native :=
    disclose(callCommitment(ScalarTarget, UnregisteredUpdate, "update", opening, [1], [1]))
end

/-- undisclosed private parameter -/
#guard_msgs (substring := true) in
noctium_circuit undisclosedInterfaceCaller where
  private opening : Native
  output binding : Native :=
    callCommitment(ScalarTarget, ScalarUpdate, "update", opening, [1], [1])
end

/-- requires a declared callee contract -/
#guard_msgs (substring := true) in
noctium_circuit interfaceWithoutImplementation where
  private opening : Native
  output binding : Native :=
    disclose(callCommitment(ScalarUpdate, "update", opening, [1], [1]))
end
