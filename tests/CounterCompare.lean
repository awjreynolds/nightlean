import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit counterCompareInputs where
  private owner : Bytes32
  private spender : Bytes32
  public threshold : UInt 64
  public enabled : Bool
end

noctium_contract CounterCompare where
  counter total
  tree epochs : Bytes32 => Bytes32 => Counter

  entry inspect uses counterCompareInputs where
    increment total by 300
    counterLessThan total against threshold as isBelow
    return below : Bool := isBelow
  end

  entry seedNested uses counterCompareInputs where
    member epochs[disclose(owner)] as ownerPresent
    if eq(ownerPresent, false) then {
      insert epochs[disclose(owner)] := emptyMap
    } else {
    }
    member epochs[disclose(owner)][disclose(spender)] as counterPresent
    if eq(counterPresent, false) then {
      reset epochs[disclose(owner)][disclose(spender)]
    } else {
    }
    increment epochs[disclose(owner)][disclose(spender)] by 300
  end

  entry inspectNested uses counterCompareInputs where
    when enabled counterLessThan epochs[disclose(owner)][disclose(spender)]
      against assertThen(enabled, threshold) as isBelow
    return below : Bool := isBelow
  end
end

private def counterCompareEntry (name : String) : Entrypoint :=
  match CounterCompare.entrypoints.find? (·.name == name) with
  | some found => found
  | none => {name := "missing", circuit := {name := "missing"}}

#guard match Backend.Impact.lower CounterCompare.state (counterCompareEntry "inspect") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Impact.lower CounterCompare.state (counterCompareEntry "inspectNested") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint CounterCompare.state
    (counterCompareEntry "inspectNested") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

private def counterCompareContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by this fixture"
}

#guard match Entrypoint.run counterCompareContext (counterCompareEntry "inspect")
    [ ("owner", .bytes 32 (List.replicate 32 1))
    , ("spender", .bytes 32 (List.replicate 32 2))
    , ("threshold", .uint (2 ^ 64 - 1) 301)
    , ("enabled", .bool Bool.true)
    ]
    {trees := [
      ("total", .scalar (.uint (2 ^ 64 - 1) 0)),
      ("epochs", .map [])
    ]} with
  | .ok (outputs, state) =>
      outputs.lookup "below" == some (.bool Bool.true) &&
      state.trees.lookup "total" == some (.scalar (.uint (2 ^ 64 - 1) 300))
  | .error _ => Bool.false

private def counterCompareHiddenPath : Entrypoint := {
  name := "hiddenPath"
  circuit := {
    name := "hiddenPath"
    inputs := [
      {name := "owner", ty := .bytes 32, visibility := .private},
      {name := "threshold", ty := .uint (2 ^ 64 - 1), visibility := .public}
    ]
  }
  effects := [.counterLessThan "epochs" "below" [
    .mk (.bytes 32) (.ref (ty := .bytes 32) "owner")
  ] (.ref (ty := .uint (2 ^ 64 - 1)) "threshold")]
}

#guard match Disclosure.entrypoint counterCompareHiddenPath with
  | .error diagnostic => diagnostic.message.contains "undisclosed private parameter 'owner'"
  | .ok _ => Bool.false

private def counterCompareHiddenThreshold : Entrypoint := {
  name := "hiddenThreshold"
  circuit := {
    name := "hiddenThreshold"
    inputs := [
      {name := "owner", ty := .bytes 32, visibility := .public},
      {name := "threshold", ty := .uint (2 ^ 64 - 1), visibility := .private}
    ]
  }
  effects := [.counterLessThan "epochs" "below" [
    .mk (.bytes 32) (.ref (ty := .bytes 32) "owner")
  ] (.ref (ty := .uint (2 ^ 64 - 1)) "threshold")]
}

#guard match Disclosure.entrypoint counterCompareHiddenThreshold with
  | .error diagnostic => diagnostic.message.contains "undisclosed private parameter 'threshold'"
  | .ok _ => Bool.false
