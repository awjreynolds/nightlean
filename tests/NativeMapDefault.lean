import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Disclosure

open scoped Noctium
open Noctium

noctium_circuit nativeHistoricPathInputs where
  private owner : Bytes32
end

noctium_circuit nativeHistoricLeafInputs where
  private owner : Bytes32
  private leaf : Bool
end

noctium_circuit nativeMapDefaultInputs where
  private owner : Bytes32
  private key : Native
  private amount : Native
  public enabled : Bool
end

noctium_contract NativeMapDefault where
  map values : Native => Native
  tree nestedValues : Bytes32 => Native => Native
  tree nestedMaps : Bytes32 => Native => Native
  tree sets : Bytes32 => Set Native
  tree lists : Bytes32 => List Native
  tree counters : Bytes32 => Counter
  tree ordinary : Bytes32 => MerkleTree 2
  tree historic : Bytes32 => HistoricMerkleTree 2 of Bool
  tree records : Bytes32 => struct Record {
    amount : Native
    payload : Bytes32
    recipient : JubjubPoint
  }

  entry seed uses nativeMapDefaultInputs where
    insert values[disclose(key)] := disclose(amount)
    member values[disclose(key)] as present
    size values as count
    read values[disclose(key)] as value
    return hasEntry : Bool := present
    return entries : UInt 64 := count
    return stored : Native := value
  end

  entry defaultValue uses nativeMapDefaultInputs where
    insertDefault values[disclose(key)]
    member values[disclose(key)] as present
    size values as count
    read values[disclose(key)] as value
    return hasEntry : Bool := present
    return entries : UInt 64 := count
    return stored : Native := value
  end

  entry defaults uses nativeMapDefaultInputs where
    insert nestedValues[disclose(owner)] := emptyMap
    insertDefault nestedValues[disclose(owner)][disclose(key)]
    insertDefault nestedMaps[disclose(owner)]
    insertDefault sets[disclose(owner)]
    insertDefault lists[disclose(owner)]
    insertDefault counters[disclose(owner)]
    insertDefault ordinary[disclose(owner)]
    insertDefault historic[disclose(owner)]
    when enabled insertDefault records[disclose(owner)]
  end

  entry missingParent uses nativeMapDefaultInputs where
    when enabled insertDefault nestedValues[disclose(owner)][disclose(key)]
  end

  entry defaultHistoric uses nativeHistoricPathInputs where
    insertDefault historic[disclose(owner)]
  end

  entry appendHistoric uses nativeHistoricLeafInputs where
    insertLeaf historic[disclose(owner)] := disclose(leaf)
  end

  entry checkHistoricZero uses nativeHistoricPathInputs where
    checkRoot historic[disclose(owner)] against 0 as hasZeroRoot
    return known : Bool := hasZeroRoot
  end

  entry resetHistoric uses nativeHistoricPathInputs where
    reset historic[disclose(owner)]
  end
end

private def nativeMapDefaultEntry (name : String) : Entrypoint :=
  match NativeMapDefault.entrypoints.find? (·.name == name) with
  | some found => found
  | none => {name := "missing", circuit := {name := "missing"}}

#guard match Backend.Impact.lower NativeMapDefault.state (nativeMapDefaultEntry "seed") with
  | .ok plan => plan.operations.any (fun op => match op with
      | .insert 2 => Bool.true
      | _ => Bool.false)
  | .error _ => Bool.false

#guard match Backend.Impact.lower NativeMapDefault.state (nativeMapDefaultEntry "defaultValue") with
  | .ok plan => plan.operations.any (fun op => match op with
      | .insert 2 => Bool.true
      | _ => Bool.false)
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint NativeMapDefault.state
    (nativeMapDefaultEntry "defaults") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

/-- undisclosed private parameter 'owner' -/
#guard_msgs (substring := true) in
noctium_contract NativeMapDefaultUndisclosed where
  map hidden : Bytes32 => Native
  entry update uses nativeMapDefaultInputs where
    insertDefault hidden[owner]
  end
end
