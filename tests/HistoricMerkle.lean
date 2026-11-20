import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit historicNoInputs where
end

noctium_circuit historicHash where
  private leafHash : Bytes32
end

noctium_circuit historicField where
  private leaf : Native
end

noctium_circuit historicHashIndex where
  private position : UInt 64
  private leafHash : Bytes32
end

noctium_circuit historicFieldIndex where
  private position : UInt 64
  private leaf : Native
end

noctium_circuit historicDigest where
  private expectedRoot : Native
end

noctium_circuit appendAndCheckHistoric where
  private leafHash : Bytes32
  private expectedRoot : Native
end

noctium_circuit guardedHistoricClear where
  public active : Bool
  private expectedRoot : Native
end

noctium_contract NativeHistoricMerkle where
  historicMerkleTree claims : 2

  entry appendHash uses historicHash where
    insertHash claims := disclose(leafHash)
  end

  entry appendField uses historicField where
    insertField claims := disclose(leaf)
  end

  entry writeHashIndex uses historicHashIndex where
    insertHashIndex claims at disclose(position) := disclose(leafHash)
  end

  entry writeFieldIndex uses historicFieldIndex where
    insertFieldIndex claims at disclose(position) := disclose(leaf)
  end

  entry checkDigest uses historicDigest where
    checkRoot claims against disclose(expectedRoot) as known
    isFull claims as full
    return knownRoot : Bool := known
    return fullStatus : Bool := full
  end

  entry appendAndCheck uses appendAndCheckHistoric where
    insertHash claims := disclose(leafHash)
    checkRoot claims against disclose(expectedRoot) as known
    return knownRoot : Bool := known
  end

  entry guardedClearHistory uses guardedHistoricClear where
    when active resetHistory claims
    checkRoot claims against disclose(expectedRoot) as known
    return knownRoot : Bool := known
  end

  entry clearHistory uses historicNoInputs where
    resetHistory claims
  end

  entry resetTree uses historicNoInputs where
    reset claims
  end
end

private def historicModelContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused"
  transientHash := fun roots => pure (roots.foldl (· + ·) 0 % Field.modulus)
}

private def historicModel : Except String _root_.Bool := do
  let lookup := fun name => NativeHistoricMerkle.entrypoints.find? (·.name == name)
  let some appendEntry := lookup "appendHash" | throw "missing historic append"
  let some checkEntry := lookup "checkDigest" | throw "missing historic root check"
  let some clearEntry := lookup "clearHistory" | throw "missing historic reset"
  let hash := Value.bytes 32 (1 :: List.replicate 31 0)
  let (_, populated) ← appendEntry.run historicModelContext [("leafHash", hash)] {
    trees := [("claims", LedgerValue.emptyHistoricMerkleTree 2)]
  }
  let oldRoot := [("expectedRoot", Value.native 0)]
  let (before, _) ← checkEntry.run historicModelContext oldRoot populated
  let (_, cleared) ← clearEntry.run historicModelContext [] populated
  let (after, _) ← checkEntry.run historicModelContext oldRoot cleared
  let (tip, _) ← checkEntry.run historicModelContext [("expectedRoot", .native 1)] cleared
  pure (before.lookup "knownRoot" == some (.bool Bool.true) &&
    after.lookup "knownRoot" == some (.bool Bool.false) &&
    tip.lookup "knownRoot" == some (.bool Bool.true))

#guard match historicModel with
  | .ok result => result
  | .error _ => Bool.false

/-- undisclosed private parameter -/
#guard_msgs (substring := true) in
noctium_contract UndisclosedHistoricRoot where
  historicMerkleTree claims : 2
  entry check uses historicDigest where
    checkRoot claims against expectedRoot as known
    return knownRoot : Bool := known
  end
end
