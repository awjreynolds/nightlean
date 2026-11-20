import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit resetInputs where
  public enabled : Bool
end

noctium_circuit resetSeed where
end

noctium_contract NativeCellReset where
  cell amount : UInt 64
  cell nonce : Native
  cell active : Bool
  cell memo : Bytes 4
  entry seed uses resetSeed where
    write amount := uint(42)
    write nonce := 17
    write active := true
    write memo := bytes(4, "seed")
  end
  entry clear uses resetInputs where
    when enabled reset amount
    when enabled reset nonce
    when enabled reset active
    when enabled reset memo
    read amount as amountCurrent
    read nonce as nonceCurrent
    read active as activeCurrent
    read memo as memoCurrent
    return amountAfter : UInt 64 := amountCurrent
    return nonceAfter : Native := nonceCurrent
    return activeAfter : Bool := activeCurrent
    return memoAfter : Bytes 4 := memoCurrent
  end
end

noctium_contract NativeCellResetSealed where
  cell ordinary : Native
  sealed cell fixed : Native
  constructor() where
    initialize fixed := 42
  end
  entry clear uses resetSeed where
    reset ordinary
  end
end

#guard match NativeCellReset.entrypoints with
  | [_, clear] =>
    match clear.effects, clear.returns, clear.effectGuards with
    | [.writeCell "amount" (.uint resetMaximum) (.uint _ 0),
       .writeCell "nonce" .native (.native 0),
       .writeCell "active" .bool (.bool Bool.false),
       .writeCell "memo" (.bytes 4) (.bytesLiteral 4 [0, 0, 0, 0]),
       .readCell "amount" "amountCurrent" (.uint readMaximum),
       .readCell "nonce" "nonceCurrent" .native,
       .readCell "active" "activeCurrent" .bool,
       .readCell "memo" "memoCurrent" (.bytes 4)],
      [{name := "amountAfter", ty := .uint amountReturnMaximum,
          value := .ref "amountCurrent", span := _},
       {name := "nonceAfter", ty := .native, value := .ref "nonceCurrent", span := _},
       {name := "activeAfter", ty := .bool, value := .ref "activeCurrent", span := _},
       {name := "memoAfter", ty := .bytes 4, value := .ref "memoCurrent", span := _}],
      [some (.ref "enabled"), some (.ref "enabled"), some (.ref "enabled"),
       some (.ref "enabled"), none, none, none, none] =>
        resetMaximum == 2 ^ 64 - 1 && readMaximum == resetMaximum &&
          amountReturnMaximum == resetMaximum
    | _, _, _ => Bool.false
  | _ => Bool.false

private def resetSealedEffect (effect : Effect) : Effect :=
  match effect with
  | .writeCell "ordinary" .native value => .writeCell "fixed" .native value
  | other => other

private def resetSealedEntry (entrypoint : Entrypoint) : Entrypoint :=
  {entrypoint with effects := entrypoint.effects.map resetSealedEffect}

#guard
  match ({NativeCellResetSealed with
      entrypoints := NativeCellResetSealed.entrypoints.map resetSealedEntry}).validate
      Capabilities.source with
  | .error diagnostic => diagnostic.message ==
      "sealed state 'fixed' cannot be written by an entrypoint"
  | .ok _ => Bool.false

/-- error: cell reset does not accept a key path -/
#guard_msgs in
noctium_contract InvalidCellResetPath where
  cell amount : UInt 64
  entry clear uses resetInputs where
    when enabled reset amount[1]
  end
end
