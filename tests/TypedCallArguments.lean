import Noctium.Frontend
import Noctium.Backend.Zkir
import Noctium.EntryPointHash
import Noctium.NativeExpression

open scoped Noctium

#guard Noctium.EntryPointHash.hash (String.ofList (List.replicate 23 'a')) ==
  [0xaa, 0x22, 0xa8, 0xcb, 0x2e, 0x5e, 0x1d, 0xc4, 0x2a, 0x82, 0xc7, 0xb5, 0x1b, 0x51, 0x20, 0x85,
   0x5f, 0xdf, 0x07, 0x11, 0x89, 0xb8, 0x2c, 0x74, 0x9d, 0x06, 0x10, 0xa0, 0xbc, 0xc5, 0x6c, 0x4d]
#guard Noctium.EntryPointHash.hash (String.ofList (List.replicate 24 'a')) ==
  [0xd2, 0x38, 0x1b, 0xe8, 0x8a, 0x1e, 0x92, 0xb1, 0xb4, 0x35, 0x39, 0x92, 0xc6, 0x6d, 0xf6, 0x8c,
   0xb8, 0xc9, 0x1a, 0x09, 0xc2, 0x61, 0xf6, 0x9f, 0x17, 0xf1, 0xf7, 0xe4, 0x77, 0x4d, 0x04, 0x28]

noctium_circuit typedCallInput where
  private score : UInt 8
  private aux : Native
  private payload : Bytes 33
  private flag : Bool
  private point : JubjubPoint
  private scalar : JubjubScalar
  private field : Secp256k1Base
  private empty : Bytes 0
  assert eq(aux, 7)
  assert eq(jubjubX(point), 0)
  assert eq(jubjubScalarToNative(scalar), 1)
  assert eq(field, secp256k1Base(9))
end

noctium_contract TypedCallArguments where
  cell stored : UInt 8
  entry store uses typedCallInput arguments [flag, payload, score, point, scalar, field, empty] where
    if disclose(flag) then {
      write stored := disclose(score)
    } else {}
    return tail : UInt 8 := disclose(byteAt(payload, 32))
    return result : UInt 8 := disclose(score)
    return approved : Bool := disclose(flag)
  end
end

noctium_circuit typedCallerInput where
  private opening : Native
  private flag : Bool
  private payload : Bytes 33
  private score : UInt 8
  private point : JubjubPoint
  private scalar : JubjubScalar
  private field : Secp256k1Base
  private empty : Bytes 0
  private emptyAccepted : Bool
  private expectedTail : UInt 8
  private expectedScore : UInt 8
  private expectedApproval : Bool
end

noctium_circuit rotateRouteInput where
  public newTarget : Bytes32
  private authority : Native
end

noctium_contract TypedCaller where
  cell route : Bytes32
  cell adminCommitment : Native
  entry claim uses typedCallerInput where
    read route as target
    claimContractCall(target,
      disclose(callCommitment(TypedCallArguments, "store", opening,
        [flag, payload, score, point, scalar, field, assertThen(emptyAccepted, empty)],
        [expectedTail, expectedScore, expectedApproval])))
  end
  entry rotateRoute uses rotateRouteInput where
    read adminCommitment as admin
    require eq(transientHashNativeVector([authority]), admin)
    write route := newTarget
  end
end

/-- error: two-argument claimContractCall requires callCommitment, optionally wrapped in disclose -/
#guard_msgs in
noctium_contract MissingCallInterface where
  cell route : Bytes32
  entry claim uses typedCallerInput where
    read route as target
    claimContractCall(target, 1)
  end
end

/-- error: callCommitment argument count does not match the callee -/
#guard_msgs in
noctium_circuit wrongCallArity where
  output commitment : Native := callCommitment(TypedCallArguments, "store", 1, [], [])
end

/-- error: Noctium expression type mismatch -/
#guard_msgs in
noctium_circuit wrongCallType where
  output commitment : Native := callCommitment(TypedCallArguments, "store", 1,
    [1, bytes(33, ""), 0, default(JubjubPoint), default(JubjubScalar), secp256k1Base(0), bytes(0, "")],
    [0, 0, false])
end

private def firstCall : Noctium.Entrypoint :=
  match TypedCallArguments.entrypoints with
  | found :: _ => found
  | [] => {name := "missing", circuit := {name := "missing"}}

#guard !(Noctium.Disclosure.entrypoint
  {firstCall with returns := [{name := "secret", ty := .bool, value := .ref "flag"}]}).isOk

private def argumentFieldsOverflow : Noctium.Entrypoint :=
  let names := (List.range 8).map fun i => s!"blob{i}"
  let inputs : List Noctium.Input := names.map fun name =>
    {name, ty := .bytes 1024, visibility := .private}
  {firstCall with circuit := {name := "overBudget", inputs}, callInputs := names, effects := [], effectSpans := [], effectGuards := [], returns := []}

#guard !(argumentFieldsOverflow.validate Noctium.Capabilities.crypto []).isOk


private def wideBindingSequence : Noctium.Expr .native :=
  (List.range 150).foldr (fun i body =>
    .letE s!"argument{i}" (.native i) body) (.ref "argument149")

#guard match (Noctium.NativeExpression.toJson wideBindingSequence).getObjVal? "bindings" with
  | .ok (.arr bindings) => bindings.size == 150
  | _ => Bool.false
