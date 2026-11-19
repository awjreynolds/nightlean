import Noctium.Frontend
import Noctium.Backend.Zkir
import Noctium.NativeExpression

open scoped Noctium

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
  public target : Bytes32
  public entryHash : Bytes32
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

noctium_contract TypedCaller where
  cell marker : Native
  entry claim uses typedCallerInput where
    claimContractCall(target, entryHash,
      disclose(callCommitment(TypedCallArguments, "store", opening,
        [flag, payload, score, point, scalar, field, assertThen(emptyAccepted, empty)],
        [expectedTail, expectedScore, expectedApproval])))
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
