import Nightlean.Backend.Impact
import Nightlean.Backend.NativeExpected
import Nightlean.Backend.Zkir
import Nightlean.Frontend

open scoped Nightlean
open Nightlean
open Lean

nightlean_circuit issue70HashPreimages where
  private secret : Bytes32
  private count : Native
  public expectedKey : Bytes32
  public expectedCredit : Bytes32
end

nightlean_contract Issue70HashPreimages where
  map registered : Bytes32 => Bool
  entry register uses issue70HashPreimages where
    insert registered[disclose(persistentHashVector32([bytes32("ElGamal:secretToScalar"), secret]))] := true
    member registered[expectedKey] as accountFound
    require eq(accountFound, true)
    insert registered[disclose(persistentHashVector32([secret, bytes32("credit_balance"), secret, persistentHashNative(count)]))] := true
    member registered[expectedCredit] as creditFound
    require eq(creditFound, true)
  end
end

private def issue70PreimageEntry : Entrypoint :=
  match Issue70HashPreimages.entrypoints with
  | ep :: _ => ep
  | _ => {name := "missing", circuit := {name := "missing"}}

#guard match Backend.Zkir.lowerEntrypoint Issue70HashPreimages.state issue70PreimageEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

private def issue70PreimageCapabilities : Capabilities :=
  {persistentHash32 := Bool.true, persistentHashVector32 := Bool.true, persistentHashNative := Bool.true}

private def issue70UndisclosedPreimage : Entrypoint :=
  {issue70PreimageEntry with effects := issue70PreimageEntry.effects.map fun effect =>
    match effect with
    | .writeMap name keyTy valueTy (.disclose _ key) value =>
      .writeMap name keyTy valueTy key value
    | other => other}

#guard match Disclosure.entrypoint issue70UndisclosedPreimage with
  | .error _ => Bool.true
  | .ok _ => Bool.false

private def issue70UndisclosedNativeHash : Entrypoint :=
  {issue70PreimageEntry with effects := issue70PreimageEntry.effects.map fun effect =>
    match effect with
    | .writeMap name _ valueTy _ value =>
      .writeMap name (.bytes 32) valueTy (.persistentHashNative (.ref "count")) value
    | other => other}

#guard match Disclosure.entrypoint issue70UndisclosedNativeHash with
  | .error _ => Bool.true
  | .ok _ => Bool.false

#guard match (Expr.persistentHashVector32 ([] : List (Expr (.bytes 32)))).validate issue70PreimageCapabilities [] with
  | .error _ => Bool.true
  | .ok _ => Bool.false

#guard match (Expr.persistentHashVector32 (List.replicate 33 (Expr.bytes32Literal (List.replicate 32 0)))).validate issue70PreimageCapabilities [] with
  | .error _ => Bool.true
  | .ok _ => Bool.false

#guard match (Expr.bytes32Literal (List.replicate 31 0)).validate issue70PreimageCapabilities [] with
  | .error _ => Bool.true
  | .ok _ => Bool.false

private def issue70PreimageReplace (value : Json) (name : String) (replacement : Json) : Json :=
  match value.getObj? with
  | .error _ => value
  | .ok object => Json.mkObj ((object.toList.filter (·.1 != name)) ++ [(name, replacement)])

private def issue70PreimageMutate (program : Json) (transform : Array Json → Array Json) : Json :=
  let instructions := (program.getObjValD "instructions").getArr?.toOption.getD #[]
  issue70PreimageReplace program "instructions" (Json.arr (transform instructions))

private def issue70PreimageOpcode (instruction : Json) : Option String :=
  (instruction.getObjVal? "op").toOption.bind fun value => value.getStr?.toOption

private def issue70SwapFirstHashOperands (program : Json) : Json :=
  issue70PreimageMutate program fun instructions => instructions.map fun instruction =>
    if issue70PreimageOpcode instruction == some "persistent_hash" then
      let values := (instruction.getObjValD "inputs").getArr?.toOption.getD #[]
      if values.size >= 2 then
        issue70PreimageReplace instruction "inputs"
          (Json.arr (#[values[1]!, values[0]!] ++ values.extract 2 values.size))
      else instruction
    else instruction

private def issue70ShortenFirstHashAlignment (program : Json) : Json :=
  issue70PreimageMutate program fun instructions => instructions.map fun instruction =>
    if issue70PreimageOpcode instruction == some "persistent_hash" then
      issue70PreimageReplace instruction "alignment" (Json.arr #[Json.mkObj [
        ("tag", toJson ("atom" : String)),
        ("value", Json.mkObj [("tag", toJson ("bytes" : String)), ("length", toJson (32 : Nat))])]])
    else instruction

private def issue70PreimageProducerRejects (transform : Json → Json) : _root_.Bool :=
  match Backend.Native.expectedEntrypoint Issue70HashPreimages.state issue70PreimageEntry with
  | .error _ => Bool.false
  | .ok expected => match Backend.Zkir.lowerEntrypoint Issue70HashPreimages.state issue70PreimageEntry with
    | .error _ => Bool.false
    | .ok program => match Backend.Native.validate expected (transform program) with
      | .error _ => Bool.true
      | .ok _ => Bool.false

#guard issue70PreimageProducerRejects issue70SwapFirstHashOperands
#guard issue70PreimageProducerRejects issue70ShortenFirstHashAlignment
