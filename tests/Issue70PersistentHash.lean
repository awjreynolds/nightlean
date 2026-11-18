import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Frontend

open scoped Noctium
open Noctium
open Lean

noctium_circuit issue70PersistentHash where
  private secret : Bytes32
  public expected : Bytes32
end

noctium_contract Issue70PersistentHash where
  map registered : Bytes32 => Bool
  entry register uses issue70PersistentHash where
    insert registered[disclose(persistentHash32(secret))] := true
    member registered[expected] as found
    require eq(found, true)
  end
end

private def issue70HashEntry : Entrypoint :=
  match Issue70PersistentHash.entrypoints with
  | ep :: _ => ep
  | _ => {name := "missing", circuit := {name := "missing"}}

#guard match Backend.Zkir.lowerEntrypoint Issue70PersistentHash.state issue70HashEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

private def issue70UndisclosedHashKey : Entrypoint :=
  {issue70HashEntry with effects := issue70HashEntry.effects.map fun effect =>
    match effect with
    | .writeMap name _ valueTy _ value =>
      .writeMap name (.bytes 32) valueTy (.persistentHash32 (.ref "secret")) value
    | other => other}

#guard match Disclosure.entrypoint issue70UndisclosedHashKey with
  | .error _ => Bool.true
  | .ok _ => Bool.false

private def issue70Replace (value : Json) (name : String) (replacement : Json) : Json :=
  match value.getObj? with
  | .error _ => value
  | .ok object => Json.mkObj ((object.toList.filter (·.1 != name)) ++ [(name, replacement)])

private def issue70InsertBeforeOutput (instructions : Array Json) (next : Json) : Array Json :=
  match instructions.toList.reverse with
  | lastInstruction :: rest => (rest.reverse ++ [next, lastInstruction]).toArray
  | [] => instructions

private def issue70InstructionName (instruction : Json) : Option String :=
  (instruction.getObjVal? "op").toOption.bind fun value => value.getStr?.toOption

private def issue70HashOutput (instructions : Array Json) : Option String := do
  let instruction ← instructions.toList.find? fun value => issue70InstructionName value == some "persistent_hash"
  let hashResult ← (instruction.getObjVal? "output").toOption
  hashResult.getStr?.toOption

private def issue70MutateInstructions (program : Json) (transform : Array Json → Array Json) : Json :=
  let instructions := (program.getObjValD "instructions").getArr?.toOption.getD #[]
  issue70Replace program "instructions" (Json.arr (transform instructions))

private def issue70ProducerRejects (transform : Json → Json) : _root_.Bool :=
  match Backend.Native.expectedEntrypoint Issue70PersistentHash.state issue70HashEntry with
  | .error _ => _root_.Bool.false
  | .ok expected => match Backend.Zkir.lowerEntrypoint Issue70PersistentHash.state issue70HashEntry with
    | .error _ => _root_.Bool.false
    | .ok program => match Backend.Native.validate expected (transform program) with
      | .error _ => _root_.Bool.true
      | .ok _ => _root_.Bool.false

private def issue70HashAsNativeArithmetic (program : Json) : Json :=
  issue70MutateInstructions program fun instructions =>
    match issue70HashOutput instructions with
    | none => instructions
    | some digest => issue70InsertBeforeOutput instructions (Json.mkObj [
        ("op", toJson ("add" : String)), ("a", toJson digest),
        ("b", toJson ("0x00" : String)), ("output", toJson ("%bad_add" : String))])

private def issue70HashAsConstraint (program : Json) : Json :=
  issue70MutateInstructions program fun instructions =>
    match issue70HashOutput instructions with
    | none => instructions
    | some digest => issue70InsertBeforeOutput instructions (Json.mkObj [
        ("op", toJson ("constrain_bits" : String)), ("val", toJson digest),
        ("bits", toJson (8 : Nat))])

private def issue70ShortEncode (program : Json) : Json :=
  issue70MutateInstructions program fun instructions => instructions.map fun instruction =>
    if issue70InstructionName instruction == some "encode" then
      issue70Replace instruction "outputs" (toJson (["%short_encode"] : List String))
    else instruction

private def issue70WrongHashAlignment (program : Json) : Json :=
  issue70MutateInstructions program fun instructions => instructions.map fun instruction =>
    if issue70InstructionName instruction == some "persistent_hash" then
      issue70Replace instruction "alignment" (Json.arr #[Json.mkObj [
        ("tag", toJson ("atom" : String)),
        ("value", Json.mkObj [("tag", toJson ("bytes" : String)), ("length", toJson (31 : Nat))])]])
    else instruction

#guard issue70ProducerRejects issue70HashAsNativeArithmetic
#guard issue70ProducerRejects issue70HashAsConstraint
#guard issue70ProducerRejects issue70ShortEncode
#guard issue70ProducerRejects issue70WrongHashAlignment
