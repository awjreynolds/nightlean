import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Compiler
import Noctium.Types.Maybe
import Noctium.Types.ValueSchema

open scoped Noctium
open Lean
open Noctium
open Noctium.Types

noctium_circuit scalarListMaybePushInputs where
  private value : UInt 8
end

noctium_circuit scalarListMaybeNoInputs where
end

noctium_circuit scalarListMaybeReturnInputs where
  public present : Bool
  public payload : UInt 8
end

noctium_contract NativeScalarListMaybe where
  list values : UInt 8

  entry push uses scalarListMaybePushInputs arguments [value] where
    pushFront values := disclose(value)
  end

  entry head uses scalarListMaybeNoInputs where
    headOrDefault values as (present, payload)
    returnMaybe head as (present, payload)
  end

  entry canonicalize uses scalarListMaybeReturnInputs where
    returnMaybe maybeResult as (present, payload)
  end
end

private def maybeContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by scalar List Maybe fixture"
}

private def maybeEntry (name : String) : Entrypoint :=
  (NativeScalarListMaybe.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

private def runMaybeEntry (name : String) (inputs : EvalEnv) (state : LedgerState) :=
  (maybeEntry name).run maybeContext inputs state

private def emptyMaybeState : LedgerState := {trees := [("values", .list [])]}

#guard match Backend.Impact.lower NativeScalarListMaybe.state (maybeEntry "push") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Impact.lower NativeScalarListMaybe.state (maybeEntry "head") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint NativeScalarListMaybe.state (maybeEntry "head") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

-- Empty and populated List heads become the Compact Maybe value shape.
#guard match runMaybeEntry "head" [] emptyMaybeState with
  | .ok (outputs, _) =>
      outputs.lookup "head_is_some" == some (.native 0) &&
      outputs.lookup "head_value" == some (.native 0)
  | .error _ => Bool.false

#guard match runMaybeEntry "push" [("value", .uint 255 37)] emptyMaybeState with
  | .ok (_, populated) =>
    match runMaybeEntry "head" [] populated with
    | .ok (outputs, _) =>
        outputs.lookup "head_is_some" == some (.native 1) &&
        outputs.lookup "head_value" == some (.native 37)
    | .error _ => Bool.false
  | .error _ => Bool.false

#guard match runMaybeEntry "canonicalize"
    [("present", .bool Bool.false), ("payload", .uint 255 37)] emptyMaybeState with
  | .ok (outputs, _) =>
      outputs.lookup "maybeResult_is_some" == some (.native 0) &&
      outputs.lookup "maybeResult_value" == some (.native 0)
  | .error _ => Bool.false

#guard match runMaybeEntry "canonicalize"
    [("present", .bool Bool.true), ("payload", .uint 255 37)] emptyMaybeState with
  | .ok (outputs, _) =>
      outputs.lookup "maybeResult_is_some" == some (.native 1) &&
      outputs.lookup "maybeResult_value" == some (.native 37)
  | .error _ => Bool.false

private def maybeUInt8Id : String :=
  (Maybe.scalarTypeId "NativeScalarListMaybe" (.uint 255)).toOption.getD ""

private def maybeUInt8Environment : CompositeEnv :=
  (Maybe.scalarEnvironment maybeUInt8Id (.uint 255)).toOption.getD {}

private def maybeUInt8Type : CompositeType := Maybe.scalarType maybeUInt8Id

private def maybeUInt8Leaves (present : _root_.Bool) (payload : Nat) : Except String (List Nat) := do
  let compiled ← (compileType maybeUInt8Environment maybeUInt8Type).mapError (·.message)
  let value := Maybe.scalarValue maybeUInt8Id (.uint 255) present payload
  let checked ← checkValue compiled value
  flatten compiled checked.value

#guard maybeUInt8Id == "NativeScalarListMaybe.MaybeUInt8"
#guard match maybeUInt8Leaves _root_.Bool.false 37 with
  | .ok leaves => leaves == [0, 0]
  | .error _ => Bool.false
#guard match maybeUInt8Leaves _root_.Bool.true 37 with
  | .ok leaves => leaves == [1, 37]
  | .error _ => Bool.false

private def maybeUInt8Schema : Except String Lean.Json := do
  let compiled ← (compileType maybeUInt8Environment maybeUInt8Type).mapError (·.message)
  schemaJson compiled

private def headPlanJson : Except String Lean.Json := do
  let headEntrypoint := maybeEntry "head"
  let plan ← (Backend.Impact.lower NativeScalarListMaybe.state headEntrypoint).mapError (·.message)
  pure (Compiler.nativePlanJson TargetProfile.selected321 `NativeScalarListMaybe
    NativeScalarListMaybe.state none headEntrypoint plan)

-- Compact's pinned scalar Maybe ABI has `is_some` before `value`.
#guard match headPlanJson, maybeUInt8Schema with
  | .ok plan, .ok schema =>
      match (plan.getObjVal? "returnViews").toOption, (schema.getObjVal? "layout").toOption with
      | some (.arr #[view]), some layout =>
          view.getObjValD "name" == toJson ("head" : String) &&
          view.getObjValD "schema" == schema &&
          view.getObjValD "fields" == toJson (["head_is_some", "head_value"] : List String) &&
          layout.getObjValD "kind" == toJson ("struct" : String) &&
          layout.getObjValD "fields" == toJson ([
            Lean.Json.mkObj [
              ("name", toJson ("is_some" : String)),
              ("layout", Lean.Json.mkObj [
                ("kind", toJson ("scalar" : String)),
                ("leaf", Lean.Json.mkObj [("kind", toJson ("bool" : String))])])],
            Lean.Json.mkObj [
              ("name", toJson ("value" : String)),
              ("layout", Lean.Json.mkObj [
                ("kind", toJson ("scalar" : String)),
                ("leaf", Lean.Json.mkObj [
                  ("kind", toJson ("uint" : String)),
                  ("maximum", toJson ("255" : String))])])]
          ] : List Lean.Json)
      | _, _ => Bool.false
  | _, _ => Bool.false
