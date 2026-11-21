import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Compiler
import Noctium.Types.Either
import Noctium.Types.ValueSchema

open scoped Noctium
open Lean
open Noctium
open Noctium.Types

noctium_circuit scalarEitherInputs where
  public isLeft : Bool
  public leftValue : UInt 8
  public rightValue : UInt 16
end

noctium_contract NativeScalarEitherReturns where
  entry canonicalize uses scalarEitherInputs where
    returnEither result as (isLeft, leftValue, rightValue)
  end
end

private def eitherContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by scalar Either fixture"
}

private def eitherEntry : Entrypoint :=
  (NativeScalarEitherReturns.entrypoints.find? (·.name == "canonicalize")).getD
    {name := "missing", circuit := {name := "missing"}}

private def runEither (isLeft : _root_.Bool) (leftValue : Nat) (rightValue : Nat) :=
  eitherEntry.run eitherContext [
    ("isLeft", .bool isLeft),
    ("leftValue", .uint 255 leftValue),
    ("rightValue", .uint 65535 rightValue)
  ] {trees := []}

#guard match Backend.Impact.lower NativeScalarEitherReturns.state eitherEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint NativeScalarEitherReturns.state eitherEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

-- Both directions keep the selected value and zero the inactive side.
#guard match runEither Bool.true 37 513 with
  | .ok (outputs, _) =>
      outputs.lookup "result_is_left" == some (.native 1) &&
      outputs.lookup "result_left" == some (.native 37) &&
      outputs.lookup "result_right" == some (.native 0)
  | .error _ => Bool.false

#guard match runEither Bool.false 37 513 with
  | .ok (outputs, _) =>
      outputs.lookup "result_is_left" == some (.native 0) &&
      outputs.lookup "result_left" == some (.native 0) &&
      outputs.lookup "result_right" == some (.native 513)
  | .error _ => Bool.false

private def eitherId : String :=
  (Either.scalarTypeId "NativeScalarEitherReturns" (.uint 255) (.uint 65535)).toOption.getD ""

private def eitherEnvironment : CompositeEnv :=
  (Either.scalarEnvironment eitherId (.uint 255) (.uint 65535)).toOption.getD {}

private def eitherSchema : Except String Lean.Json := do
  let compiled ← (compileType eitherEnvironment (Either.scalarType eitherId)).mapError (·.message)
  schemaJson compiled

private def entryPlanJson : Except String Lean.Json := do
  let plan ← (Backend.Impact.lower NativeScalarEitherReturns.state eitherEntry).mapError (·.message)
  pure (Compiler.nativePlanJson TargetProfile.selected321 `NativeScalarEitherReturns
    NativeScalarEitherReturns.state none eitherEntry plan)

#guard eitherId == "NativeScalarEitherReturns.EitherLeftUInt8RightUInt16"
#guard match entryPlanJson, eitherSchema with
  | .ok plan, .ok schema =>
      match (plan.getObjVal? "returnViews").toOption, (schema.getObjVal? "layout").toOption with
      | some (.arr #[view]), some layout =>
          view.getObjValD "name" == toJson ("result" : String) &&
          view.getObjValD "schema" == schema &&
          view.getObjValD "fields" == toJson (["result_is_left", "result_left", "result_right"] : List String) &&
          layout.getObjValD "kind" == toJson ("struct" : String) &&
          layout.getObjValD "fields" == toJson ([
            Lean.Json.mkObj [
              ("name", toJson ("is_left" : String)),
              ("layout", Lean.Json.mkObj [
                ("kind", toJson ("scalar" : String)),
                ("leaf", Lean.Json.mkObj [("kind", toJson ("bool" : String))])])],
            Lean.Json.mkObj [
              ("name", toJson ("left" : String)),
              ("layout", Lean.Json.mkObj [
                ("kind", toJson ("scalar" : String)),
                ("leaf", Lean.Json.mkObj [
                  ("kind", toJson ("uint" : String)),
                  ("maximum", toJson ("255" : String))])])],
            Lean.Json.mkObj [
              ("name", toJson ("right" : String)),
              ("layout", Lean.Json.mkObj [
                ("kind", toJson ("scalar" : String)),
                ("leaf", Lean.Json.mkObj [
                  ("kind", toJson ("uint" : String)),
                  ("maximum", toJson ("65535" : String))])])]
          ] : List Lean.Json)
      | _, _ => Bool.false
  | _, _ => Bool.false
