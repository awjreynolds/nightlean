import Noctium.Verification.GenericStateEncoding
import Noctium.Verification.SourceEffects

open Noctium Noctium.Verification.NativeRelation
open Noctium.Verification.NativeState
open Noctium.Verification.GenericStateEncoding

private def declarations : List StateDecl := [
  {name := "counter", kind := .cell .native},
  {name := "flag", kind := .cell .bool},
  {name := "spent", kind := .map .native .bool}
]

private def before : LedgerState := {
  cells := [("counter", .native 0), ("flag", .bool false)],
  maps := [("spent", [])]
}

#guard decide (encodeState declarations before =
  some [.cell (field zero), .cell (field zero), .map []])

#guard decide (encodeState declarations {before with cells :=
  [("counter", .native 0), ("flag", .uint 1 0)]} = none)

#guard decide (encodeState declarations {before with maps :=
  [("spent", [(.native 0, .bool false), (.native 0, .bool true)])]} = none)

private def sequential : List Op := [
  .push (field zero) false, .push (field one) true, .insert 1,
  .dup, .index 0 false, .popeq (field one),
  .dup, .index 2 false, .push (field zero) false, .member, .popeq (boolean false),
  .index 2 true, .push (field zero) false, .push (field one) true, .insert 2
]

example : run sequential (initial [.cell (field zero), .cell (field zero), .map []]) =
    some ⟨[.vector [.cell (field one), .cell (field zero), .map [(zero, one)]]],
      [field one, boolean false]⟩ := by decide +kernel

example : run [.push (field zero) false, .push (field one) true, .insert 1,
    .dup, .index 0 false, .popeq (field zero)]
    (initial [.cell (field zero)]) = none := by decide +kernel

private def ctx : EvalContext := {
  modulus := Field.modulus,
  poseidon2 := fun _ _ _ => .error "hash unused by this fixture"
}

private def effects : List Effect := [
  .writeCell "counter" .native (.native 1),
  .readCell "counter" "seen" .native,
  .require (.eq (.ref "seen" : Expr .native) (.native 1)),
  .requireAbsent "spent" .native (.native 0),
  .writeMap "spent" .native .bool (.native 0) (.bool true)
]

private def afterSource : LedgerState := {
  cells := [("counter", .native 1), ("flag", .bool false)],
  maps := [("spent", [(.native 0, .bool true)])]
}

#guard match runEffects ctx effects [] before with
  | .ok state => state == afterSource
  | .error _ => false
#guard match Noctium.Verification.SourceEffects.fold ctx effects ([], before) with
  | .ok (env, state) => env == [("seen", .native 1)] && state == afterSource
  | .error _ => false

#guard decide (encodeState declarations afterSource =
  some [.cell (field one), .cell (field zero), .map [(zero, one)]])

#guard match runEffects ctx [
  .writeCell "counter" .native (.native 1),
  .require (.eq (.ref "counter" : Expr .native) (.native 1))] [] before with
    | .error _ => true
    | .ok _ => false

#guard match runEffects ctx [
  .writeMap "spent" .native .bool (.native 0) (.bool true),
  .requireAbsent "spent" .native (.native 0)] [] before with
    | .error message => message == "state map key already present"
    | .ok _ => false

private def mixedDeclarations : List StateDecl := [
  {name := "flag", kind := .cell .bool},
  {name := "quota", kind := .cell (.uint 5)},
  {name := "first", kind := .map .native .bool},
  {name := "second", kind := .map (.uint 5) .native}
]

private def mixedBefore : LedgerState := {
  cells := [("flag", .bool false), ("quota", .uint 5 3)],
  maps := [("first", []), ("second", [])]
}

private def mixedEffects : List Effect := [
  .requireAbsent "first" .native (.native 2),
  .writeMap "first" .native .bool (.native 2) (.bool true),
  .requireAbsent "second" (.uint 5) (.uint 5 3),
  .writeMap "second" (.uint 5) .native (.uint 5 3) (.native 4)
]

private def mixedAfter : LedgerState := {
  cells := mixedBefore.cells,
  maps := [("second", [(.uint 5 3, .native 4)]),
    ("first", [(.native 2, .bool true)])]
}

#guard match runEffects ctx mixedEffects [] mixedBefore with
  | .ok state => state == mixedAfter
  | .error _ => false

#guard decide (encodeState mixedDeclarations mixedBefore =
  some [.cell (field zero), .cell (field (scalar 3)), .map [], .map []])
#guard decide (encodeState mixedDeclarations mixedAfter =
  some [.cell (field zero), .cell (field (scalar 3)),
    .map [(scalar 2, one)], .map [(scalar 3, scalar 4)]])

example : run [.index 3 true, .push (field (scalar 3)) false,
    .push (field (scalar 4)) true, .insert 2,
    .index 2 true, .push (field (scalar 2)) false,
    .push (field one) true, .insert 2]
    (initial [.cell (field zero), .cell (field (scalar 3)), .map [], .map []]) =
    some ⟨[.vector [.cell (field zero), .cell (field (scalar 3)),
      .map [(scalar 2, one)], .map [(scalar 3, scalar 4)]]], []⟩ := by
  decide +kernel

example : run [.index 2 true, .push (field (scalar 3)) false,
    .push (field one) true, .insert 2]
    (initial [.cell (field zero), .cell (field (scalar 3)), .map [], .map []]) =
    some ⟨[.vector [.cell (field zero), .cell (field (scalar 3)),
      .map [(scalar 3, one)], .map []]], []⟩ := by
  decide +kernel
