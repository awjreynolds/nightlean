import Noctium.Backend.Impact

open Noctium
open Noctium.Backend.Impact

private def boundaryState : List StateDecl :=
  [{name := "cell", kind := .cell .native}]

private def boundaryEntry : Entrypoint := {
  name := "boundaryEntry"
  circuit := {
    name := "boundaryEntry"
    inputs := [{name := "enabled", ty := .bool, visibility := .«public»}]}
  effects := [
    .readCell "cell" "before" .native,
    .require (.bool true),
    .writeCell "cell" .native (.native 2)]
  effectGuards := [none, none, some (.ref "enabled")]
}

example (state : List StateDecl) (entry : Entrypoint) :
    lower state entry = (lowerWithEffectBoundaries state entry).map Prod.fst := rfl

#guard match lowerWithEffectBoundaries boundaryState boundaryEntry with
  | .ok (plan, boundaries) =>
    boundaries == [5, 5, 8] && plan.operations.length == 8 &&
      (match lower boundaryState boundaryEntry with
      | .ok ordinary => ordinary.operations.length == plan.operations.length
      | .error _ => false)
  | .error _ => false
