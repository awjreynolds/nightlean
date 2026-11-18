import Noctium.Frontend

open scoped Noctium
open Noctium
open Noctium.Helpers

def nativeBranchProgram : Program := {
  declarations := [{
    id := ⟨0, 0⟩, name := "main"
    parameters := [⟨"enabled", .bool⟩, ⟨"value", .native⟩]
    result := .scalar .native
    body := [
      .bind "outer" (.scalar .native) (.ref "value"),
      .branch (.disclose {} (.ref "enabled")) [
        .bind "outer" (.scalar .native) (.native 99),
        .assert (.eq (.ref "value") (.native 7)),
        .evaluate (.cast (.uint 7) (.ref "value"))] [],
      .return (some (.ref "outer"))]}]
  exports := [{name := "update", target := ⟨0, 0⟩, inputs := [
    {name := "enabled", ty := .bool, visibility := .private},
    {name := "value", ty := .native, visibility := .public}]}]
}

noctium_helper_circuit nativeBranchValues from nativeBranchProgram entry "update"

noctium_contract NativeHelperBranches where
  cell balance : Native
  entry update uses nativeBranchValues where
    if disclose(enabled) then {
      write balance := result
    } else {
    }
    return observed : Native := result
  end
end

private def branchContext : EvalContext := {
  modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "unused"}

private def evaluatesTo (program : Program) (wanted : Noctium.Value) : _root_.Bool :=
  match Helpers.compile program "main" with
  | .ok circuit => match circuit.run branchContext [] with
    | .ok outputs => outputs.lookup "result" == some wanted
    | .error _ => Bool.false
  | .error _ => Bool.false

private def closedBranch (body : List Statement) (result : ResultType := .scalar .native) : Program := {
  declarations := [{id := ⟨0, 0⟩, name := "main", result, body}]
  exports := [{name := "main", target := ⟨0, 0⟩}]
}

#guard evaluatesTo (closedBranch [
  .branch (.bool Bool.true) [.return (some (.native 5))] [],
  .return (some (.native 9))]) (.native 5)

#guard evaluatesTo (closedBranch [.return (some (
  .ite (.bool Bool.false) (.cast (.uint 0) (.native 1)) (.uint 0 0))) ]
    (.scalar (.uint 0))) (.uint 0 0)

#guard evaluatesTo (closedBranch [.return (some (
  .andThen (.bool Bool.false) (.eq (.cast (.uint 0) (.native 1)) (.uint 0 0))))]
    (.scalar .bool)) (.bool Bool.false)

#guard evaluatesTo (closedBranch [.return (some (
  .orElse (.bool Bool.true) (.eq (.cast (.uint 0) (.native 1)) (.uint 0 0))))]
    (.scalar .bool)) (.bool Bool.true)

#guard match Helpers.compile (closedBranch [
  .branch (.bool Bool.false) [.assert (.bool Bool.false)] [], .return none] .unit) "main" with
  | .ok circuit => (circuit.run branchContext []).isOk
  | .error _ => Bool.false

#guard match Helpers.compile {nativeBranchProgram with declarations := [{
    id := ⟨0, 0⟩, name := "main", parameters := [⟨"enabled", .bool⟩, ⟨"value", .native⟩]
    result := .scalar .native
    body := [.branch (.ref "enabled") [.return (some (.native 1))]
      [.return (some (.native 2))]]}]} "update" with
  | .error diagnostic => (diagnostic.message.splitOn "undisclosed private").length > 1
  | .ok _ => Bool.false

private def aggregateBranch : Program := {
  composites := {structures := [{id := "Branch.Pair", fields := [
    ⟨"first", .scalar .native, {}⟩, ⟨"second", .scalar .native, {}⟩]}]}
  declarations := [{
    id := ⟨0, 0⟩
    name := "main"
    result := .composite (.structure "Branch.Pair")
    body := [.return (some (.ite (.bool Bool.true)
      (.composite (.structure "Branch.Pair") [.native 1, .native 2])
      (.composite (.structure "Branch.Pair") [.native 3, .native 4])))]}]
  exports := [{name := "main", target := ⟨0, 0⟩}]
}

#guard match Helpers.compile aggregateBranch "main" with
  | .ok circuit => match circuit.run branchContext [] with
    | .ok outputs => outputs.map (·.2) == [.native 1, .native 2]
    | .error _ => Bool.false
  | .error _ => Bool.false

#guard match Helpers.compile (closedBranch [
  .branch (.bool Bool.true) [.assert (.bool Bool.false)] [], .return none] .unit) "main" with
  | .ok circuit => match circuit.run branchContext [] with
    | .error _ => Bool.true
    | .ok _ => Bool.false
  | .error _ => Bool.false

private def emptyBranch (enabled : _root_.Bool) : Program := {
  declarations := [
    {id := ⟨0, 0⟩, name := "main", result := .composite (.tuple []), body := [
      .branch (.bool enabled) [.evaluate (.call "failure" [])] [],
      .return (some (.composite (.tuple []) []))]},
    {id := ⟨0, 1⟩, name := "failure", result := .unit, body := [.assert (.bool Bool.false)]}]
  exports := [{name := "main", target := ⟨0, 0⟩}]
}

#guard match Helpers.compile (emptyBranch Bool.false) "main" with
  | .ok circuit => (circuit.run branchContext []).isOk
  | .error _ => Bool.false

#guard match Helpers.compile (emptyBranch Bool.true) "main" with
  | .ok circuit => match circuit.run branchContext [] with
    | .error _ => Bool.true
    | .ok _ => Bool.false
  | .error _ => Bool.false

#guard match Helpers.compile (closedBranch [
  .branch (.bool Bool.true) [
    .bind "local" (.scalar .native) (.native 1),
    .bind "local" (.scalar .native) (.native 2)] [],
  .return (some (.native 0))]) "main" with
  | .error diagnostic => (diagnostic.message.splitOn "duplicate helper value").length > 1
  | .ok _ => Bool.false
