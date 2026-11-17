import Nightlean.Frontend
import Nightlean.Backend.Zkir
import Nightlean.Verification.NativeRelationJson
import Nightlean.Verification.GenericStateOps
import Nightlean.Verification.GenericStateInputValues
import Nightlean.Verification.GenericStateEncoding

open scoped Nightlean
open Nightlean Nightlean.Verification
open Nightlean.Verification.NativeRelation
open Nightlean.Verification.NativeState

nightlean_circuit issue66OutputCircuit where
  public supplied : Native
  output selected : Native := add(supplied, 1)
end

nightlean_contract Issue66OutputState where
  cell counter : Native
  entry apply uses issue66OutputCircuit where
    write counter := selected
    read counter as observed
    require eq(observed, selected)
  end
end

private def issue66OutputEntry : Entrypoint :=
  match Issue66OutputState.entrypoints with
  | ep :: _ => ep
  | _ => {name := "missing", circuit := {name := "missing"}}

private def issue66OutputContext : EvalContext :=
  { modulus := Field.modulus,
    poseidon2 := fun _ _ _ => .error "unused by this fixture" }

private def issue66OutputBefore : LedgerState :=
  { cells := [("counter", .native 0)] }

#guard match issue66OutputEntry.run issue66OutputContext
    [("supplied", .native 4)] issue66OutputBefore with
  | .ok (outputs, next) =>
    outputs.lookup "selected" == some (.native 5) &&
    next.cells.lookup "counter" == some (.native 5)
  | .error _ => Bool.false

#guard match Backend.Impact.lower Issue66OutputState.state issue66OutputEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint Issue66OutputState.state issue66OutputEntry with
  | .ok json =>
    match NativeRelationJson.decode json with
    | .ok _ => Bool.true
    | .error _ => Bool.false
  | .error _ => Bool.false

private def issue66OutputWitness (name : String) : Scalar :=
  if name == "%input_supplied" then scalar 4 else
  if name == "%input_observed" then scalar 5 else zero

private def issue66OutputNativeRun (witness : Assignment) : Option Machine :=
  match Backend.Impact.lower Issue66OutputState.state issue66OutputEntry with
  | .error _ => none
  | .ok plan =>
    let reads := plan.reads.drop
      ((issue66OutputEntry.circuit.inputs.filter (·.visibility == .«public»)).length)
    let env := [("selected", Value.native 5), ("supplied", Value.native 4)] ++
      GenericStateInputValues.decodeReads reads witness
    match GenericStateOps.evalPlan issue66OutputContext env plan with
    | .error _ => none
    | .ok operations => run operations
        (GenericStateEncoding.initial [.cell (field zero)])

#guard decide (issue66OutputNativeRun issue66OutputWitness =
  some ⟨[.vector [.cell (field (scalar 5))]],
    [field (scalar 4), field (scalar 5)]⟩)

#guard decide (issue66OutputNativeRun (fun name =>
  if name == "%input_observed" then scalar 6 else
    issue66OutputWitness name) = none)

-- Public source inputs enter the Impact plan from the supplied source values.
-- Their relation assignment is bound separately by CanonicalInputs.
#guard decide (issue66OutputNativeRun (fun name =>
  if name == "%input_supplied" then scalar 6 else
    issue66OutputWitness name) =
  some ⟨[.vector [.cell (field (scalar 5))]],
    [field (scalar 4), field (scalar 5)]⟩)
