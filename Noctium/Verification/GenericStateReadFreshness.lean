import Noctium.Verification.GenericStateNativeReadNames
import Noctium.Verification.GenericStateOutputEnvironment

namespace Noctium.Verification.GenericStateReadFreshness
open Backend ScalarNormalization

private theorem lookup_none_of_absent_keys (items : List (String × α))
    (name : String) (absent : name ∉ items.map Prod.fst) :
    items.lookup name = none := by
  apply List.lookup_eq_none_iff.mpr
  intro pair member
  have different : name ≠ pair.1 := by
    intro equal
    exact absent (by simpa [equal] using
      (List.mem_map.mpr ⟨pair, member, rfl⟩ : pair.1 ∈ items.map Prod.fst))
  simp [different]

private theorem lookup_member (items : List (String × α))
    (name : String) (value : α)
    (found : items.lookup name = some value) : (name, value) ∈ items := by
  obtain ⟨before, after, equal, _⟩ := List.lookup_eq_some_iff.mp found
  rw [equal]
  simp

theorem source_outputs_names (ctx : EvalContext) (values : EvalEnv)
    (outputs : List Output) (result : EvalEnv)
    (evaluated : outputs.mapM (evalOutput ctx values) = .ok result) :
    result.map Prod.fst = outputs.map (·.name) := by
  induction outputs generalizing result with
  | nil => simp at evaluated; cases evaluated; rfl
  | cons output rest ih =>
    simp only [List.mapM_cons] at evaluated
    cases head : evalOutput ctx values output with
    | error message => simp [head, bind, Except.bind] at evaluated
    | ok pair =>
      cases tail : rest.mapM (evalOutput ctx values) with
      | error message => simp [head, tail, bind, Except.bind] at evaluated
      | ok restResult =>
        simp [head, tail, bind, Except.bind] at evaluated
        cases evaluated
        obtain ⟨value, item⟩ := pair
        unfold evalOutput at head
        cases expression : output.value.eval ctx values with
        | error message => simp [expression, bind, Except.bind] at head
        | ok found =>
          simp [expression, bind, Except.bind] at head
          cases head
          simp [ih restResult tail]

/-- Source output bindings and admitted circuit inputs leave every native
ledger-read name fresh in the actual source-order effect environment. -/
theorem lower_read_base_fresh (state : List StateDecl) (ep : Entrypoint)
    (plan : Impact.Plan) (ctx : EvalContext)
    (values result : EvalEnv) (witness : NativeRelation.Assignment)
    (admitted : CanonicalInputs ep.circuit values witness)
    (lowered : Impact.lower state ep = .ok plan)
    (source : ep.circuit.run ctx values = .ok result) :
    ∀ read ∈ plan.reads.drop
      ((ep.circuit.inputs.filter (·.visibility == .«public»)).length),
      (result ++ values).lookup read.name = none ∧
      (ep.circuit.outputs.map (fun output => (output.name, output.ty)) ++
        ep.circuit.inputs.map (fun input => (input.name, input.ty))).lookup
        read.name = none := by
  have nativeNames := GenericStateNativeReadNames.lower_native_read_names
    state ep plan lowered
  obtain ⟨_, outputEval⟩ :=
    ScalarNormalization.circuit_run_steps ctx ep.circuit values result source
  have resultNames := source_outputs_names ctx values ep.circuit.outputs result outputEval
  intro read member
  have absent := nativeNames.2 read member
  have absentInput : read.name ∉ ep.circuit.inputs.map (·.name) := by
    intro present
    exact absent (List.mem_append_left _ present)
  have absentOutput : read.name ∉ ep.circuit.outputs.map (·.name) := by
    intro present
    exact absent (List.mem_append_right _ present)
  have resultNone : result.lookup read.name = none :=
    lookup_none_of_absent_keys result read.name (by rw [resultNames]; exact absentOutput)
  have valuesNone : values.lookup read.name = none := by
    cases found : values.lookup read.name with
    | none => rfl
    | some raw =>
      obtain ⟨input, inputMember, same⟩ :=
        admitted.declared read.name raw
          (lookup_member values read.name raw found)
      exact False.elim (absentInput (by
        apply List.mem_map.mpr
        exact ⟨input, inputMember, same⟩))
  constructor
  · simp [List.lookup_append, resultNone, valuesNone]
  · have outputNone :
        (ep.circuit.outputs.map (fun output => (output.name, output.ty))).lookup
          read.name = none :=
      lookup_none_of_absent_keys _ read.name (by
        simpa [List.map_map, Function.comp_def] using absentOutput)
    have inputNone :
        (ep.circuit.inputs.map (fun input => (input.name, input.ty))).lookup
          read.name = none :=
      lookup_none_of_absent_keys _ read.name (by
        simpa [List.map_map, Function.comp_def] using absentInput)
    simp [List.lookup_append, outputNone, inputNone]

theorem lower_read_pairwise (state : List StateDecl) (ep : Entrypoint)
    (plan : Impact.Plan) (accepted : Impact.lower state ep = .ok plan) :
    (plan.reads.drop ((ep.circuit.inputs.filter
      (·.visibility == .«public»)).length)).Pairwise
        (fun left right => left.name ≠ right.name) := by
  have unique :=
    (GenericStateNativeReadNames.lower_native_read_names state ep plan accepted).1
  have remainingUnique :
      ((plan.reads.drop ((ep.circuit.inputs.filter
        (·.visibility == .«public»)).length)).map (·.name)).Nodup := by
    rw [List.map_drop]
    exact List.Nodup.sublist
      (List.drop_sublist _ (plan.reads.map (·.name))) unique
  exact List.Pairwise.of_map (fun read : Impact.Read => read.name)
    (by intro left right different; exact different)
    (List.nodup_iff_pairwise_ne.mp remainingUnique)

end Noctium.Verification.GenericStateReadFreshness
