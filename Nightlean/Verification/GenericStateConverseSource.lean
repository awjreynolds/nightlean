import Nightlean.Verification.GenericStateConverseInitialEnvironment
import Nightlean.Verification.GenericStateSourceReadInputs
import Nightlean.Verification.GenericStateReadAssignment

namespace Nightlean.Verification.GenericStateConverseSource
open Backend ScalarNormalization

/-- A successful original call determines the source read tape without
assuming any native relation result or desired native state. -/
theorem source_read_tape_of_entry_run (ctx : EvalContext)
    (entry : Entrypoint) (values outputs : EvalEnv)
    (initial next : LedgerState)
    (success : entry.run ctx values initial = .ok (outputs, next)) :
    ∃ finalEnv entries,
      entry.circuit.run ctx values = .ok outputs ∧
      GenericStateSourceReadInputs.sourceReadInputs ctx entry.effects
        ((entry.circuit.inputs.filter (·.visibility == .«public»)).length)
        (outputs ++ values, initial) = .ok (entries, (finalEnv, next)) := by
  unfold Entrypoint.run at success
  cases disclosure : Disclosure.entrypoint entry with
  | error diagnostic =>
    simp [disclosure, throw, throwThe, bind, Except.bind] at success
  | ok disclosureUnit =>
    cases circuit : entry.circuit.run ctx values with
    | error message =>
      simp [disclosure, circuit, bind, Except.bind] at success
    | ok result =>
      cases effects : runEffects ctx entry.effects (result ++ values) initial with
      | error message =>
        simp [disclosure, circuit, effects, bind, Except.bind] at success
      | ok finalState =>
        simp [disclosure, circuit, effects, bind, Except.bind] at success
        cases success
        obtain ⟨finalEnv, fold⟩ :=
          (SourceEffects.runEffects_ok_iff ctx entry.effects
            (outputs ++ values) initial next).mp effects
        obtain ⟨entries, instrumented⟩ :=
          GenericStateSourceReadInputs.sourceReadInputs_of_fold ctx
            entry.effects
            ((entry.circuit.inputs.filter (·.visibility == .«public»)).length)
            (outputs ++ values, initial) (finalEnv, next) fold
        exact ⟨finalEnv, entries, rfl, instrumented⟩

/-- The original successful call determines one bounded assignment whose
read metadata matches the accepted production plan. All declared circuit
input values survive the new read bindings. -/
theorem source_assignment_of_entry_run (ctx : EvalContext)
    (state : List StateDecl) (entry : Entrypoint) (plan : Impact.Plan)
    (values outputs : EvalEnv) (initial next : LedgerState)
    (inputs : NativeRelation.Assignment)
    (accepted : Impact.lower state entry = .ok plan)
    (modulus : ctx.modulus = Field.modulus)
    (success : entry.run ctx values initial = .ok (outputs, next)) :
    ∃ finalEnv entries,
      entry.circuit.run ctx values = .ok outputs ∧
      GenericStateSourceReadInputs.sourceReadInputs ctx entry.effects
        ((entry.circuit.inputs.filter (·.visibility == .«public»)).length)
        (outputs ++ values, initial) = .ok (entries, (finalEnv, next)) ∧
      entries.map Prod.fst = plan.reads.drop
        ((entry.circuit.inputs.filter (·.visibility == .«public»)).length) ∧
      (∀ pair ∈ entries, pair.2.val ≤ Native.sourceMaximum pair.1.ty) ∧
      (GenericStateReadAssignment.keys entries).Nodup ∧
      (∀ input ∈ entry.circuit.inputs,
        GenericStateReadAssignment.assign inputs entries
          ("%input_" ++ input.name) = inputs ("%input_" ++ input.name)) := by
  obtain ⟨finalEnv, entries, circuit, instrumented⟩ :=
    source_read_tape_of_entry_run ctx entry values outputs initial next success
  refine ⟨finalEnv, entries, circuit, instrumented, ?_, ?_, ?_, ?_⟩
  · rw [GenericStateReadTape.lower_read_chunks state entry plan accepted]
    exact GenericStateSourceReadInputs.sourceReadInputs_names ctx entry.effects
      ((entry.circuit.inputs.filter (·.visibility == .«public»)).length)
      (outputs ++ values, initial) (finalEnv, next) entries instrumented
  · exact GenericStateSourceReadInputs.sourceReadInputs_bounds ctx entry.effects
      ((entry.circuit.inputs.filter (·.visibility == .«public»)).length)
      (outputs ++ values, initial) (finalEnv, next) entries modulus instrumented
  · exact GenericStateReadAssignment.sourceReadInputs_distinct state entry plan ctx
      (outputs ++ values, initial) (finalEnv, next) entries accepted instrumented
  · intro input present
    exact GenericStateReadAssignment.assign_circuit_input state entry plan ctx
      (outputs ++ values, initial) (finalEnv, next) entries inputs input present
      accepted instrumented

end Nightlean.Verification.GenericStateConverseSource
