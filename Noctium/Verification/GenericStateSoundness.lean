import Noctium.Verification.GenericStateLowering
import Noctium.Verification.GenericStateOutputSoundness

namespace Noctium.Verification.GenericStateSoundness
open NativeRelation ScalarNormalization

/-- An arbitrary satisfying witness of an actually emitted, strictly decoded
ledger-call relation forces the original source circuit to evaluate. The
named results are internal effect bindings, not ledger public returns. -/
theorem accepted_circuit_run_sound (state : List StateDecl)
    (entry : Entrypoint) (json : Lean.Json) (relation : Program)
    (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash)
    (values : EvalEnv) (witness : Assignment)
    (streams : InputStreams) (publicGroups : List (List Scalar))
    (admitted : CanonicalInputs entry.circuit values witness)
    (lowered : Backend.Zkir.lowerEntrypoint state entry = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (satisfies : CircuitSatisfies hash relation streams witness publicGroups) :
    ∃ result, entry.circuit.run ctx values = .ok result ∧
      result.map Prod.fst = entry.circuit.outputs.map (·.name) := by
  obtain ⟨plan, expected, planAccepted, expectedAccepted,
    groups, bounds, assertions⟩ :=
    GenericStateLowering.accepted_relation_groups_self state entry json relation
      hash witness streams publicGroups lowered decoded satisfies
  have prunedAdmission : CanonicalInputs
      (Passes.pruneEntrypoint entry).circuit values witness := by
    exact ⟨admitted.unique, admitted.declared,
      admitted.complete, admitted.binding⟩
  obtain ⟨result, source, names⟩ :=
    GenericStateOutputSoundness.expected_circuit_run_sound state
      (Passes.pruneEntrypoint entry) expected expectedAccepted ctx hash
      implementation witness values prunedAdmission bounds assertions
  refine ⟨result, ?_, ?_⟩
  · simpa only [Passes.pruneEntrypoint, Passes.pruneCircuit_run] using source
  · simpa only [Passes.pruneEntrypoint, Passes.pruneCircuit] using names

end Noctium.Verification.GenericStateSoundness
