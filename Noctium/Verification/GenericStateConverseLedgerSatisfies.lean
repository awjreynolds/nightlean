import Noctium.Verification.ScalarValidation
import Noctium.Verification.ScalarLowering
import Noctium.Verification.NativeState

namespace Noctium.Verification.GenericStateConverseLedgerSatisfies
open Backend NativeRelation ScalarLowering ScalarNormalization

/-- The meaning of the exact production ledger body transfers to every
instruction in its strictly decoded relation. -/
theorem lowered_body_instructions_hold (state : List StateDecl)
    (entry : Entrypoint) (json : Lean.Json) (relation : Program)
    (plan : Impact.Plan) (hash : Hash) (witness : NativeRelation.Assignment)
    (lowered : Zkir.lowerEntrypoint state entry = .ok json)
    (accepted : Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (meaning : LowerStateMeaning hash witness
      ((Zkir.lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {}).2) :
    ∀ instruction ∈ relation.instructions,
      instruction.Holds hash witness := by
  obtain ⟨samePlan, sameAccepted, instructions⟩ :=
    Zkir.lowerEntrypoint_instructions state entry json lowered
  have same : samePlan = plan := by
    rw [accepted] at sameAccepted
    exact (Except.ok.inj sameAccepted).symm
  subst samePlan
  obtain ⟨raw, parsed, trace⟩ := ScalarValidation.decode_result decoded
  rw [instructions] at parsed
  cases parsed
  exact meaning.holds relation.instructions trace

/-- Input streams and Impact groups are observations of the constructed
assignment. The nontrivial obligation is every decoded instruction. -/
theorem lowered_body_circuit_satisfies (state : List StateDecl)
    (entry : Entrypoint) (json : Lean.Json) (relation : Program)
    (plan : Impact.Plan) (hash : Hash) (witness : NativeRelation.Assignment)
    (lowered : Zkir.lowerEntrypoint state entry = .ok json)
    (accepted : Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (meaning : LowerStateMeaning hash witness
      ((Zkir.lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {}).2) :
    CircuitSatisfies hash relation
      ⟨relation.inputValues .«public» witness,
        relation.inputValues .«private» witness⟩
      witness (relation.groups witness) := by
  refine ⟨lowered_body_instructions_hold state entry json relation plan hash
    witness lowered accepted decoded meaning, rfl, rfl, rfl⟩

/-- The independent producer validator ties decoded Impact observations to
the source-derived expected groups. The VM trace supplies their meaning. -/
theorem lowered_body_authenticated_groups (state : List StateDecl)
    (entry : Entrypoint) (json : Lean.Json) (relation : Program)
    (plan : Impact.Plan) (expected : Backend.Native.Expected)
    (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (native : List NativeState.Op)
    (lowered : Zkir.lowerEntrypoint state entry = .ok json)
    (accepted : Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (validated : Backend.Native.validate expected json = .ok ())
    (inputAgreement : ScalarValidation.InputAgreement expected inputs witness)
    (meaning : LowerStateMeaning hash witness
      ((Zkir.lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {}).2)
    (sourceGroups : expected.groups.map (List.map (interpret hash inputs)) =
      NativeState.groups native) :
    relation.groups witness = NativeState.groups native := by
  have holds := lowered_body_instructions_hold state entry json relation plan hash
    witness lowered accepted decoded meaning
  exact (ScalarValidation.validate_observations inputAgreement validated decoded holds).1.trans
    sourceGroups

end Noctium.Verification.GenericStateConverseLedgerSatisfies
