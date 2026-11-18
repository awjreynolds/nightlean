import Noctium.Verification.GenericStateConverseResult
import Noctium.Verification.GenericStateLowering

namespace Noctium.Verification.GenericStateConverseLowered
open Backend NativeRelation ScalarNormalization NativeState Backend.Native

/-- Actual accepted ZKIR lowering fixes the pruned plan and independent
expected ledger statement. Original source success supplies
their bounded meaning and checked native execution. -/
theorem lowered_source_expected_checked (state : List StateDecl)
    (entry : Entrypoint) (json : Lean.Json) (relation : Program)
    (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash)
    (values outputs : EvalEnv) (inputs : Assignment)
    (initial next : LedgerState) (slots : List Slot)
    (admittedInputs : CanonicalInputs entry.circuit values inputs)
    (admittedState : GenericStateEncoding.AdmittedState state initial slots)
    (lowered : Zkir.lowerEntrypoint state entry = .ok json)
    (_decoded : NativeRelationJson.decode json = .ok relation)
    (modulus : ctx.modulus = Field.modulus)
    (source : entry.run ctx values initial = .ok (outputs, next)) :
    ∃ plan expected witness native finalSlots finalReads,
      Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) =
        .ok expected ∧
      Native.validate expected json = .ok () ∧
      GenericStateCheckedSchedule.CheckedPlan ctx
        (Passes.pruneEntrypoint entry) plan values witness slots
        ⟨[.vector finalSlots], finalReads⟩ ∧
      GenericStateEncoding.encodeState state next = some finalSlots ∧
      CanonicalInputs (Passes.pruneEntrypoint entry).circuit values witness ∧
      (∀ requirement ∈ expected.bounds,
        (interpret hash witness requirement.1).val ≤ requirement.2) ∧
      (∀ assertion ∈ expected.assertions,
        interpret hash witness assertion = one) ∧
      expected.groups.map (fun group => group.map (interpret hash witness)) =
        NativeState.groups native ∧
      GenericStateOps.evalPlan ctx
        (GenericStateCheckedSchedule.outputCandidates ctx
          (Passes.pruneEntrypoint entry) values ++
          GenericStateInputValues.decodeReads
            (plan.reads.drop
              (((Passes.pruneEntrypoint entry).circuit.inputs.filter
                (·.visibility == .«public»)).length)) witness) plan =
        .ok native := by
  obtain ⟨plan, expected, planAccepted, expectedAccepted, producerAccepted⟩ :=
    GenericStateLowering.lowerEntrypoint_validated state entry json lowered
  have admittedPruned : CanonicalInputs
      (Passes.pruneEntrypoint entry).circuit values inputs :=
    ⟨admittedInputs.unique, admittedInputs.declared,
      admittedInputs.complete, admittedInputs.binding⟩
  have sourcePruned : (Passes.pruneEntrypoint entry).run ctx values initial =
      .ok (outputs, next) := by
    simpa only [Passes.pruneEntrypoint_run] using source
  obtain ⟨finalEnv, entries, witness, native, finalSlots, finalReads,
    instrumented, witnessShape, checked, encoded, canonical,
    expectedBounds, expectedAssertions, expectedGroups, planEval⟩ :=
    GenericStateConverseResult.source_call_expected_checked state
      (Passes.pruneEntrypoint entry) plan expected ctx hash implementation
      values outputs inputs initial next slots admittedPruned admittedState
      planAccepted expectedAccepted modulus sourcePruned
  exact ⟨plan, expected, witness, native, finalSlots, finalReads,
    planAccepted, expectedAccepted, producerAccepted, checked, encoded,
    canonical, expectedBounds, expectedAssertions, expectedGroups, planEval⟩

end Noctium.Verification.GenericStateConverseLowered
