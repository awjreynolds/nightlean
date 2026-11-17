import Nightlean.Backend.Zkir
import Nightlean.Verification.ScalarValidation

namespace Nightlean.Verification.GenericStateLowering
open Backend

private theorem bind_ok {α β : Type} {first : Except ε α} {next : α → Except ε β}
    {result : β} : (first >>= next) = .ok result ↔
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

/-- An accepted ledger-call relation passed the actual independent expected
statement and mandatory native producer validator. The statement is derived
from the pruned source and ordered Impact plan. -/
theorem lowerEntrypoint_validated (state : List StateDecl) (entry : Entrypoint)
    (json : Lean.Json) (lowered : Zkir.lowerEntrypoint state entry = .ok json) :
    ∃ plan expected,
      Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected ∧
      Native.validate expected json = .ok () := by
  simp only [Zkir.lowerEntrypoint, bind_ok] at lowered
  rcases lowered with ⟨plan, planAccepted, remaining⟩
  split at remaining
  simp only [bind_ok] at remaining
  rcases remaining with ⟨expected, expectedAccepted, accepted⟩
  obtain ⟨same, checked⟩ := (Zkir.validateProduced_ok _ _ _ _).mp accepted
  subst json
  exact ⟨plan, expected, planAccepted, expectedAccepted, checked⟩

/-- The actual accepted lowering fixes every native opcode group's field
values through the mandatory validator. InputAgreement binds the declared
public/private and ledger-read input names to the supplied assignment. -/
theorem accepted_relation_groups (state : List StateDecl) (entry : Entrypoint)
    (json : Lean.Json) (relation : NativeRelation.Program)
    (hash : NativeRelation.Hash) (inputs witness : NativeRelation.Assignment)
    (streams : NativeRelation.InputStreams)
    (publicGroups : List (List NativeRelation.Scalar))
    (lowered : Zkir.lowerEntrypoint state entry = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (satisfies : NativeRelation.CircuitSatisfies hash relation streams witness publicGroups)
    (binding : ∀ expected, Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected →
      ScalarValidation.InputAgreement expected inputs witness) :
    ∃ plan expected,
      Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected ∧
      publicGroups = expected.groups.map (List.map (ScalarNormalization.interpret hash inputs)) ∧
      (∀ requirement ∈ expected.bounds,
        (ScalarNormalization.interpret hash inputs requirement.1).val ≤ requirement.2) ∧
      (∀ assertion ∈ expected.assertions,
        ScalarNormalization.interpret hash inputs assertion = NativeRelation.one) := by
  obtain ⟨plan, expected, planAccepted, expectedAccepted, validated⟩ :=
    lowerEntrypoint_validated state entry json lowered
  have relationFacts := ScalarValidation.validate_sound (binding expected expectedAccepted)
    validated decoded satisfies
  exact ⟨plan, expected, planAccepted, expectedAccepted,
    relationFacts.groups, relationFacts.requirements.bounds,
    relationFacts.requirements.assertions⟩

/-- Interpreting the native terms under the actual satisfying witness needs
no separate agreement assumption. -/
theorem accepted_relation_groups_self (state : List StateDecl) (entry : Entrypoint)
    (json : Lean.Json) (relation : NativeRelation.Program)
    (hash : NativeRelation.Hash) (witness : NativeRelation.Assignment)
    (streams : NativeRelation.InputStreams)
    (publicGroups : List (List NativeRelation.Scalar))
    (lowered : Zkir.lowerEntrypoint state entry = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (satisfies : NativeRelation.CircuitSatisfies hash relation streams witness publicGroups) :
    ∃ plan expected,
      Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected ∧
      publicGroups = expected.groups.map (List.map (ScalarNormalization.interpret hash witness)) ∧
      (∀ requirement ∈ expected.bounds,
        (ScalarNormalization.interpret hash witness requirement.1).val ≤ requirement.2) ∧
      (∀ assertion ∈ expected.assertions,
        ScalarNormalization.interpret hash witness assertion = NativeRelation.one) := by
  exact accepted_relation_groups state entry json relation hash witness witness streams
    publicGroups lowered decoded satisfies (by intro expected _ requirement _; rfl)

/-- The mandatory native producer also constrains every declared circuit and
ledger-read input to its source type's numeric range. This is derived from
the same arbitrary satisfying assignment, not an extra range assumption. -/
theorem accepted_relation_input_bounds_self (state : List StateDecl)
    (entry : Entrypoint) (json : Lean.Json) (relation : NativeRelation.Program)
    (hash : NativeRelation.Hash) (witness : NativeRelation.Assignment)
    (streams : NativeRelation.InputStreams)
    (publicGroups : List (List NativeRelation.Scalar))
    (lowered : Zkir.lowerEntrypoint state entry = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (satisfies : NativeRelation.CircuitSatisfies hash relation streams witness publicGroups) :
    ∃ expected,
      Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) = .ok expected ∧
      ∀ requirement ∈ expected.inputs,
        (witness requirement.identifier).val ≤ Native.sourceMaximum requirement.ty := by
  obtain ⟨plan, expected, _, expectedAccepted, validated⟩ :=
    lowerEntrypoint_validated state entry json lowered
  have relationFacts := ScalarValidation.validate_sound
    (by intro requirement _; rfl) validated decoded satisfies
  exact ⟨expected, expectedAccepted, relationFacts.requirements.inputBounds⟩

end Nightlean.Verification.GenericStateLowering
