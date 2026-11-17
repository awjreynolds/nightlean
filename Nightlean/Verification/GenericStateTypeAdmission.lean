import Nightlean.Verification.GenericStateAdmission
import Nightlean.Verification.GenericStateAliases

namespace Nightlean.Verification.GenericStateTypeAdmission
open Backend

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

/-- Accepted native lowering validates every cell type and both map types
through the actual source entrypoint validator. -/
theorem validated_state_types (state : List StateDecl) (ep : Entrypoint)
    (plan : Impact.Plan) (accepted : Impact.lower state ep = .ok plan) :
    ∀ decl ∈ state,
      ∀ ty ∈ (match decl.kind with
        | .cell ty => [ty]
        | .map keyTy valueTy => [keyTy, valueTy]),
      ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok () := by
  have source := GenericStateAdmission.lower_source_validated state ep plan accepted
  unfold Entrypoint.validate at source
  simp only [bind_ok] at source
  rcases source with ⟨_, stateChecked, checkedUnit, _, _⟩
  cases checkedUnit
  refine GenericStateAliases.forIn_extract _
    (fun decl => ∀ ty ∈ (match decl.kind with
      | .cell ty => [ty]
      | .map keyTy valueTy => [keyTy, valueTy]),
      ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok ())
    state ?_ stateChecked
  intro decl step success
  simp only [bind_ok] at success
  obtain ⟨result, typesChecked, tail⟩ := success
  cases result
  have stepEqual : step = .yield .unit := by
    change Except.ok (ForInStep.yield PUnit.unit) = Except.ok step at tail
    exact Except.ok.inj tail.symm
  refine ⟨stepEqual, ?_⟩
  refine GenericStateAliases.forIn_extract _
    (fun ty => ty.validate
      {poseidon2 := true, stateCells := true, stateMaps := true} = .ok ())
    _ ?_ typesChecked
  intro ty typeStep success
  cases checked : ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} with
  | error message =>
    simp [checked, throw, throwThe, bind, Except.bind] at success
  | ok result =>
    cases result
    simp only [checked] at success
    change Except.ok (ForInStep.yield PUnit.unit) = Except.ok typeStep at success
    exact ⟨Except.ok.inj success.symm, rfl⟩

end Nightlean.Verification.GenericStateTypeAdmission
