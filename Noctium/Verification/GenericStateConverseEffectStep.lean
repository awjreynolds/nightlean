import Noctium.Verification.GenericStateConverseCandidates
import Noctium.Verification.GenericStateConverseAbsence
import Noctium.Verification.GenericStateConverseRequire
import Noctium.Verification.GenericStateEffectValidation
import Noctium.Verification.GenericStatePrefixEnvironment

namespace Noctium.Verification.GenericStateConverseEffectStep
open Backend NativeRelation ScalarNormalization NativeState
open GenericStatePrefixEnvironment

/-- One successful original effect supplies the exact production native
segment and VM successor, provided its source-read candidate was constructed
from the original state tape. -/
theorem source_effect_native (ctx : EvalContext) (state : List StateDecl)
    (types nextTypes : TypeEnv) (effect : Effect)
    (sourceEnv complete : EvalEnv) (current : LedgerState)
    (sourceAfter : SourceEffects.Frame) (slots : List NativeState.Slot)
    (reads : List NativeState.Cell) (base : Impact.Plan)
    (validated : GenericStateEffectValidation.EffectValidation
      state types effect nextTypes)
    (sourceStep : SourceEffects.step ctx effect (sourceEnv, current) =
      .ok sourceAfter)
    (agrees : AgreesOnTypes types sourceEnv complete)
    (readCandidate : ∀ name destination ty,
      effect = .readCell name destination ty →
      complete.lookup destination = sourceAfter.1.lookup destination)
    (compiled : Impact.appendEffect state effect {} = .ok base)
    (encoded : GenericStateEncoding.encodeState state current = some slots)
    (distinct : state.Pairwise (fun left right => left.name ≠ right.name))
    (stateBound : state.length < Field.modulus)
    (modulus : ctx.modulus = Field.modulus) :
    ∃ segment nextSlots nextReads,
      base.operations.mapM (GenericStateOps.evalOp ctx complete) = .ok segment ∧
      NativeState.run segment ⟨[.vector slots], reads⟩ =
        some ⟨[.vector nextSlots], nextReads⟩ ∧
      GenericStateEncoding.encodeState state sourceAfter.2 = some nextSlots ∧
      AgreesOnTypes nextTypes sourceAfter.1 complete := by
  cases validated with
  | @readCell stateName destination ty declared fresh =>
    obtain ⟨declaration, found, kind⟩ := declared
    have named : declaration.name = stateName := by
      exact beq_iff_eq.mp (List.find?_some
        (p := fun item : StateDecl => item.name == stateName) found)
    obtain ⟨slot, value, located, evaluation, nativeRun, frame⟩ :=
      GenericStateConverseRead.source_readCell_native ctx sourceEnv complete
        state current slots stateName destination ty sourceAfter base reads
        sourceStep (readCandidate stateName destination ty rfl)
        declaration found named kind compiled encoded modulus
    refine ⟨GenericStateVM.readCellOps slot
      (field (scalar (number ty value))), slots,
      reads ++ [field (scalar (number ty value))], evaluation, nativeRun, ?_, ?_⟩
    · rw [frame]
      exact encoded
    · rw [frame]
      apply extend_read types sourceEnv complete destination ty
        (Value.pack ty value) agrees fresh
      rw [readCandidate stateName destination ty rfl, frame]
      simp
  | @readMap stateName destination keyTy valueTy key declared keyValid fresh =>
    simp [Impact.appendEffect] at compiled
  | @require condition conditionValid =>
    have candidateAgreement := eval_scoped types sourceEnv complete agrees ctx
      GenericStateEffectValidation.stateEffectCaps condition conditionValid
    obtain ⟨_, evaluation, nativeRun, frame⟩ :=
      GenericStateConverseRequire.source_require_native ctx sourceEnv complete
        state current slots condition sourceAfter base reads sourceStep
        candidateAgreement.symm compiled
    refine ⟨[], slots, reads, evaluation, nativeRun, ?_, ?_⟩
    · rw [frame]; exact encoded
    · rw [frame]; exact agrees
  | @writeCell stateName ty value declared valueValid =>
    obtain ⟨declaration, found, kind⟩ := declared
    have named : declaration.name = stateName := by
      exact beq_iff_eq.mp (List.find?_some
        (p := fun item : StateDecl => item.name == stateName) found)
    have candidateAgreement := eval_scoped types sourceEnv complete agrees ctx
      GenericStateEffectValidation.stateEffectCaps value valueValid
    obtain ⟨slot, valueFound, nextSlots, _, evaluation, encodedNext,
      nativeRun, frame⟩ :=
      GenericStateConverseWrite.source_writeCell_native ctx sourceEnv complete
        state current slots stateName ty value sourceAfter base reads sourceStep
        candidateAgreement.symm declaration found named kind compiled encoded distinct
        stateBound modulus
    exact ⟨GenericStateVM.writeCellOps slot
      (field (scalar (number ty valueFound))), nextSlots, reads,
      evaluation, nativeRun, encodedNext, by rw [frame]; exact agrees⟩
  | @writeMap stateName keyTy valueTy key value declared keyValid valueValid =>
    obtain ⟨declaration, found, kind⟩ := declared
    have named : declaration.name = stateName := by
      exact beq_iff_eq.mp (List.find?_some
        (p := fun item : StateDecl => item.name == stateName) found)
    have keyAgreement := eval_scoped types sourceEnv complete agrees ctx
      GenericStateEffectValidation.stateEffectCaps key keyValid
    have valueAgreement := eval_scoped types sourceEnv complete agrees ctx
      GenericStateEffectValidation.stateEffectCaps value valueValid
    obtain ⟨slot, keyFound, valueFound, nextSlots, _, evaluation,
      encodedNext, nativeRun, frame⟩ :=
      GenericStateConverseWrite.source_writeMap_native ctx sourceEnv complete
        state current slots stateName keyTy valueTy key value sourceAfter base
        reads sourceStep keyAgreement.symm valueAgreement.symm declaration found named kind
        compiled encoded distinct stateBound modulus
    exact ⟨GenericStateVM.writeMapOps slot (scalar (number keyTy keyFound))
      (scalar (number valueTy valueFound)), nextSlots, reads,
      evaluation, nativeRun, encodedNext, by rw [frame]; exact agrees⟩
  | @requireAbsent stateName keyTy key valueTy declared keyValid =>
    obtain ⟨declaration, found, kind⟩ := declared
    have named : declaration.name = stateName := by
      exact beq_iff_eq.mp (List.find?_some
        (p := fun item : StateDecl => item.name == stateName) found)
    have keyAgreement := eval_scoped types sourceEnv complete agrees ctx
      GenericStateEffectValidation.stateEffectCaps key keyValid
    obtain ⟨slot, keyFound, _, evaluation, nativeRun, frame⟩ :=
      GenericStateConverseAbsence.source_requireAbsent_native ctx sourceEnv complete
        state current slots stateName keyTy valueTy key sourceAfter base reads
        sourceStep keyAgreement.symm declaration found named kind compiled encoded modulus
    exact ⟨GenericStateVM.requireAbsentOps slot (scalar (number keyTy keyFound)),
      slots, reads ++ [boolean false], evaluation, nativeRun,
      by rw [frame]; exact encoded, by rw [frame]; exact agrees⟩

end Noctium.Verification.GenericStateConverseEffectStep
