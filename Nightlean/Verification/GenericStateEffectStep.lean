import Nightlean.Verification.GenericStateEffectValidation
import Nightlean.Verification.GenericStateWriteAuthentication
import Nightlean.Verification.GenericStateEvaluationCanonical

namespace Nightlean.Verification.GenericStateEffectStep
open Backend NativeRelation ScalarNormalization NativeState
open GenericStatePrefixEnvironment

/-- The complete relation environment provides a typed candidate for each
source cell read. Its native segment still has to authenticate the value. -/
def ReadCandidate (effect : Effect) (complete : EvalEnv) : Prop :=
  match effect with
  | .readCell _ destination ty =>
    ∃ value : ty.Denote,
      complete.lookup destination = some (Value.pack ty value) ∧
      Canonical ty value
  | _ => True

def GuardTrue (ctx : EvalContext) (effect : Effect) (complete : EvalEnv) : Prop :=
  match effect with
  | .require condition => condition.eval ctx complete = .ok true
  | _ => True

/-- One validated source effect and its actual compiled/evaluated, checked
native segment agree on the next source state, encoding, read tape, and
bindings visible to later effects. -/
theorem checked_effect_step (ctx : EvalContext) (state : List StateDecl)
    (types nextTypes : TypeEnv) (effect : Effect)
    (sourceEnv complete : EvalEnv) (current : LedgerState)
    (slots : List NativeState.Slot) (reads : List NativeState.Cell)
    (base : Impact.Plan) (segment : List NativeState.Op)
    (after : NativeState.Machine)
    (validated : GenericStateEffectValidation.EffectValidation
      state types effect nextTypes)
    (agrees : AgreesOnTypes types sourceEnv complete)
    (readCandidate : ReadCandidate effect complete)
    (guardTrue : GuardTrue ctx effect complete)
    (compiled : Impact.appendEffect state effect {} = .ok base)
    (evaluated : base.operations.mapM (GenericStateOps.evalOp ctx complete) =
      .ok segment)
    (checked : NativeState.run segment ⟨[.vector slots], reads⟩ = some after)
    (encoded : GenericStateEncoding.encodeState state current = some slots)
    (distinct : state.Pairwise (fun left right => left.name ≠ right.name))
    (stateBound : state.length < Field.modulus)
    (modulus : ctx.modulus = Field.modulus) :
    ∃ nextEnv nextState nextSlots nextReads,
      SourceEffects.step ctx effect (sourceEnv, current) =
        .ok (nextEnv, nextState) ∧
      GenericStateEncoding.encodeState state nextState = some nextSlots ∧
      after = ⟨[.vector nextSlots], nextReads⟩ ∧
      AgreesOnTypes nextTypes nextEnv complete := by
  cases validated with
  | @readCell stateName destination ty declared fresh =>
    obtain ⟨declaration, sourceFound, kind⟩ := declared
    obtain ⟨candidate, lookup, canonical⟩ := readCandidate
    obtain ⟨slot, located, _⟩ :=
      GenericStateReadCellEvaluation.readCell_candidate_eval state _ _ _ base
        ctx complete candidate compiled lookup modulus canonical
    have declarationAt := GenericStateAdmission.source_find_matches_slot
      state _ slot declaration sourceFound located
    have named : declaration.name = stateName := by
      have predicate : (declaration.name == stateName) = true :=
        List.find?_some (p := fun (item : StateDecl) => item.name == stateName) sourceFound
      exact beq_iff_eq.mp predicate
    obtain ⟨sourceStep, final⟩ :=
      GenericStateReadAuthentication.readCell_candidate_source_step ctx
        sourceEnv complete state current slots _ _ _ base segment slot candidate
        reads after compiled located declaration declarationAt named kind
        encoded lookup canonical modulus evaluated checked
    refine ⟨(_, Value.pack _ candidate) :: sourceEnv, current, slots,
      reads ++ [NativeState.field (scalar (number _ candidate))],
      sourceStep, encoded, final, ?_⟩
    exact extend_read types sourceEnv complete _ _ _ agrees fresh lookup
  | @readMap stateName destination keyTy valueTy key declared keyValid fresh =>
    simp [Impact.appendEffect] at compiled
  | @require condition conditionValid =>
    have candidateTruth : condition.eval ctx complete = .ok true := guardTrue
    have sourceTruth : condition.eval ctx sourceEnv = .ok true := by
      rw [eval_scoped types sourceEnv complete agrees ctx
        GenericStateEffectValidation.stateEffectCaps _ conditionValid]
      exact candidateTruth
    have sourceStep := GenericStateVM.require_source_step
      ctx sourceEnv current _ sourceTruth
    have noOperations : base.operations = [] := by
      simp [Impact.appendEffect] at compiled
      cases compiled
      rfl
    rw [noOperations] at evaluated
    simp at evaluated
    cases evaluated
    simp [NativeState.run] at checked
    cases checked
    exact ⟨sourceEnv, current, slots, reads, sourceStep, encoded, rfl, agrees⟩
  | @writeCell stateName ty value declared valueValid =>
    obtain ⟨declaration, sourceFound, kind⟩ := declared
    have named : declaration.name = stateName := by
      have predicate : (declaration.name == stateName) = true :=
        List.find?_some (p := fun (item : StateDecl) => item.name == stateName) sourceFound
      exact beq_iff_eq.mp predicate
    obtain ⟨candidate, candidateEval⟩ :=
      GenericStateWriteInversion.writeCell_source_evaluates state _ _ _ base
        ctx complete segment compiled modulus evaluated
    have canonical := GenericStateEvaluationCanonical.expression_eval_canonical
      ctx complete _ candidate modulus candidateEval
    have sourceEval : value.eval ctx sourceEnv = .ok candidate := by
      rw [eval_scoped types sourceEnv complete agrees ctx
        GenericStateEffectValidation.stateEffectCaps _ valueValid]
      exact candidateEval
    obtain ⟨next, nextSlots, sourceStep, nextEncoded, final⟩ :=
      GenericStateWriteAuthentication.writeCell_candidate_source_step ctx
        sourceEnv complete state current slots _ _ _ candidate base segment reads
        after compiled declaration sourceFound named kind distinct encoded
        stateBound modulus candidateEval sourceEval canonical evaluated checked
    exact ⟨sourceEnv, next, nextSlots, reads, sourceStep, nextEncoded, final, agrees⟩
  | @writeMap stateName keyTy valueTy key value declared keyValid valueValid =>
    obtain ⟨declaration, sourceFound, kind⟩ := declared
    have named : declaration.name = stateName := by
      have predicate : (declaration.name == stateName) = true :=
        List.find?_some (p := fun (item : StateDecl) => item.name == stateName) sourceFound
      exact beq_iff_eq.mp predicate
    obtain ⟨candidateKeyValue, candidateMapValue, candidateKey, candidateValue⟩ :=
      GenericStateWriteInversion.writeMap_source_evaluates state _ _ _ _ _
        base ctx complete segment compiled modulus evaluated
    have keyCanonical := GenericStateEvaluationCanonical.expression_eval_canonical
      ctx complete _ candidateKeyValue modulus candidateKey
    have valueCanonical := GenericStateEvaluationCanonical.expression_eval_canonical
      ctx complete _ candidateMapValue modulus candidateValue
    have sourceKey : key.eval ctx sourceEnv = .ok candidateKeyValue := by
      rw [eval_scoped types sourceEnv complete agrees ctx
        GenericStateEffectValidation.stateEffectCaps _ keyValid]
      exact candidateKey
    have sourceValue : value.eval ctx sourceEnv = .ok candidateMapValue := by
      rw [eval_scoped types sourceEnv complete agrees ctx
        GenericStateEffectValidation.stateEffectCaps _ valueValid]
      exact candidateValue
    obtain ⟨next, nextSlots, sourceStep, nextEncoded, final⟩ :=
      GenericStateWriteAuthentication.writeMap_candidate_source_step ctx
        sourceEnv complete state current slots _ _ _ _ _ candidateKeyValue
        candidateMapValue base segment
        reads after compiled declaration sourceFound named kind distinct encoded
        stateBound modulus candidateKey candidateValue sourceKey sourceValue
        keyCanonical valueCanonical evaluated checked
    exact ⟨sourceEnv, next, nextSlots, reads, sourceStep, nextEncoded, final, agrees⟩
  | @requireAbsent stateName keyTy key valueTy declared keyValid =>
    obtain ⟨declaration, sourceFound, kind⟩ := declared
    have named : declaration.name = stateName := by
      have predicate : (declaration.name == stateName) = true :=
        List.find?_some (p := fun (item : StateDecl) => item.name == stateName) sourceFound
      exact beq_iff_eq.mp predicate
    obtain ⟨candidateKey, candidateEval⟩ :=
      GenericStateAbsenceInversion.requireAbsent_source_evaluates state _ _ _
        base ctx complete segment compiled modulus evaluated
    have canonical := GenericStateEvaluationCanonical.expression_eval_canonical
      ctx complete _ candidateKey modulus candidateEval
    have sourceEval : key.eval ctx sourceEnv = .ok candidateKey := by
      rw [eval_scoped types sourceEnv complete agrees ctx
        GenericStateEffectValidation.stateEffectCaps _ keyValid]
      exact candidateEval
    obtain ⟨sourceStep, final⟩ :=
      GenericStateAbsenceAuthentication.requireAbsent_candidate_source_step ctx
        sourceEnv complete state current slots _ _ _ _ candidateKey base segment reads
        after compiled declaration sourceFound named kind encoded modulus
        candidateEval sourceEval canonical evaluated checked
    exact ⟨sourceEnv, current, slots, reads ++ [NativeState.boolean false],
      sourceStep, encoded, final, agrees⟩

end Nightlean.Verification.GenericStateEffectStep
