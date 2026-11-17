import Nightlean.Verification.GenericStateOps
import Nightlean.Verification.GenericStateVM
import Nightlean.Verification.GenericStateCaps
import Nightlean.Verification.GenericStateAliases
import Nightlean.Backend.NativeExpected
import Nightlean.Verification.ScalarNormalizationSoundness

namespace Nightlean.Verification.GenericStateAdmission
open Backend

private theorem bind_ok {α β : Type} {first : Except ε α} {next : α → Except ε β}
    {result : β} : (first >>= next) = .ok result ↔
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

theorem finishPlan_validated (ep : Entrypoint) (result : Except String Impact.Plan)
    (plan : Impact.Plan) (accepted : Impact.finishPlan ep result = .ok plan) :
    plan.validate ep = .ok () := by
  cases result with
  | error message => simp [Impact.finishPlan] at accepted
  | ok candidate =>
    simp only [Impact.finishPlan] at accepted
    cases valid : candidate.validate ep with
    | error message => simp [valid] at accepted
    | ok checkedUnit =>
      cases checkedUnit
      simp [valid] at accepted
      cases accepted
      exact valid

/-- Successful production Impact lowering passed the production plan validator. -/
theorem lower_validated (state : List StateDecl) (ep : Entrypoint)
    (plan : Impact.Plan) (accepted : Impact.lower state ep = .ok plan) :
    plan.validate ep = .ok () := by
  unfold Impact.lower at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨_, _, _, _, finished⟩
  exact finishPlan_validated ep _ plan finished

/-- Production Impact lowering first ran the source entrypoint's typed,
ordered state-effect validator on this exact declaration schema. -/
theorem lower_source_validated (state : List StateDecl) (ep : Entrypoint)
    (plan : Impact.Plan) (accepted : Impact.lower state ep = .ok plan) :
    ep.validate {poseidon2 := true, stateCells := true, stateMaps := true} state =
      .ok () := by
  unfold Impact.lower at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨_, validated, _, _, _⟩
  exact validated

theorem lower_circuit_validated (state : List StateDecl) (ep : Entrypoint)
    (plan : Impact.Plan) (accepted : Impact.lower state ep = .ok plan) :
    ep.circuit.validate {poseidon2 := true} = .ok () := by
  have source := lower_source_validated state ep plan accepted
  unfold Entrypoint.validate at source
  simp only [bind_ok] at source
  rcases source with ⟨_, _, checkedUnit, circuitChecked, _⟩
  cases checkedUnit
  rw [GenericStateCaps.circuit_validate_state_caps] at circuitChecked
  exact circuitChecked

theorem lower_output_names_unused (state : List StateDecl) (ep : Entrypoint)
    (plan : Impact.Plan) (values : EvalEnv)
    (inputs : NativeRelation.Assignment)
    (admitted : ScalarNormalization.CanonicalInputs ep.circuit values inputs)
    (accepted : Impact.lower state ep = .ok plan) :
    ∀ output ∈ ep.circuit.outputs, values.lookup output.name = none := by
  exact GenericStateAliases.canonicalInputs_output_unused ep.circuit values
    inputs admitted (lower_circuit_validated state ep plan accepted)

/-- The production public-input prefix consists of matched push/equality
pairs. This is a structural property of the actual fold, independent of
source return values or ledger state. -/
theorem publicInputPlan_pairs (inputs : List Input) (initial : Impact.Plan) :
    ∃ values : List Impact.Aligned,
      (Impact.publicInputPlan inputs initial).operations = initial.operations ++
        values.flatMap (fun value => [.push value, .popeq value]) := by
  induction inputs generalizing initial with
  | nil => exact ⟨[], by simp [Impact.publicInputPlan]⟩
  | cons input rest ih =>
    let middle := Impact.publicInputPlan [input] initial
    obtain ⟨values, restShape⟩ := ih middle
    have foldShape : Impact.publicInputPlan (input :: rest) initial =
        Impact.publicInputPlan rest middle := rfl
    rw [foldShape, restShape]
    cases input with
    | mk name ty visibility span =>
      cases visibility with
      | «private» =>
        refine ⟨values, ?_⟩
        have unchanged : middle.operations = initial.operations := by
          rfl
        rw [unchanged]
      | «public» =>
        have one : ∃ value : Impact.Aligned,
            middle.operations = initial.operations ++ [.push value, .popeq value] := by
          exact ⟨_, rfl⟩
        obtain ⟨value, shape⟩ := one
        refine ⟨value :: values, ?_⟩
        rw [shape]
        simp [List.append_assoc]

private theorem eval_public_pair (ctx : EvalContext) (env : EvalEnv)
    (value : Impact.Aligned) (ops : List NativeState.Op)
    (accepted : [Impact.Op.push value, .popeq value].mapM
      (GenericStateOps.evalOp ctx env) = .ok ops) :
    ∃ cell, ops = [.push cell false, .popeq cell] := by
  cases evaluated : GenericStateOps.evalAligned ctx env value with
  | error message =>
    simp [List.mapM_cons, GenericStateOps.evalOp, evaluated,
      Except.bind, Except.map, Functor.map] at accepted
    change (Except.error message : Except String (List NativeState.Op)) =
      .ok ops at accepted
    cases accepted
  | ok cell =>
    simp [List.mapM_cons, GenericStateOps.evalOp, evaluated,
      Except.bind, Except.map, Functor.map] at accepted
    change (Except.ok [.push cell false, .popeq cell] :
      Except String (List NativeState.Op)) = .ok ops at accepted
    exact ⟨cell, (Except.ok.inj accepted).symm⟩

theorem eval_public_pairs (ctx : EvalContext) (env : EvalEnv)
    (values : List Impact.Aligned) (ops : List NativeState.Op)
    (evaluated : (values.flatMap (fun value =>
      [Impact.Op.push value, .popeq value])).mapM
      (GenericStateOps.evalOp ctx env) = .ok ops) :
    ∃ cells : List NativeState.Cell,
      ops = cells.flatMap (fun cell =>
        [NativeState.Op.push cell false, .popeq cell]) := by
  induction values generalizing ops with
  | nil =>
    simp at evaluated
    cases evaluated
    exact ⟨[], rfl⟩
  | cons value rest ih =>
    simp only [List.flatMap_cons, List.mapM_append, bind_ok] at evaluated
    rcases evaluated with ⟨first, pairAccepted, remaining, restAccepted, result⟩
    obtain ⟨cell, pairShape⟩ := eval_public_pair ctx env value first pairAccepted
    obtain ⟨cells, restShape⟩ := ih remaining restAccepted
    cases result
    exact ⟨cell :: cells, by simp [pairShape, restShape]⟩

/-- The evaluated production public-input prefix records each consumed
public value in the read tape and leaves the native root and stack intact. -/
theorem public_prefix_run (inputs : List Input)
    (ctx : EvalContext) (env : EvalEnv) (ops : List NativeState.Op)
    (stack : List NativeState.Node) (reads : List NativeState.Cell)
    (evaluated : (Impact.publicInputPlan inputs {}).operations.mapM
      (GenericStateOps.evalOp ctx env) = .ok ops) :
    ∃ cells : List NativeState.Cell,
      ops = cells.flatMap (fun cell =>
        [NativeState.Op.push cell false, .popeq cell]) ∧
      NativeState.run ops ⟨stack, reads⟩ =
        some ⟨stack, reads ++ cells⟩ := by
  obtain ⟨aligned, shape⟩ := publicInputPlan_pairs inputs {}
  simp only [Impact.Plan.operations] at shape
  rw [shape] at evaluated
  simp only [List.nil_append] at evaluated
  obtain ⟨cells, nativeShape⟩ := eval_public_pairs ctx env aligned ops evaluated
  refine ⟨cells, nativeShape, ?_⟩
  rw [nativeShape]
  exact GenericStateVM.run_input_pairs cells stack reads

private theorem finishPlan_result (ep : Entrypoint) (result : Except String Impact.Plan)
    (plan : Impact.Plan) (accepted : Impact.finishPlan ep result = .ok plan) :
    result = .ok plan := by
  cases result with
  | error message => simp [Impact.finishPlan] at accepted
  | ok candidate =>
    simp only [Impact.finishPlan] at accepted
    cases valid : candidate.validate ep with
    | error message => simp [valid] at accepted
    | ok checked =>
      cases checked
      simp [valid] at accepted
      cases accepted
      rfl

/-- An accepted production plan arose from the actual public-input prefix
followed by the ordered effect fold. -/
theorem lower_effect_fold (state : List StateDecl) (ep : Entrypoint)
    (plan : Impact.Plan) (accepted : Impact.lower state ep = .ok plan) :
    Impact.appendEffects state ep.effects
      (Impact.publicInputPlan ep.circuit.inputs {}) = .ok plan := by
  unfold Impact.lower at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨_, _, _, _, finished⟩
  have result := finishPlan_result ep _ plan finished
  split at result
  · simp [bind, Except.bind] at result
  · simpa only [bind_pure] using result

/-- The production effect helper appends an operation chunk independent of
the accumulator. Read names and guards still use the live plan. -/
theorem appendEffect_operations (state : List StateDecl) (effect : Effect)
    (before : Impact.Plan) :
    Impact.Plan.operations <$> Impact.appendEffect state effect before =
      (fun base => before.operations ++ base.operations) <$>
        Impact.appendEffect state effect {} := by
  cases effect <;>
    simp only [Impact.appendEffect, map_bind,
      LawfulApplicative.map_pure, pure_bind, List.append_nil] <;> rfl

def effectChunks (state : List StateDecl) (effects : List Effect) :
    Except String (List (List Impact.Op)) :=
  effects.mapM fun effect => Impact.Plan.operations <$> Impact.appendEffect state effect {}

def EffectChunk (state : List StateDecl) (effect : Effect)
    (operations : List Impact.Op) : Prop :=
  ∃ base, Impact.appendEffect state effect {} = .ok base ∧
    base.operations = operations

inductive AlignedChunks (state : List StateDecl) :
    List Effect → List (List Impact.Op) → Prop where
  | nil : AlignedChunks state [] []
  | cons {effect rest operations chunks}
      (first : EffectChunk state effect operations)
      (remaining : AlignedChunks state rest chunks) :
      AlignedChunks state (effect :: rest) (operations :: chunks)

inductive EvaluatedChunks (state : List StateDecl)
    (ctx : EvalContext) (values : EvalEnv) :
    List Effect → List (List NativeState.Op) → Prop where
  | nil : EvaluatedChunks state ctx values [] []
  | cons {effect rest operations segments} (base : Impact.Plan)
      (compiled : Impact.appendEffect state effect {} = .ok base)
      (evaluated : base.operations.mapM (GenericStateOps.evalOp ctx values) =
        .ok operations)
      (remaining : EvaluatedChunks state ctx values rest segments) :
      EvaluatedChunks state ctx values (effect :: rest) (operations :: segments)

theorem alignedChunks_eval (state : List StateDecl)
    (ctx : EvalContext) (values : EvalEnv)
    (effects : List Effect) (chunks : List (List Impact.Op))
    (segments : List (List NativeState.Op))
    (aligned : AlignedChunks state effects chunks)
    (evaluated : chunks.mapM (fun chunk => chunk.mapM
      (GenericStateOps.evalOp ctx values)) = .ok segments) :
    EvaluatedChunks state ctx values effects segments := by
  induction aligned generalizing segments with
  | nil =>
    simp at evaluated
    cases evaluated
    exact .nil
  | @cons effect rest operations chunks first remaining ih =>
    simp only [List.mapM_cons, bind_ok] at evaluated
    rcases evaluated with ⟨head, headEval, tail, tailEval, result⟩
    cases result
    obtain ⟨base, compiled, shape⟩ := first
    rw [← shape] at headEval
    exact .cons base compiled headEval (ih tail tailEval)

theorem effectChunks_aligned (state : List StateDecl)
    (effects : List Effect) (chunks : List (List Impact.Op))
    (accepted : effectChunks state effects = .ok chunks) :
    AlignedChunks state effects chunks := by
  induction effects generalizing chunks with
  | nil =>
    simp [effectChunks] at accepted
    cases accepted
    exact .nil
  | cons effect rest ih =>
    simp only [effectChunks, List.mapM_cons, bind_ok] at accepted
    rcases accepted with ⟨head, headAccepted, remaining, tailAccepted, result⟩
    cases result
    cases one : Impact.appendEffect state effect {} with
    | error message => simp [one, Except.map, Functor.map] at headAccepted
    | ok base =>
      simp [one, Except.map, Functor.map] at headAccepted
      cases headAccepted
      exact .cons ⟨base, one, rfl⟩ (ih remaining tailAccepted)

/-- Successful production effect lowering fixes every operation chunk and
their concatenation in source order. First-error behavior is inherited from
the same `appendEffect` call used by the compiler. -/
theorem appendEffects_operations (state : List StateDecl) (effects : List Effect)
    (before after : Impact.Plan)
    (accepted : Impact.appendEffects state effects before = .ok after) :
    ∃ chunks, effectChunks state effects = .ok chunks ∧
      after.operations = before.operations ++ chunks.flatten := by
  induction effects generalizing before with
  | nil =>
    simp [Impact.appendEffects] at accepted
    cases accepted
    exact ⟨[], rfl, by simp⟩
  | cons effect rest ih =>
    simp only [Impact.appendEffects, List.foldlM_cons] at accepted
    cases one : Impact.appendEffect state effect before with
    | error message => simp [one, bind, Except.bind] at accepted
    | ok middle =>
      simp only [one, bind, Except.bind] at accepted
      obtain ⟨remaining, restChunks, restOps⟩ := ih middle accepted
      have shape := appendEffect_operations state effect before
      rw [one] at shape
      cases base : Impact.appendEffect state effect {} with
      | error message => simp [base, Except.map, Functor.map] at shape
      | ok basePlan =>
        simp [base, Except.map, Functor.map] at shape
        refine ⟨basePlan.operations :: remaining, ?_, ?_⟩
        · have restM : rest.mapM (fun effect =>
            Impact.Plan.operations <$> Impact.appendEffect state effect {}) =
              .ok remaining := restChunks
          simp only [effectChunks, List.mapM_cons, base, restM]
          rfl
        · rw [restOps, shape]
          simp [List.append_assoc]

theorem lower_effect_chunks (state : List StateDecl) (ep : Entrypoint)
    (plan : Impact.Plan) (accepted : Impact.lower state ep = .ok plan) :
    ∃ chunks, effectChunks state ep.effects = .ok chunks ∧
      plan.operations =
        (Impact.publicInputPlan ep.circuit.inputs {}).operations ++ chunks.flatten := by
  exact appendEffects_operations state ep.effects
    (Impact.publicInputPlan ep.circuit.inputs {}) plan
      (lower_effect_fold state ep plan accepted)

/-- Evaluating an actual accepted plan retains the public-input prefix and
one native VM operation segment per source effect. -/
theorem lower_eval_chunks (state : List StateDecl) (ep : Entrypoint)
    (plan : Impact.Plan) (ctx : EvalContext) (values : EvalEnv)
    (native : List NativeState.Op)
    (lowered : Impact.lower state ep = .ok plan)
    (evaluated : GenericStateOps.evalPlan ctx values plan = .ok native) :
    ∃ chunks initial groups,
      effectChunks state ep.effects = .ok chunks ∧
      (Impact.publicInputPlan ep.circuit.inputs {}).operations.mapM
        (GenericStateOps.evalOp ctx values) = .ok initial ∧
      chunks.mapM (fun chunk => chunk.mapM (GenericStateOps.evalOp ctx values)) =
        .ok groups ∧
      native = initial ++ groups.flatten := by
  obtain ⟨chunks, chunksAccepted, operationShape⟩ :=
    lower_effect_chunks state ep plan lowered
  unfold GenericStateOps.evalPlan at evaluated
  rw [operationShape, List.mapM_append] at evaluated
  simp only [bind_ok] at evaluated
  rcases evaluated with ⟨initial, initialEval, remaining, remainingEval, final⟩
  obtain ⟨groups, groupsEval, flat⟩ :=
    GenericStateOps.evalOperations_chunks ctx values chunks remaining remainingEval
  change Except.ok (initial ++ remaining) = .ok native at final
  exact ⟨chunks, initial, groups, chunksAccepted, initialEval, groupsEval,
    by rw [← flat]; exact (Except.ok.inj final).symm⟩

/-- An arbitrary successful checked VM run of the actual evaluated plan
starts with the production public-input tape and then visits every source
effect chunk in order. No source transition result is assumed. -/
theorem lower_checked_trace (state : List StateDecl) (ep : Entrypoint)
    (plan : Impact.Plan) (ctx : EvalContext) (values : EvalEnv)
    (native : List NativeState.Op) (slots : List NativeState.Slot)
    (final : NativeState.Machine)
    (lowered : Impact.lower state ep = .ok plan)
    (evaluated : GenericStateOps.evalPlan ctx values plan = .ok native)
    (checked : NativeState.run native (GenericStateEncoding.initial slots) = some final) :
    ∃ chunks segments publicCells,
      effectChunks state ep.effects = .ok chunks ∧
      AlignedChunks state ep.effects chunks ∧
      chunks.mapM (fun chunk => chunk.mapM
        (GenericStateOps.evalOp ctx values)) = .ok segments ∧
      EvaluatedChunks state ctx values ep.effects segments ∧
      GenericStateVM.RunsChunks segments
        ⟨[.vector slots], publicCells⟩ final := by
  obtain ⟨chunks, initial, segments, chunksAccepted, initialEval,
    segmentsEval, wholeShape⟩ :=
    lower_eval_chunks state ep plan ctx values native lowered evaluated
  obtain ⟨publicCells, _, prefixRun⟩ :=
    public_prefix_run ep.circuit.inputs ctx values initial
      [.vector slots] [] initialEval
  have aligned := effectChunks_aligned state ep.effects chunks chunksAccepted
  refine ⟨chunks, segments, publicCells, chunksAccepted,
    aligned, segmentsEval,
    alignedChunks_eval state ctx values ep.effects chunks segments aligned segmentsEval,
    ?_⟩
  rw [wholeShape, NativeState.run_append] at checked
  change (NativeState.run initial ⟨[.vector slots], []⟩).bind
    (NativeState.run segments.flatten) = some final at checked
  rw [prefixRun] at checked
  simp only [List.nil_append, Option.bind_some] at checked
  exact (GenericStateVM.run_chunks_iff segments _ final).mp checked

private def projectedScalar : (ty : Ty) → Expr ty → Expr .native
  | .native, expression => expression
  | .bool, expression => .select expression (.native 1) (.native 0)
  | .uint _, expression => .cast .native expression

private theorem projectedScalar_eval (ty : Ty) (expression : Expr ty)
    (ctx : EvalContext) (env : EvalEnv) (value : ty.Denote)
    (modulus : ctx.modulus = Field.modulus)
    (evaluated : expression.eval ctx env = .ok value)
    (canonical : ScalarNormalization.Canonical ty value) :
    (projectedScalar ty expression).eval ctx env =
      .ok (ScalarNormalization.number ty value) := by
  cases ty with
  | native => exact evaluated
  | bool =>
    change (Expr.select expression (.native 1) (.native 0)).eval ctx env =
      .ok (ScalarNormalization.number .bool value)
    cases value <;> simp [Expr.eval, evaluated, modulus, Field.modulus,
      ScalarNormalization.number, bind, Except.bind] <;> rfl
  | uint maximum =>
    simp only [projectedScalar, Expr.eval, evaluated, bind_ok,
      ScalarNormalization.number]
    refine ⟨value, rfl, ?_⟩
    change (if value < ctx.modulus then Except.ok value
      else Except.error "noncanonical scalar conversion") = .ok value
    rw [modulus]
    have bound : value < Field.modulus := canonical.1
    simp [bound]

theorem writeCell_chunk (state : List StateDecl) (name : String)
    (ty : Ty) (expression : Expr ty) (base : Impact.Plan)
    (ctx : EvalContext) (env : EvalEnv) (value : ty.Denote)
    (accepted : Impact.appendEffect state (.writeCell name ty expression) {} = .ok base) :
    ∃ (slot : Nat) (nativeExpr : Expr .native),
      base.operations = [.push (.field (.native slot)),
        .push (.field nativeExpr) true, .insert 1] ∧
      (ctx.modulus = Field.modulus → expression.eval ctx env = .ok value →
        ScalarNormalization.Canonical ty value →
        nativeExpr.eval ctx env = .ok (ScalarNormalization.number ty value)) := by
  simp only [Impact.appendEffect, bind_ok] at accepted
  rcases accepted with ⟨slot, _, result⟩
  cases result
  refine ⟨slot, projectedScalar ty expression, rfl, ?_⟩
  exact fun modulus evaluated canonical =>
    projectedScalar_eval ty expression ctx env value modulus evaluated canonical

/-- The actual map write emits the key and value scalar projections in the
VM's index/push/push/insert order. Their value equations follow from source
evaluation and canonicality, independently of the desired successor state. -/
theorem writeMap_chunk (state : List StateDecl) (name : String)
    (keyTy valueTy : Ty) (keyExpr : Expr keyTy)
    (valueExpr : Expr valueTy) (base : Impact.Plan)
    (ctx : EvalContext) (env : EvalEnv)
    (key : keyTy.Denote) (value : valueTy.Denote)
    (accepted : Impact.appendEffect state
      (.writeMap name keyTy valueTy keyExpr valueExpr) {} = .ok base) :
    ∃ (slot : Nat) (nativeKey nativeValue : Expr .native),
      base.operations = [.index slot true, .push (.field nativeKey),
        .push (.field nativeValue) true, .insert 2] ∧
      (ctx.modulus = Field.modulus → keyExpr.eval ctx env = .ok key →
        ScalarNormalization.Canonical keyTy key →
        nativeKey.eval ctx env = .ok (ScalarNormalization.number keyTy key)) ∧
      (ctx.modulus = Field.modulus → valueExpr.eval ctx env = .ok value →
        ScalarNormalization.Canonical valueTy value →
        nativeValue.eval ctx env = .ok
          (ScalarNormalization.number valueTy value)) := by
  simp only [Impact.appendEffect, bind_ok] at accepted
  rcases accepted with ⟨slot, _, result⟩
  cases result
  refine ⟨slot, projectedScalar keyTy keyExpr,
    projectedScalar valueTy valueExpr, rfl, ?_, ?_⟩
  · exact fun modulus evaluated canonical =>
      projectedScalar_eval keyTy keyExpr ctx env key modulus evaluated canonical
  · exact fun modulus evaluated canonical =>
      projectedScalar_eval valueTy valueExpr ctx env value modulus evaluated canonical

/-- The source read's destination is the same expression used by the
production native equality operation. -/
theorem readCell_chunk (state : List StateDecl) (name destination : String)
    (ty : Ty) (base : Impact.Plan)
    (accepted : Impact.appendEffect state (.readCell name destination ty) {} = .ok base) :
    ∃ (slot : Nat) (nativeRead : Expr .native),
      base.operations = [.dup, .index slot, .popeq (.field nativeRead)] ∧
      base.reads = [{name := destination, ty}] := by
  simp only [Impact.appendEffect, bind_ok] at accepted
  rcases accepted with ⟨slot, _, result⟩
  cases result
  exact ⟨slot, _, rfl, rfl⟩

/-- An absence effect names its read from the live prefix length. This
empty-plan projection records the exact first segment and its guard. -/
theorem requireAbsent_chunk (state : List StateDecl) (name : String)
    (keyTy : Ty) (keyExpr : Expr keyTy) (base : Impact.Plan)
    (ctx : EvalContext) (env : EvalEnv) (key : keyTy.Denote)
    (accepted : Impact.appendEffect state
      (.requireAbsent name keyTy keyExpr) {} = .ok base) :
    ∃ (slot : Nat) (nativeKey : Expr .native),
      base.operations = [.dup, .index slot,
        .push (.field nativeKey), .member, .popeq (.bit false)] ∧
      base.reads = [{name := "_nightlean_absence_0", ty := .bool}] ∧
      base.guards = [.eq (.ref "_nightlean_absence_0" : Expr .bool) (.bool false)] ∧
      (ctx.modulus = Field.modulus → keyExpr.eval ctx env = .ok key →
        ScalarNormalization.Canonical keyTy key →
        nativeKey.eval ctx env = .ok (ScalarNormalization.number keyTy key)) := by
  simp only [Impact.appendEffect, bind_ok] at accepted
  rcases accepted with ⟨slot, _, result⟩
  cases result
  refine ⟨slot, projectedScalar keyTy keyExpr, rfl, rfl, rfl, ?_⟩
  exact fun modulus evaluated canonical =>
    projectedScalar_eval keyTy keyExpr ctx env key modulus evaluated canonical

theorem writeMap_chunk_eval (state : List StateDecl) (name : String)
    (keyTy valueTy : Ty) (keyExpr : Expr keyTy)
    (valueExpr : Expr valueTy) (base : Impact.Plan)
    (ctx : EvalContext) (env : EvalEnv)
    (key : keyTy.Denote) (value : valueTy.Denote)
    (accepted : Impact.appendEffect state
      (.writeMap name keyTy valueTy keyExpr valueExpr) {} = .ok base)
    (modulus : ctx.modulus = Field.modulus)
    (keyEval : keyExpr.eval ctx env = .ok key)
    (valueEval : valueExpr.eval ctx env = .ok value)
    (keyCanonical : ScalarNormalization.Canonical keyTy key)
    (valueCanonical : ScalarNormalization.Canonical valueTy value) :
    ∃ slot, base.operations.mapM (GenericStateOps.evalOp ctx env) =
      .ok (GenericStateVM.writeMapOps slot
        (NativeRelation.scalar (ScalarNormalization.number keyTy key))
        (NativeRelation.scalar (ScalarNormalization.number valueTy value))) := by
  obtain ⟨slot, nativeKey, nativeValue, shape, keyMeaning, valueMeaning⟩ :=
    writeMap_chunk state name keyTy valueTy keyExpr valueExpr base ctx env key value accepted
  refine ⟨slot, ?_⟩
  rw [shape]
  have keyNative := keyMeaning modulus keyEval keyCanonical
  have valueNative := valueMeaning modulus valueEval valueCanonical
  simp [GenericStateVM.writeMapOps, GenericStateOps.evalOp,
    GenericStateOps.evalAligned, keyNative, valueNative,
    Except.map, Functor.map] <;> rfl

theorem writeCell_chunk_eval (state : List StateDecl) (name : String)
    (ty : Ty) (expression : Expr ty) (base : Impact.Plan)
    (ctx : EvalContext) (env : EvalEnv) (value : ty.Denote)
    (accepted : Impact.appendEffect state (.writeCell name ty expression) {} = .ok base)
    (modulus : ctx.modulus = Field.modulus)
    (evaluated : expression.eval ctx env = .ok value)
    (canonical : ScalarNormalization.Canonical ty value) :
    ∃ slot, slot < Field.modulus →
      base.operations.mapM (GenericStateOps.evalOp ctx env) =
        .ok (GenericStateVM.writeCellOps slot
          (NativeState.field (NativeRelation.scalar
            (ScalarNormalization.number ty value)))) := by
  obtain ⟨slot, nativeExpr, shape, meaning⟩ :=
    writeCell_chunk state name ty expression base ctx env value accepted
  refine ⟨slot, ?_⟩
  intro slotBound
  rw [shape]
  have valueNative := meaning modulus evaluated canonical
  have slotEval : (Expr.native slot : Expr .native).eval ctx env = .ok slot := by
    simp [Expr.eval, modulus, slotBound] <;> rfl
  simp [GenericStateVM.writeCellOps, GenericStateOps.evalOp,
    GenericStateOps.evalAligned, slotEval, valueNative,
    Except.map, Functor.map] <;> rfl

theorem requireAbsent_chunk_eval (state : List StateDecl) (name : String)
    (keyTy : Ty) (keyExpr : Expr keyTy) (base : Impact.Plan)
    (ctx : EvalContext) (env : EvalEnv) (key : keyTy.Denote)
    (accepted : Impact.appendEffect state
      (.requireAbsent name keyTy keyExpr) {} = .ok base)
    (modulus : ctx.modulus = Field.modulus)
    (keyEval : keyExpr.eval ctx env = .ok key)
    (keyCanonical : ScalarNormalization.Canonical keyTy key) :
    ∃ slot, base.operations.mapM (GenericStateOps.evalOp ctx env) =
      .ok (GenericStateVM.requireAbsentOps slot
        (NativeRelation.scalar (ScalarNormalization.number keyTy key))) := by
  obtain ⟨slot, nativeKey, shape, _, _, meaning⟩ :=
    requireAbsent_chunk state name keyTy keyExpr base ctx env key accepted
  refine ⟨slot, ?_⟩
  rw [shape]
  have keyNative := meaning modulus keyEval keyCanonical
  simp [GenericStateVM.requireAbsentOps, GenericStateOps.evalOp,
    GenericStateOps.evalAligned, keyNative,
    Except.map, Functor.map] <;> rfl

theorem readCell_chunk_eval (state : List StateDecl)
    (name destination : String) (ty : Ty) (base : Impact.Plan)
    (ctx : EvalContext) (env : EvalEnv)
    (accepted : Impact.appendEffect state
      (.readCell name destination ty) {} = .ok base) :
    ∃ (slot : Nat) (nativeRead : Expr .native),
      base.reads = [{name := destination, ty}] ∧
      (∀ number, nativeRead.eval ctx env = .ok number →
        base.operations.mapM (GenericStateOps.evalOp ctx env) =
          .ok (GenericStateVM.readCellOps slot
            (NativeState.field (NativeRelation.scalar number)))) := by
  obtain ⟨slot, nativeRead, shape, reads⟩ :=
    readCell_chunk state name destination ty base accepted
  refine ⟨slot, nativeRead, reads, ?_⟩
  intro number evaluated
  rw [shape]
  simp [GenericStateVM.readCellOps, GenericStateOps.evalOp,
    GenericStateOps.evalAligned, evaluated,
    Except.map, Functor.map] <;> rfl

private theorem index_has_name (state : List StateDecl) (name : String)
    (slot : Nat) (found : state.findIdx? (·.name == name) = some slot) :
    ∃ declaration, state[slot]? = some declaration ∧
      declaration.name = name ∧ slot < state.length := by
  obtain ⟨inside, predicate, _⟩ := List.findIdx?_eq_some_iff_getElem.mp found
  refine ⟨state[slot], List.getElem?_eq_getElem inside, ?_, inside⟩
  exact beq_iff_eq.mp predicate

/-- Source type checking and Impact's slot lookup use the same first matching
declaration, without an extra schema-agreement premise. -/
theorem source_find_matches_slot (state : List StateDecl) (name : String)
    (slot : Nat) (declaration : StateDecl)
    (sourceFound : state.find? (·.name == name) = some declaration)
    (impactFound : state.findIdx? (·.name == name) = some slot) :
    state[slot]? = some declaration := by
  rw [List.find?_eq_bind_findIdx?_getElem?, impactFound] at sourceFound
  exact sourceFound

/-- The slot literal in a production cell-write chunk points at the named
declared item. Type agreement comes from source validation, extracted above. -/
theorem writeCell_chunk_slot (state : List StateDecl) (name : String)
    (ty : Ty) (expression : Expr ty) (base : Impact.Plan)
    (accepted : Impact.appendEffect state (.writeCell name ty expression) {} = .ok base) :
    ∃ (slot : Nat) (declaration : StateDecl) (nativeExpr : Expr .native),
      state[slot]? = some declaration ∧
      declaration.name = name ∧ slot < state.length ∧
      base.operations = [.push (.field (.native slot)),
        .push (.field nativeExpr) true, .insert 1] := by
  simp only [Impact.appendEffect, bind_ok] at accepted
  rcases accepted with ⟨slot, found, result⟩
  cases result
  change (match state.findIdx? (·.name == name) with
    | some index => (pure index : Except String Nat)
    | none => throw s!"unknown ledger state '{name}'") = .ok slot at found
  cases located : state.findIdx? (·.name == name) with
  | none => simp [located] at found
  | some actual =>
    simp [located] at found
    cases found
    obtain ⟨declaration, entry, named, inside⟩ := index_has_name state name slot located
    exact ⟨slot, declaration, _, entry, named, inside, rfl⟩

private theorem validated_member {α : Type} (items : List α)
    (check : α → Except String Unit)
    (accepted : items.foldlM (fun _ item => check item) () = .ok ()) :
    ∀ item ∈ items, check item = .ok () := by
  induction items with
  | nil => simp
  | cons head tail ih =>
    simp only [List.foldlM_cons] at accepted
    cases checked : check head with
    | error message =>
      simp only [checked] at accepted
      change (Except.error message : Except String Unit) = .ok () at accepted
      cases accepted
    | ok checkedUnit =>
      cases checkedUnit
      simp [checked] at accepted
      intro item member
      rcases List.mem_cons.mp member with rfl | tailMember
      · exact checked
      · exact ih accepted item tailMember

theorem validated_fields (plan : Impact.Plan) (ep : Entrypoint)
    (accepted : plan.validate ep = .ok ()) :
    ∀ expression ∈ plan.fields,
      expression.validate {poseidon2 := true} (ep.circuit.inputs.map
        (fun input => (input.name, input.ty)) ++
        ep.circuit.outputs.map (fun output => (output.name, output.ty)) ++
        (plan.reads.drop ((ep.circuit.inputs.filter (·.visibility == .«public»)).length)).map
          (fun read => (read.name, read.ty))) = .ok () := by
  unfold Impact.Plan.validate at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨_, fieldsAccepted, _, _, _⟩
  let check : Impact.Scalar → Except String Unit := fun expression =>
    expression.validate {poseidon2 := true} (ep.circuit.inputs.map
      (fun input => (input.name, input.ty)) ++
      ep.circuit.outputs.map (fun output => (output.name, output.ty)) ++
      (plan.reads.drop ((ep.circuit.inputs.filter (·.visibility == .«public»)).length)).map
        (fun read => (read.name, read.ty)))
  have forInFold :
      (forIn plan.fields () fun expression _ => do
        let _ ← check expression
        pure (ForInStep.yield ())) =
      plan.fields.foldlM (fun _ expression => check expression) () := by
    calc
      _ = (forIn plan.fields () fun expression _ =>
          ForInStep.yield <$> check expression) := by
            congr 1
      _ = plan.fields.foldlM (fun _ expression => check expression) () := by
        rw [List.forIn_yield_eq_foldlM]
        congr 1
        funext _ expression
        cases check expression <;> rfl
  apply validated_member plan.fields check
  rw [← forInFold]
  exact fieldsAccepted

private theorem native_literal_bound (n : Nat) (env : TypeEnv)
    (accepted : (Expr.native n : Expr .native).validate
      {poseidon2 := true} env = .ok ()) : n < Field.modulus := by
  by_cases bound : n < Field.modulus
  · exact bound
  · simp [Expr.validate, bound] at accepted

private theorem fieldAdmitted_of_fields (operation : Impact.Op)
    (env : TypeEnv)
    (validated : ∀ expression ∈ operation.fields,
      expression.validate {poseidon2 := true} env = .ok ()) :
    GenericStateOps.FieldAdmitted operation := by
  cases operation with
  | index slot path =>
    apply native_literal_bound slot env
    apply validated
    simp [Impact.Op.fields, Impact.Aligned.fields]
  | insert levels =>
    apply native_literal_bound (0x90 + levels) env
    apply validated
    simp [Impact.Op.fields]
  | push value storage => trivial
  | popeq value => trivial
  | dup => trivial
  | member => trivial

/-- Actual accepted Impact plans admit every operation's field literals. This
discharges the slot and opcode bounds used by the native group bridge. -/
theorem plan_operations_admitted (plan : Impact.Plan) (ep : Entrypoint)
    (accepted : plan.validate ep = .ok ()) :
    ∀ operation ∈ plan.operations,
      GenericStateOps.FieldAdmitted operation := by
  have allFields := validated_fields plan ep accepted
  intro operation member
  apply fieldAdmitted_of_fields operation _
  intro expression inOperation
  apply allFields expression
  exact List.mem_flatMap.mpr ⟨operation, member, inOperation⟩

theorem lower_operations_admitted (state : List StateDecl) (ep : Entrypoint)
    (plan : Impact.Plan) (accepted : Impact.lower state ep = .ok plan) :
    ∀ operation ∈ plan.operations,
      GenericStateOps.FieldAdmitted operation :=
  plan_operations_admitted plan ep (lower_validated state ep plan accepted)

/-- The actual accepted Impact plan's evaluated field groups are the same
ordered, bounded native VM opcode groups. -/
theorem lower_plan_groups (state : List StateDecl) (ep : Entrypoint)
    (plan : Impact.Plan) (ctx : EvalContext) (env : EvalEnv)
    (ops : List NativeState.Op)
    (lowered : Impact.lower state ep = .ok plan)
    (modulus : ctx.modulus = Field.modulus)
    (evaluated : GenericStateOps.evalPlan ctx env plan = .ok ops) :
    plan.operations.mapM (fun operation =>
      GenericStateOps.evalFields ctx env operation.fields) =
      .ok (NativeState.groups ops) := by
  exact GenericStateOps.evalOperations_fields ctx env plan.operations ops modulus
    (lower_operations_admitted state ep plan lowered) evaluated

private def appendPiece
    (frame : List Native.Term × List (List Native.Term) × List (Native.Term × Nat))
    (piece : List Native.Term × List (Native.Term × Nat) × List Native.Term) :=
  (frame.1 ++ piece.2.2, frame.2.1 ++ [piece.1], frame.2.2 ++ piece.2.1)

private theorem fold_operations_projection (span : SourceSpan)
    (aliases : Native.AliasEnvironment) (operations : List Impact.Op)
    (start : List Native.Term × List (List Native.Term) × List (Native.Term × Nat)) :
    operations.foldlM (fun frame operation =>
      appendPiece frame <$> Native.collectOperation span aliases operation) start =
    (do
      let pieces ← operations.mapM (Native.collectOperation span aliases)
      pure (start.1 ++ pieces.flatMap (fun piece => piece.2.2),
        start.2.1 ++ pieces.map (fun piece => piece.1),
        start.2.2 ++ pieces.flatMap (fun piece => piece.2.1))) := by
  induction operations generalizing start with
  | nil => simp [Except.pure]
  | cons operation rest ih =>
    simp only [List.foldlM_cons, List.mapM_cons]
    cases checked : Native.collectOperation span aliases operation with
    | error message => rfl
    | ok piece =>
      rw [show appendPiece start <$> (Except.ok piece : Except Diagnostic _) =
        Except.ok (appendPiece start piece) from rfl]
      simp only [bind, Except.bind]
      rw [ih (appendPiece start piece)]
      cases later : rest.mapM (Native.collectOperation span aliases) with
      | error message => simp [later, Except.bind, Except.map, Functor.map]
      | ok remaining =>
        simp only [bind, Except.bind]
        simp [appendPiece, List.append_assoc, Except.pure] <;> rfl

private theorem operation_forIn_fold (span : SourceSpan)
    (aliases : Native.AliasEnvironment) (operations : List Impact.Op)
    (start : List Native.Term × List (List Native.Term) × List (Native.Term × Nat)) :
    (forIn operations start fun operation frame => do
      let (values, requirements, nestedAssertions) ←
        Native.collectOperation span aliases operation
      pure (ForInStep.yield
        (frame.1 ++ nestedAssertions, frame.2.1 ++ [values],
          frame.2.2 ++ requirements))) =
    operations.foldlM (fun frame operation =>
      appendPiece frame <$> Native.collectOperation span aliases operation) start := by
  simpa only [appendPiece, map_eq_pure_bind] using
    (List.forIn_yield_eq_foldlM (m := Except Diagnostic) (l := operations)
      (fun operation _ => Native.collectOperation span aliases operation)
      (fun _ frame piece => appendPiece frame piece) start)

/-- The exact operation accumulator used before the ordered mapM extraction.
This reference exists only to prove the production refactor preserves every
result and first error. -/
def previousOperationFold (span : SourceSpan) (aliases : Native.AliasEnvironment)
    (operations : List Impact.Op) (initialBounds : List (Native.Term × Nat)) :
    Except Diagnostic (List (List Native.Term) × List (Native.Term × Nat) × List Native.Term) := do
  let mut operationAssertions := []
  let mut groups := []
  let mut bounds := initialBounds
  for operation in operations do
    let (values, requirements, nestedAssertions) ← Native.collectOperation span aliases operation
    operationAssertions := operationAssertions ++ nestedAssertions
    groups := groups ++ [values]
    bounds := bounds ++ requirements
  pure (groups, bounds, operationAssertions)

theorem previousOperationFold_eq_mapM (span : SourceSpan)
    (aliases : Native.AliasEnvironment) (operations : List Impact.Op)
    (initialBounds : List (Native.Term × Nat)) :
    previousOperationFold span aliases operations initialBounds =
      (do
        let pieces ← operations.mapM (Native.collectOperation span aliases)
        pure (pieces.map (fun piece => piece.1),
          initialBounds ++ pieces.flatMap (fun piece => piece.2.1),
          pieces.flatMap (fun piece => piece.2.2))) := by
  unfold previousOperationFold
  simp only [operation_forIn_fold, fold_operations_projection]
  simp [Except.bind, Except.pure]

/-- Every old loop result and first error equals the refactored production
collector, for all operations, aliases, spans, and starting bounds. -/
theorem previousOperationFold_eq_production (span : SourceSpan)
    (aliases : Native.AliasEnvironment) (operations : List Impact.Op)
    (initialBounds : List (Native.Term × Nat)) :
    previousOperationFold span aliases operations initialBounds =
      Native.collectOperations span aliases operations initialBounds := by
  rw [previousOperationFold_eq_mapM]
  rfl

theorem expected_operation_groups (span : SourceSpan)
    (aliases : Native.AliasEnvironment) (operations : List Impact.Op)
    (initialBounds : List (Native.Term × Nat))
    (groups : List (List Native.Term)) (bounds : List (Native.Term × Nat))
    (assertions : List Native.Term)
    (accepted : Native.collectOperations span aliases operations initialBounds =
      .ok (groups, bounds, assertions)) :
    ∃ pieces,
      operations.mapM (Native.collectOperation span aliases) = .ok pieces ∧
      groups = pieces.map (fun piece => piece.1) ∧
      bounds = initialBounds ++ pieces.flatMap (fun piece => piece.2.1) ∧
      assertions = pieces.flatMap (fun piece => piece.2.2) := by
  unfold Native.collectOperations at accepted
  cases collected : operations.mapM (Native.collectOperation span aliases) with
  | error message =>
    rw [collected] at accepted
    simp only [map_eq_pure_bind, bind, Except.bind] at accepted
    change (Except.error message : Except Diagnostic
      (List (List Native.Term) × List (Native.Term × Nat) × List Native.Term)) =
      .ok (groups, bounds, assertions) at accepted
    cases accepted
  | ok pieces =>
    simp [collected] at accepted
    cases accepted
    exact ⟨pieces, rfl, rfl, rfl, rfl⟩

theorem collectOperation_parts (span : SourceSpan)
    (aliases : Native.AliasEnvironment) (operation : Impact.Op)
    (values : List Native.Term) (bounds : List (Native.Term × Nat))
    (assertions : List Native.Term)
    (accepted : Native.collectOperation span aliases operation =
      .ok (values, bounds, assertions)) :
    ∃ normalized,
      operation.fields.mapM (Native.normalize aliases) = .ok normalized ∧
      values = normalized.map (·.term) ∧
      bounds = normalized.flatMap (·.bounds) ∧
      assertions = normalized.flatMap (·.assertions) := by
  unfold Native.collectOperation at accepted
  have converted := (Native.convert_ok span _ _).mp accepted
  rw [Native.collect_eq] at converted
  simp only [bind_ok] at converted
  rcases converted with ⟨normalized, normalizedAccepted, result⟩
  cases result
  exact ⟨normalized, normalizedAccepted, rfl, rfl, rfl⟩

private theorem normalized_fields_sound (ctx : EvalContext)
    (hash : NativeRelation.Hash)
    (implementation : NativeRelation.HashAgreement ctx hash)
    (inputs : NativeRelation.Assignment)
    (types : TypeEnv) (aliases : Native.AliasEnvironment) (values : EvalEnv)
    (environment : ScalarNormalization.TypedEnvironment hash inputs aliases values types)
    (fields : List Impact.Scalar) (normalized : List Native.Normalized)
    (valid : ∀ expression ∈ fields,
      expression.validate {poseidon2 := true} types = .ok ())
    (normal : fields.mapM (Native.normalize aliases) = .ok normalized)
    (requirements : ∀ item ∈ normalized,
      ScalarNormalization.Requirements hash inputs item) :
    GenericStateOps.evalFields ctx values fields =
      .ok (normalized.map (fun item => ScalarNormalization.interpret hash inputs item.term)) := by
  induction fields generalizing normalized with
  | nil =>
    simp only [List.mapM_nil] at normal
    cases normal
    rfl
  | cons expression rest ih =>
    simp only [List.mapM_cons, bind_ok] at normal
    rcases normal with ⟨first, firstNormal, remaining, restNormal, result⟩
    cases result
    have firstValid := valid expression (by simp)
    have firstRequirements := requirements first (by simp)
    obtain ⟨value, evaluated, represented⟩ :=
      ScalarNormalization.normalize_sound ctx hash implementation inputs types aliases values
        environment expression first firstValid firstNormal firstRequirements
    have restValid : ∀ expression ∈ rest,
        expression.validate {poseidon2 := true} types = .ok () := by
      intro item member
      exact valid item (by simp [member])
    have restRequirements : ∀ item ∈ remaining,
        ScalarNormalization.Requirements hash inputs item := by
      intro item member
      exact requirements item (by simp [member])
    have tail := ih remaining restValid restNormal restRequirements
    have tailMap : rest.mapM (fun item => NativeRelation.scalar <$> item.eval ctx values) =
        .ok (remaining.map (fun item => ScalarNormalization.interpret hash inputs item.term)) :=
      tail
    simp only [GenericStateOps.evalFields, List.mapM_cons, evaluated]
    rw [tailMap]
    simp [represented.2.2, Except.bind, Except.map, Functor.map, Except.pure] <;> rfl

/-- Actual normalized operation groups evaluate to the source expressions
when their own producer bounds/assertions hold in a typed alias environment. -/
theorem collectOperation_meaning (ctx : EvalContext)
    (hash : NativeRelation.Hash)
    (implementation : NativeRelation.HashAgreement ctx hash)
    (inputs : NativeRelation.Assignment)
    (types : TypeEnv) (aliases : Native.AliasEnvironment) (values : EvalEnv)
    (environment : ScalarNormalization.TypedEnvironment hash inputs aliases values types)
    (span : SourceSpan) (operation : Impact.Op)
    (terms : List Native.Term) (bounds : List (Native.Term × Nat))
    (assertions : List Native.Term)
    (accepted : Native.collectOperation span aliases operation =
      .ok (terms, bounds, assertions))
    (valid : ∀ expression ∈ operation.fields,
      expression.validate {poseidon2 := true} types = .ok ())
    (boundsHold : ∀ requirement ∈ bounds,
      (ScalarNormalization.interpret hash inputs requirement.1).val ≤ requirement.2)
    (assertionsHold : ∀ assertion ∈ assertions,
      ScalarNormalization.interpret hash inputs assertion = NativeRelation.one) :
    GenericStateOps.evalFields ctx values operation.fields =
      .ok (terms.map (ScalarNormalization.interpret hash inputs)) := by
  obtain ⟨normalized, normal, termsExact, boundsExact, assertionsExact⟩ :=
    collectOperation_parts span aliases operation terms bounds assertions accepted
  have eachRequirements : ∀ item ∈ normalized,
      ScalarNormalization.Requirements hash inputs item := by
    intro item member
    constructor
    · intro requirement inItem
      apply boundsHold requirement
      rw [boundsExact]
      exact List.mem_flatMap.mpr ⟨item, member, inItem⟩
    · intro assertion inItem
      apply assertionsHold assertion
      rw [assertionsExact]
      exact List.mem_flatMap.mpr ⟨item, member, inItem⟩
  rw [termsExact]
  simpa only [List.map_map, Function.comp_def] using
    (normalized_fields_sound ctx hash implementation inputs types aliases values
      environment operation.fields normalized valid normal eachRequirements)

theorem operation_pieces_meaning (ctx : EvalContext)
    (hash : NativeRelation.Hash)
    (implementation : NativeRelation.HashAgreement ctx hash)
    (inputs : NativeRelation.Assignment)
    (types : TypeEnv) (aliases : Native.AliasEnvironment) (values : EvalEnv)
    (environment : ScalarNormalization.TypedEnvironment hash inputs aliases values types)
    (span : SourceSpan) (operations : List Impact.Op)
    (pieces : List (List Native.Term × List (Native.Term × Nat) × List Native.Term))
    (collected : operations.mapM (Native.collectOperation span aliases) = .ok pieces)
    (valid : ∀ expression ∈ operations.flatMap Impact.Op.fields,
      expression.validate {poseidon2 := true} types = .ok ())
    (boundsHold : ∀ requirement ∈ pieces.flatMap (fun piece => piece.2.1),
      (ScalarNormalization.interpret hash inputs requirement.1).val ≤ requirement.2)
    (assertionsHold : ∀ assertion ∈ pieces.flatMap (fun piece => piece.2.2),
      ScalarNormalization.interpret hash inputs assertion = NativeRelation.one) :
    operations.mapM (fun operation =>
      GenericStateOps.evalFields ctx values operation.fields) =
      .ok (pieces.map (fun piece => piece.1.map (ScalarNormalization.interpret hash inputs))) := by
  induction operations generalizing pieces with
  | nil =>
    simp only [List.mapM_nil] at collected
    cases collected
    rfl
  | cons operation rest ih =>
    simp only [List.mapM_cons, bind_ok] at collected
    rcases collected with ⟨first, firstCollected, remaining, restCollected, result⟩
    cases result
    have firstValid : ∀ expression ∈ operation.fields,
        expression.validate {poseidon2 := true} types = .ok () := by
      intro expression member
      apply valid expression
      exact List.mem_flatMap.mpr ⟨operation, by simp, member⟩
    have firstBounds : ∀ requirement ∈ first.2.1,
        (ScalarNormalization.interpret hash inputs requirement.1).val ≤ requirement.2 := by
      intro requirement member
      apply boundsHold requirement
      exact List.mem_flatMap.mpr ⟨first, by simp, member⟩
    have firstAssertions : ∀ assertion ∈ first.2.2,
        ScalarNormalization.interpret hash inputs assertion = NativeRelation.one := by
      intro assertion member
      apply assertionsHold assertion
      exact List.mem_flatMap.mpr ⟨first, by simp, member⟩
    have one := collectOperation_meaning ctx hash implementation inputs types aliases values
      environment span operation first.1 first.2.1 first.2.2 firstCollected
      firstValid firstBounds firstAssertions
    have restValid : ∀ expression ∈ rest.flatMap Impact.Op.fields,
        expression.validate {poseidon2 := true} types = .ok () := by
      intro expression member
      exact valid expression (by simp [member])
    have restBounds : ∀ requirement ∈ remaining.flatMap (fun piece => piece.2.1),
        (ScalarNormalization.interpret hash inputs requirement.1).val ≤ requirement.2 := by
      intro requirement member
      exact boundsHold requirement (by simp [member])
    have restAssertions : ∀ assertion ∈ remaining.flatMap (fun piece => piece.2.2),
        ScalarNormalization.interpret hash inputs assertion = NativeRelation.one := by
      intro assertion member
      exact assertionsHold assertion (by simp [member])
    have others := ih remaining restCollected restValid restBounds restAssertions
    simp [List.mapM_cons, one, others, Except.bind, Except.map,
      Functor.map, Except.pure] <;> rfl

/-- The independently built expected statement takes its ordered native
groups from the accepted Impact plan and the exact production operation fold. -/
theorem expectedEntrypoint_groups (state : List StateDecl) (ep : Entrypoint)
    (expected : Native.Expected)
    (accepted : Native.expectedEntrypoint state ep = .ok expected) :
    ∃ plan aliases pieces,
      Impact.lower state ep = .ok plan ∧
      plan.operations.mapM (Native.collectOperation ep.span aliases) = .ok pieces ∧
      expected.groups = pieces.map (fun piece => piece.1) ∧
      (∀ requirement ∈ pieces.flatMap (fun piece => piece.2.1),
        requirement ∈ expected.bounds) ∧
      (∀ assertion ∈ pieces.flatMap (fun piece => piece.2.2),
        assertion ∈ expected.assertions) := by
  unfold Native.expectedEntrypoint at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨plan, lowered, outputFrame, _, _, _, _, _, _, _,
    _, _, operationFrame, operationsAccepted, produced⟩
  obtain ⟨pieces, piecesAccepted, groupsExact, boundsExact, assertionsExact⟩ :=
    expected_operation_groups ep.span outputFrame.1 plan.operations outputFrame.2.1
      operationFrame.1 operationFrame.2.1 operationFrame.2.2 operationsAccepted
  cases produced
  refine ⟨plan, outputFrame.1, pieces, lowered, piecesAccepted, groupsExact, ?_, ?_⟩
  · intro requirement member
    rw [boundsExact]
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inr member))
  · intro assertion member
    rw [assertionsExact]
    exact List.mem_append_right _ member

/-- The independent expected constructor authenticates input order and the
public status of ledger reads against the actual accepted Impact read list. -/
theorem expectedEntrypoint_inputs (state : List StateDecl) (ep : Entrypoint)
    (expected : Native.Expected)
    (accepted : Native.expectedEntrypoint state ep = .ok expected) :
    ∃ plan,
      Impact.lower state ep = .ok plan ∧
      expected.inputs =
        ep.circuit.inputs.map (fun input =>
          ({identifier := "%input_" ++ input.name,
            visibility := input.visibility, ty := input.ty} : Native.InputRequirement)) ++
        (plan.reads.drop ((ep.circuit.inputs.filter
          (·.visibility == .«public»)).length)).map (fun read =>
          ({identifier := "%input_" ++ read.name,
            visibility := .«public», ty := read.ty} : Native.InputRequirement)) := by
  unfold Native.expectedEntrypoint at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨plan, lowered, _, _, _, _, _, _, _, _, _, _, _, _, produced⟩
  cases produced
  exact ⟨plan, lowered, by simp [Native.inputRequirement_eq]⟩

def planTypes (plan : Impact.Plan) (ep : Entrypoint) : TypeEnv :=
  ep.circuit.inputs.map (fun input => (input.name, input.ty)) ++
  ep.circuit.outputs.map (fun output => (output.name, output.ty)) ++
  (plan.reads.drop ((ep.circuit.inputs.filter (·.visibility == .«public»)).length)).map
    (fun read => (read.name, read.ty))

/-- An accepted independent expected statement fixes the native field groups
of the actual Impact plan. The remaining typed alias environment must be
established from circuit outputs and authenticated ledger reads. -/
theorem expected_groups_native_fields (state : List StateDecl) (ep : Entrypoint)
    (expected : Native.Expected)
    (expectedAccepted : Native.expectedEntrypoint state ep = .ok expected)
    (ctx : EvalContext) (hash : NativeRelation.Hash)
    (implementation : NativeRelation.HashAgreement ctx hash)
    (inputs : NativeRelation.Assignment)
    (allBounds : ∀ requirement ∈ expected.bounds,
      (ScalarNormalization.interpret hash inputs requirement.1).val ≤ requirement.2)
    (allAssertions : ∀ assertion ∈ expected.assertions,
      ScalarNormalization.interpret hash inputs assertion = NativeRelation.one) :
    ∃ plan aliases pieces,
      Impact.lower state ep = .ok plan ∧
      plan.operations.mapM (Native.collectOperation ep.span aliases) = .ok pieces ∧
      (∀ values, ScalarNormalization.TypedEnvironment hash inputs aliases values
          (planTypes plan ep) →
        ∃ ops, GenericStateOps.evalPlan ctx values plan = .ok ops ∧
          expected.groups.map (List.map (ScalarNormalization.interpret hash inputs)) =
            NativeState.groups ops) := by
  obtain ⟨plan, aliases, pieces, lowered, collected, groupsExact,
    pieceBounds, pieceAssertions⟩ :=
    expectedEntrypoint_groups state ep expected expectedAccepted
  refine ⟨plan, aliases, pieces, lowered, collected, ?_⟩
  intro values environment
  have allFields : ∀ expression ∈ plan.operations.flatMap Impact.Op.fields,
      expression.validate {poseidon2 := true} (planTypes plan ep) = .ok () := by
    simpa only [Impact.Plan.fields, planTypes] using
      (validated_fields plan ep (lower_validated state ep plan lowered))
  have operationFields := operation_pieces_meaning ctx hash implementation inputs
    (planTypes plan ep) aliases values environment ep.span plan.operations pieces
    collected allFields
    (fun requirement member => allBounds requirement (pieceBounds requirement member))
    (fun assertion member => allAssertions assertion (pieceAssertions assertion member))
  obtain ⟨ops, evaluated⟩ := GenericStateOps.evalOperations_of_fields ctx values
    plan.operations _ operationFields
  refine ⟨ops, evaluated, ?_⟩
  have nativeFields := lower_plan_groups state ep plan ctx values ops lowered
    implementation.modulus evaluated
  rw [operationFields] at nativeFields
  have same := Except.ok.inj nativeFields
  simpa only [groupsExact, List.map_map, Function.comp_def] using same


end Nightlean.Verification.GenericStateAdmission
