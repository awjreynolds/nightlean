import Noctium.Verification.GenericStateAdmission

namespace Noctium.Verification.GenericStateOperationCompleteness
open Backend NativeRelation ScalarNormalization

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

/-- Successful source fields satisfy the exact normalized terms and every
range/assertion collected from those fields, in their original order. -/
theorem normalized_fields_complete (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (aliases : Native.AliasEnvironment) (values : EvalEnv)
    (agreement : AliasAgreement hash inputs aliases values)
    (expressions : List (Expr .native)) (normalized : List Native.Normalized)
    (numbers : List Scalar)
    (normal : expressions.mapM (Native.normalize aliases) = .ok normalized)
    (evaluated : GenericStateOps.evalFields ctx values expressions = .ok numbers) :
    normalized.map (fun item => interpret hash inputs item.term) = numbers ∧
      ∀ item ∈ normalized, Requirements hash inputs item := by
  induction expressions generalizing normalized numbers with
  | nil =>
    simp only [List.mapM_nil] at normal
    cases normal
    change Except.ok [] = .ok numbers at evaluated
    cases evaluated
    simp
  | cons expression rest ih =>
    simp only [List.mapM_cons, bind_ok] at normal
    obtain ⟨head, headNormal, remaining, tailNormal, result⟩ := normal
    cases result
    unfold GenericStateOps.evalFields at evaluated
    rw [List.mapM_cons] at evaluated
    change (do
      let head ← scalar <$> expression.eval ctx values
      let tail ← GenericStateOps.evalFields ctx values rest
      pure (head :: tail)) = .ok numbers at evaluated
    cases source : expression.eval ctx values with
    | error message =>
      simp [source, bind, Except.bind, Except.map, Functor.map] at evaluated
    | ok value =>
      cases tail : GenericStateOps.evalFields ctx values rest with
      | error message =>
        simp [source, tail, Except.map, Functor.map, bind, Except.bind] at evaluated

      | ok tailNumbers =>
        have exactValues : numbers = scalar value :: tailNumbers := by
          simp only [source, tail, Except.map, Functor.map, bind, Except.bind] at evaluated
          change Except.ok (scalar value :: tailNumbers) = .ok numbers at evaluated
          exact (Except.ok.inj evaluated).symm
        obtain ⟨actual, actualNormal, represented⟩ := normalize_success ctx hash
          implementation inputs aliases values agreement expression value source
        rw [headNormal] at actualNormal
        cases actualNormal
        obtain ⟨tailMeaning, tailRequirements⟩ := ih remaining tailNumbers tailNormal tail
        constructor
        · simp only [List.map_cons, represented.2.2, tailMeaning, exactValues]
          rfl
        · intro item member
          rcases List.mem_cons.mp member with equal | present
          · subst item
            exact represented.2.1
          · exact tailRequirements item present

/-- Completeness of the actual production normalizer for one evaluated Impact
operation. Source success supplies every collected constraint. -/
theorem collectOperation_complete (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (aliases : Native.AliasEnvironment) (values : EvalEnv)
    (agreement : AliasAgreement hash inputs aliases values)
    (span : SourceSpan) (operation : Impact.Op) (native : NativeState.Op)
    (terms : List Native.Term) (bounds : List (Native.Term × Nat))
    (assertions : List Native.Term)
    (collected : Native.collectOperation span aliases operation = .ok (terms, bounds, assertions))
    (admitted : GenericStateOps.FieldAdmitted operation)
    (evaluated : GenericStateOps.evalOp ctx values operation = .ok native) :
    terms.map (interpret hash inputs) = native.fields ∧
      (∀ requirement ∈ bounds, (interpret hash inputs requirement.1).val ≤ requirement.2) ∧
      (∀ assertion ∈ assertions, interpret hash inputs assertion = one) := by
  obtain ⟨normalized, normal, termsExact, boundsExact, assertionsExact⟩ :=
    GenericStateAdmission.collectOperation_parts span aliases operation terms bounds assertions collected
  have fields := GenericStateOps.evalOp_fields ctx values operation native
    implementation.modulus admitted evaluated
  obtain ⟨meaning, requirements⟩ := normalized_fields_complete ctx hash
    implementation inputs aliases values agreement operation.fields normalized native.fields normal fields
  constructor
  · rw [termsExact]
    simpa only [List.map_map, Function.comp_def] using meaning
  constructor
  · intro requirement member
    rw [boundsExact] at member
    obtain ⟨item, present, inItem⟩ := List.mem_flatMap.mp member
    exact (requirements item present).1 requirement inItem
  · intro assertion member
    rw [assertionsExact] at member
    obtain ⟨item, present, inItem⟩ := List.mem_flatMap.mp member
    exact (requirements item present).2 assertion inItem

/-- Successful source operation evaluation supplies every requirement and
exact native group of the actual ordered production collection. -/
theorem operation_pieces_complete (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (aliases : Native.AliasEnvironment) (values : EvalEnv)
    (agreement : AliasAgreement hash inputs aliases values)
    (span : SourceSpan) (operations : List Impact.Op) (native : List NativeState.Op)
    (pieces : List (List Native.Term × List (Native.Term × Nat) × List Native.Term))
    (collected : operations.mapM (Native.collectOperation span aliases) = .ok pieces)
    (admitted : ∀ operation ∈ operations, GenericStateOps.FieldAdmitted operation)
    (evaluated : operations.mapM (GenericStateOps.evalOp ctx values) = .ok native) :
    pieces.map (fun piece => piece.1.map (interpret hash inputs)) = native.map NativeState.Op.fields ∧
      (∀ requirement ∈ pieces.flatMap (fun piece => piece.2.1),
        (interpret hash inputs requirement.1).val ≤ requirement.2) ∧
      (∀ assertion ∈ pieces.flatMap (fun piece => piece.2.2),
        interpret hash inputs assertion = one) := by
  induction operations generalizing native pieces with
  | nil =>
    simp only [List.mapM_nil] at collected evaluated
    cases collected
    cases evaluated
    simp
  | cons operation rest ih =>
    simp only [List.mapM_cons, bind_ok] at collected evaluated
    obtain ⟨piece, first, remaining, later, produced⟩ := collected
    obtain ⟨next, firstEval, following, restEval, nativeShape⟩ := evaluated
    cases produced
    cases nativeShape
    have head := collectOperation_complete ctx hash implementation inputs aliases values
      agreement span operation next piece.1 piece.2.1 piece.2.2 first
      (admitted operation (by simp)) firstEval
    have tail := ih following remaining later
      (fun item member => admitted item (by simp [member])) restEval
    constructor
    · simp only [List.map_cons, head.1, tail.1]
    constructor
    · intro requirement member
      simp only [List.flatMap_cons, List.mem_append] at member
      rcases member with present | present
      · exact head.2.1 requirement present
      · exact tail.2.1 requirement present
    · intro assertion member
      simp only [List.flatMap_cons, List.mem_append] at member
      rcases member with present | present
      · exact head.2.2 assertion present
      · exact tail.2.2 assertion present

/-- Completeness of the actual production operation collector, including
its ordered prefix of output bounds. -/
theorem collectOperations_complete (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (aliases : Native.AliasEnvironment) (values : EvalEnv)
    (agreement : AliasAgreement hash inputs aliases values)
    (span : SourceSpan) (operations : List Impact.Op) (native : List NativeState.Op)
    (initialBounds : List (Native.Term × Nat))
    (frame : List (List Native.Term) × List (Native.Term × Nat) × List Native.Term)
    (collected : Native.collectOperations span aliases operations initialBounds = .ok frame)
    (initialHold : ∀ requirement ∈ initialBounds,
      (interpret hash inputs requirement.1).val ≤ requirement.2)
    (admitted : ∀ operation ∈ operations, GenericStateOps.FieldAdmitted operation)
    (evaluated : operations.mapM (GenericStateOps.evalOp ctx values) = .ok native) :
    frame.1.map (fun group => group.map (interpret hash inputs)) = native.map NativeState.Op.fields ∧
      (∀ requirement ∈ frame.2.1, (interpret hash inputs requirement.1).val ≤ requirement.2) ∧
      (∀ assertion ∈ frame.2.2, interpret hash inputs assertion = one) := by
  unfold Native.collectOperations at collected
  simp only [bind_ok] at collected
  obtain ⟨pieces, normalized, equal⟩ := collected
  cases equal
  have complete := operation_pieces_complete ctx hash implementation inputs aliases values
    agreement span operations native pieces normalized admitted evaluated
  refine ⟨?_, ?_, complete.2.2⟩
  · simpa only [List.map_map, Function.comp_def] using complete.1
  intro requirement member
  rcases List.mem_append.mp member with prefixMember | generated
  · exact initialHold requirement prefixMember
  · exact complete.2.1 requirement generated

end Noctium.Verification.GenericStateOperationCompleteness
