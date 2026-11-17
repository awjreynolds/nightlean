import Nightlean.Verification.GenericStateAbsenceInversion

namespace Nightlean.Verification.GenericStateWriteAuthentication
open Backend NativeState NativeRelation ScalarNormalization

/-- A checked production cell write has exactly the original source
transition and encoded successor, at Impact's actual chosen slot. -/
theorem writeCell_candidate_source_step (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (current : LedgerState) (slots : List NativeState.Slot)
    (name : String) (ty : Ty) (expression : Expr ty) (value : ty.Denote)
    (base : Impact.Plan) (segment : List NativeState.Op)
    (reads : List NativeState.Cell) (after : NativeState.Machine)
    (compiled : Impact.appendEffect state (.writeCell name ty expression) {} = .ok base)
    (sourceDeclaration : StateDecl)
    (sourceFound : state.find? (·.name == name) = some sourceDeclaration)
    (sourceNamed : sourceDeclaration.name = name)
    (sourceKind : sourceDeclaration.kind = .cell ty)
    (distinct : state.Pairwise (fun left right => left.name ≠ right.name))
    (encoded : GenericStateEncoding.encodeState state current = some slots)
    (stateBound : state.length < Field.modulus)
    (modulus : ctx.modulus = Field.modulus)
    (candidateEval : expression.eval ctx candidateEnv = .ok value)
    (sourceEval : expression.eval ctx sourceEnv = .ok value)
    (canonical : Canonical ty value)
    (evaluated : base.operations.mapM (GenericStateOps.evalOp ctx candidateEnv) =
      .ok segment)
    (checked : NativeState.run segment ⟨[.vector slots], reads⟩ = some after) :
    ∃ next nextSlots,
      SourceEffects.step ctx (.writeCell name ty expression) (sourceEnv, current) =
        .ok (sourceEnv, next) ∧
      GenericStateEncoding.encodeState state next = some nextSlots ∧
      after = ⟨[.vector nextSlots], reads⟩ := by
  obtain ⟨slot, declaration, located, declarationAt, _, _, segmentEval⟩ :=
    GenericStateWriteEvaluation.writeCell_candidate_eval_located state name ty
      expression base ctx candidateEnv value compiled stateBound modulus
      candidateEval canonical
  have typedAt : state[slot]? = some sourceDeclaration :=
    GenericStateAdmission.source_find_matches_slot state name slot
      sourceDeclaration sourceFound located
  obtain ⟨next, sourceStep, nextEncoded, nativeRun⟩ :=
    GenericStateSchemaSpans.writeCell_source_step ctx sourceEnv state current
      slots slot sourceDeclaration name ty expression value reads typedAt
      sourceNamed sourceKind distinct encoded stateBound sourceEval canonical
  rw [segmentEval] at evaluated
  cases evaluated
  rw [nativeRun] at checked
  cases checked
  exact ⟨next, slots.set slot (.cell (field (scalar (number ty value)))),
    sourceStep, nextEncoded, rfl⟩

/-- A checked production map write updates the source map and its encoded
native slot by the same key and value. -/
theorem writeMap_candidate_source_step (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (current : LedgerState) (slots : List NativeState.Slot)
    (name : String) (keyTy valueTy : Ty)
    (keyExpr : Expr keyTy) (valueExpr : Expr valueTy)
    (key : keyTy.Denote) (value : valueTy.Denote)
    (base : Impact.Plan) (segment : List NativeState.Op)
    (reads : List NativeState.Cell) (after : NativeState.Machine)
    (compiled : Impact.appendEffect state
      (.writeMap name keyTy valueTy keyExpr valueExpr) {} = .ok base)
    (sourceDeclaration : StateDecl)
    (sourceFound : state.find? (·.name == name) = some sourceDeclaration)
    (sourceNamed : sourceDeclaration.name = name)
    (sourceKind : sourceDeclaration.kind = .map keyTy valueTy)
    (distinct : state.Pairwise (fun left right => left.name ≠ right.name))
    (encoded : GenericStateEncoding.encodeState state current = some slots)
    (stateBound : state.length < Field.modulus)
    (modulus : ctx.modulus = Field.modulus)
    (candidateKey : keyExpr.eval ctx candidateEnv = .ok key)
    (candidateValue : valueExpr.eval ctx candidateEnv = .ok value)
    (sourceKey : keyExpr.eval ctx sourceEnv = .ok key)
    (sourceValue : valueExpr.eval ctx sourceEnv = .ok value)
    (keyCanonical : Canonical keyTy key)
    (valueCanonical : Canonical valueTy value)
    (evaluated : base.operations.mapM (GenericStateOps.evalOp ctx candidateEnv) =
      .ok segment)
    (checked : NativeState.run segment ⟨[.vector slots], reads⟩ = some after) :
    ∃ next nextSlots,
      SourceEffects.step ctx
        (.writeMap name keyTy valueTy keyExpr valueExpr) (sourceEnv, current) =
        .ok (sourceEnv, next) ∧
      GenericStateEncoding.encodeState state next = some nextSlots ∧
      after = ⟨[.vector nextSlots], reads⟩ := by
  obtain ⟨slot, located, segmentEval⟩ :=
    GenericStateWriteEvaluation.writeMap_candidate_eval state name keyTy valueTy
      keyExpr valueExpr base ctx candidateEnv key value compiled modulus
      candidateKey candidateValue keyCanonical valueCanonical
  have typedAt : state[slot]? = some sourceDeclaration :=
    GenericStateAdmission.source_find_matches_slot state name slot
      sourceDeclaration sourceFound located
  obtain ⟨next, entries, sourceStep, nextEncoded, nativeRun⟩ :=
    GenericStateSchemaSpans.writeMap_source_step ctx sourceEnv state current
      slots slot sourceDeclaration name keyTy valueTy keyExpr valueExpr key value
      reads typedAt sourceNamed sourceKind distinct encoded stateBound sourceKey
      sourceValue keyCanonical valueCanonical
  rw [segmentEval] at evaluated
  cases evaluated
  rw [nativeRun] at checked
  cases checked
  exact ⟨next, slots.set slot (.map ((scalar (number keyTy key),
    scalar (number valueTy value)) ::
    entries.filter (fun pair => pair.1 != scalar (number keyTy key)))),
    sourceStep, nextEncoded, rfl⟩

end Nightlean.Verification.GenericStateWriteAuthentication
