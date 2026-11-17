import Nightlean.Verification.GenericStateConverseRead
import Nightlean.Verification.GenericStateWriteSourceTrace
import Nightlean.Verification.GenericStateWriteEvaluation

namespace Nightlean.Verification.GenericStateConverseWrite
open Backend NativeRelation ScalarNormalization NativeState GenericStateEncoding

/-- A successful original cell write drives the actual compiled segment and
the same encoded VM successor. Candidate evaluation must agree on the
source-validated expression scope, established separately for full calls. -/
theorem source_writeCell_native (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (current : LedgerState) (slots : List Slot)
    (name : String) (ty : Ty) (expression : Expr ty)
    (sourceAfter : SourceEffects.Frame) (base : Impact.Plan)
    (reads : List Cell)
    (sourceStep : SourceEffects.step ctx (.writeCell name ty expression)
      (sourceEnv, current) = .ok sourceAfter)
    (candidateAgreement : expression.eval ctx candidateEnv =
      expression.eval ctx sourceEnv)
    (sourceDeclaration : StateDecl)
    (declared : state.find? (·.name == name) = some sourceDeclaration)
    (named : sourceDeclaration.name = name)
    (kind : sourceDeclaration.kind = .cell ty)
    (compiled : Impact.appendEffect state (.writeCell name ty expression) {} =
      .ok base)
    (encoded : encodeState state current = some slots)
    (distinct : state.Pairwise (fun left right => left.name ≠ right.name))
    (stateBound : state.length < Field.modulus)
    (modulus : ctx.modulus = Field.modulus) :
    ∃ slot value nextSlots,
      state.findIdx? (·.name == name) = some slot ∧
      base.operations.mapM (GenericStateOps.evalOp ctx candidateEnv) =
        .ok (GenericStateVM.writeCellOps slot
          (field (scalar (number ty value)))) ∧
      encodeState state sourceAfter.2 = some nextSlots ∧
      run (GenericStateVM.writeCellOps slot
        (field (scalar (number ty value))))
        ⟨[.vector slots], reads⟩ =
        some ⟨[.vector nextSlots], reads⟩ ∧
      sourceAfter.1 = sourceEnv := by
  obtain ⟨oldValue, value, _, sourceEval, canonical, sourceShape⟩ :=
    GenericStateWriteSourceTrace.writeCell_step_value ctx sourceEnv current
      name ty expression sourceAfter modulus sourceStep
  have candidateEval : expression.eval ctx candidateEnv = .ok value := by
    rw [candidateAgreement]
    exact sourceEval
  obtain ⟨slot, declaration, located, _, _, _, segmentEval⟩ :=
    GenericStateWriteEvaluation.writeCell_candidate_eval_located state name ty
      expression base ctx candidateEnv value compiled stateBound modulus
      candidateEval canonical
  have declarationAt := GenericStateAdmission.source_find_matches_slot
    state name slot sourceDeclaration declared located
  obtain ⟨next, sourceAgain, encodedNext, nativeRun⟩ :=
    GenericStateSchemaSpans.writeCell_source_step ctx sourceEnv state current
      slots slot sourceDeclaration name ty expression value reads declarationAt
      named kind distinct encoded stateBound sourceEval canonical
  have sameFrame : sourceAfter = (sourceEnv, next) := by
    rw [sourceStep] at sourceAgain
    exact Except.ok.inj sourceAgain
  refine ⟨slot, value,
    slots.set slot (.cell (field (scalar (number ty value)))), located,
    segmentEval, ?_, nativeRun, ?_⟩
  · rw [sameFrame]
    exact encodedNext
  · rw [sameFrame]

/-- A successful original map write drives the actual compiled key/value
segment and the same encoded VM successor. -/
theorem source_writeMap_native (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (current : LedgerState) (slots : List Slot)
    (name : String) (keyTy valueTy : Ty)
    (keyExpr : Expr keyTy) (valueExpr : Expr valueTy)
    (sourceAfter : SourceEffects.Frame) (base : Impact.Plan)
    (reads : List Cell)
    (sourceStep : SourceEffects.step ctx
      (.writeMap name keyTy valueTy keyExpr valueExpr)
      (sourceEnv, current) = .ok sourceAfter)
    (candidateKeyAgreement : keyExpr.eval ctx candidateEnv =
      keyExpr.eval ctx sourceEnv)
    (candidateValueAgreement : valueExpr.eval ctx candidateEnv =
      valueExpr.eval ctx sourceEnv)
    (sourceDeclaration : StateDecl)
    (declared : state.find? (·.name == name) = some sourceDeclaration)
    (named : sourceDeclaration.name = name)
    (kind : sourceDeclaration.kind = .map keyTy valueTy)
    (compiled : Impact.appendEffect state
      (.writeMap name keyTy valueTy keyExpr valueExpr) {} = .ok base)
    (encoded : encodeState state current = some slots)
    (distinct : state.Pairwise (fun left right => left.name ≠ right.name))
    (stateBound : state.length < Field.modulus)
    (modulus : ctx.modulus = Field.modulus) :
    ∃ slot key value nextSlots,
      state.findIdx? (·.name == name) = some slot ∧
      base.operations.mapM (GenericStateOps.evalOp ctx candidateEnv) =
        .ok (GenericStateVM.writeMapOps slot
          (scalar (number keyTy key)) (scalar (number valueTy value))) ∧
      encodeState state sourceAfter.2 = some nextSlots ∧
      run (GenericStateVM.writeMapOps slot
        (scalar (number keyTy key)) (scalar (number valueTy value)))
        ⟨[.vector slots], reads⟩ =
        some ⟨[.vector nextSlots], reads⟩ ∧
      sourceAfter.1 = sourceEnv := by
  obtain ⟨key, value, oldEntries, sourceKey, sourceValue,
    canonicalKey, canonicalValue, _, sourceShape⟩ :=
    GenericStateWriteSourceTrace.writeMap_step_values ctx sourceEnv current
      name keyTy valueTy keyExpr valueExpr sourceAfter modulus sourceStep
  have candidateKey : keyExpr.eval ctx candidateEnv = .ok key := by
    rw [candidateKeyAgreement]
    exact sourceKey
  have candidateValue : valueExpr.eval ctx candidateEnv = .ok value := by
    rw [candidateValueAgreement]
    exact sourceValue
  obtain ⟨slot, located, segmentEval⟩ :=
    GenericStateWriteEvaluation.writeMap_candidate_eval state name keyTy valueTy
      keyExpr valueExpr base ctx candidateEnv key value compiled modulus
      candidateKey candidateValue canonicalKey canonicalValue
  have declarationAt := GenericStateAdmission.source_find_matches_slot
    state name slot sourceDeclaration declared located
  obtain ⟨next, encodedEntries, sourceAgain, encodedNext, nativeRun⟩ :=
    GenericStateSchemaSpans.writeMap_source_step ctx sourceEnv state current
      slots slot sourceDeclaration name keyTy valueTy keyExpr valueExpr key value
      reads declarationAt named kind distinct encoded stateBound sourceKey
      sourceValue canonicalKey canonicalValue
  have sameFrame : sourceAfter = (sourceEnv, next) := by
    rw [sourceStep] at sourceAgain
    exact Except.ok.inj sourceAgain
  refine ⟨slot, key, value,
    slots.set slot (.map ((scalar (number keyTy key),
      scalar (number valueTy value)) ::
      encodedEntries.filter (fun pair => pair.1 != scalar (number keyTy key)))),
    located, segmentEval, ?_, nativeRun, ?_⟩
  · rw [sameFrame]
    exact encodedNext
  · rw [sameFrame]

end Nightlean.Verification.GenericStateConverseWrite
