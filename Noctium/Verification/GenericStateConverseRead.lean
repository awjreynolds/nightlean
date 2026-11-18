import Noctium.Verification.GenericStateSourceReadInputs
import Noctium.Verification.GenericStateReadCellEvaluation
import Noctium.Verification.GenericStateSchemaSpans

namespace Noctium.Verification.GenericStateConverseRead
open Backend NativeRelation ScalarNormalization NativeState GenericStateEncoding

/-- A successful original cell read supplies the exact candidate for the
production read equality segment. The current encoded slot makes the VM
segment succeed, including after an earlier source write. -/
theorem source_readCell_native (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (current : LedgerState) (slots : List Slot)
    (name destination : String) (ty : Ty)
    (sourceAfter : SourceEffects.Frame) (base : Impact.Plan)
    (reads : List Cell)
    (sourceStep : SourceEffects.step ctx (.readCell name destination ty)
      (sourceEnv, current) = .ok sourceAfter)
    (candidateLookup : candidateEnv.lookup destination =
      sourceAfter.1.lookup destination)
    (sourceDeclaration : StateDecl)
    (declared : state.find? (·.name == name) = some sourceDeclaration)
    (named : sourceDeclaration.name = name)
    (kind : sourceDeclaration.kind = .cell ty)
    (compiled : Impact.appendEffect state (.readCell name destination ty) {} =
      .ok base)
    (encoded : encodeState state current = some slots)
    (modulus : ctx.modulus = Field.modulus) :
    ∃ slot value,
      state.findIdx? (·.name == name) = some slot ∧
      base.operations.mapM (GenericStateOps.evalOp ctx candidateEnv) =
        .ok (GenericStateVM.readCellOps slot
          (field (scalar (number ty value)))) ∧
      run (GenericStateVM.readCellOps slot
        (field (scalar (number ty value))))
        ⟨[.vector slots], reads⟩ =
        some ⟨[.vector slots], reads ++ [field (scalar (number ty value))]⟩ ∧
      sourceAfter = ((destination, Value.pack ty value) :: sourceEnv, current) := by
  obtain ⟨value, sourceLookup, canonical, sourceShape⟩ :=
    GenericStateSourceTrace.readCell_step_value ctx sourceEnv current name
      destination ty sourceAfter modulus sourceStep
  have candidate : candidateEnv.lookup destination =
      some (Value.pack ty value) := by
    rw [candidateLookup, sourceShape]
    simp
  obtain ⟨slot, located, evaluated⟩ :=
    GenericStateReadCellEvaluation.readCell_candidate_eval state name
      destination ty base ctx candidateEnv value compiled candidate modulus canonical
  have declarationAt := GenericStateAdmission.source_find_matches_slot
    state name slot sourceDeclaration declared located
  have slotEncoding := encodeState_slot state current slots slot encoded
  rw [declarationAt] at slotEncoding
  simp only [Option.bind_some] at slotEncoding
  have declarationEncoding : encodeDeclaration current sourceDeclaration =
      some (.cell (field (scalar (number ty value)))) := by
    simp [encodeDeclaration, named, kind, sourceLookup,
      encodeValue_pack ty value canonical]
  rw [declarationEncoding] at slotEncoding
  refine ⟨slot, value, located, evaluated, ?_, sourceShape⟩
  exact GenericStateVM.readCell_exact slots slot
    (field (scalar (number ty value))) reads slotEncoding

end Noctium.Verification.GenericStateConverseRead
