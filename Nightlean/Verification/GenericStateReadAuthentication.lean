import Nightlean.Verification.GenericStateReadCellEvaluation
import Nightlean.Verification.GenericStatePrefixEnvironment
import Nightlean.Verification.GenericStateSchemaSpans

namespace Nightlean.Verification.GenericStateReadAuthentication
open Backend NativeRelation ScalarNormalization NativeState

private theorem sourceCanonical (ctx : EvalContext) (ty : Ty)
    (value : ty.Denote) (modulus : ctx.modulus = Field.modulus)
    (canonical : Canonical ty value) :
    SourceEffects.canonicalValue ctx ty value = true := by
  cases ty with
  | native =>
    simpa [SourceEffects.canonicalValue, Canonical, number, modulus] using canonical.1
  | bool => rfl
  | uint maximum =>
    rcases canonical with ⟨bound, maximumBound, valueBound⟩
    have fieldBound : value < Field.modulus := by simpa [number] using bound
    simp [SourceEffects.canonicalValue, modulus, fieldBound,
      maximumBound, valueBound]

/-- A checked production cell-read segment authenticates the typed relation
candidate against the current source ledger slot. Earlier writes are allowed,
since the premise encodes the current tentative source state. -/
theorem readCell_candidate_source_step (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (current : LedgerState) (slots : List NativeState.Slot)
    (name destination : String) (ty : Ty)
    (base : Impact.Plan) (segment : List NativeState.Op)
    (slot : Nat) (candidate : ty.Denote)
    (reads : List NativeState.Cell) (after : NativeState.Machine)
    (compiled : Impact.appendEffect state (.readCell name destination ty) {} = .ok base)
    (found : state.findIdx? (·.name == name) = some slot)
    (declaration : StateDecl)
    (declarationAt : state[slot]? = some declaration)
    (named : declaration.name = name)
    (kind : declaration.kind = .cell ty)
    (encoded : GenericStateEncoding.encodeState state current = some slots)
    (lookup : candidateEnv.lookup destination = some (Value.pack ty candidate))
    (canonical : Canonical ty candidate)
    (modulus : ctx.modulus = Field.modulus)
    (evaluated : base.operations.mapM (GenericStateOps.evalOp ctx candidateEnv) =
      .ok segment)
    (checked : NativeState.run segment ⟨[.vector slots], reads⟩ = some after) :
    SourceEffects.step ctx (.readCell name destination ty) (sourceEnv, current) =
      .ok ((destination, Value.pack ty candidate) :: sourceEnv, current) ∧
    after = ⟨[.vector slots], reads ++
      [NativeState.field (scalar (number ty candidate))]⟩ := by
  obtain ⟨actualSlot, actualFound, actualEval⟩ :=
    GenericStateReadCellEvaluation.readCell_candidate_eval state name destination
      ty base ctx candidateEnv candidate compiled lookup modulus canonical
  rw [found] at actualFound
  have sameSlot : actualSlot = slot := (Option.some.inj actualFound).symm
  subst actualSlot
  rw [actualEval] at evaluated
  cases evaluated
  obtain ⟨value, sourceLookup, sourceCanonicalValue, sameCell, final⟩ :=
    GenericStateSchemaSpans.readCell_source_typed state current slots slot
      declaration name ty
      (NativeState.field (scalar (number ty candidate))) reads after
      declarationAt named kind encoded checked
  have sameEncoding :
      GenericStateEncoding.encodeValue ty (Value.pack ty candidate) =
        GenericStateEncoding.encodeValue ty (Value.pack ty value) := by
    rw [GenericStateEncoding.encodeValue_pack ty candidate canonical,
      GenericStateEncoding.encodeValue_pack ty value sourceCanonicalValue]
    exact congrArg some sameCell
  have equal := GenericStateEncoding.encodeValue_pack_injective ty
    candidate value canonical sourceCanonicalValue sameEncoding
  subst value
  have checkedCanonical := sourceCanonical ctx ty candidate modulus canonical
  constructor
  · simp [SourceEffects.step, sourceLookup, number_pack_as, checkedCanonical]
    rfl
  · exact final

end Nightlean.Verification.GenericStateReadAuthentication
