import Nightlean.Verification.GenericStateConverseRead
import Nightlean.Verification.GenericStateAbsenceAuthentication

namespace Nightlean.Verification.GenericStateConverseAbsence
open Backend NativeRelation ScalarNormalization NativeState GenericStateEncoding

private theorem value_beq_sound (left right : Value) (same : (left == right) = true) :
    left = right := by
  cases left <;> cases right <;> simp_all [BEq.beq, Nightlean.instBEqValue.beq]

/-- Absence in the original typed map implies absence in its exact native
encoding. Canonical typed encodings prevent field-key collisions. -/
theorem source_absent_encoded (keyTy valueTy : Ty)
    (entries : List (Value × Value)) (encoded : List (Scalar × Scalar))
    (key : keyTy.Denote) (canonical : Canonical keyTy key)
    (mapped : entries.mapM (encodeMapEntry keyTy valueTy) = some encoded)
    (missing : entries.lookup (Value.pack keyTy key) = none) :
    encoded.any (fun pair => pair.1 == scalar (number keyTy key)) = false := by
  induction entries generalizing encoded with
  | nil =>
    simp only [List.mapM_nil] at mapped
    cases mapped
    rfl
  | cons entry rest ih =>
    simp only [List.mapM_cons] at mapped
    cases first : encodeMapEntry keyTy valueTy entry with
    | none => simp [first] at mapped
    | some pair =>
      cases later : rest.mapM (encodeMapEntry keyTy valueTy) with
      | none => simp [first, later] at mapped
      | some remaining =>
        simp [first, later] at mapped
        cases mapped
        have noSource := List.lookup_eq_none_iff.mp missing
        have tailMissing : rest.lookup (Value.pack keyTy key) = none := by
          apply List.lookup_eq_none_iff.mpr
          intro item member
          exact noSource item (List.mem_cons_of_mem _ member)
        have matched := encodeMapEntry_key_match keyTy valueTy entry pair key canonical first
        have headMissing : (pair.1 == scalar (number keyTy key)) = false := by
          cases equal : (pair.1 == scalar (number keyTy key)) with
          | false => rfl
          | true =>
            have rawEqual := value_beq_sound entry.1 (Value.pack keyTy key) (matched.trans equal)
            have different := noSource entry (by simp)
            rw [rawEqual] at different
            cases keyTy <;> simp [Value.pack, bne, BEq.beq, Nightlean.instBEqValue.beq] at different
        have tailAbsent := ih remaining later tailMissing
        simp [headMissing, tailAbsent]

private theorem encoded_map_slot (declarations : List StateDecl)
    (current : LedgerState) (slots : List Slot) (slot : Nat)
    (declaration : StateDecl) (name : String) (keyTy valueTy : Ty)
    (entries : List (Value × Value))
    (declared : declarations[slot]? = some declaration)
    (named : declaration.name = name)
    (kind : declaration.kind = .map keyTy valueTy)
    (encoded : encodeState declarations current = some slots)
    (lookup : current.maps.lookup name = some entries) :
    ∃ nativeEntries, entries.mapM (encodeMapEntry keyTy valueTy) = some nativeEntries ∧
      slots[slot]? = some (.map nativeEntries) := by
  have inRange : slot < declarations.length := List.getElem?_eq_some_iff.mp declared |>.1
  have slotsRange : slot < slots.length := by
    rw [encodeState_length declarations current slots encoded]
    exact inRange
  have slotEncoding := encodeState_slot declarations current slots slot encoded
  rw [declared] at slotEncoding
  simp only [Option.bind_some] at slotEncoding
  cases mapped : entries.mapM (encodeMapEntry keyTy valueTy) with
  | none =>
    have absent : slots[slot]? = none := by
      simpa [encodeDeclaration, named, kind, lookup, mapped] using slotEncoding
    exact False.elim (Nat.not_le_of_gt slotsRange (List.getElem?_eq_none_iff.mp absent))
  | some nativeEntries =>
    by_cases unique : (nativeEntries.map Prod.fst).eraseDups.length = nativeEntries.length
    · refine ⟨nativeEntries, rfl, ?_⟩
      simpa [encodeDeclaration, named, kind, lookup, mapped, unique] using slotEncoding
    · have absent : slots[slot]? = none := by
        simpa [encodeDeclaration, named, kind, lookup, mapped, unique] using slotEncoding
      exact False.elim (Nat.not_le_of_gt slotsRange (List.getElem?_eq_none_iff.mp absent))

/-- Original source absence drives the exact compiled segment and a successful
native missing-key check, with arbitrary source declaration spans. -/
theorem source_requireAbsent_native (ctx : EvalContext)
    (sourceEnv candidateEnv : EvalEnv) (state : List StateDecl)
    (current : LedgerState) (slots : List Slot)
    (name : String) (keyTy valueTy : Ty) (keyExpr : Expr keyTy)
    (sourceAfter : SourceEffects.Frame) (base : Impact.Plan) (reads : List Cell)
    (sourceStep : SourceEffects.step ctx (.requireAbsent name keyTy keyExpr)
      (sourceEnv, current) = .ok sourceAfter)
    (candidateAgreement : keyExpr.eval ctx candidateEnv = keyExpr.eval ctx sourceEnv)
    (declaration : StateDecl)
    (declared : state.find? (·.name == name) = some declaration)
    (named : declaration.name = name) (kind : declaration.kind = .map keyTy valueTy)
    (compiled : Impact.appendEffect state (.requireAbsent name keyTy keyExpr) {} = .ok base)
    (encoded : encodeState state current = some slots)
    (modulus : ctx.modulus = Field.modulus) :
    ∃ slot key, state.findIdx? (·.name == name) = some slot ∧
      base.operations.mapM (GenericStateOps.evalOp ctx candidateEnv) =
        .ok (GenericStateVM.requireAbsentOps slot (scalar (number keyTy key))) ∧
      run (GenericStateVM.requireAbsentOps slot (scalar (number keyTy key)))
        ⟨[.vector slots], reads⟩ = some ⟨[.vector slots], reads ++ [boolean false]⟩ ∧
      sourceAfter = (sourceEnv, current) := by
  obtain ⟨key, entries, keyEval, canonical, lookup, missing, sourceShape⟩ :=
    GenericStateSourceTrace.requireAbsent_step_key ctx sourceEnv current name keyTy keyExpr
      sourceAfter modulus sourceStep
  have candidateEval : keyExpr.eval ctx candidateEnv = .ok key := by
    rw [candidateAgreement]
    exact keyEval
  obtain ⟨slot, located, segmentEval⟩ :=
    GenericStateAbsenceAuthentication.requireAbsent_candidate_eval state name keyTy keyExpr
      base ctx candidateEnv key compiled modulus candidateEval canonical
  have declarationAt := GenericStateAdmission.source_find_matches_slot state name slot declaration declared located
  obtain ⟨nativeEntries, mapped, slotFound⟩ := encoded_map_slot state current slots slot
    declaration name keyTy valueTy entries declarationAt named kind encoded lookup
  have absent := source_absent_encoded keyTy valueTy entries nativeEntries key canonical mapped missing
  exact ⟨slot, key, located, segmentEval,
    GenericStateVM.requireAbsent_exact slots slot nativeEntries (scalar (number keyTy key))
      reads slotFound absent, sourceShape⟩

end Nightlean.Verification.GenericStateConverseAbsence
