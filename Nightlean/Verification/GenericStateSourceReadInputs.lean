import Nightlean.Verification.GenericStateSourceTrace
import Nightlean.Verification.GenericStateReadTape
import Nightlean.Verification.GenericStateInputValues

namespace Nightlean.Verification.GenericStateSourceReadInputs
open Backend NativeRelation ScalarNormalization

/-- Record the relation input value observed after one original source effect.
The current read count fixes the generated absence name, matching production
Impact.appendEffect. A successful cell read always binds its destination. -/
def effectEntries (effect : Effect) (ordinal : Nat)
    (after : SourceEffects.Frame) : List (Impact.Read × Scalar) :=
  match effect with
  | .readCell _ destination ty =>
    [({name := destination, ty},
      match after.1.lookup destination with
      | some raw => scalar (valueNumber raw)
      | none => zero)]
  | .requireAbsent .. =>
    [({name := GenericStateNativeReadNames.absenceName ordinal, ty := .bool}, zero)]
  | _ => []

theorem effectEntries_names (effect : Effect) (ordinal : Nat)
    (after : SourceEffects.Frame) :
    (effectEntries effect ordinal after).map Prod.fst =
      GenericStateReadTape.effectReadChunk effect ordinal := by
  cases effect <;> rfl

theorem effectEntries_length (effect : Effect) (ordinal : Nat)
    (after : SourceEffects.Frame) :
    (effectEntries effect ordinal after).length =
      (GenericStateReadTape.effectReadChunk effect ordinal).length := by
  rw [← effectEntries_names, List.length_map]

/-- On a successful source cell read, the instrumented value equals the
canonical field encoding of the actual value bound for later effects. -/
theorem effectEntries_readCell (ctx : EvalContext) (before after : SourceEffects.Frame)
    (ordinal : Nat) (name destination : String) (ty : Ty)
    (modulus : ctx.modulus = Field.modulus)
    (success : SourceEffects.step ctx (.readCell name destination ty) before =
      .ok after) :
    ∃ value : ty.Denote,
      Canonical ty value ∧
      effectEntries (.readCell name destination ty) ordinal after =
        [({name := destination, ty}, scalar (number ty value))] := by
  rcases before with ⟨env, state⟩
  obtain ⟨value, _, canonical, final⟩ :=
    GenericStateSourceTrace.readCell_step_value ctx env state name destination
      ty after modulus success
  subst after
  refine ⟨value, canonical, ?_⟩
  simp [effectEntries, valueNumber_pack]

theorem effectEntries_absence (ordinal : Nat) (after : SourceEffects.Frame)
    (name : String) (keyTy : Ty) (keyExpr : Expr keyTy) :
    effectEntries (.requireAbsent name keyTy keyExpr) ordinal after =
      [({name := GenericStateNativeReadNames.absenceName ordinal, ty := .bool},
        zero)] := rfl

theorem canonical_source_bound (ty : Ty) (value : ty.Denote)
    (canonical : Canonical ty value) :
    (scalar (number ty value)).val ≤ Native.sourceMaximum ty := by
  have noWrap : (scalar (number ty value)).val = number ty value := by
    exact Nat.mod_eq_of_lt canonical.1
  rw [noWrap]
  cases ty with
  | native =>
    have bound : number .native value < Field.modulus := canonical.1
    change number .native value ≤ Field.modulus - 1
    omega
  | bool =>
    cases value <;> simp [Native.sourceMaximum, number]
  | uint maximum =>
    exact canonical.2.2

theorem sourceValue_roundtrip (ty : Ty) (value : ty.Denote)
    (canonical : Canonical ty value) :
    GenericStateInputValues.sourceValue ty (scalar (number ty value)) = value := by
  cases ty with
  | native =>
    change (scalar value).val = value
    exact scalar_no_wrap value (by simpa [number] using canonical.1)
  | bool =>
    cases value <;>
      simp [GenericStateInputValues.sourceValue, number, scalar, Field.modulus]
  | uint maximum =>
    change (scalar value).val = value
    exact scalar_no_wrap value (by simpa [number] using canonical.1)

/-- Successful source effects produce native read values within each
declared type's actual relation input bound. -/
theorem effectEntries_bounds (ctx : EvalContext) (effect : Effect)
    (ordinal : Nat) (before after : SourceEffects.Frame)
    (modulus : ctx.modulus = Field.modulus)
    (success : SourceEffects.step ctx effect before = .ok after) :
    ∀ pair ∈ effectEntries effect ordinal after,
      pair.2.val ≤ Native.sourceMaximum pair.1.ty := by
  cases effect with
  | readCell name destination ty =>
    obtain ⟨value, canonical, shape⟩ :=
      effectEntries_readCell ctx before after ordinal name destination ty
        modulus success
    rw [shape]
    intro pair member
    simp only [List.mem_singleton] at member
    subst pair
    exact canonical_source_bound ty value canonical
  | requireAbsent name keyTy key =>
    rw [effectEntries_absence]
    intro pair member
    simp only [List.mem_singleton] at member
    subst pair
    simp [Native.sourceMaximum, NativeRelation.zero]
  | readMap name destination keyTy valueTy key => simp [effectEntries]
  | require condition => simp [effectEntries]
  | writeCell name ty value => simp [effectEntries]
  | writeMap name keyTy valueTy key value => simp [effectEntries]

/-- A proof-side pass over the original source step evaluator. It records
typed native read inputs in exact source effect order while returning the
same final source frame. -/
def sourceReadInputs (ctx : EvalContext) :
    List Effect → Nat → SourceEffects.Frame →
      Except String (List (Impact.Read × Scalar) × SourceEffects.Frame)
  | [], _, frame => .ok ([], frame)
  | effect :: rest, ordinal, frame => do
      let next ← SourceEffects.step ctx effect frame
      let head := effectEntries effect ordinal next
      let (tail, final) ← sourceReadInputs ctx rest (ordinal + head.length) next
      pure (head ++ tail, final)

/-- Inversion of the instrumentation keeps the original source step and its
live read-count ordinal visible to the native-trace completeness induction. -/
theorem sourceReadInputs_cons (ctx : EvalContext) (effect : Effect)
    (rest : List Effect) (ordinal : Nat)
    (before after : SourceEffects.Frame)
    (entries : List (Impact.Read × Scalar))
    (success : sourceReadInputs ctx (effect :: rest) ordinal before =
      .ok (entries, after)) :
    ∃ middle tail,
      SourceEffects.step ctx effect before = .ok middle ∧
      sourceReadInputs ctx rest
        (ordinal + (effectEntries effect ordinal middle).length) middle =
        .ok (tail, after) ∧
      entries = effectEntries effect ordinal middle ++ tail := by
  cases first : SourceEffects.step ctx effect before with
  | error message => simp [sourceReadInputs, first, bind, Except.bind] at success
  | ok middle =>
    cases later : sourceReadInputs ctx rest
      (ordinal + (effectEntries effect ordinal middle).length) middle with
    | error message =>
      simp [sourceReadInputs, first, later, bind, Except.bind] at success
    | ok pair =>
      rcases pair with ⟨tail, final⟩
      simp only [sourceReadInputs, first, later, bind, Except.bind,
        pure, Except.pure] at success
      cases success
      exact ⟨middle, tail, rfl, later, rfl⟩

/-- Every successful original effect fold has exactly one instrumented read
list with the same final environment and tentative ledger state. -/
theorem sourceReadInputs_of_fold (ctx : EvalContext) (effects : List Effect)
    (ordinal : Nat) (before after : SourceEffects.Frame)
    (success : SourceEffects.fold ctx effects before = .ok after) :
    ∃ entries, sourceReadInputs ctx effects ordinal before = .ok (entries, after) := by
  induction effects generalizing ordinal before with
  | nil =>
    simp only [SourceEffects.fold_nil] at success
    cases success
    exact ⟨[], rfl⟩
  | cons effect rest ih =>
    obtain ⟨middle, first, later⟩ :=
      GenericStateSourceTrace.source_cons ctx effect rest before after success
    obtain ⟨tail, tailResult⟩ := ih (ordinal +
      (effectEntries effect ordinal middle).length) middle later
    refine ⟨effectEntries effect ordinal middle ++ tail, ?_⟩
    simp [sourceReadInputs, first, tailResult, bind, Except.bind,
      pure, Except.pure]

theorem sourceReadInputs_frame (ctx : EvalContext) (effects : List Effect)
    (ordinal : Nat) (before after : SourceEffects.Frame)
    (entries : List (Impact.Read × Scalar))
    (success : sourceReadInputs ctx effects ordinal before = .ok (entries, after)) :
    SourceEffects.fold ctx effects before = .ok after := by
  induction effects generalizing ordinal before after entries with
  | nil =>
    simp only [sourceReadInputs] at success
    cases success
    rfl
  | cons effect rest ih =>
    cases first : SourceEffects.step ctx effect before with
    | error message => simp [sourceReadInputs, first, bind, Except.bind] at success
    | ok middle =>
      cases later : sourceReadInputs ctx rest
        (ordinal + (effectEntries effect ordinal middle).length) middle with
      | error message =>
        simp [sourceReadInputs, first, later, bind, Except.bind] at success
      | ok pair =>
        rcases pair with ⟨tail, final⟩
        simp only [sourceReadInputs, first, later, bind, Except.bind,
          pure, Except.pure] at success
        cases success
        rw [SourceEffects.fold_cons, first]
        exact ih _ _ _ _ later

/-- The instrumented source reads have exactly the metadata order and
generated absence ordinals of the actual production read chunks. -/
theorem sourceReadInputs_names (ctx : EvalContext) (effects : List Effect)
    (ordinal : Nat) (before after : SourceEffects.Frame)
    (entries : List (Impact.Read × Scalar))
    (success : sourceReadInputs ctx effects ordinal before = .ok (entries, after)) :
    entries.map Prod.fst =
      (GenericStateReadTape.readChunks effects ordinal).flatten := by
  induction effects generalizing ordinal before after entries with
  | nil =>
    simp only [sourceReadInputs] at success
    cases success
    rfl
  | cons effect rest ih =>
    cases first : SourceEffects.step ctx effect before with
    | error message => simp [sourceReadInputs, first, bind, Except.bind] at success
    | ok middle =>
      cases later : sourceReadInputs ctx rest
        (ordinal + (effectEntries effect ordinal middle).length) middle with
      | error message =>
        simp [sourceReadInputs, first, later, bind, Except.bind] at success
      | ok pair =>
        rcases pair with ⟨tail, final⟩
        simp only [sourceReadInputs, first, later, bind, Except.bind,
          pure, Except.pure] at success
        cases success
        simp only [List.map_append, GenericStateReadTape.readChunks,
          List.flatten_cons]
        rw [effectEntries_names]
        rw [← effectEntries_length effect ordinal middle]
        exact congrArg (GenericStateReadTape.effectReadChunk effect ordinal ++ ·)
          (ih _ _ _ _ later)

/-- The input bounds needed by the native relation producer follow from
successful original source execution, one recorded read at a time. -/
theorem sourceReadInputs_bounds (ctx : EvalContext) (effects : List Effect)
    (ordinal : Nat) (before after : SourceEffects.Frame)
    (entries : List (Impact.Read × Scalar))
    (modulus : ctx.modulus = Field.modulus)
    (success : sourceReadInputs ctx effects ordinal before = .ok (entries, after)) :
    ∀ pair ∈ entries, pair.2.val ≤ Native.sourceMaximum pair.1.ty := by
  induction effects generalizing ordinal before after entries with
  | nil =>
    simp only [sourceReadInputs] at success
    cases success
    simp
  | cons effect rest ih =>
    cases first : SourceEffects.step ctx effect before with
    | error message => simp [sourceReadInputs, first, bind, Except.bind] at success
    | ok middle =>
      cases later : sourceReadInputs ctx rest
        (ordinal + (effectEntries effect ordinal middle).length) middle with
      | error message =>
        simp [sourceReadInputs, first, later, bind, Except.bind] at success
      | ok pair =>
        rcases pair with ⟨tail, final⟩
        simp only [sourceReadInputs, first, later, bind, Except.bind,
          pure, Except.pure] at success
        cases success
        intro item member
        rcases List.mem_append.mp member with firstMember | tailMember
        · exact effectEntries_bounds ctx effect ordinal before middle modulus
            first item firstMember
        · exact ih _ _ _ _ later item tailMember

end Nightlean.Verification.GenericStateSourceReadInputs
