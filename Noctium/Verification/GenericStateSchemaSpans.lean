import Noctium.Verification.GenericStateVM

namespace Noctium.Verification.GenericStateSchemaSpans
open GenericStateEncoding NativeState

/-- Source locations affect diagnostics. Native ledger encoding uses the
declared name and kind, so erasing locations preserves every slot. -/
def eraseSpan (declaration : StateDecl) : StateDecl :=
  {name := declaration.name, kind := declaration.kind}

def eraseSpans (declarations : List StateDecl) : List StateDecl :=
  declarations.map eraseSpan

theorem encodeDeclaration_eraseSpan (state : LedgerState) (declaration : StateDecl) :
    encodeDeclaration state (eraseSpan declaration) =
      encodeDeclaration state declaration := by
  cases declaration with
  | mk name kind span => cases kind <;> rfl

theorem encodeState_eraseSpans (declarations : List StateDecl)
    (state : LedgerState) :
    encodeState (eraseSpans declarations) state =
      encodeState declarations state := by
  induction declarations with
  | nil => rfl
  | cons head tail ih =>
    have tailEq : (tail.map eraseSpan).mapM (encodeDeclaration state) =
        tail.mapM (encodeDeclaration state) := by
      simpa only [eraseSpans, encodeState] using ih
    simp only [eraseSpans, List.map_cons, encodeState, List.mapM_cons]
    rw [encodeDeclaration_eraseSpan, tailEq]

theorem eraseSpans_length (declarations : List StateDecl) :
    (eraseSpans declarations).length = declarations.length := by
  simp [eraseSpans]

theorem eraseSpans_at (declarations : List StateDecl) (slot : Nat)
    (declaration : StateDecl)
    (found : declarations[slot]? = some declaration) :
    (eraseSpans declarations)[slot]? = some (eraseSpan declaration) := by
  simp [eraseSpans, List.getElem?_map, found]

theorem eraseSpans_distinct (declarations : List StateDecl)
    (distinct : declarations.Pairwise
      (fun left right => left.name ≠ right.name)) :
    (eraseSpans declarations).Pairwise
      (fun left right => left.name ≠ right.name) := by
  induction declarations with
  | nil => exact List.Pairwise.nil
  | cons head tail ih =>
    cases distinct with
    | cons headDistinct tailDistinct =>
      apply List.Pairwise.cons
      · intro item member
        obtain ⟨original, present, equal⟩ := List.mem_map.mp member
        subst item
        exact headDistinct original present
      · exact ih tailDistinct

theorem erased_at_cell (declarations : List StateDecl) (slot : Nat)
    (declaration : StateDecl) (name : String) (ty : Ty)
    (found : declarations[slot]? = some declaration)
    (named : declaration.name = name)
    (kind : declaration.kind = .cell ty) :
    (eraseSpans declarations)[slot]? = some {name, kind := .cell ty} := by
  rw [eraseSpans_at declarations slot declaration found]
  cases declaration with
  | mk actual actualKind span =>
    simp only at named kind
    subst actual
    subst actualKind
    rfl

theorem erased_at_map (declarations : List StateDecl) (slot : Nat)
    (declaration : StateDecl) (name : String) (keyTy valueTy : Ty)
    (found : declarations[slot]? = some declaration)
    (named : declaration.name = name)
    (kind : declaration.kind = .map keyTy valueTy) :
    (eraseSpans declarations)[slot]? =
      some {name, kind := .map keyTy valueTy} := by
  rw [eraseSpans_at declarations slot declaration found]
  cases declaration with
  | mk actual actualKind span =>
    simp only at named kind
    subst actual
    subst actualKind
    rfl

/-- The legacy typed read lemma applies to every source span carried by an
accepted declaration. -/
theorem readCell_source_typed (declarations : List StateDecl)
    (state : LedgerState) (items : List Slot) (slot : Nat)
    (declaration : StateDecl) (name : String) (ty : Ty)
    (expected : Cell) (reads : List Cell) (after : Machine)
    (found : declarations[slot]? = some declaration)
    (named : declaration.name = name)
    (kind : declaration.kind = .cell ty)
    (encoded : encodeState declarations state = some items)
    (accepted : run (GenericStateVM.readCellOps slot expected)
      ⟨[.vector items], reads⟩ = some after) :
    ∃ value,
      state.cells.lookup name = some (Value.pack ty value) ∧
      ScalarNormalization.Canonical ty value ∧
      expected = field (NativeRelation.scalar (ScalarNormalization.number ty value)) ∧
      after = ⟨[.vector items], reads ++ [expected]⟩ := by
  exact GenericStateVM.readCell_source_typed (eraseSpans declarations)
    state items slot name ty expected reads after
    (erased_at_cell declarations slot declaration name ty found named kind)
    (by rw [encodeState_eraseSpans]; exact encoded) accepted

/-- A source absence check has the same checked native result for arbitrary
declaration source spans. -/
theorem requireAbsent_source_step (ctx : EvalContext) (env : EvalEnv)
    (declarations : List StateDecl) (state : LedgerState)
    (items : List Slot) (slot : Nat) (declaration : StateDecl)
    (name : String) (keyTy valueTy : Ty) (keyExpr : Expr keyTy)
    (key : keyTy.Denote) (reads : List Cell) (after : Machine)
    (found : declarations[slot]? = some declaration)
    (named : declaration.name = name)
    (kind : declaration.kind = .map keyTy valueTy)
    (encoded : encodeState declarations state = some items)
    (keyEval : keyExpr.eval ctx env = .ok key)
    (canonical : ScalarNormalization.Canonical keyTy key)
    (accepted : run (GenericStateVM.requireAbsentOps slot
      (NativeRelation.scalar (ScalarNormalization.number keyTy key)))
      ⟨[.vector items], reads⟩ = some after) :
    SourceEffects.step ctx (.requireAbsent name keyTy keyExpr) (env, state) =
      .ok (env, state) ∧
    after = ⟨[.vector items], reads ++ [boolean false]⟩ := by
  exact GenericStateVM.requireAbsent_source_step ctx env (eraseSpans declarations)
    state items slot name keyTy valueTy keyExpr key reads after
    (erased_at_map declarations slot declaration name keyTy valueTy found named kind)
    (by rw [encodeState_eraseSpans]; exact encoded) keyEval canonical accepted

/-- The existing cell-write transition proof transfers across arbitrary
source locations without altering its source or native semantics. -/
theorem writeCell_source_step (ctx : EvalContext) (env : EvalEnv)
    (declarations : List StateDecl) (state : LedgerState)
    (items : List Slot) (slot : Nat) (declaration : StateDecl)
    (name : String) (ty : Ty) (expression : Expr ty)
    (value : ty.Denote) (reads : List Cell)
    (found : declarations[slot]? = some declaration)
    (named : declaration.name = name)
    (kind : declaration.kind = .cell ty)
    (distinct : declarations.Pairwise
      (fun left right => left.name ≠ right.name))
    (encoded : encodeState declarations state = some items)
    (slotBound : declarations.length < Field.modulus)
    (evaluated : expression.eval ctx env = .ok value)
    (canonical : ScalarNormalization.Canonical ty value) :
    ∃ next,
      SourceEffects.step ctx (.writeCell name ty expression) (env, state) =
        .ok (env, next) ∧
      encodeState declarations next =
        some (items.set slot (.cell (field
          (NativeRelation.scalar (ScalarNormalization.number ty value))))) ∧
      run (GenericStateVM.writeCellOps slot
        (field (NativeRelation.scalar (ScalarNormalization.number ty value))))
        ⟨[.vector items], reads⟩ =
        some ⟨[.vector (items.set slot (.cell (field
          (NativeRelation.scalar (ScalarNormalization.number ty value)))))], reads⟩ := by
  obtain ⟨next, source, successor, native⟩ :=
    GenericStateVM.writeCell_source_step ctx env (eraseSpans declarations)
      state items slot name ty expression value reads
      (erased_at_cell declarations slot declaration name ty found named kind)
      (eraseSpans_distinct declarations distinct)
      (by rw [encodeState_eraseSpans]; exact encoded)
      (by simpa [eraseSpans_length] using slotBound) evaluated canonical
  exact ⟨next, source, by simpa only [encodeState_eraseSpans] using successor,
    native⟩

/-- The existing map-write transition proof transfers across arbitrary
declaration source locations. -/
theorem writeMap_source_step (ctx : EvalContext) (env : EvalEnv)
    (declarations : List StateDecl) (state : LedgerState)
    (items : List Slot) (slot : Nat) (declaration : StateDecl)
    (name : String) (keyTy valueTy : Ty)
    (keyExpr : Expr keyTy) (valueExpr : Expr valueTy)
    (key : keyTy.Denote) (value : valueTy.Denote) (reads : List Cell)
    (found : declarations[slot]? = some declaration)
    (named : declaration.name = name)
    (kind : declaration.kind = .map keyTy valueTy)
    (distinct : declarations.Pairwise
      (fun left right => left.name ≠ right.name))
    (encoded : encodeState declarations state = some items)
    (slotBound : declarations.length < Field.modulus)
    (keyEval : keyExpr.eval ctx env = .ok key)
    (valueEval : valueExpr.eval ctx env = .ok value)
    (keyCanonical : ScalarNormalization.Canonical keyTy key)
    (valueCanonical : ScalarNormalization.Canonical valueTy value) :
    ∃ (next : LedgerState)
      (encodedEntries : List (NativeRelation.Scalar × NativeRelation.Scalar)),
      SourceEffects.step ctx (.writeMap name keyTy valueTy keyExpr valueExpr)
        (env, state) = .ok (env, next) ∧
      encodeState declarations next =
        some (items.set slot (.map
          ((NativeRelation.scalar (ScalarNormalization.number keyTy key),
            NativeRelation.scalar (ScalarNormalization.number valueTy value)) ::
          encodedEntries.filter (fun pair => pair.1 !=
            NativeRelation.scalar (ScalarNormalization.number keyTy key))))) ∧
      run (GenericStateVM.writeMapOps slot
        (NativeRelation.scalar (ScalarNormalization.number keyTy key))
        (NativeRelation.scalar (ScalarNormalization.number valueTy value)))
        ⟨[.vector items], reads⟩ =
        some ⟨[.vector (items.set slot (.map
          ((NativeRelation.scalar (ScalarNormalization.number keyTy key),
            NativeRelation.scalar (ScalarNormalization.number valueTy value)) ::
          encodedEntries.filter (fun pair => pair.1 !=
            NativeRelation.scalar (ScalarNormalization.number keyTy key)))))], reads⟩ := by
  obtain ⟨next, entries, source, successor, native⟩ :=
    GenericStateVM.writeMap_source_step ctx env (eraseSpans declarations)
      state items slot name keyTy valueTy keyExpr valueExpr key value reads
      (erased_at_map declarations slot declaration name keyTy valueTy found named kind)
      (eraseSpans_distinct declarations distinct)
      (by rw [encodeState_eraseSpans]; exact encoded)
      (by simpa [eraseSpans_length] using slotBound)
      keyEval valueEval keyCanonical valueCanonical
  exact ⟨next, entries, source,
    by simpa only [encodeState_eraseSpans] using successor, native⟩

end Noctium.Verification.GenericStateSchemaSpans
