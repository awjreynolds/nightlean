import Nightlean.Verification.NativeState
import Nightlean.Verification.ScalarNormalization
import Nightlean.Verification.SourceEffects
import Nightlean.Verification.GenericStateKeys

namespace Nightlean.Verification.GenericStateEncoding
open NativeRelation NativeState ScalarNormalization

/-- A native field cell retains the source type in the declaration schema.
Boolean cells use field alignment; membership results use bit alignment. -/
def encodeValue (ty : Ty) (raw : Value) : Option Cell := do
  let some value := raw.as ty | none
  let allowed : Bool := match ty with
    | .native => decide (number .native value < Field.modulus)
    | .bool => true
    | .uint maximum => decide (maximum ≤ ScalarPolicy.maxUint) &&
        decide (number (.uint maximum) value ≤ maximum) &&
          decide (number (.uint maximum) value < Field.modulus)
  if allowed then
    some (field (scalar (number ty value)))
  else none

def decodeValue : Ty → Cell → Option Value
  | .native, ⟨.field, value⟩ => some (.native value.val)
  | .bool, ⟨.field, value⟩ =>
    if value = zero then some (.bool false)
    else if value = one then some (.bool true) else none
  | .uint maximum, ⟨.field, value⟩ =>
    if value.val ≤ maximum then some (.uint maximum value.val) else none
  | _, _ => none

def encodeMapEntry (keyTy valueTy : Ty) (entry : Value × Value) : Option (Scalar × Scalar) := do
  let some key := encodeValue keyTy entry.1 | none
  let some value := encodeValue valueTy entry.2 | none
  some (key.value, value.value)

def encodeDeclaration (state : LedgerState) (declaration : StateDecl) : Option Slot :=
  match declaration.kind with
  | .cell ty => do
    let raw ← state.cells.lookup declaration.name
    let value ← encodeValue ty raw
    some (Slot.cell value)
  | .map keyTy valueTy => do
    let entries ← state.maps.lookup declaration.name
    let encoded ← entries.mapM (encodeMapEntry keyTy valueTy)
    if (encoded.map Prod.fst).eraseDups.length != encoded.length then none else
    some (Slot.map encoded)

/-- The ordered declarations are exactly the native root array slots. Missing,
mistyped, or noncanonical declared values reject before a VM trace is admitted. -/
def encodeState (declarations : List StateDecl) (state : LedgerState) :
    Option (List Slot) := declarations.mapM (encodeDeclaration state)

def initial (slots : List Slot) : Machine :=
  ⟨[.vector slots], []⟩

def cellCount (declarations : List StateDecl) : Nat :=
  (declarations.filter fun declaration => match declaration.kind with
    | .cell _ => true
    | .map _ _ => false).length

def mapCount (declarations : List StateDecl) : Nat :=
  declarations.length - cellCount declarations

/-- Admission concerns the schema and initial encoding. It asserts no source
transition result and no native trace outcome. -/
structure AdmittedState (declarations : List StateDecl)
    (source : LedgerState) (slots : List Slot) : Prop where
  uniqueDeclarations : uniqueNames (declarations.map (·.name)) = true
  uniqueCells : uniqueNames (source.cells.map Prod.fst) = true
  uniqueMaps : uniqueNames (source.maps.map Prod.fst) = true
  exactCellCount : source.cells.length = cellCount declarations
  exactMapCount : source.maps.length = mapCount declarations
  slotBound : declarations.length < Field.modulus
  encoded : encodeState declarations source = some slots

theorem AdmittedState.distinctDeclarations
    (admitted : AdmittedState declarations source slots) :
    declarations.Pairwise (fun left right => left.name ≠ right.name) := by
  have unique : (declarations.map (·.name)).eraseDups.length =
      (declarations.map (·.name)).length := by
    apply beq_iff_eq.mp
    simpa [uniqueNames] using admitted.uniqueDeclarations
  have namesDistinct := GenericStateKeys.nodup_of_eraseDups_length_eq
    (declarations.map (·.name)) unique
  exact List.Pairwise.of_map (fun declaration : StateDecl => declaration.name)
    (by intro left right different; exact different)
    (List.nodup_iff_pairwise_ne.mp namesDistinct)

theorem encodeState_nil (state : LedgerState) : encodeState [] state = some [] := rfl

theorem encodeState_length (declarations : List StateDecl) (state : LedgerState)
    (slots : List Slot) (encoded : encodeState declarations state = some slots) :
    slots.length = declarations.length := by
  induction declarations generalizing slots with
  | nil => simp [encodeState] at encoded; cases encoded; rfl
  | cons head tail ih =>
    simp only [encodeState, List.mapM_cons] at encoded
    cases first : encodeDeclaration state head with
    | none => simp [first] at encoded
    | some value =>
      cases rest : tail.mapM (encodeDeclaration state) with
      | none => simp [first, rest] at encoded
      | some result =>
        simp [first, rest] at encoded
        cases encoded
        simp [ih result rest]

/-- Each native root slot comes from the corresponding declared state item.
The option equality also covers out-of-range indexes without inventing a slot. -/
theorem encodeState_slot (declarations : List StateDecl) (state : LedgerState)
    (slots : List Slot) (slot : Nat)
    (accepted : encodeState declarations state = some slots) :
    slots[slot]? = (declarations[slot]?).bind (encodeDeclaration state) := by
  induction declarations generalizing slots slot with
  | nil =>
    simp [encodeState] at accepted
    cases accepted
    simp
  | cons declaration rest ih =>
    simp only [encodeState, List.mapM_cons] at accepted
    cases first : encodeDeclaration state declaration with
    | none => simp [first] at accepted
    | some value =>
      cases later : rest.mapM (encodeDeclaration state) with
      | none => simp [first, later] at accepted
      | some remainder =>
        simp [first, later] at accepted
        cases accepted
        cases slot with
        | zero => simp [first]
        | succ index => simpa using ih remainder index later

theorem encodeValue_pack (ty : Ty) (value : ty.Denote)
    (canonical : Canonical ty value) :
    encodeValue ty (Value.pack ty value) = some (field (scalar (number ty value))) := by
  cases ty with
  | native =>
    simp only [Canonical, number] at canonical
    simp [encodeValue, Value.pack, Value.as, number, canonical.1]
  | bool =>
    cases value <;> simp [encodeValue, Value.pack, Value.as]
  | uint maximum =>
    simp only [Canonical, number] at canonical
    simp [encodeValue, Value.pack, Value.as, number, canonical.1, canonical.2.1, canonical.2.2]

theorem encodeMapEntry_pack (keyTy valueTy : Ty)
    (key : keyTy.Denote) (value : valueTy.Denote)
    (keyCanonical : Canonical keyTy key)
    (valueCanonical : Canonical valueTy value) :
    encodeMapEntry keyTy valueTy
      (Value.pack keyTy key, Value.pack valueTy value) =
      some (scalar (number keyTy key), scalar (number valueTy value)) := by
  simp [encodeMapEntry, encodeValue_pack, keyCanonical, valueCanonical, field]

theorem decode_encode_pack (ty : Ty) (value : ty.Denote)
    (canonical : Canonical ty value) :
    decodeValue ty (field (scalar (number ty value))) = some (Value.pack ty value) := by
  cases ty with
  | native =>
    simp only [Canonical, number] at canonical
    simp [decodeValue, field, Value.pack, number, scalar_no_wrap _ canonical.1]
  | bool =>
    cases value <;> decide
  | uint maximum =>
    simp only [Canonical, number] at canonical
    simp [decodeValue, field, Value.pack, number,
      scalar_no_wrap _ canonical.1, canonical.2.2]

/-- Accepted typed encodings round-trip. This rules out a native read being
attributed to a different source value of the same declared type. -/
theorem decode_encodeValue (ty : Ty) (raw : Value) (cell : Cell)
    (accepted : encodeValue ty raw = some cell) :
    decodeValue ty cell = some raw := by
  cases ty with
  | native =>
    cases raw with
    | native value =>
      by_cases canonical : value < Field.modulus
      · simp [encodeValue, Value.as, number, canonical] at accepted
        cases accepted
        exact decode_encode_pack .native value ⟨canonical, trivial⟩
      · simp [encodeValue, Value.as, number, canonical] at accepted
    | bool _ => simp [encodeValue, Value.as] at accepted
    | uint _ _ => simp [encodeValue, Value.as] at accepted
  | bool =>
    cases raw with
    | native _ => simp [encodeValue, Value.as] at accepted
    | bool value =>
      simp [encodeValue, Value.as] at accepted
      cases accepted
      exact decode_encode_pack .bool value ⟨by cases value <;> decide, trivial⟩
    | uint _ _ => simp [encodeValue, Value.as] at accepted
  | uint maximum =>
    cases raw with
    | native _ => simp [encodeValue, Value.as] at accepted
    | bool _ => simp [encodeValue, Value.as] at accepted
    | uint found value =>
      by_cases same : maximum = found
      · subst found
        by_cases within : maximum ≤ ScalarPolicy.maxUint ∧
            value ≤ maximum ∧ value < Field.modulus
        · simp [encodeValue, Value.as, number, within.1, within.2.1,
            within.2.2] at accepted
          cases accepted
          exact decode_encode_pack (.uint maximum) value
            ⟨within.2.2, within.1, within.2.1⟩
        · simp [encodeValue, Value.as, number] at accepted
          have allowed : maximum ≤ ScalarPolicy.maxUint ∧
              value ≤ maximum ∧ value < Field.modulus :=
            ⟨accepted.1.1.1, of_decide_eq_true accepted.1.1.2,
              of_decide_eq_true accepted.1.2⟩
          exact False.elim (within allowed)
      · simp [encodeValue, Value.as, same] at accepted

theorem encodeValue_source (ty : Ty) (raw : Value) (cell : Cell)
    (accepted : encodeValue ty raw = some cell) :
    ∃ value, raw.as ty = some value ∧ Canonical ty value ∧
      cell = field (scalar (number ty value)) := by
  cases ty with
  | native =>
    cases raw with
    | native value =>
      by_cases bound : value < Field.modulus
      · simp [encodeValue, Value.as, number, bound] at accepted
        cases accepted
        exact ⟨value, rfl, ⟨bound, trivial⟩, rfl⟩
      · simp [encodeValue, Value.as, number, bound] at accepted
    | bool _ => simp [encodeValue, Value.as] at accepted
    | uint _ _ => simp [encodeValue, Value.as] at accepted
  | bool =>
    cases raw with
    | native _ => simp [encodeValue, Value.as] at accepted
    | bool value =>
      simp [encodeValue, Value.as] at accepted
      cases accepted
      exact ⟨value, rfl, ⟨by cases value <;> decide, trivial⟩, rfl⟩
    | uint _ _ => simp [encodeValue, Value.as] at accepted
  | uint maximum =>
    cases raw with
    | native _ => simp [encodeValue, Value.as] at accepted
    | bool _ => simp [encodeValue, Value.as] at accepted
    | uint found value =>
      by_cases same : maximum = found
      · subst found
        simp [encodeValue, Value.as, number] at accepted
        have hmax := accepted.1.1.1
        have hvalue := of_decide_eq_true accepted.1.1.2
        have hfield := of_decide_eq_true accepted.1.2
        have equal := accepted.2
        cases equal
        exact ⟨value, by simp [Value.as], ⟨hfield, hmax, hvalue⟩, rfl⟩
      · simp [encodeValue, Value.as, same] at accepted

theorem encoded_cell_source (state : LedgerState) (name : String)
    (ty : Ty) (cell : Cell)
    (encoded : encodeDeclaration state {name, kind := .cell ty} =
      some (.cell cell)) :
    ∃ raw, state.cells.lookup name = some raw ∧ decodeValue ty cell = some raw := by
  unfold encodeDeclaration at encoded
  cases found : state.cells.lookup name with
  | none => simp [found] at encoded
  | some raw =>
    cases packed : encodeValue ty raw with
    | none => simp [found, packed] at encoded
    | some actual =>
      simp [found, packed] at encoded
      cases encoded
      exact ⟨raw, rfl, decode_encodeValue ty raw cell packed⟩

theorem encoded_cell_typed (state : LedgerState) (name : String)
    (ty : Ty) (cell : Cell)
    (encoded : encodeDeclaration state {name, kind := .cell ty} =
      some (.cell cell)) :
    ∃ value,
      state.cells.lookup name = some (Value.pack ty value) ∧
      Canonical ty value ∧
      cell = field (scalar (number ty value)) := by
  unfold encodeDeclaration at encoded
  cases found : state.cells.lookup name with
  | none => simp [found] at encoded
  | some raw =>
    cases packed : encodeValue ty raw with
    | none => simp [found, packed] at encoded
    | some actual =>
      simp [found, packed] at encoded
      cases encoded
      obtain ⟨value, typed, canonical, same⟩ := encodeValue_source ty raw cell packed
      cases ty with
      | native =>
        cases raw <;> simp [Value.as] at typed
        cases typed
        exact ⟨value, rfl, canonical, same⟩
      | bool =>
        cases raw <;> simp [Value.as] at typed
        cases typed
        exact ⟨value, rfl, canonical, same⟩
      | uint maximum =>
        cases raw <;> simp [Value.as] at typed
        rcases typed with ⟨sameMax, sameValue⟩
        subst sameMax
        cases sameValue
        exact ⟨value, rfl, canonical, same⟩

private theorem option_mapM_member {α β : Type} (f : α → Option β)
    (items : List α) (results : List β) (item : α)
    (accepted : items.mapM f = some results) (member : item ∈ items) :
    ∃ result, f item = some result ∧ result ∈ results := by
  induction items generalizing results with
  | nil => simp at member
  | cons head tail ih =>
    simp only [List.mapM_cons] at accepted
    cases first : f head with
    | none => simp [first] at accepted
    | some value =>
      cases later : tail.mapM f with
      | none => simp [first, later] at accepted
      | some rest =>
        simp [first, later] at accepted
        cases accepted
        rcases List.mem_cons.mp member with equal | inTail
        · subst item
          exact ⟨value, first, by simp⟩
        · obtain ⟨result, encoded, inResults⟩ := ih rest later inTail
          exact ⟨result, encoded, List.mem_cons_of_mem _ inResults⟩

private theorem value_beq_eq (left right : Value) (same : (left == right) = true) :
    left = right := by
  cases left <;> cases right <;>
    simp [BEq.beq, Nightlean.instBEqValue.beq] at same ⊢ <;>
    exact same

private theorem lookup_member_value (entries : List (Value × Value))
    (key raw : Value) (found : entries.lookup key = some raw) :
    (key, raw) ∈ entries := by
  induction entries with
  | nil => simp at found
  | cons head tail ih =>
    rcases head with ⟨oldKey, oldValue⟩
    simp only [List.lookup_cons] at found
    split at found
    next same =>
      have keyEqual := value_beq_eq key oldKey same
      cases found
      simp [keyEqual]
    next => exact List.mem_cons_of_mem _ (ih found)

private theorem encodedMapEntry_key (keyTy valueTy : Ty)
    (key : keyTy.Denote) (raw : Value) (result : Scalar × Scalar)
    (canonical : Canonical keyTy key)
    (accepted : encodeMapEntry keyTy valueTy (Value.pack keyTy key, raw) =
      some result) :
    result.1 = scalar (number keyTy key) := by
  unfold encodeMapEntry at accepted
  rw [encodeValue_pack keyTy key canonical] at accepted
  cases valueEncoded : encodeValue valueTy raw with
  | none => simp [valueEncoded] at accepted
  | some cell =>
    simp [valueEncoded] at accepted
    cases accepted
    rfl

/-- A missing key in an encoded native map was also absent from the original
typed source map. A source association shadow cannot fabricate absence. -/
theorem encodedMap_absent (keyTy valueTy : Ty)
    (entries : List (Value × Value)) (encoded : List (Scalar × Scalar))
    (key : keyTy.Denote)
    (canonical : Canonical keyTy key)
    (accepted : entries.mapM (encodeMapEntry keyTy valueTy) = some encoded)
    (absent : encoded.any (fun pair => pair.1 == scalar (number keyTy key)) = false) :
    entries.lookup (Value.pack keyTy key) = none := by
  cases found : entries.lookup (Value.pack keyTy key) with
  | none => rfl
  | some raw =>
    have sourceMember : (Value.pack keyTy key, raw) ∈ entries :=
      lookup_member_value entries (Value.pack keyTy key) raw found
    obtain ⟨pair, encodedPair, pairMember⟩ :=
      option_mapM_member (encodeMapEntry keyTy valueTy) entries encoded
        (Value.pack keyTy key, raw) accepted sourceMember
    have keyEqual := encodedMapEntry_key keyTy valueTy key raw pair canonical encodedPair
    have present : encoded.any (fun item => item.1 == scalar (number keyTy key)) = true := by
      apply List.any_eq_true.mpr
      exact ⟨pair, pairMember, by simp [keyEqual]⟩
    rw [present] at absent
    contradiction

theorem encoded_map_source (state : LedgerState) (name : String)
    (keyTy valueTy : Ty) (encoded : List (Scalar × Scalar))
    (accepted : encodeDeclaration state {name, kind := .map keyTy valueTy} =
      some (.map encoded)) :
    ∃ entries,
      state.maps.lookup name = some entries ∧
      entries.mapM (encodeMapEntry keyTy valueTy) = some encoded := by
  unfold encodeDeclaration at accepted
  cases found : state.maps.lookup name with
  | none => simp [found] at accepted
  | some entries =>
    cases mapped : entries.mapM (encodeMapEntry keyTy valueTy) with
    | none => simp [found, mapped] at accepted
    | some result =>
      by_cases unique : (result.map Prod.fst).eraseDups.length != result.length
      · simp [found, mapped] at accepted
        have sameLength := accepted.1
        simp [sameLength] at unique
      · simp [found, mapped] at accepted
        cases accepted.2
        exact ⟨entries, rfl, mapped⟩

theorem encoded_map_nodup (state : LedgerState) (name : String)
    (keyTy valueTy : Ty) (encoded : List (Scalar × Scalar))
    (accepted : encodeDeclaration state {name, kind := .map keyTy valueTy} =
      some (.map encoded)) : (encoded.map Prod.fst).Nodup := by
  unfold encodeDeclaration at accepted
  cases found : state.maps.lookup name with
  | none => simp [found] at accepted
  | some entries =>
    cases mapped : entries.mapM (encodeMapEntry keyTy valueTy) with
    | none => simp [found, mapped] at accepted
    | some result =>
      simp [found, mapped] at accepted
      have lengthEq := accepted.1
      cases accepted.2
      apply GenericStateKeys.nodup_of_eraseDups_length_eq
      simpa only [List.length_map] using lengthEq

theorem updateEntry_lookup_same (key : String) (value : β)
    (entries : List (String × β)) :
    (SourceEffects.updateEntry key value entries).lookup key = some value := by
  simp [SourceEffects.updateEntry]

theorem updateEntry_lookup_other (key other : String) (value : β)
    (entries : List (String × β)) (different : other ≠ key) :
    (SourceEffects.updateEntry key value entries).lookup other =
      entries.lookup other := by
  unfold SourceEffects.updateEntry
  simp only [List.lookup_cons, show (other == key) = false by simp [different]]
  induction entries with
  | nil => rfl
  | cons head tail ih =>
    rcases head with ⟨oldKey, oldValue⟩
    by_cases removed : oldKey = key
    · have notOther : other ≠ oldKey := by simpa [removed] using different
      have notEqual : (other == oldKey) = false := by simp [notOther]
      have notKey : (other == key) = false := by simp [different]
      simp [removed, List.lookup_cons, notKey, ih]
    · by_cases found : other = oldKey
      · simp [removed, found]
      · have notEqual : (other == oldKey) = false := by simp [found]
        simp [removed, List.lookup_cons, notEqual, ih]

theorem encodeDeclaration_updateCell_other (state : LedgerState)
    (name : String) (raw : Value) (declaration : StateDecl)
    (different : declaration.name ≠ name) :
    encodeDeclaration {state with cells :=
      (SourceEffects.updateEntry name raw state.cells)} declaration =
      encodeDeclaration state declaration := by
  cases kind : declaration.kind with
  | cell ty =>
    simp [encodeDeclaration, kind,
      updateEntry_lookup_other name declaration.name raw state.cells different]
  | map keyTy valueTy => simp [encodeDeclaration, kind]

theorem encodeDeclaration_updateCell_same (state : LedgerState)
    (name : String) (ty : Ty) (value : ty.Denote)
    (canonical : Canonical ty value) :
    encodeDeclaration {state with cells :=
      (SourceEffects.updateEntry name (Value.pack ty value) state.cells)}
      {name, kind := .cell ty} =
      some (.cell (field (scalar (number ty value)))) := by
  simp [encodeDeclaration, updateEntry_lookup_same,
    encodeValue_pack, canonical]

theorem encodeState_updateCell_framed (declarations : List StateDecl)
    (state : LedgerState) (name : String) (raw : Value)
    (different : ∀ declaration ∈ declarations, declaration.name ≠ name) :
    encodeState declarations {state with cells :=
      (SourceEffects.updateEntry name raw state.cells)} =
      encodeState declarations state := by
  induction declarations with
  | nil => rfl
  | cons declaration rest ih =>
    have headDifferent := different declaration (by simp)
    have restDifferent : ∀ item ∈ rest, item.name ≠ name := by
      intro item member
      exact different item (by simp [member])
    have tailEq := ih restDifferent
    change rest.mapM (encodeDeclaration {state with cells :=
      (SourceEffects.updateEntry name raw state.cells)}) =
        rest.mapM (encodeDeclaration state) at tailEq
    simp only [encodeState, List.mapM_cons,
      encodeDeclaration_updateCell_other state name raw declaration headDifferent]
    rw [tailEq]

theorem encodeState_updateCell_at (declarations : List StateDecl)
    (state : LedgerState) (slots : List Slot) (slot : Nat)
    (name : String) (ty : Ty) (value : ty.Denote)
    (encoded : encodeState declarations state = some slots)
    (declaration : declarations[slot]? = some {name, kind := .cell ty})
    (distinct : declarations.Pairwise (fun left right => left.name ≠ right.name))
    (canonical : Canonical ty value) :
    encodeState declarations {state with cells :=
      (SourceEffects.updateEntry name (Value.pack ty value) state.cells)} =
      some (slots.set slot (.cell (field (scalar (number ty value))))) := by
  induction declarations generalizing slots slot with
  | nil => simp at declaration
  | cons head tail ih =>
    cases distinct with
    | cons headDifferent tailDistinct =>
      simp only [encodeState, List.mapM_cons] at encoded
      cases first : encodeDeclaration state head with
      | none => simp [first] at encoded
      | some old =>
        cases restEncoded : tail.mapM (encodeDeclaration state) with
        | none => simp [first, restEncoded] at encoded
        | some oldTail =>
          simp [first, restEncoded] at encoded
          cases encoded
          cases slot with
          | zero =>
            simp at declaration
            subst head
            have framed : encodeState tail {state with cells :=
                (SourceEffects.updateEntry name (Value.pack ty value) state.cells)} =
                encodeState tail state := by
              apply encodeState_updateCell_framed
              intro item member
              exact (headDifferent item member).symm
            have tailEq : tail.mapM (encodeDeclaration {state with cells :=
                (SourceEffects.updateEntry name (Value.pack ty value) state.cells)}) =
                tail.mapM (encodeDeclaration state) := framed
            simp only [encodeState, List.mapM_cons,
              encodeDeclaration_updateCell_same state name ty value canonical]
            rw [tailEq, restEncoded]
            rfl
          | succ index =>
            simp only [List.getElem?_cons_succ] at declaration
            have headNotTarget : head.name ≠ name :=
              headDifferent {name, kind := .cell ty} (List.mem_of_getElem? declaration)
            have tailUpdated := ih oldTail index restEncoded declaration tailDistinct
            have tailEq : tail.mapM (encodeDeclaration {state with cells :=
                (SourceEffects.updateEntry name (Value.pack ty value) state.cells)}) =
                some (oldTail.set index (.cell (field (scalar (number ty value))))) :=
              tailUpdated
            simp only [encodeState, List.mapM_cons,
              encodeDeclaration_updateCell_other state name (Value.pack ty value)
                head headNotTarget]
            rw [first, tailEq]
            rfl

/-- Each fixed source type has a left inverse through its canonical field
cell. Thus distinct typed keys cannot collapse in the native map encoding. -/
theorem encodeValue_pack_injective (ty : Ty) (left right : ty.Denote)
    (leftCanonical : Canonical ty left) (rightCanonical : Canonical ty right)
    (same : encodeValue ty (Value.pack ty left) = encodeValue ty (Value.pack ty right)) :
    left = right := by
  rw [encodeValue_pack ty left leftCanonical,
    encodeValue_pack ty right rightCanonical] at same
  have sameCell := Option.some.inj same
  have decoded := congrArg (decodeValue ty) sameCell
  rw [decode_encode_pack ty left leftCanonical,
    decode_encode_pack ty right rightCanonical] at decoded
  have packed := Option.some.inj decoded
  cases ty with
  | native => exact Value.native.inj packed
  | bool => exact Value.bool.inj packed
  | uint _ => exact Value.uint.inj packed |>.2

private theorem encodeMapEntry_key_cell (keyTy valueTy : Ty)
    (entry : Value × Value) (pair : Scalar × Scalar)
    (accepted : encodeMapEntry keyTy valueTy entry = some pair) :
    encodeValue keyTy entry.1 = some (field pair.1) := by
  unfold encodeMapEntry at accepted
  cases keyCell : encodeValue keyTy entry.1 with
  | none => simp [keyCell] at accepted
  | some cell =>
    cases valueCell : encodeValue valueTy entry.2 with
    | none => simp [keyCell, valueCell] at accepted
    | some result =>
      simp [keyCell, valueCell] at accepted
      cases accepted
      obtain ⟨typed, _, _, same⟩ := encodeValue_source keyTy entry.1 cell keyCell
      simp [same, field]

/-- The typed source key comparison and encoded scalar comparison agree for
each successful map entry. This prevents an encoded update from removing a
different source key. -/
theorem encodeMapEntry_key_match (keyTy valueTy : Ty)
    (entry : Value × Value) (pair : Scalar × Scalar)
    (key : keyTy.Denote) (canonical : Canonical keyTy key)
    (accepted : encodeMapEntry keyTy valueTy entry = some pair) :
    (entry.1 == Value.pack keyTy key) =
      (pair.1 == scalar (number keyTy key)) := by
  have cell := encodeMapEntry_key_cell keyTy valueTy entry pair accepted
  by_cases same : entry.1 = Value.pack keyTy key
  · rw [same] at cell ⊢
    rw [encodeValue_pack keyTy key canonical] at cell
    have pairEqual : pair.1 = scalar (number keyTy key) := by
      simpa [field] using congrArg Cell.value (Option.some.inj cell).symm
    cases keyTy <;> simp [pairEqual, Value.pack, BEq.beq, Nightlean.instBEqValue.beq]
  · have sourceFalse : (entry.1 == Value.pack keyTy key) = false := by
      cases sourceEq : (entry.1 == Value.pack keyTy key) with
      | false => rfl
      | true => exact False.elim (same (value_beq_eq _ _ sourceEq))
    have scalarFalse : (pair.1 == scalar (number keyTy key)) = false := by
      cases scalarEq : (pair.1 == scalar (number keyTy key)) with
      | false => rfl
      | true =>
        have pairEqual : pair.1 = scalar (number keyTy key) := by
          simpa using scalarEq
        rw [pairEqual] at cell
        have decoded := decode_encodeValue keyTy entry.1 _ cell
        rw [decode_encode_pack keyTy key canonical] at decoded
        exact False.elim (same (Option.some.inj decoded).symm)
    simp [sourceFalse, scalarFalse]

theorem encodeMapEntries_filter_key (keyTy valueTy : Ty)
    (entries : List (Value × Value)) (encoded : List (Scalar × Scalar))
    (key : keyTy.Denote) (canonical : Canonical keyTy key)
    (accepted : entries.mapM (encodeMapEntry keyTy valueTy) = some encoded) :
    (entries.filter (fun entry => !(entry.1 == Value.pack keyTy key))).mapM
      (encodeMapEntry keyTy valueTy) =
      some (encoded.filter (fun pair => pair.1 != scalar (number keyTy key))) := by
  induction entries generalizing encoded with
  | nil =>
    simp only [List.filter_nil, List.mapM_nil] at accepted ⊢
    simp at accepted
    cases accepted
    rfl
  | cons entry rest ih =>
    simp only [List.mapM_cons] at accepted
    cases first : encodeMapEntry keyTy valueTy entry with
    | none => simp [first] at accepted
    | some pair =>
      cases later : rest.mapM (encodeMapEntry keyTy valueTy) with
      | none => simp [first, later] at accepted
      | some remaining =>
        simp [first, later] at accepted
        cases accepted
        have restFiltered := ih remaining later
        have matched := encodeMapEntry_key_match keyTy valueTy entry pair key canonical first
        cases equal : (entry.1 == Value.pack keyTy key) with
        | false =>
          have encodedEqual : (pair.1 == scalar (number keyTy key)) = false := by
            simpa [equal] using matched.symm
          simp [equal, first, restFiltered, bne, encodedEqual]
        | true =>
          have encodedEqual : (pair.1 == scalar (number keyTy key)) = true := by
            simpa [equal] using matched.symm
          simp [equal, restFiltered, bne, encodedEqual]

theorem encodeMapEntries_update_key (keyTy valueTy : Ty)
    (entries : List (Value × Value)) (encoded : List (Scalar × Scalar))
    (key : keyTy.Denote) (value : valueTy.Denote)
    (keyCanonical : Canonical keyTy key)
    (valueCanonical : Canonical valueTy value)
    (accepted : entries.mapM (encodeMapEntry keyTy valueTy) = some encoded) :
    (SourceEffects.updateEntry (Value.pack keyTy key) (Value.pack valueTy value)
      entries).mapM (encodeMapEntry keyTy valueTy) =
      some ((scalar (number keyTy key), scalar (number valueTy value)) ::
        encoded.filter (fun pair => pair.1 != scalar (number keyTy key))) := by
  unfold SourceEffects.updateEntry
  simp [List.mapM_cons,
    encodeMapEntry_pack keyTy valueTy key value keyCanonical valueCanonical,
    encodeMapEntries_filter_key keyTy valueTy entries encoded key keyCanonical accepted]

theorem eraseDups_eq_self_of_nodup {α : Type} [BEq α] [LawfulBEq α]
    (items : List α) (distinct : items.Nodup) : items.eraseDups = items := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨headAbsent, tailDistinct⟩ := List.nodup_cons.mp distinct
    rw [List.eraseDups_cons]
    have retained : (tail.filter fun item => !(item == head)) = tail := by
      apply List.filter_eq_self.mpr
      intro item member
      apply bne_iff_ne.mpr
      intro same
      exact headAbsent (same ▸ member)
    rw [retained, ih tailDistinct]

theorem encodedMap_update_distinct (encoded : List (Scalar × Scalar))
    (key value : Scalar) (distinct : (encoded.map Prod.fst).Nodup) :
    (((key, value) :: encoded.filter (fun pair => pair.1 != key)).map Prod.fst).Nodup := by
  have pairwise : encoded.Pairwise (fun left right => left.1 ≠ right.1) :=
    List.pairwise_map.mp (List.nodup_iff_pairwise_ne.mp distinct)
  have filtered : ((encoded.filter (fun pair => pair.1 != key)).map Prod.fst).Nodup :=
    List.nodup_iff_pairwise_ne.mpr
      (List.pairwise_map.mpr (pairwise.filter fun pair => pair.1 != key))
  apply List.nodup_cons.mpr
  constructor
  · intro member
    obtain ⟨pair, pairMember, equal⟩ := List.mem_map.mp member
    obtain ⟨_, different⟩ := List.mem_filter.mp pairMember
    have differentKey : pair.1 ≠ key := bne_iff_ne.mp different
    exact differentKey equal
  · exact filtered

theorem encodeDeclaration_updateMap_other (state : LedgerState)
    (name : String) (entries : List (Value × Value)) (declaration : StateDecl)
    (different : declaration.name ≠ name) :
    encodeDeclaration {state with maps := (SourceEffects.updateEntry name entries state.maps)} declaration =
      encodeDeclaration state declaration := by
  cases kind : declaration.kind with
  | cell ty => simp [encodeDeclaration, kind]
  | map keyTy valueTy =>
    simp [encodeDeclaration, kind,
      updateEntry_lookup_other name declaration.name entries state.maps different]

theorem encodeDeclaration_updateMap_same (state : LedgerState)
    (name : String) (keyTy valueTy : Ty)
    (entries : List (Value × Value)) (encoded : List (Scalar × Scalar))
    (key : keyTy.Denote) (value : valueTy.Denote)
    (oldEncoded : entries.mapM (encodeMapEntry keyTy valueTy) = some encoded)
    (distinct : (encoded.map Prod.fst).Nodup)
    (keyCanonical : Canonical keyTy key)
    (valueCanonical : Canonical valueTy value) :
    encodeDeclaration {state with maps := (SourceEffects.updateEntry name
        (SourceEffects.updateEntry (Value.pack keyTy key) (Value.pack valueTy value) entries)
        state.maps)} {name, kind := .map keyTy valueTy} =
      some (.map ((scalar (number keyTy key), scalar (number valueTy value)) ::
        encoded.filter (fun pair => pair.1 != scalar (number keyTy key)))) := by
  have updated := encodeMapEntries_update_key keyTy valueTy entries encoded key value
    keyCanonical valueCanonical oldEncoded
  have noDuplicates := encodedMap_update_distinct encoded
    (scalar (number keyTy key)) (scalar (number valueTy value)) distinct
  have sameLength := eraseDups_eq_self_of_nodup _ noDuplicates
  simp [encodeDeclaration, updateEntry_lookup_same, updated]
  have concrete := sameLength
  simp only [List.map_cons] at concrete
  rw [concrete]
  simp

theorem encodeState_updateMap_framed (declarations : List StateDecl)
    (state : LedgerState) (name : String) (entries : List (Value × Value))
    (different : ∀ declaration ∈ declarations, declaration.name ≠ name) :
    encodeState declarations {state with maps := (SourceEffects.updateEntry name entries state.maps)} =
      encodeState declarations state := by
  induction declarations with
  | nil => rfl
  | cons declaration rest ih =>
    have headDifferent := different declaration (by simp)
    have restDifferent : ∀ item ∈ rest, item.name ≠ name := by
      intro item member
      exact different item (by simp [member])
    have tailEq := ih restDifferent
    change rest.mapM (encodeDeclaration {state with maps :=
      (SourceEffects.updateEntry name entries state.maps)}) =
        rest.mapM (encodeDeclaration state) at tailEq
    simp only [encodeState, List.mapM_cons,
      encodeDeclaration_updateMap_other state name entries declaration headDifferent]
    rw [tailEq]

theorem encodeState_updateMap_at (declarations : List StateDecl)
    (state : LedgerState) (slots : List Slot) (slot : Nat)
    (name : String) (keyTy valueTy : Ty)
    (entries : List (Value × Value)) (encodedEntries : List (Scalar × Scalar))
    (key : keyTy.Denote) (value : valueTy.Denote)
    (encoded : encodeState declarations state = some slots)
    (declaration : declarations[slot]? = some {name, kind := .map keyTy valueTy})
    (distinct : declarations.Pairwise (fun left right => left.name ≠ right.name))
    (mapEncoded : entries.mapM (encodeMapEntry keyTy valueTy) = some encodedEntries)
    (distinctKeys : (encodedEntries.map Prod.fst).Nodup)
    (keyCanonical : Canonical keyTy key)
    (valueCanonical : Canonical valueTy value) :
    encodeState declarations {state with maps := (SourceEffects.updateEntry name
      (SourceEffects.updateEntry (Value.pack keyTy key) (Value.pack valueTy value) entries)
      state.maps)} =
      some (slots.set slot (.map ((scalar (number keyTy key), scalar (number valueTy value)) ::
        encodedEntries.filter (fun pair => pair.1 != scalar (number keyTy key))))) := by
  induction declarations generalizing slots slot with
  | nil => simp at declaration
  | cons head tail ih =>
    cases distinct with
    | cons headDifferent tailDistinct =>
      simp only [encodeState, List.mapM_cons] at encoded
      cases first : encodeDeclaration state head with
      | none => simp [first] at encoded
      | some old =>
        cases restEncoded : tail.mapM (encodeDeclaration state) with
        | none => simp [first, restEncoded] at encoded
        | some oldTail =>
          simp [first, restEncoded] at encoded
          cases encoded
          cases slot with
          | zero =>
            simp at declaration
            subst head
            have framed : encodeState tail {state with maps := (SourceEffects.updateEntry name
                (SourceEffects.updateEntry (Value.pack keyTy key) (Value.pack valueTy value) entries)
                state.maps)} = encodeState tail state := by
              apply encodeState_updateMap_framed
              intro item member
              exact (headDifferent item member).symm
            have tailEq : tail.mapM (encodeDeclaration {state with maps := (SourceEffects.updateEntry name
                (SourceEffects.updateEntry (Value.pack keyTy key) (Value.pack valueTy value) entries)
                state.maps)}) = tail.mapM (encodeDeclaration state) := framed
            simp only [encodeState, List.mapM_cons,
              encodeDeclaration_updateMap_same state name keyTy valueTy entries encodedEntries key value
                mapEncoded distinctKeys keyCanonical valueCanonical]
            rw [tailEq, restEncoded]
            rfl
          | succ index =>
            simp only [List.getElem?_cons_succ] at declaration
            have headNotTarget : head.name ≠ name :=
              headDifferent {name, kind := .map keyTy valueTy} (List.mem_of_getElem? declaration)
            have tailUpdated := ih oldTail index restEncoded declaration tailDistinct
            have tailEq : tail.mapM (encodeDeclaration {state with maps := (SourceEffects.updateEntry name
                (SourceEffects.updateEntry (Value.pack keyTy key) (Value.pack valueTy value) entries)
                state.maps)}) =
                some (oldTail.set index (.map ((scalar (number keyTy key), scalar (number valueTy value)) ::
                  encodedEntries.filter (fun pair => pair.1 != scalar (number keyTy key))))) :=
              tailUpdated
            simp only [encodeState, List.mapM_cons,
              encodeDeclaration_updateMap_other state name
                (SourceEffects.updateEntry (Value.pack keyTy key) (Value.pack valueTy value) entries)
                head headNotTarget]
            rw [first, tailEq]
            rfl

theorem encodedMapEntry_typed (keyTy valueTy : Ty)
    (entry : Value × Value) (pair : Scalar × Scalar)
    (accepted : encodeMapEntry keyTy valueTy entry = some pair) :
    ∃ key value,
      entry.1.as keyTy = some key ∧ entry.2.as valueTy = some value ∧
      Canonical keyTy key ∧ Canonical valueTy value := by
  unfold encodeMapEntry at accepted
  cases keyCell : encodeValue keyTy entry.1 with
  | none => simp [keyCell] at accepted
  | some first =>
    cases valueCell : encodeValue valueTy entry.2 with
    | none => simp [keyCell, valueCell] at accepted
    | some second =>
      obtain ⟨key, keyTyped, keyCanonical, _⟩ :=
        encodeValue_source keyTy entry.1 first keyCell
      obtain ⟨value, valueTyped, valueCanonical, _⟩ :=
        encodeValue_source valueTy entry.2 second valueCell
      exact ⟨key, value, keyTyped, valueTyped, keyCanonical, valueCanonical⟩

theorem encodedMapEntries_typed (keyTy valueTy : Ty)
    (entries : List (Value × Value)) (encoded : List (Scalar × Scalar))
    (accepted : entries.mapM (encodeMapEntry keyTy valueTy) = some encoded) :
    ∀ entry ∈ entries,
      ∃ key value, entry.1.as keyTy = some key ∧ entry.2.as valueTy = some value := by
  intro entry member
  obtain ⟨pair, encodedPair, _⟩ := option_mapM_member
    (encodeMapEntry keyTy valueTy) entries encoded entry accepted member
  obtain ⟨key, value, keyTyped, valueTyped, _, _⟩ :=
    encodedMapEntry_typed keyTy valueTy entry pair encodedPair
  exact ⟨key, value, keyTyped, valueTyped⟩

end Nightlean.Verification.GenericStateEncoding
