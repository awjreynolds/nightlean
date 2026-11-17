import Nightlean.Verification.GenericStateNativeReadNames
import Nightlean.Verification.GenericStateAliases

namespace Nightlean.Verification.GenericStateReadAliasLookup
open Backend.Native GenericStateCircuitParts

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem except_bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    Except.bind first next = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Except.bind]

private theorem read_alias_lookup (reads : List Backend.Impact.Read)
    (read : Backend.Impact.Read) (member : read ∈ reads) :
    (reads.map (fun item => (item.name, Term.input ("%input_" ++ item.name)))).lookup
      read.name = some (.input ("%input_" ++ read.name)) := by
  induction reads with
  | nil => cases member
  | cons head rest ih =>
    by_cases same : read.name = head.name
    · simp [same]
    · have different : (read.name == head.name) = false := by simp [same]
      have present : read ∈ rest := by
        rcases List.mem_cons.mp member with equal | present
        · cases equal
          exact False.elim (same rfl)
        · exact present
      simp only [List.map_cons, List.lookup_cons, different]
      exact ih present

private theorem lookup_none_of_names_absent (items : List (String × α))
    (name : String) (absent : name ∉ items.map Prod.fst) :
    items.lookup name = none := by
  apply List.lookup_eq_none_iff.mpr
  intro pair member
  have different : name ≠ pair.1 := by
    intro equal
    exact absent (List.mem_map.mpr ⟨pair, member, equal.symm⟩)
  simp [different]

/-- Normalizing fresh output aliases does not replace an existing read alias. -/
theorem outputFold_preserves_lookup (outputs : List Output)
    (before after : OutputFrame) (name : String)
    (fresh : ∀ output ∈ outputs, name ≠ output.name)
    (accepted : outputFold before outputs = .ok after) :
    after.1.lookup name = before.1.lookup name := by
  induction outputs generalizing before with
  | nil =>
    change Except.ok before = .ok after at accepted
    cases accepted
    rfl
  | cons output rest ih =>
    rw [outputFold_cons] at accepted
    simp only [except_bind_ok] at accepted
    obtain ⟨middle, first, later⟩ := accepted
    have suffix := ih middle (fun item member => fresh item (by simp [member])) later
    rw [suffix]
    unfold appendOutput at first
    simp only [bind_ok] at first
    obtain ⟨result, _, equal⟩ := first
    cases equal
    have different : (name == output.name) = false := by
      simp [fresh output (by simp)]
    simp only [List.lookup_cons, different]

/-- The accepted production output fold retains each actual ledger read as
its exact native input term. This follows from actual source name freshness. -/
theorem normalized_read_alias_lookup (state : List StateDecl) (ep : Entrypoint)
    (plan : Backend.Impact.Plan) (frame : OutputFrame)
    (lowered : Backend.Impact.lower state ep = .ok plan)
    (normalized : normalizeOutputs (initialAliases ep plan) ep.circuit.outputs = .ok frame) :
    ∀ read ∈ plan.reads.drop ((ep.circuit.inputs.filter (·.visibility == .«public»)).length),
      frame.1.lookup read.name = some (.input ("%input_" ++ read.name)) := by
  have fresh := (GenericStateNativeReadNames.lower_native_read_names
    state ep plan lowered).2
  intro read member
  have absent := fresh read member
  have unchanged := outputFold_preserves_lookup ep.circuit.outputs
    (initialAliases ep plan, [], []) frame read.name
    (by
      intro output present equal
      apply absent
      exact List.mem_append_right _ (List.mem_map.mpr ⟨output, present, equal.symm⟩))
    normalized
  rw [unchanged, GenericStateAliases.initialAliases_eq]
  have inputAbsent :
      (ScalarNormalization.circuitAliases ep.circuit).lookup read.name = none := by
    apply lookup_none_of_names_absent
    simpa only [ScalarNormalization.circuitAliases, List.map_map,
      Function.comp_def] using (fun member => absent (List.mem_append_left _ member))
  simp only [List.lookup_append, inputAbsent, Option.none_or]
  exact read_alias_lookup _ read member

/-- Invert the actual native expected constructor and retain exact read alias
lookups in its accepted output frame. -/
theorem expected_read_alias_lookup (state : List StateDecl) (ep : Entrypoint)
    (expected : Expected) (accepted : expectedEntrypoint state ep = .ok expected) :
    ∃ (plan : Backend.Impact.Plan) (frame : OutputFrame),
      Backend.Impact.lower state ep = .ok plan ∧
      normalizeOutputs (initialAliases ep plan) ep.circuit.outputs = .ok frame ∧
      ∀ read ∈ plan.reads.drop ((ep.circuit.inputs.filter (·.visibility == .«public»)).length),
        frame.1.lookup read.name = some (.input ("%input_" ++ read.name)) := by
  obtain ⟨plan, frame, _, _, _, lowered, normalized, _⟩ :=
    expectedEntrypoint_parts state ep expected accepted
  exact ⟨plan, frame, lowered, normalized,
    normalized_read_alias_lookup state ep plan frame lowered normalized⟩

end Nightlean.Verification.GenericStateReadAliasLookup
