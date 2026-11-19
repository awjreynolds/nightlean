import Lean
import Noctium.ScalarPolicy
import Std.Data.HashMap.Lemmas

namespace Noctium.Backend.RangeDedup
open Lean

def key? (instruction : Json) : Option (String × Nat) := do
  let object ← instruction.getObj?.toOption
  guard (object.size == 3)
  let opcode ← (instruction.getObjVal? "op" >>= Json.getStr?).toOption
  guard (opcode == "constrain_bits")
  let operand ← (instruction.getObjVal? "val" >>= Json.getStr?).toOption
  guard (operand.startsWith '%')
  let bits ← (instruction.getObjVal? "bits" >>= Json.getNat?).toOption
  guard (0 < bits && bits ≤ ScalarPolicy.maxBits)
  pure (operand, bits)

private structure State where
  widths : Std.HashMap String Nat := {}
  retained : Array Json := #[]

private def step (state : State) (instruction : Json) : State :=
  match key? instruction with
  | none => {state with retained := state.retained.push instruction}
  | some (operand, bits) =>
    if (state.widths[operand]?.any (· ≤ bits)) then state
    else ⟨state.widths.insert operand bits, state.retained.push instruction⟩

/-- A prior unconditional check at an equal or narrower width already bounds
the same immutable SSA operand. Retain earlier checks before any narrowing. -/
def run (instructions : Array Json) : Array Json :=
  (instructions.foldl step {}).retained

private def comparison? (item : Json) : Option ((String × String × Nat) × String) := do
  let object ← item.getObj?.toOption
  guard (object.size == 5)
  guard ((← (item.getObjVal? "op" >>= Json.getStr?).toOption) == "less_than")
  let left ← (item.getObjVal? "a" >>= Json.getStr?).toOption
  let right ← (item.getObjVal? "b" >>= Json.getStr?).toOption
  let width ← (item.getObjVal? "bits" >>= Json.getNat?).toOption
  let output ← (item.getObjVal? "output" >>= Json.getStr?).toOption
  pure ((left, right, width), output)

/-- Reuse the result of an identical, earlier comparison over immutable SSA
operands. Keep output identifiers, check ordering and per-use assertions. -/
def reuseComparisons (instructions : Array Json) : Array Json := Id.run do
  let mut seen : Std.HashMap (String × String × Nat) String := {}
  let mut result := #[]
  for item in instructions do
    if let some (key, output) := comparison? item then
      if let some first := seen[key]? then
        result := result.push (Json.mkObj [
          ("op", toJson ("copy" : String)), ("val", toJson first), ("output", toJson output)])
        continue
      seen := seen.insert key output
    result := result.push item
  return result

private theorem step_retained (state : State) (item : Json) :
    (step state item).retained = state.retained ∨
      (step state item).retained = state.retained.push item := by
  unfold step
  split
  · exact .inr rfl
  · split
    · exact .inl rfl
    · exact .inr rfl

private theorem step_observation (observe : Json → List α) (state : State) (item : Json)
    (silent : ∀ name width, key? item = some (name, width) → observe item = []) :
    (step state item).retained.toList.flatMap observe =
      state.retained.toList.flatMap observe ++ observe item := by
  cases key : key? item with
  | none => simp [step, key]
  | some entry =>
    obtain ⟨operand, bits⟩ := entry
    rcases step_retained state item with retained | retained
    · simp [retained, silent operand bits key]
    · simp [retained]

private theorem fold_observations (observe : Json → List α) (instructions : List Json)
    (state : State)
    (silent : ∀ item ∈ instructions, ∀ name width, key? item = some (name, width) → observe item = []) :
    (instructions.foldl step state).retained.toList.flatMap observe =
      state.retained.toList.flatMap observe ++ instructions.flatMap observe := by
  induction instructions generalizing state with
  | nil => simp
  | cons item rest ih =>
    rw [List.foldl_cons, ih (step state item) (fun x hx => silent x (List.mem_cons_of_mem _ hx)),
      step_observation observe state item (silent item List.mem_cons_self)]
    simp [List.append_assoc]

private def Tracks (state : State) : Prop :=
  ∀ name width, state.widths[name]? = some width →
    ∃ item ∈ state.retained.toList, key? item = some (name, width)

private theorem tracks_step (state : State) (item : Json) (tracks : Tracks state) :
    Tracks (step state item) := by
  unfold step
  split
  next =>
    intro name width found
    obtain ⟨earlier, member, key⟩ := tracks name width found
    exact ⟨earlier, by simp [member], key⟩
  next operand bits key =>
    split
    · exact tracks
    · intro name width found
      by_cases same : operand = name
      · subst name
        change (state.widths.insert operand bits)[operand]? = some width at found
        simp at found
        subst width
        exact ⟨item, by simp, key⟩
      · obtain ⟨earlier, member, check⟩ := tracks name width (by
          simpa [Std.HashMap.getElem?_insert, same] using found)
        exact ⟨earlier, by simp [member], check⟩

private theorem fold_sublist (items : List Json) (state : State) :
    (items.foldl step state).retained.toList.Sublist (state.retained.toList ++ items) := by
  induction items generalizing state with
  | nil => simp
  | cons item rest ih =>
    have retained := ih (step state item)
    rcases step_retained state item with dropped | kept
    · rw [dropped] at retained
      exact retained.trans ((List.Sublist.cons item (List.Sublist.refl rest)).append_left _)
    · simpa [kept, List.append_assoc] using retained

/-- Optimization only removes items and preserves the original ordering. -/
theorem sublist (instructions : Array Json) :
    (run instructions).toList.Sublist instructions.toList := by
  simpa [run, Array.foldl_toList] using fold_sublist instructions.toList {}

private theorem recover_satisfaction (holds : Json → Prop) (read : String → Nat)
    (items : List Json) (state : State) (tracks : Tracks state)
    (meaning : ∀ item ∈ state.retained.toList ++ items, ∀ name width,
      key? item = some (name, width) → (holds item ↔ read name < 2 ^ width))
    (accepted : ∀ item ∈ (items.foldl step state).retained.toList, holds item) :
    ∀ item ∈ state.retained.toList ++ items, holds item := by
  induction items generalizing state with
  | nil => simpa using accepted
  | cons item rest ih =>
    have nextMeaning : ∀ json ∈ (step state item).retained.toList ++ rest, ∀ name width,
        key? json = some (name, width) → (holds json ↔ read name < 2 ^ width) := by
      intro json member
      apply meaning json
      rcases step_retained state item with dropped | kept
      · rw [dropped] at member
        exact (List.Sublist.cons item (List.Sublist.refl rest)).append_left state.retained.toList
          |>.subset member
      · simpa [kept, List.append_assoc] using member
    have recovered := ih (step state item) (tracks_step state item tracks) nextMeaning accepted
    cases key : key? item with
    | none => simpa [step, key, List.append_assoc] using recovered
    | some check =>
      obtain ⟨operand, bits⟩ := check
      by_cases covered : state.widths[operand]?.any (· ≤ bits)
      · have current : holds item := by
          cases lookup : state.widths[operand]? with
          | none => simp [lookup] at covered
          | some width =>
            simp [lookup] at covered
            obtain ⟨earlier, member, earlierKey⟩ := tracks operand width lookup
            have earlierHolds := recovered earlier (by simp [step, key, lookup, covered, member])
            have bound := (meaning earlier (List.mem_append_left _ member) operand width earlierKey).mp
              earlierHolds
            exact (meaning item (by simp) operand bits key).mpr
              (Nat.lt_of_lt_of_le bound (Nat.pow_le_pow_right (by decide) covered))
        intro json member
        simp only [step, key, covered, ↓reduceIte] at recovered
        rcases List.mem_append.mp member with prefixMember | suffixMember
        · exact recovered json (List.mem_append_left _ prefixMember)
        · rcases List.mem_cons.mp suffixMember with rfl | suffixMember
          · exact current
          · exact recovered json (List.mem_append_right _ suffixMember)
      · simpa [step, key, covered, List.append_assoc] using recovered

/-- Removing an implied range check preserves satisfaction for every assignment,
including assignments rejected by the original program. -/
theorem preserves_satisfaction (instructions : Array Json) (holds : Json → Prop)
    (read : String → Nat)
    (meaning : ∀ item ∈ instructions.toList, ∀ name width, key? item = some (name, width) →
      (holds item ↔ read name < 2 ^ width)) :
    (∀ item ∈ (run instructions).toList, holds item) ↔
      (∀ item ∈ instructions.toList, holds item) := by
  constructor
  · simpa [run, Array.foldl_toList] using
      recover_satisfaction holds read instructions.toList {} (by simp [Tracks]) (by simpa using meaning)
  · intro accepted item member
    exact accepted item ((sublist _).subset member)

/-- Range constraints do not project an input, an Impact event, or an output. -/
theorem preserves_observations (instructions : Array Json) (observe : Json → List α)
    (silent : ∀ item ∈ instructions.toList, ∀ name width,
      key? item = some (name, width) → observe item = []) :
    (run instructions).toList.flatMap observe = instructions.toList.flatMap observe := by
  simpa [run, Array.foldl_toList] using fold_observations observe instructions.toList {} silent

end Noctium.Backend.RangeDedup
