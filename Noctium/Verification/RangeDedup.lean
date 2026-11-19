import Noctium.Backend.RangeDedup
import Noctium.Verification.NativeRelationJson

namespace Noctium.Verification.RangeDedup

open Lean NativeRelation NativeRelationJson
open Noctium.Backend.RangeDedup

private theorem naturalField_of_getNat (item : Json) (field : String) (width : Nat)
    (found : (item.getObjVal? field >>= Json.getNat?) = .ok width) :
    naturalField item field = .ok width := by
  cases lookup : item.getObjVal? field with
  | error message => simp [lookup, bind, Except.bind] at found
  | ok json =>
    simp only [lookup, bind, Except.bind] at found
    cases json with
    | num number =>
      obtain ⟨mantissa, exponent⟩ := number
      cases mantissa <;> cases exponent <;>
        simp [Json.getNat?, naturalField, lookup, bind, Except.bind, pure, Except.pure, ensure] at found ⊢
      exact Except.ok.inj found
    | _ => simp [Json.getNat?, throw] at found

private theorem prefix_disjoint (name : String) (starts : name.startsWith '%' = true) :
    name.startsWith "0x" = false := by
  simp only [String.startsWith_char_eq_head?, beq_iff_eq] at starts
  cases isHex : name.startsWith "0x"
  · rfl
  · obtain ⟨suffix, eq⟩ := String.startsWith_string_iff.mp isHex
    rw [← eq] at starts
    simp at starts

private theorem option_guard_some (condition : Prop) [Decidable condition] (witness : Unit) :
    guard (f := Option) condition = some witness ↔ condition := by
  cases witness
  by_cases test : condition <;> simp [guard, test, pure, failure]

private theorem toOption_some {result : Except String α} {value : α}
    (found : result.toOption = some value) : result = .ok value := by
  cases result <;> simp_all [Except.toOption]

private theorem key_fields (item : Json) (name : String) (bits : Nat)
    (key : key? item = some (name, bits)) :
    stringField item "op" = .ok "constrain_bits" ∧
      stringField item "val" = .ok name ∧
      name.startsWith '%' = true ∧ naturalField item "bits" = .ok bits := by
  simp only [key?, bind, Option.bind_eq_some_iff, option_guard_some, pure,
    Option.some.injEq, Prod.mk.injEq] at key
  obtain ⟨_, _, _, _, opcodeValue, opcode, _, opcodeEq, operandValue, operand, _, starts,
    bitWidth, width, _, _, rfl, rfl⟩ := key
  have opcodeEq := beq_iff_eq.mp opcodeEq
  exact ⟨opcodeEq ▸ toOption_some opcode, toOption_some operand, starts,
    naturalField_of_getNat item "bits" _ (toOption_some width)⟩

private theorem key_instruction (item : Json) (instruction : Instruction) (name : String)
    (bits : Nat) (key : key? item = some (name, bits))
    (decoded : decodeInstruction item = .ok instruction) :
    instruction = .bits (.reference name) bits := by
  obtain ⟨opcode, operand, starts, width⟩ := key_fields item name bits key
  simp only [decodeInstruction, opcode, bind, Except.bind] at decoded
  cases fields : exactFields item ["op", "val", "bits"] with
  | error message => simp [fields] at decoded
  | ok _ =>
    simp only [fields, width] at decoded
    cases allowed : ensure (0 < bits && bits ≤ ScalarPolicy.maxBits) "unsupported native bit width" with
    | error message => simp [allowed] at decoded
    | ok _ =>
      simp only [allowed, decodeOperandField, bind, Except.bind] at decoded
      have text : (item.getObjVal? "val" >>= Json.getStr?) = .ok name := operand
      cases json : item.getObjVal? "val" with
      | error message => simp [json, bind, Except.bind] at text
      | ok value =>
        simp only [json, bind, Except.bind] at text
        simp only [json, decodeOperand, text, bind, Except.bind, prefix_disjoint name starts,
          Bool.false_eq_true, ↓reduceIte] at decoded
        cases valid : ensure (validIdentifier name) "invalid native SSA reference" with
        | error message => simp [valid] at decoded
        | ok _ => simpa [valid, pure, Except.pure] using decoded.symm

private def decodedItem (item : Json) : Instruction :=
  (decodeInstruction item).toOption.getD (.output [])

private theorem decode_list (items : List Json) (instructions : List Instruction) :
    items.mapM decodeInstruction = .ok instructions ↔
      items.map decodedItem = instructions ∧
        ∀ item ∈ items, decodeInstruction item = .ok (decodedItem item) := by
  induction items generalizing instructions with
  | nil => simp [pure, Except.pure, eq_comm]
  | cons item rest ih =>
    cases decoded : decodeInstruction item with
    | error message =>
      simp [List.mapM_cons, bind, Except.bind, decoded]
    | ok decodedHead =>
      have head : decodedItem item = decodedHead := by simp [decodedItem, decoded, Except.toOption]
      simp only [List.mapM_cons, bind, Except.bind, decoded, List.map_cons, head]
      cases tail : rest.mapM decodeInstruction with
      | error message =>
        constructor
        · intro impossible
          cases impossible
        · rintro ⟨_, accepted⟩
          have impossible := (ih (rest.map decodedItem)).mpr
            ⟨rfl, fun json member => accepted json (List.mem_cons_of_mem _ member)⟩
          rw [tail] at impossible
          cases impossible
      | ok decodedTail =>
        have facts := (ih decodedTail).mp tail
        simp only [pure, Except.pure, Except.ok.injEq, facts.1]
        exact ⟨fun equal => ⟨equal, fun json member => by
          rcases List.mem_cons.mp member with rfl | member
          · simpa only [head] using decoded
          · exact facts.2 json member⟩, And.left⟩

/-- Inputs, Impact operations and outputs all occur among these ordered
instructions. Dropping range checks has no effect on their observations. -/
def nonRange : Instruction → Bool
  | .bits .. => false
  | _ => true

private theorem filter_map (items : List Json) :
    (items.map decodedItem).filter nonRange =
      items.flatMap fun item => if nonRange (decodedItem item) then [decodedItem item] else [] := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    by_cases kept : nonRange (decodedItem item) <;> simp [kept, ih]

/-- The actual JSON range pass preserves decode success, ordered non-range
instructions and field-level satisfaction for every assignment accepted or
rejected by the existing scalar relation model. -/
theorem preserves_decoded (instructions : Array Json) (original : List Instruction)
    (decoded : instructions.toList.mapM decodeInstruction = .ok original) :
    ∃ optimized,
      (run instructions).toList.mapM decodeInstruction = .ok optimized ∧
      optimized.filter nonRange = original.filter nonRange ∧
      ∀ hash witness,
        (∀ instruction ∈ optimized, instruction.Holds hash witness) ↔
        (∀ instruction ∈ original, instruction.Holds hash witness) := by
  obtain ⟨originalForm, admitted⟩ := (decode_list _ _).mp decoded
  subst original
  refine ⟨_, (decode_list _ _).mpr ⟨rfl, fun item member => admitted item ((sublist _).subset member)⟩, ?_, ?_⟩
  · let observe := fun item => if nonRange (decodedItem item) then [decodedItem item] else []
    have observed := preserves_observations instructions observe (by
      intro item member name width key
      simp [observe, key_instruction item _ name width key (admitted item member), nonRange])
    simpa only [filter_map, observe] using observed
  · intro hash witness
    simp only [List.forall_mem_map]
    exact preserves_satisfaction _ _ (fun name => (witness name).val) (by
      intro item member name width key
      rw [key_instruction item _ name width key (admitted item member)]
      rfl)

end Noctium.Verification.RangeDedup
