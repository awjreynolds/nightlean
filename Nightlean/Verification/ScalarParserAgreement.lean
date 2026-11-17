import Nightlean.Backend.NativeProducer
import Nightlean.Verification.NativeRelationJson

namespace Nightlean.Verification.ScalarParserAgreement

open Nightlean.Backend.Native
open Nightlean.Verification.NativeRelationJson

def exceptToOption (result : Except ε α) : Option α :=
  match result with
  | .error _ => none
  | .ok value => some value

theorem throw_error {α} (message : String) :
    (throw message : Except String α) = .error message := rfl

theorem pure_eq_ok {α} (value : α) :
    (pure value : Except String α) = Except.ok value := rfl

theorem bind_ok {α β} {value : Except String α} {next : α → Except String β} {result : β} :
    (value >>= next) = .ok result ↔ ∃ found, value = .ok found ∧ next found = .ok result := by
  cases value <;> simp [Bind.bind, Except.bind]

theorem exceptToOption_bind_pure {α β} (f : α → β) (result : Except String α) :
    exceptToOption (do let value ← result; pure (f value)) =
      Option.map f (exceptToOption result) := by
  cases result <;> rfl

theorem decodeHexBytes_option_aux (n : Nat) : ∀ chars, chars.length = n →
    exceptToOption (Nightlean.Verification.NativeRelationJson.decodeHexBytes chars) =
      Nightlean.Backend.Native.hexBytes chars := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro chars hlen
    cases chars with
    | nil => rfl
    | cons high rest =>
      cases rest with
      | nil => rfl
      | cons low tail =>
        have hlen' : tail.length + 2 = n := by simpa using hlen
        have smaller : tail.length < n := by omega
        have tailEq := ih tail.length smaller tail rfl
        simp only [Nightlean.Verification.NativeRelationJson.decodeHexBytes,
          Nightlean.Backend.Native.hexBytes]
        rw [show Nightlean.Verification.NativeRelationJson.hexDigit high =
            Nightlean.Backend.Native.hexDigit high by rfl,
          show Nightlean.Verification.NativeRelationJson.hexDigit low =
            Nightlean.Backend.Native.hexDigit low by rfl]
        cases hh : Nightlean.Backend.Native.hexDigit high with
        | none => simp [hh, exceptToOption, throw_error]
        | some highValue =>
          cases hl : Nightlean.Backend.Native.hexDigit low with
          | none => simp [hh, hl, exceptToOption, throw_error]
          | some lowValue =>
            simp only [hh, hl]
            rw [exceptToOption_bind_pure, tailEq]
            cases Nightlean.Backend.Native.hexBytes tail <;> rfl

theorem decodeHexBytes_option (chars : List Char) :
    exceptToOption (Nightlean.Verification.NativeRelationJson.decodeHexBytes chars) =
      Nightlean.Backend.Native.hexBytes chars :=
  decodeHexBytes_option_aux chars.length chars rfl

theorem decodeHexBytes_success (chars : List Char) (bytes : List Nat) :
    Nightlean.Verification.NativeRelationJson.decodeHexBytes chars = .ok bytes ↔
      Nightlean.Backend.Native.hexBytes chars = some bytes := by
  have optionEq := decodeHexBytes_option chars
  constructor
  · intro decoded
    have mapped : exceptToOption
        (Nightlean.Verification.NativeRelationJson.decodeHexBytes chars) = some bytes := by
      simp [exceptToOption, decoded]
    rw [optionEq] at mapped
    exact mapped
  · intro parsed
    rw [← optionEq] at parsed
    cases decoded : Nightlean.Verification.NativeRelationJson.decodeHexBytes chars with
    | error message => simp [exceptToOption, decoded] at parsed
    | ok found =>
      simp [exceptToOption, decoded] at parsed
      subst found
      rfl

theorem littleEndian_agree (bytes : List Nat) :
    Nightlean.Backend.Native.littleEndian bytes =
      Nightlean.Verification.NativeRelationJson.littleEndianValue bytes := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih =>
    simp [Nightlean.Backend.Native.littleEndian,
      Nightlean.Verification.NativeRelationJson.littleEndianValue, ih]

theorem native_success (text : String) (number : Nat) :
    Nightlean.Backend.Native.immediate text = .ok number ↔
    text.startsWith "0x" = true ∧
      ∃ bytes, Nightlean.Backend.Native.hexBytes (text.toList.drop 2) = some bytes ∧
      (!bytes.isEmpty && bytes.length ≤ 32) = true ∧
      (bytes.length == 1 || bytes.getLast? != some 0) = true ∧
      Nightlean.Backend.Native.littleEndian bytes < Nightlean.Field.modulus ∧
      Nightlean.Backend.Native.littleEndian bytes = number := by
  unfold Nightlean.Backend.Native.immediate
  rw [bind_ok]
  simp [Nightlean.Backend.Native.ensure, pure_eq_ok, throw_error]
  intro hprefix
  cases hbytes : Nightlean.Backend.Native.hexBytes (text.toList.drop 2) with
  | none => simp [hbytes, throw_error]
  | some bytes =>
    simp [hbytes, Nightlean.Backend.Native.ensure, pure_eq_ok, throw_error, Except.bind, Bind.bind]
    by_cases h1 : bytes ≠ [] ∧ bytes.length ≤ 32
    all_goals by_cases h2 : bytes.length = 1 ∨ bytes.getLast? ≠ some 0
    all_goals by_cases h3 : Nightlean.Backend.Native.littleEndian bytes < Nightlean.Field.modulus
    all_goals simp [h1, h2, h3] <;> omega

theorem relation_success (text : String) (number : Nat) :
    Nightlean.Verification.NativeRelationJson.decodeImmediate text = .ok number ↔
    text.startsWith "0x" = true ∧
      ∃ bytes, Nightlean.Verification.NativeRelationJson.decodeHexBytes
          (text.toList.drop 2) = .ok bytes ∧
      (!bytes.isEmpty && bytes.length ≤ 32) = true ∧
      (bytes.length == 1 || bytes.getLast? != some 0) = true ∧
      Nightlean.Verification.NativeRelationJson.littleEndianValue bytes < Nightlean.Field.modulus ∧
      Nightlean.Verification.NativeRelationJson.littleEndianValue bytes = number := by
  unfold Nightlean.Verification.NativeRelationJson.decodeImmediate
  rw [bind_ok]
  simp [Nightlean.Verification.NativeRelationJson.ensure, pure_eq_ok, throw_error,
    Except.bind, Bind.bind]
  intro hprefix
  cases parsed : Nightlean.Verification.NativeRelationJson.decodeHexBytes
      (text.toList.drop 2) with
  | error errorMessage => simp [parsed]
  | ok bytes =>
    simp [parsed, Nightlean.Verification.NativeRelationJson.ensure, pure_eq_ok,
      Except.bind, Bind.bind]
    by_cases h1 : bytes ≠ [] ∧ bytes.length ≤ 32
    all_goals by_cases h2 : bytes.length = 1 ∨ bytes.getLast? ≠ some 0
    all_goals by_cases h3 : Nightlean.Verification.NativeRelationJson.littleEndianValue bytes <
      Nightlean.Field.modulus
    all_goals simp [h1, h2, h3] <;> omega

theorem producer_immediate_success (text : String) (number : Nat) :
    Nightlean.Backend.Native.immediate text = .ok number ↔
      Nightlean.Verification.NativeRelationJson.decodeImmediate text = .ok number := by
  constructor
  · intro producer
    obtain ⟨prefixOk, bytes, parsed, nonempty, minimal, field, value⟩ :=
      (native_success text number).mp producer
    have decoded := (decodeHexBytes_success (text.toList.drop 2) bytes).mpr parsed
    apply (relation_success text number).mpr
    refine ⟨prefixOk, bytes, decoded, nonempty, minimal, ?_, ?_⟩
    · rw [← littleEndian_agree]
      exact field
    · rw [← littleEndian_agree]
      exact value
  · intro decoded
    obtain ⟨prefixOk, bytes, parsed, nonempty, minimal, field, value⟩ :=
      (relation_success text number).mp decoded
    have encoded := (decodeHexBytes_success (text.toList.drop 2) bytes).mp parsed
    apply (native_success text number).mpr
    refine ⟨prefixOk, bytes, encoded, nonempty, minimal, ?_, ?_⟩
    · rw [littleEndian_agree]
      exact field
    · rw [littleEndian_agree]
      exact value

theorem producer_natField_extract (value : Lean.Json) (name : String) (number : Nat)
    (parsed : Nightlean.Backend.Native.natField value name = .ok number) :
    ∃ item, value.getObjVal? name = .ok item ∧ item.getNat? = .ok number := by
  unfold Nightlean.Backend.Native.natField at parsed
  rw [bind_ok] at parsed
  rcases parsed with ⟨item, field, rest⟩
  rw [bind_ok] at rest
  rcases rest with ⟨found, natural, rest⟩
  rw [bind_ok] at rest
  rcases rest with ⟨_, _, result⟩
  change Except.ok found = Except.ok number at result
  have same : found = number := Except.ok.inj result
  subst number
  exact ⟨item, field, natural⟩

theorem decoder_naturalField_extract (value : Lean.Json) (name : String) (number : Nat)
    (parsed : Nightlean.Verification.NativeRelationJson.naturalField value name = .ok number) :
    ∃ item, value.getObjVal? name = .ok item ∧ item.getNat? = .ok number := by
  unfold Nightlean.Verification.NativeRelationJson.naturalField at parsed
  rw [bind_ok] at parsed
  rcases parsed with ⟨item, field, rest⟩
  cases item with
  | num jsonNumber =>
    cases jsonNumber with
    | mk mantissa exponent =>
      cases exponent with
      | zero =>
        cases mantissa with
        | ofNat found =>
          simp [Nightlean.Verification.NativeRelationJson.ensure, Except.bind, Bind.bind] at rest
          change Except.ok found = Except.ok number at rest
          have same : found = number := Except.ok.inj rest
          subst number
          exact ⟨Lean.Json.num {mantissa := Int.ofNat found, exponent := 0}, field, rfl⟩
        | negSucc _ => simp [Nightlean.Verification.NativeRelationJson.ensure,
            Except.bind, Bind.bind] at rest
      | succ _ => simp [Nightlean.Verification.NativeRelationJson.ensure,
          Except.bind, Bind.bind] at rest
  | null => simp [Except.bind, Bind.bind] at rest
  | bool _ => simp [Except.bind, Bind.bind] at rest
  | str _ => simp [Except.bind, Bind.bind] at rest
  | arr _ => simp [Except.bind, Bind.bind] at rest
  | obj _ => simp [Except.bind, Bind.bind] at rest

theorem natField_naturalField_agree (value : Lean.Json) (name : String) (producerValue decoderValue : Nat)
    (producer : Nightlean.Backend.Native.natField value name = .ok producerValue)
    (decoder : Nightlean.Verification.NativeRelationJson.naturalField value name = .ok decoderValue) :
    producerValue = decoderValue := by
  obtain ⟨producerItem, producerField, producerNat⟩ :=
    producer_natField_extract value name producerValue producer
  obtain ⟨decoderItem, decoderField, decoderNat⟩ :=
    decoder_naturalField_extract value name decoderValue decoder
  have sameItem : producerItem = decoderItem :=
    Except.ok.inj (producerField.symm.trans decoderField)
  cases sameItem
  exact Except.ok.inj (producerNat.symm.trans decoderNat)

end Nightlean.Verification.ScalarParserAgreement
