import Nightlean.Verification.ScalarLowering

namespace Nightlean.Verification.ScalarCache

open Lean Backend NativeRelation NativeRelationJson ScalarNormalization ScalarLowering ScalarInstructionEncoding

theorem cached_testEq_meaning (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (invariant : LowerStateMeaning hash witness state)
    (left right result : String) (leftTerm rightTerm : Backend.Native.Term)
    (leftMeaning : OperandMeaning hash inputs witness left leftTerm)
    (rightMeaning : OperandMeaning hash inputs witness right rightTerm)
    (hit : state.expressions.lookup ("test_eq", [left, right], none) = some result) :
    OperandMeaning hash inputs witness result (.binary "test_eq" leftTerm rightTerm) := by
  rcases leftMeaning with ⟨leftOperand, leftDecoded, leftValue⟩
  rcases rightMeaning with ⟨rightOperand, rightDecoded, rightValue⟩
  obtain ⟨instructions, decoded, instruction, member, correspondence⟩ :=
    invariant.cacheTrace _ result (ScalarValidation.lookup_member hit)
  cases instruction <;> simp [CacheCorresponds] at correspondence
  next foundLeft foundRight output =>
    rcases correspondence with ⟨resultEq, a, b, ⟨rfl, rfl⟩, foundLeftDecoded, foundRightDecoded, outputValid⟩
    subst result
    have leftEq : foundLeft = leftOperand := Except.ok.inj (foundLeftDecoded.symm.trans leftDecoded)
    have rightEq : foundRight = rightOperand := Except.ok.inj (foundRightDecoded.symm.trans rightDecoded)
    have holds := invariant.holds instructions decoded (.testEq foundLeft foundRight output) member
    rw [leftEq, rightEq] at holds
    refine ⟨.reference output, (OperandEncoding.reference output outputValid).decode, ?_⟩
    simp only [Operand.read]
    rw [holds, interpret_testEq, leftValue, rightValue]

theorem cached_neg_meaning (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (invariant : LowerStateMeaning hash witness state)
    (text result : String) (term : Backend.Native.Term)
    (meaning : OperandMeaning hash inputs witness text term)
    (hit : state.expressions.lookup ("neg", [text], none) = some result) :
    OperandMeaning hash inputs witness result (.unary "neg" term) := by
  rcases meaning with ⟨operand, operandDecoded, operandValue⟩
  obtain ⟨instructions, decoded, instruction, member, correspondence⟩ :=
    invariant.cacheTrace _ result (ScalarValidation.lookup_member hit)
  cases instruction <;> simp [CacheCorresponds] at correspondence
  next found output =>
    rcases correspondence with ⟨resultEq, foundDecoded, outputValid⟩
    subst result
    have operandEq : found = operand := Except.ok.inj (foundDecoded.symm.trans operandDecoded)
    have holds := invariant.holds instructions decoded (.neg found output) member
    rw [operandEq] at holds
    refine ⟨.reference output, (OperandEncoding.reference output outputValid).decode, ?_⟩
    simp only [Operand.read]
    rw [holds, interpret_neg, operandValue]

theorem cached_not_meaning (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (invariant : LowerStateMeaning hash witness state)
    (text result : String) (term : Backend.Native.Term)
    (meaning : OperandMeaning hash inputs witness text term)
    (hit : state.expressions.lookup ("not", [text], none) = some result) :
    OperandMeaning hash inputs witness result (.unary "not" term) := by
  rcases meaning with ⟨operand, operandDecoded, operandValue⟩
  obtain ⟨instructions, decoded, instruction, member, correspondence⟩ :=
    invariant.cacheTrace _ result (ScalarValidation.lookup_member hit)
  cases instruction <;> simp [CacheCorresponds] at correspondence
  next found output =>
    rcases correspondence with ⟨resultEq, foundDecoded, outputValid⟩
    subst result
    have operandEq : found = operand := Except.ok.inj (foundDecoded.symm.trans operandDecoded)
    have holds := invariant.holds instructions decoded (.not found output) member
    rw [operandEq] at holds
    have boolean : interpret hash inputs term = zero ∨ interpret hash inputs term = one := by
      simpa only [operandValue] using holds.1
    have resultValue := holds.2
    rw [operandValue] at resultValue
    refine ⟨.reference output, (OperandEncoding.reference output outputValid).decode, ?_⟩
    simp only [Operand.read]
    rcases boolean with isZero | isOne
    · simpa [interpret_not, bit, isZero] using resultValue
    · simpa [interpret_not, bit, isOne, Ne.symm zero_ne_one] using resultValue

theorem cached_select_meaning (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (invariant : LowerStateMeaning hash witness state)
    (condition yes no result : String) (conditionTerm yesTerm noTerm : Backend.Native.Term)
    (conditionMeaning : OperandMeaning hash inputs witness condition conditionTerm)
    (yesMeaning : OperandMeaning hash inputs witness yes yesTerm)
    (noMeaning : OperandMeaning hash inputs witness no noTerm)
    (hit : state.expressions.lookup ("cond_select", [condition, yes, no], none) = some result) :
    OperandMeaning hash inputs witness result (.select conditionTerm yesTerm noTerm) := by
  rcases conditionMeaning with ⟨conditionOperand, conditionDecoded, conditionValue⟩
  rcases yesMeaning with ⟨yesOperand, yesDecoded, yesValue⟩
  rcases noMeaning with ⟨noOperand, noDecoded, noValue⟩
  obtain ⟨instructions, decoded, instruction, member, correspondence⟩ :=
    invariant.cacheTrace _ result (ScalarValidation.lookup_member hit)
  cases instruction <;> simp [CacheCorresponds] at correspondence
  next foundCondition foundYes foundNo output =>
    rcases correspondence with ⟨resultEq, c, a, b, ⟨rfl, rfl, rfl⟩, foundConditionDecoded, foundYesDecoded, foundNoDecoded, outputValid⟩
    subst result
    have conditionEq : foundCondition = conditionOperand :=
      Except.ok.inj (foundConditionDecoded.symm.trans conditionDecoded)
    have yesEq : foundYes = yesOperand := Except.ok.inj (foundYesDecoded.symm.trans yesDecoded)
    have noEq : foundNo = noOperand := Except.ok.inj (foundNoDecoded.symm.trans noDecoded)
    have holds := invariant.holds instructions decoded (.select foundCondition foundYes foundNo output) member
    rw [conditionEq, yesEq, noEq] at holds
    have boolean : interpret hash inputs conditionTerm = zero ∨
        interpret hash inputs conditionTerm = one := by
      simpa only [conditionValue] using holds.1
    have resultValue := holds.2
    rw [conditionValue, yesValue, noValue] at resultValue
    refine ⟨.reference output, (OperandEncoding.reference output outputValid).decode, ?_⟩
    simp only [Operand.read]
    rcases boolean with isZero | isOne
    · simpa [interpret_select, isZero, zero_ne_one] using resultValue
    · simpa [interpret_select, isOne] using resultValue

theorem cached_hash_meaning (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (invariant : LowerStateMeaning hash witness state)
    (domain : Nat) (left right result : String) (leftTerm rightTerm : Backend.Native.Term)
    (leftMeaning : OperandMeaning hash inputs witness left leftTerm)
    (rightMeaning : OperandMeaning hash inputs witness right rightTerm)
    (hit : state.expressions.lookup ("transient_hash", [left, right], some domain) = some result) :
    OperandMeaning hash inputs witness result (.hash [.constant domain, leftTerm, rightTerm]) := by
  rcases leftMeaning with ⟨leftOperand, leftDecoded, leftValue⟩
  rcases rightMeaning with ⟨rightOperand, rightDecoded, rightValue⟩
  obtain ⟨instructions, decoded, instruction, member, correspondence⟩ :=
    invariant.cacheTrace _ result (ScalarValidation.lookup_member hit)
  cases instruction <;> simp [CacheCorresponds] at correspondence
  next values output =>
    rcases correspondence with ⟨resultEq, foundDomain, a, b, ⟨⟨rfl, rfl⟩, rfl⟩, domainText, foundLeft, foundRight, valuesEq,
      domainDecoded, foundLeftDecoded, foundRightDecoded, outputValid⟩
    subst result
    have leftEq : foundLeft = leftOperand := Except.ok.inj (foundLeftDecoded.symm.trans leftDecoded)
    have rightEq : foundRight = rightOperand := Except.ok.inj (foundRightDecoded.symm.trans rightDecoded)
    have holds := invariant.holds instructions decoded (.hash values output) member
    rw [valuesEq, leftEq, rightEq] at holds
    refine ⟨.reference output, (OperandEncoding.reference output outputValid).decode, ?_⟩
    simp only [Operand.read]
    simpa only [Instruction.Holds, List.map_cons, List.map_nil,
      show (Operand.immediate (scalar domain)).read witness = scalar domain from rfl,
      leftValue, rightValue, interpret_hash, interpret_constant] using holds

end Nightlean.Verification.ScalarCache
