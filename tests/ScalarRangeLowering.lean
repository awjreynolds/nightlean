import Nightlean.Verification.ScalarRangeLowering

namespace ScalarRangeLoweringTests

open Lean Nightlean Nightlean.Backend Nightlean.Verification
open NativeRelation ScalarRangeLowering ScalarWitness

example (state : Zkir.LowerState) (text : String) :
    ((Zkir.constrainUnsigned 0 text).run state).2.next = state.next := by
  rw [zero_run]

example (state : Zkir.LowerState) (text : String) :
    ((Zkir.constrainUnsigned 255 text).run state).2.next = state.next := by
  rw [power_run state 255 text (by decide) (by decide)]

example (state : Zkir.LowerState) (text : String) :
    ((Zkir.constrainUnsigned 200 text).run state).2.next = state.next + 1 := by
  rw [nonpower_run state 200 text (by decide) (by decide)]

example (maximum : Nat) (admitted : maximum ≤ ScalarPolicy.maxUint) :
    maximum + 1 < Field.modulus := threshold_canonical maximum admitted

/-- Completeness covers every admitted UInt maximum and literal value, including
zero and full bit widths. The witness theorem executes the actual emitter. -/
example (hash : Hash) (witness : Assignment) (maximum number : Nat)
    (admitted : maximum ≤ ScalarPolicy.maxUint) (range : number ≤ maximum) :
    ∃ afterWitness : Assignment, ∃ instructions : List Instruction,
      ((Zkir.constrainUnsigned maximum (Zkir.fieldImmediate number)).run {}).2.instructions.toList.mapM
        NativeRelationJson.decodeInstruction = .ok instructions ∧
      (∀ instruction ∈ instructions, instruction.Holds hash afterWitness) ∧
      (∀ name, name ≠ "%v0" → afterWitness name = witness name) := by
  have canonical : number < Field.modulus :=
    Nat.lt_of_le_of_lt (Nat.le_trans range admitted) ScalarPolicy.maxUint_lt_native
  have readRange : ((Operand.immediate (scalar number)).read witness).val ≤ maximum :=
    Nat.le_trans (Nat.mod_le number Field.modulus) range
  obtain ⟨afterWitness, instructions, decoded, holds, stable, frame, extension⟩ :=
    constrainUnsigned_complete hash witness {} maximum (Zkir.fieldImmediate number)
      (.immediate (scalar number)) []
      (ScalarImmediate.decodeOperand_fieldImmediate_exact number canonical) rfl
      (by intro instruction member; cases member) readRange admitted (by decide)
      trivial (by intro instruction member; cases member)
  exact ⟨afterWitness, instructions, decoded, holds, frame⟩

#print axioms Nightlean.Verification.ScalarRangeLowering.constrainUnsigned_complete
#print axioms Nightlean.Verification.ScalarRangeLowering.nonpower_decode

end ScalarRangeLoweringTests
