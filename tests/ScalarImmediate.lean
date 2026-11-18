import Noctium.Verification.ScalarImmediate

namespace ScalarImmediateTests

open Noctium Noctium.Backend Noctium.Verification

example : Zkir.fieldImmediate 0 = "0x00" := by decide
example : Zkir.fieldImmediate 1 = "0x01" := by decide
example : Zkir.fieldImmediate 255 = "0xff" := by decide
example : Zkir.fieldImmediate 256 = "0x0001" := by decide
example : Zkir.fieldImmediate 65535 = "0xffff" := by decide
example : Zkir.fieldImmediate 65536 = "0x000001" := by decide

example : Native.immediate (Zkir.fieldImmediate 0) = .ok 0 :=
  ScalarImmediate.fieldImmediate_exact 0 (by decide)

example : Native.immediate (Zkir.fieldImmediate 256) = .ok 256 :=
  ScalarImmediate.fieldImmediate_exact 256 (by decide)

example : Native.immediate (Zkir.fieldImmediate (Field.modulus - 1)) = .ok (Field.modulus - 1) :=
  ScalarImmediate.fieldImmediate_exact (Field.modulus - 1) (by decide)

/-- This checks every canonical field value, including eagerly evaluated
constants whose values never reach the circuit's final output. -/
example (number : Nat) (canonical : number < Field.modulus) :
    NativeRelationJson.decodeImmediate (Zkir.fieldImmediate number) = .ok number :=
  ScalarImmediate.decode_fieldImmediate_exact number canonical

example (state : Native.State) (number : Nat) (canonical : number < Field.modulus) :
    Native.operand state (Zkir.fieldImmediate number) =
      .ok {term := .constant number, maximum := number} :=
  ScalarImmediate.operand_fieldImmediate_exact state number canonical

#print axioms Noctium.Verification.ScalarImmediate.fieldImmediate_exact
#print axioms Noctium.Verification.ScalarImmediate.decode_fieldImmediate_exact
#print axioms Noctium.Verification.ScalarImmediate.decodeOperand_fieldImmediate_exact

end ScalarImmediateTests
