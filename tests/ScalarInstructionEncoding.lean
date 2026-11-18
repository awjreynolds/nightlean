import Noctium.Verification.ScalarInstructionEncoding

namespace ScalarInstructionEncodingTests

open Lean Noctium Noctium.Backend Noctium.Verification NativeRelation ScalarInstructionEncoding

private theorem valid0 : NativeRelationJson.validIdentifier "%v0" = true :=
  fresh_identifier 0 (by decide)

private theorem valid1 : NativeRelationJson.validIdentifier "%v1" = true :=
  fresh_identifier 1 (by decide)

private theorem reference0 : NativeRelationJson.decodeOperand (toJson ("%v0" : String)) =
    .ok (.reference "%v0") := (OperandEncoding.reference "%v0" valid0).decode

private theorem literal256 : NativeRelationJson.decodeOperand (toJson (Zkir.fieldImmediate 256)) =
    .ok (.immediate (scalar 256)) := ScalarImmediate.decodeOperand_fieldImmediate_exact 256 (by decide)

example : NativeRelationJson.decodeInstruction (Zkir.instruction "add"
    [("a", toJson ("%v0" : String)), ("b", toJson (Zkir.fieldImmediate 256)), ("output", toJson ("%v1" : String))]) =
    .ok (.add (.reference "%v0") (.immediate (scalar 256)) "%v1") :=
  decode_binary_instruction_add reference0 literal256 valid1

example : NativeRelationJson.decodeInstruction (Zkir.instruction "mul"
    [("a", toJson ("%v0" : String)), ("b", toJson (Zkir.fieldImmediate 256)), ("output", toJson ("%v1" : String))]) =
    .ok (.mul (.reference "%v0") (.immediate (scalar 256)) "%v1") :=
  decode_binary_instruction_mul reference0 literal256 valid1

example : NativeRelationJson.decodeInstruction (Zkir.instruction "test_eq"
    [("a", toJson ("%v0" : String)), ("b", toJson ("0x00" : String)), ("output", toJson ("%v1" : String))]) =
    .ok (.testEq (.reference "%v0") (.immediate zero) "%v1") :=
  decode_binary_instruction_test_eq reference0 encoded_zero.decode valid1

example : NativeRelationJson.decodeInstruction (Zkir.instruction "neg"
    [("a", toJson ("%v0" : String)), ("output", toJson ("%v1" : String))]) =
    .ok (.neg (.reference "%v0") "%v1") :=
  decode_unary_instruction_neg reference0 valid1

example : NativeRelationJson.decodeInstruction (Zkir.instruction "not"
    [("a", toJson ("0x01" : String)), ("output", toJson ("%v1" : String))]) =
    .ok (.not (.immediate one) "%v1") :=
  decode_unary_instruction_not encoded_one.decode valid1

example : NativeRelationJson.decodeInstruction (Zkir.instruction "cond_select"
    [("bit", toJson ("0x01" : String)), ("a", toJson ("%v0" : String)),
      ("b", toJson (Zkir.fieldImmediate 256)), ("output", toJson ("%v1" : String))]) =
    .ok (.select (.immediate one) (.reference "%v0") (.immediate (scalar 256)) "%v1") :=
  decode_select_instruction encoded_one.decode reference0 literal256 valid1

example : NativeRelationJson.decodeInstruction (Zkir.instruction "constrain_eq"
    [("a", toJson ("%v0" : String)), ("b", toJson ("0x00" : String))]) =
    .ok (.equal (.reference "%v0") (.immediate zero)) :=
  decode_equal_instruction reference0 encoded_zero.decode

example : NativeRelationJson.decodeInstruction (Zkir.instruction "constrain_to_boolean"
    [("val", toJson ("%v0" : String))]) = .ok (.boolean (.reference "%v0")) :=
  decode_boolean_instruction reference0

example : NativeRelationJson.decodeInstruction (Zkir.instruction "assert"
    [("cond", toJson ("%v0" : String))]) = .ok (.assert (.reference "%v0")) :=
  decode_assert_instruction reference0

example : NativeRelationJson.decodeInstruction (Zkir.instruction "constrain_bits"
    [("val", toJson ("%v0" : String)), ("bits", toJson (8 : Nat))]) =
    .ok (.bits (.reference "%v0") 8) :=
  decode_bits_instruction 8 reference0 (by decide) (by decide)

example : NativeRelationJson.decodeInstruction (Zkir.instruction "less_than"
    [("a", toJson ("%v0" : String)), ("b", toJson (Zkir.fieldImmediate 201)),
      ("bits", toJson (8 : Nat)), ("output", toJson ("%v1" : String))]) =
    .ok (.lessThan (.reference "%v0") (.immediate (scalar 201)) 8 "%v1") :=
  decode_lessThan_instruction 8 reference0
    (ScalarImmediate.decodeOperand_fieldImmediate_exact 201 (by decide)) valid1 (by decide) (by decide)

private theorem vector : OperandsEncoding ["0x01", "%v0", Zkir.fieldImmediate 256]
    [.immediate one, .reference "%v0", .immediate (scalar 256)] :=
  ⟨encoded_one, OperandEncoding.reference "%v0" valid0, OperandEncoding.immediate 256 (by decide), trivial⟩

example : NativeRelationJson.decodeInstruction (Zkir.instruction "transient_hash"
    [("inputs", toJson (["0x01", "%v0", Zkir.fieldImmediate 256] : List String)), ("output", toJson ("%v1" : String))]) =
    .ok (.hash [.immediate one, .reference "%v0", .immediate (scalar 256)] "%v1") :=
  decode_hash_instruction vector.decode valid1

example : NativeRelationJson.decodeInstruction (Zkir.instruction "impact"
    [("guard", toJson ("0x01" : String)), ("inputs", toJson (["0x01", "%v0", Zkir.fieldImmediate 256] : List String))]) =
    .ok (.impact (.immediate one) [.immediate one, .reference "%v0", .immediate (scalar 256)]) :=
  decode_impact_instruction vector.decode

example : NativeRelationJson.decodeInstruction (Zkir.instruction "output"
    [("vals", toJson (["0x01", "%v0", Zkir.fieldImmediate 256] : List String))]) =
    .ok (.output [.immediate one, .reference "%v0", .immediate (scalar 256)]) :=
  decode_output_instruction vector.decode

example : NativeRelationJson.decodeInstruction (Zkir.instruction "public_input"
    [("guard", Json.null), ("type", toJson ("Scalar<BLS12-381>" : String)), ("output", toJson ("%v0" : String))]) =
    .ok (.input .public "%v0") := decode_publicInput "%v0" valid0

example : NativeRelationJson.decodeInstruction (Zkir.instruction "private_input"
    [("guard", Json.null), ("type", toJson ("Scalar<BLS12-381>" : String)), ("output", toJson ("%v0" : String))]) =
    .ok (.input .private "%v0") := decode_privateInput "%v0" valid0

example (left right : Nat) (same : s!"%v{left}" = s!"%v{right}") : left = right :=
  fresh_name_injective same

example : NativeRelationJson.validIdentifier s!"%v{Native.maxInstructions}" = true :=
  fresh_identifier _ (Nat.le_refl _)

#print axioms Noctium.Verification.ScalarInstructionEncoding.OperandEncoding.decode
#print axioms Noctium.Verification.ScalarInstructionEncoding.decode_binary_instruction_add
#print axioms Noctium.Verification.ScalarInstructionEncoding.decode_select_instruction
#print axioms Noctium.Verification.ScalarInstructionEncoding.decode_lessThan_instruction
#print axioms Noctium.Verification.ScalarInstructionEncoding.fresh_identifier
#print axioms Noctium.Verification.ScalarInstructionEncoding.fresh_name_injective

end ScalarInstructionEncodingTests
