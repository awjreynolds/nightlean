import Noctium.IR

namespace Noctium.Backend.Native

def inventoryRevision : String := "7a51b3385bbf4bce3604df87a7c70867c9ab43c0"

inductive OperandRule where
  | nativeUnary | nativeBinary | nativeVector | booleanAssertion | nativeSelect
  | nativeRange | nativeEquality | nativeInput | nativeOutput
  | persistentHash32 | persistentHashPreimage | encodeValue | bytes32ByteIndex
  | bytes32Conversion | bytes32Reverse | fixedBytes | fixedByteHash | boolConstant | typedBoolVector
  | jubjubScalarBridge | jubjubPointArithmetic | jubjubCoordinates | primeFieldInverse
  | qualifiedConstant | foreignTransport | qualifiedArithmetic | qualifiedCoordinates | qualifiedByteConversion
  deriving Repr, BEq, DecidableEq

inductive EncodingRule where
  | canonicalNative | fabBytes32Hash | fabAlignedHashPreimage | bytes32EncodingChunks
  | bytes32ByteExtraction | nativeLimbs | foreignEncoding | qualifiedTypedValues
  | jubjubSubgroupScalar | jubjubAffinePoint | nativeOrJubjubScalar
  | bytes32NativeSerialization | bytes32NativeDecoding | bytes32NativeChunks | bytes32Reversal | fixedBytes
  | genericBytesDecoding
  deriving Repr, BEq, DecidableEq

inductive PrivacyRule where
  | propagateAll | preserveConstraintOrigins | declaredInputOrigin | publicBindingSink | returnValue
  deriving Repr, BEq, DecidableEq

inductive EffectRule where
  | pure | constraint | transcriptInput | transcriptBinding | returnValue
  deriving Repr, BEq, DecidableEq

inductive Precondition where
  | canonicalNative | nativeBoolean | boundedOperands | matchingNativeSignature
  | alignedBytes32 | alignedHashPreimage | typedBytes32Input | typedEncodeInput
  | typedBytes32Index | typedFixedBytes | fixedByteHashPreimage | canonicalBoolConstant | typedBoolOperands
  | typedBytes32Conversion | typedBytesInput | canonicalQualifiedConstant | canonicalForeignValue
  | reducedJubjubScalar | validJubjubPoint | exactJubjubCoordinates | nonzeroField
  deriving Repr, BEq, DecidableEq

inductive GuardRule where
  | noGuard | unguardedInputOnly | sourceBoundPublicRead | sourceBoundImpactActivity
  deriving Repr, BEq, DecidableEq

inductive BindingRule where
  | none | expectedInputSchema | exactActivityGroup | exactReturnAndBinding
  | sourceHashTerm | encodedHashChunks | canonicalScalarInput | exactCoordinateRoundtrip
  | typedInverseResult | typedBytes32Conversion | typedBytesConversion | bytes32ByteIndex | typedEncoding | bytes32Reversal | fixedBytes
  deriving Repr, BEq, DecidableEq

/-- No metadata field has a default. Exposing a primitive requires every rule. -/
structure Descriptor where
  operands : OperandRule
  encoding : EncodingRule
  privacy : PrivacyRule
  effects : EffectRule
  precondition : Precondition
  guards : GuardRule
  binding : BindingRule
  fields : List String
  deriving Repr, BEq

inductive Support where
  | supported (descriptor : Descriptor)
  | unsupported (reason : String)
  deriving Repr, BEq

/-- Exact pinned native enum order. Presence is not source support. -/
def instructionNames : List String :=
  ["encode",
   "assert",
   "cond_select",
   "constrain_bits",
   "constrain_eq",
   "constrain_to_boolean",
   "copy",
   "impact",
   "ec_mul",
   "ec_mul_generator",
   "hash_to_curve",
   "into_coordinates",
   "from_coordinates",
   "into_bytes32",
   "from_bytes32",
   "reverse_bytes",
   "bytes32_into_low_high",
   "bytes32_from_low_high",
   "div_mod_power_of_two",
   "reconstitute_field",
   "transient_hash",
   "persistent_hash",
   "keccak256",
   "test_eq",
   "add",
   "mul",
   "neg",
   "inv",
   "not",
   "less_than",
   "jubjub_scalar_from_native",
   "public_input",
   "private_input",
   "output",
   "slice",
   "nth",
   "concat",
   "load_constant",
   "sha512",
   "and",
   "or",
   "xor",
   "to_bytes",
   "from_bytes",
   "reverse",
   "bytes_into_natives",
   "bytes_from_natives"]

def valueTypeNames : List String :=
  ["Native",
   "Bool",
   "Byte",
   "Bytes",
   "JubjubPoint",
   "JubjubScalar",
   "Secp256k1Point",
   "Secp256k1Base",
   "Secp256k1Scalar",
   "Secp256r1Point",
   "Secp256r1Base",
   "Secp256r1Scalar",
   "Curve25519Point",
   "Curve25519Base",
   "Curve25519Scalar"]

private def scalar (operands : OperandRule) (privacy : PrivacyRule) (effects : EffectRule)
    (precondition : Precondition) (guards : GuardRule) (binding : BindingRule)
    (fields : List String) : Descriptor :=
  {operands, encoding := .canonicalNative, privacy, effects, precondition, guards, binding, fields}

def instructionSupport (opcode : String) : Except String Support :=
  if !instructionNames.contains opcode then .error s!"unknown native instruction '{opcode}'"
  else .ok <| match opcode with
  | "add" | "mul" => .supported <|
    scalar .qualifiedArithmetic .propagateAll .pure .matchingNativeSignature .noGuard .none ["a", "b", "output"]
  | "test_eq" => .supported <|
    scalar .nativeBinary .propagateAll .pure .matchingNativeSignature .noGuard .none ["a", "b", "output"]
  | "neg" => .supported <|
    scalar .nativeUnary .propagateAll .pure .matchingNativeSignature .noGuard .none ["a", "output"]
  | "inv" => .supported <|
    let descriptor := scalar .primeFieldInverse .propagateAll .pure .nonzeroField .noGuard
      .typedInverseResult ["a", "output"]
    {descriptor with encoding := .qualifiedTypedValues}
  | "not" => .supported <|
    scalar .nativeUnary .propagateAll .pure .nativeBoolean .noGuard .none ["a", "output"]
  | "assert" => .supported <|
    scalar .booleanAssertion .preserveConstraintOrigins .constraint .nativeBoolean .noGuard .none ["cond"]
  -- Qualified constants are Bool, foreign fields and foreign point identities only.
  | "load_constant" => .supported <|
    scalar .qualifiedConstant .propagateAll .pure .canonicalQualifiedConstant .noGuard .typedEncoding
      ["type", "encoding", "output"]
  | "and" | "or" | "xor" => .supported <|
    scalar .typedBoolVector .propagateAll .pure .typedBoolOperands .noGuard .typedEncoding
      ["inputs", "output"]
  | "cond_select" => .supported <|
    scalar .nativeSelect .propagateAll .pure .nativeBoolean .noGuard .none ["bit", "a", "b", "output"]
  | "constrain_bits" => .supported <|
    scalar .nativeRange .preserveConstraintOrigins .constraint .canonicalNative .noGuard .none ["val", "bits"]
  | "constrain_eq" => .supported <|
    scalar .nativeEquality .preserveConstraintOrigins .constraint .canonicalNative .noGuard .none ["a", "b"]
  | "constrain_to_boolean" => .supported <|
    scalar .nativeUnary .preserveConstraintOrigins .constraint .canonicalNative .noGuard .none ["val"]
  | "less_than" => .supported <|
    scalar .nativeBinary .propagateAll .pure .boundedOperands .noGuard .none ["a", "b", "bits", "output"]
  | "hash_to_curve" => .supported <|
    let descriptor := scalar .nativeVector .propagateAll .pure .canonicalNative .noGuard .sourceHashTerm
      ["inputs", "output"]
    {descriptor with encoding := .qualifiedTypedValues}
  | "transient_hash" => .supported <|
    scalar .nativeVector .propagateAll .pure .canonicalNative .noGuard .none ["inputs", "output"]
  | "sha512" | "keccak256" => .supported <|
    let descriptor := scalar .fixedByteHash .propagateAll .pure .fixedByteHashPreimage .noGuard .sourceHashTerm
      ["alignment", "inputs", "output"]
    {descriptor with encoding := .fabAlignedHashPreimage}
  | "persistent_hash" => .supported <|
    let descriptor := scalar .persistentHashPreimage .propagateAll .pure .alignedHashPreimage .noGuard .sourceHashTerm
      ["alignment", "inputs", "output"]
    {descriptor with encoding := .fabAlignedHashPreimage}
  | "encode" => .supported <|
    let descriptor := scalar .encodeValue .propagateAll .pure .typedEncodeInput
      .noGuard .typedEncoding ["input", "outputs"]
    {descriptor with encoding := .nativeLimbs}
  | "nth" => .supported <|
    let descriptor := scalar .fixedBytes .propagateAll .pure .typedFixedBytes
      .noGuard .fixedBytes ["bytes", "index", "output"]
    {descriptor with encoding := .fixedBytes}
  | "to_bytes" => .supported <|
    let descriptor := scalar .qualifiedByteConversion .propagateAll .pure .matchingNativeSignature
      .noGuard .typedBytes32Conversion ["input", "output"]
    {descriptor with encoding := .bytes32NativeSerialization}
  | "reverse" => .supported <|
    let descriptor := scalar .fixedBytes .propagateAll .pure .typedFixedBytes
      .noGuard .fixedBytes ["bytes", "output"]
    {descriptor with encoding := .fixedBytes}
  | "from_bytes" => .supported <|
    let descriptor := scalar .qualifiedByteConversion .propagateAll .pure .typedBytesInput
      .noGuard .typedBytesConversion ["bytes", "type", "output"]
    {descriptor with encoding := .genericBytesDecoding}
  | "bytes_from_natives" => .supported <|
    let descriptor := scalar .fixedBytes .propagateAll .pure .typedFixedBytes
      .noGuard .fixedBytes ["inputs", "len", "output"]
    {descriptor with encoding := .fixedBytes}
  | "slice" => .supported <|
    let descriptor := scalar .fixedBytes .propagateAll .pure .typedFixedBytes
      .noGuard .fixedBytes ["bytes", "start", "len", "output"]
    {descriptor with encoding := .fixedBytes}
  | "concat" => .supported <|
    let descriptor := scalar .fixedBytes .propagateAll .pure .typedFixedBytes
      .noGuard .fixedBytes ["inputs", "output"]
    {descriptor with encoding := .fixedBytes}
  | "jubjub_scalar_from_native" => .supported <|
    let descriptor := scalar .jubjubScalarBridge .propagateAll .pure .reducedJubjubScalar
      .noGuard .canonicalScalarInput ["native", "output"]
    {descriptor with encoding := .jubjubSubgroupScalar}
  | "ec_mul" => .supported <|
    let descriptor := scalar .qualifiedArithmetic .propagateAll .pure .matchingNativeSignature
      .noGuard .sourceHashTerm ["a", "scalar", "output"]
    {descriptor with encoding := .qualifiedTypedValues}
  | "ec_mul_generator" => .supported <|
    let descriptor := scalar .qualifiedArithmetic .propagateAll .pure .matchingNativeSignature
      .noGuard .sourceHashTerm ["scalar", "output"]
    {descriptor with encoding := .qualifiedTypedValues}
  | "from_coordinates" => .supported <|
    let descriptor := scalar .qualifiedCoordinates .propagateAll .pure .matchingNativeSignature
      .noGuard .exactCoordinateRoundtrip ["inputs", "output"]
    {descriptor with encoding := .qualifiedTypedValues}
  | "into_coordinates" => .supported <|
    let descriptor := scalar .qualifiedCoordinates .propagateAll .pure .matchingNativeSignature
      .noGuard .sourceHashTerm ["point", "outputs"]
    {descriptor with encoding := .qualifiedTypedValues}
  | "public_input" => .supported <|
    scalar .nativeInput .declaredInputOrigin .transcriptInput .matchingNativeSignature .sourceBoundPublicRead
      .expectedInputSchema ["guard", "type", "output"]
  | "private_input" => .supported <|
    scalar .nativeInput .declaredInputOrigin .transcriptInput .matchingNativeSignature .unguardedInputOnly
      .expectedInputSchema ["guard", "type", "output"]
  | "impact" => .supported <|
    scalar .nativeVector .publicBindingSink .transcriptBinding .nativeBoolean .sourceBoundImpactActivity
      .exactActivityGroup ["guard", "inputs"]
  | "output" => .supported <|
    scalar .nativeOutput .returnValue .returnValue .matchingNativeSignature .noGuard
      .exactReturnAndBinding ["vals"]
  | _ => .unsupported "No safe source typing, encoding, privacy/effect, guard-totalization and native conformance package is registered"

def valueTypeSupport (name : String) : Except String Support :=
  if !valueTypeNames.contains name then .error s!"unknown native value type '{name}'"
  else if name == "Native" then
    .ok (.supported (scalar .nativeUnary .propagateAll .pure .canonicalNative .noGuard .none []))
  else if name == "JubjubScalar" then
    .ok (.supported (scalar .jubjubScalarBridge .propagateAll .pure .reducedJubjubScalar
      .noGuard .canonicalScalarInput []))
  else if name == "JubjubPoint" then
    .ok (.supported (scalar .qualifiedArithmetic .propagateAll .pure .matchingNativeSignature
      .noGuard .exactCoordinateRoundtrip []))
  else if Foreign.kinds.any (·.sourceName == name) then
    let descriptor := scalar .foreignTransport .propagateAll .pure .canonicalForeignValue
      .noGuard .typedEncoding []
    .ok (.supported {descriptor with encoding := .foreignEncoding})
  else .ok (.unsupported "Native typed Bool and byte layouts require their own source/ABI/native conformance package")

def requireInstruction (opcode : String) : Except String Descriptor := do
  match ← instructionSupport opcode with
  | .supported descriptor => pure descriptor
  | .unsupported reason => throw s!"unsupported native instruction '{opcode}': {reason}"

theorem metadata_required (opcode : String) (reason : String)
    (h : instructionSupport opcode = .ok (.unsupported reason)) :
    requireInstruction opcode = .error s!"unsupported native instruction '{opcode}': {reason}" := by
  simp [requireInstruction, h]
  rfl

end Noctium.Backend.Native
