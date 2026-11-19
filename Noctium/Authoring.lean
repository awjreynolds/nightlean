import Noctium.Frontend.Core
import Noctium.Helpers.Wire
import Noctium.Helpers.Iteration

namespace Noctium.Authoring

open Lean Elab Command
open Noctium
open Noctium.Helpers

structure PrivateStateField where
  name : String
  ty : Ty
  key : String
  capability : String
  signature : WitnessSignature
  deriving Repr

structure PrivateStateSchema where
  name : String
  fields : List PrivateStateField
  deriving Repr

structure ObservationInput where
  name : String
  ty : Ty
  visibility : Noctium.Visibility
  deriving Repr, Inhabited

/-- Source policy observations emitted with a readable witness program.
This describes declared flows and claims, not every possible failure channel. -/
structure ObservationMetadata where
  entryName : String
  inputs : List ObservationInput := []
  privateReads : List String := []
  privateStages : List String := []
  witnessNames : List String := []
  authoredProves : List String := []
  explicitReleases : List String := []
  generatedValidity : List String := []
  deriving Repr, Inhabited

private def typeName : Ty → String
  | .native => "Native"
  | .bool => "Bool"
  | .uint maximum => s!"UIntRange {maximum + 1}"
  | .bytes 32 => "Bytes32"
  | .bytes length => s!"Bytes {length}"
  | .jubjubScalar => "JubjubScalar"
  | .jubjubPoint => "JubjubPoint"
  | .foreign kind => kind.sourceName

private def inputJson (input : ObservationInput) : Json := Json.mkObj [
  ("name", Lean.toJson input.name), ("type", Lean.toJson (typeName input.ty)),
  ("visibility", Lean.toJson (if input.visibility == .public then "public" else "private"))]

def ObservationMetadata.toJson (metadata : ObservationMetadata) : Json := Json.mkObj [
  ("schemaVersion", Lean.toJson (1 : Nat)), ("kind", Lean.toJson ("noctium-authoring-observations" : String)),
  ("entryName", Lean.toJson metadata.entryName), ("inputs", Lean.toJson (metadata.inputs.map inputJson)),
  ("privateReads", Lean.toJson metadata.privateReads), ("privateStages", Lean.toJson metadata.privateStages),
  ("witnessNames", Lean.toJson metadata.witnessNames), ("authoredProves", Lean.toJson metadata.authoredProves),
  ("explicitReleases", Lean.toJson metadata.explicitReleases),
  ("generatedValidity", Lean.toJson metadata.generatedValidity)]

initialize noctiumPrivateStateRegistry : SimplePersistentEnvExtension
    Noctium.Authoring.PrivateStateSchema (Array Noctium.Authoring.PrivateStateSchema) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }

initialize noctiumWitnessSignatureRegistry : SimplePersistentEnvExtension
    Noctium.Helpers.WitnessSignature (Array Noctium.Helpers.WitnessSignature) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }

end Noctium.Authoring

namespace Noctium

open Lean Elab Command
open Noctium
open Noctium.Helpers
open Noctium.Authoring
open scoped Noctium

declare_syntax_cat noctium_private_field
scoped syntax "cell" ident ":" nltype : noctium_private_field
scoped syntax (name := noctiumPrivateStateCommand) "noctium_private_state" ident
  "where" noctium_private_field* "end" : command

declare_syntax_cat noctium_witness_parameter
scoped syntax ident ":" nltype : noctium_witness_parameter
declare_syntax_cat noctium_witness_result
scoped syntax nltype : noctium_witness_result
scoped syntax ident : noctium_witness_result
scoped syntax (name := noctiumWitnessDeclarationCommand) "noctium_witness" ident
  "(" noctium_witness_parameter,* ")" ":" noctium_witness_result : command

scoped syntax "witness" ident "(" nlexpr,* ")" : nlexpr
scoped syntax "encode(" ident "," nlexpr ")" : nlexpr
scoped syntax "decode(" ident "," nlexpr ")" : nlexpr
scoped syntax "field(" nlexpr "," ident ")" : nlexpr
scoped syntax "elementAt(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "enumTag(" nlexpr ")" : nlexpr

declare_syntax_cat noctium_witness_statement
scoped syntax "public" ident ":" nltype : noctium_witness_statement
scoped syntax "private" ident ":" nltype : noctium_witness_statement
scoped syntax "let" ident (":" nltype)? ":=" nlexpr : noctium_witness_statement
scoped syntax "read" "private" ident "as" ident : noctium_witness_statement
scoped syntax "witness" ident "(" nlexpr,* ")" : noctium_witness_statement
scoped syntax "prove" nlexpr : noctium_witness_statement
scoped syntax "stage" ident ":=" nlexpr : noctium_witness_statement
scoped syntax "output" ident (":" nltype)? ":=" nlexpr : noctium_witness_statement
scoped syntax (name := noctiumAuthoredWitnessCircuitCommand) "noctium_witness_circuit" ident
  ("using" ident,+)? "where" noctium_witness_statement* "end" : command

private abbrev SurfaceEnv := List (String × ResultType × Noctium.Helpers.Term)

private structure Lowered where
  type : ResultType
  term : Noctium.Helpers.Term
  before : List Statement := []
  signatures : List WitnessSignature := []
  witnessNames : List String := []
  generatedValidity : List String := []

private structure AuthoringExprState where
  codecs : List (Name × Helpers.Wire.Codec) := []
  composites : Types.CompositeEnv := {}
  nextCall : Nat := 0
  nextLet : Nat := 0
  allowAssertThen : _root_.Bool := _root_.Bool.false
  deriving Inhabited

private inductive LogicalAliasSource where
  | expression (value : TSyntax `nlexpr)
  | call (site : String)

private structure LogicalAliasBinding where
  name : String
  ty : Ty
  source : LogicalAliasSource

private structure AuthoredOutput where
  name : String
  value : Lowered
  span : SourceSpan
  ordinal : Nat
  source : LogicalAliasSource

private def AuthoredOutput.layoutType (item : AuthoredOutput) : Types.CompositeType :=
  match item.value.type with
  | .unit => .unit
  | .scalar (.bytes length) => .bytes length
  | .scalar ty => .scalar ty
  | .composite type => type

private abbrev ExprM := StateT AuthoringExprState CommandElabM

private def stringTerm (value : String) : TSyntax `term := ⟨Syntax.mkStrLit value⟩
private def natTerm (value : Nat) : TSyntax `term := ⟨Syntax.mkNumLit (toString value)⟩

private partial def quoteByteLeaves : List String → CommandElabM (TSyntax `term)
  | [] => `(Noctium.Expr.bytesLiteral 0 [])
  | [name] => `(Noctium.Expr.sliceBytes
      (Noctium.Expr.toBytes32 (@Noctium.Expr.ref Noctium.Ty.native $(stringTerm name))) 0 1)
  | names => do
    let (left, right) := names.splitAt (names.length / 2)
    `(Noctium.Expr.concatBytes $(← quoteByteLeaves left) $(← quoteByteLeaves right))

private def spanTerm (stx : Syntax) : CommandElabM (TSyntax `term) := do
  let fileMap ← getFileMap
  let pos := fileMap.toPosition (stx.getPos?.getD 0)
  let file ← getFileName
  `({ file := $(stringTerm file), line := $(natTerm pos.line),
      column := $(natTerm (pos.column + 1)) : Noctium.SourceSpan })

private def spanValue (stx : Syntax) : CommandElabM SourceSpan := do
  let fileMap ← getFileMap
  let pos := fileMap.toPosition (stx.getPos?.getD 0)
  pure {file := (← getFileName), line := pos.line, column := pos.column + 1}

private def quoteSpan (span : SourceSpan) : CommandElabM (TSyntax `term) := do
  `( ({
    file := $(stringTerm span.file),
    line := $(natTerm span.line),
    column := $(natTerm span.column) : Noctium.SourceSpan }))

private def readScalarTy (stx : TSyntax `nltype) : CommandElabM Ty := do
  match stx with
  | `(nltype| Native) => pure .native
  | `(nltype| Bool) => pure .bool
  | `(nltype| UInt $bits:num) =>
    match ScalarPolicy.sized bits.getNat with
    | .ok (.uint maximum) => pure (.uint maximum)
    | .error message => throwErrorAt stx message
    | _ => throwErrorAt stx "invalid unsigned width"
  | `(nltype| UIntRange $exclusive:num) =>
    match ScalarPolicy.bounded exclusive.getNat with
    | .ok (.uint maximum) => pure (.uint maximum)
    | .error message => throwErrorAt stx message
    | _ => throwErrorAt stx "invalid unsigned range"
  | `(nltype| Bytes32) => pure (.bytes 32)
  | `(nltype| Bytes $length:num) => do
    if length.getNat > Types.defaultLimits.maxVectorLength then
      throwErrorAt stx s!"byte string length exceeds the maximum of {Types.defaultLimits.maxVectorLength}"
    pure (.bytes length.getNat)
  | `(nltype| JubjubScalar) => pure .jubjubScalar
  | `(nltype| JubjubPoint) => pure .jubjubPoint
  | `(nltype| Secp256k1Base) => pure (.foreign (.base .secp256k1))
  | `(nltype| Secp256k1Scalar) => pure (.foreign (.scalar .secp256k1))
  | `(nltype| Secp256k1Point) => pure (.foreign (.point .secp256k1))
  | `(nltype| Secp256r1Base) => pure (.foreign (.base .secp256r1))
  | `(nltype| Secp256r1Scalar) => pure (.foreign (.scalar .secp256r1))
  | `(nltype| Secp256r1Point) => pure (.foreign (.point .secp256r1))
  | `(nltype| Curve25519Base) => pure (.foreign (.base .curve25519))
  | `(nltype| Curve25519Scalar) => pure (.foreign (.scalar .curve25519))
  | `(nltype| Curve25519Point) => pure (.foreign (.point .curve25519))
  | _ => throwErrorAt stx "unsupported readable witness scalar type"

private def tyTerm : Ty → CommandElabM (TSyntax `term)
  | .native => `(Noctium.Ty.native)
  | .bool => `(Noctium.Ty.bool)
  | .uint maximum => `(Noctium.Ty.uint $(natTerm maximum))
  | .bytes length => `(Noctium.Ty.bytes $(natTerm length))
  | .jubjubScalar => `(Noctium.Ty.jubjubScalar)
  | .jubjubPoint => `(Noctium.Ty.jubjubPoint)
  | .foreign (.base .secp256k1) => `(Noctium.Ty.foreign (Noctium.Foreign.Kind.base Noctium.Foreign.Curve.secp256k1))
  | .foreign (.scalar .secp256k1) => `(Noctium.Ty.foreign (Noctium.Foreign.Kind.scalar Noctium.Foreign.Curve.secp256k1))
  | .foreign (.point .secp256k1) => `(Noctium.Ty.foreign (Noctium.Foreign.Kind.point Noctium.Foreign.Curve.secp256k1))
  | .foreign (.base .secp256r1) => `(Noctium.Ty.foreign (Noctium.Foreign.Kind.base Noctium.Foreign.Curve.secp256r1))
  | .foreign (.scalar .secp256r1) => `(Noctium.Ty.foreign (Noctium.Foreign.Kind.scalar Noctium.Foreign.Curve.secp256r1))
  | .foreign (.point .secp256r1) => `(Noctium.Ty.foreign (Noctium.Foreign.Kind.point Noctium.Foreign.Curve.secp256r1))
  | .foreign (.base .curve25519) => `(Noctium.Ty.foreign (Noctium.Foreign.Kind.base Noctium.Foreign.Curve.curve25519))
  | .foreign (.scalar .curve25519) => `(Noctium.Ty.foreign (Noctium.Foreign.Kind.scalar Noctium.Foreign.Curve.curve25519))
  | .foreign (.point .curve25519) => `(Noctium.Ty.foreign (Noctium.Foreign.Kind.point Noctium.Foreign.Curve.curve25519))

private partial def compositeTypeTerm : Types.CompositeType → CommandElabM (TSyntax `term)
  | .unit => `(Noctium.Types.CompositeType.unit)
  | .scalar ty => do `(Noctium.Types.CompositeType.scalar $(← tyTerm ty))
  | .tuple items => do
    let items := (← items.mapM compositeTypeTerm).toArray
    `(Noctium.Types.CompositeType.tuple [$items,*])
  | .structure id => `(Noctium.Types.CompositeType.structure $(stringTerm id))
  | .enumeration id => `(Noctium.Types.CompositeType.enumeration $(stringTerm id))
  | .vector length element => do
    `(Noctium.Types.CompositeType.vector $(natTerm length) $(← compositeTypeTerm element))
  | .bytes length => `(Noctium.Types.CompositeType.bytes $(natTerm length))

private def resultTypeTerm : ResultType → CommandElabM (TSyntax `term)
  | .unit => `(Noctium.Helpers.ResultType.unit)
  | .scalar ty => do `(Noctium.Helpers.ResultType.scalar $(← tyTerm ty))
  | .composite type => do `(Noctium.Helpers.ResultType.composite $(← compositeTypeTerm type))

private def validIdentity (stx : Syntax) (value : String) : CommandElabM _root_.Unit :=
  unless Helpers.validWitnessIdentifier value do
    throwErrorAt stx s!"generated witness identity is invalid or too long: {value}"

private def generatedName (base : Name) (suffix : String) : Name :=
  base ++ Name.str .anonymous suffix

private def resolvedSurfaceName (id : TSyntax `ident) : CommandElabM String := do
  let current := ((← getCurrNamespace) ++ id.getId).toString
  let registry := noctiumWitnessSignatureRegistry.getState (← getEnv)
  if registry.any (·.name == current) then return current
  let direct := id.getId.toString
  if registry.any (·.name == direct) then return direct
  throwErrorAt id s!"unknown Noctium witness '{id.getId}'"

private def privateStateSchema (schema : Name) (stx : Syntax) : CommandElabM PrivateStateSchema := do
  let registry := noctiumPrivateStateRegistry.getState (← getEnv)
  let current := ((← getCurrNamespace) ++ schema).toString
  if let some value := registry.find? (·.name == current) then return value
  match registry.find? (·.name == schema.toString) with
  | some value => pure value
  | none => throwErrorAt stx s!"unknown private-state schema '{schema}'"

private def witnessSignature (function : TSyntax `ident) : CommandElabM WitnessSignature := do
  let registry := noctiumWitnessSignatureRegistry.getState (← getEnv)
  let name ← resolvedSurfaceName function
  match registry.find? (·.name == name) with
  | some signature => pure signature
  | none => throwErrorAt function s!"unknown Noctium witness '{function.getId}'"

private def splitSchemaField (fieldPath : TSyntax `ident) : CommandElabM (Name × String) := do
  match fieldPath.getId with
  | .str schema field => pure (schema, field)
  | _ => throwErrorAt fieldPath "private-state member must use Schema.field"

private def uniqueStrings (values : List String) : _root_.Bool :=
  values.length == values.eraseDups.length

private def lowerSchemaName (id : TSyntax `ident) : CommandElabM String := do
  let name := ((← getCurrNamespace) ++ id.getId).toString
  validIdentity id name
  pure name

private def quoteSignature (signature : WitnessSignature) : CommandElabM (TSyntax `term) := do
  let params ← signature.parameters.mapM fun parameter => do
    let result ← resultTypeTerm parameter.type
    `({ name := $(stringTerm parameter.name), type := $result : Noctium.Helpers.WitnessParameter })
  let params := params.toArray
  let parameters ← `([$params,*])
  let result ← resultTypeTerm signature.result
  let privateKey ← match signature.privateKey with
    | none => `(none)
    | some key => `(some $(stringTerm key))
  let span ← quoteSpan signature.span
  `( ({
    name := $(stringTerm signature.name),
    operation := $(stringTerm signature.operation),
    capability := $(stringTerm signature.capability),
    privateKey := $privateKey,
    parameters := $parameters,
    result := $result,
    span := $span : Noctium.Helpers.WitnessSignature }))

private def quoteField (field : PrivateStateField) : CommandElabM (TSyntax `term) := do
  let ty ← tyTerm field.ty
  let signature ← quoteSignature field.signature
  `(Noctium.Authoring.PrivateStateField.mk $(stringTerm field.name) $ty
    $(stringTerm field.key) $(stringTerm field.capability) $signature)

private partial def renderType : TSyntax `nltype → String
  | `(nltype| Native) => "Native"
  | `(nltype| Bool) => "Bool"
  | `(nltype| UInt $bits:num) => s!"UInt {bits.getNat}"
  | `(nltype| UIntRange $exclusive:num) => s!"UIntRange {exclusive.getNat}"
  | `(nltype| Bytes32) => "Bytes32"
  | `(nltype| Bytes $length:num) => s!"Bytes {length.getNat}"
  | `(nltype| JubjubScalar) => "JubjubScalar"
  | `(nltype| JubjubPoint) => "JubjubPoint"
  | `(nltype| Secp256k1Base) => "Secp256k1Base"
  | `(nltype| Secp256k1Scalar) => "Secp256k1Scalar"
  | `(nltype| Secp256k1Point) => "Secp256k1Point"
  | `(nltype| Secp256r1Base) => "Secp256r1Base"
  | `(nltype| Secp256r1Scalar) => "Secp256r1Scalar"
  | `(nltype| Secp256r1Point) => "Secp256r1Point"
  | `(nltype| Curve25519Base) => "Curve25519Base"
  | `(nltype| Curve25519Scalar) => "Curve25519Scalar"
  | `(nltype| Curve25519Point) => "Curve25519Point"
  | _ => "?"

private partial def renderExpr (stx : TSyntax `nlexpr) : String :=
  match stx with
  | `(nlexpr| $id:ident) => id.getId.toString
  | `(nlexpr| $n:num) => toString n.getNat
  | `(nlexpr| true) => "true"
  | `(nlexpr| false) => "false"
  | `(nlexpr| let $id:ident := $value:nlexpr in $body:nlexpr) =>
    s!"let {id.getId} := {renderExpr value} in {renderExpr body}"
  | `(nlexpr| assertThen($condition, $body)) =>
    s!"assertThen({renderExpr condition}, {renderExpr body})"
  | `(nlexpr| add($left, $right)) => s!"add({renderExpr left}, {renderExpr right})"
  | `(nlexpr| sub($left, $right)) => s!"sub({renderExpr left}, {renderExpr right})"
  | `(nlexpr| mul($left, $right)) => s!"mul({renderExpr left}, {renderExpr right})"
  | `(nlexpr| uint($n:num)) => s!"uint({n.getNat})"
  | `(nlexpr| cast($ty:nltype, $value:nlexpr)) =>
    s!"cast({renderType ty}, {renderExpr value})"
  | `(nlexpr| disclose($value)) => s!"disclose({renderExpr value})"
  | `(nlexpr| encode($codec:ident, $value)) => s!"encode({codec.getId}, {renderExpr value})"
  | `(nlexpr| decode($codec:ident, $value)) => s!"decode({codec.getId}, {renderExpr value})"
  | `(nlexpr| field($value, $name:ident)) => s!"field({renderExpr value}, {name.getId})"
  | `(nlexpr| elementAt($value, $index)) => s!"elementAt({renderExpr value}, {renderExpr index})"
  | `(nlexpr| enumTag($value)) => s!"enumTag({renderExpr value})"
  | `(nlexpr| eq($left, $right)) => s!"eq({renderExpr left}, {renderExpr right})"
  | `(nlexpr| boolAnd($left, $right)) => s!"boolAnd({renderExpr left}, {renderExpr right})"
  | `(nlexpr| boolOr($left, $right)) => s!"boolOr({renderExpr left}, {renderExpr right})"
  | `(nlexpr| boolXor($left, $right)) => s!"boolXor({renderExpr left}, {renderExpr right})"
  | `(nlexpr| select($condition, $yes, $no)) =>
    s!"select({renderExpr condition}, {renderExpr yes}, {renderExpr no})"
  | `(nlexpr| poseidon2($domain:num, $left, $right)) =>
    s!"poseidon2({domain.getNat}, {renderExpr left}, {renderExpr right})"
  | `(nlexpr| persistentHash32($value)) => s!"persistentHash32({renderExpr value})"
  | `(nlexpr| sha512($value)) => s!"sha512({renderExpr value})"
  | `(nlexpr| keccak256($value)) => s!"keccak256({renderExpr value})"
  | `(nlexpr| bytes32($literal:str)) => s!"bytes32({(toJson literal.getString).compress})"
  | `(nlexpr| bytes($length:num, $literal:str)) =>
    s!"bytes({length.getNat}, {(toJson literal.getString).compress})"
  | `(nlexpr| byteAt($value, $index:num)) =>
    s!"byteAt({renderExpr value}, {index.getNat})"
  | `(nlexpr| persistentHashVector32([$values,*])) =>
    s!"persistentHashVector32([{String.intercalate ", " (values.getElems.toList.map renderExpr)}])"
  | `(nlexpr| persistentHashNative($value)) => s!"persistentHashNative({renderExpr value})"
  | `(nlexpr| persistentHashNativeVector([$values,*])) =>
    s!"persistentHashNativeVector([{String.intercalate ", " (values.getElems.toList.map renderExpr)}])"
  | `(nlexpr| persistentHashPoint($point)) => s!"persistentHashPoint({renderExpr point})"
  | `(nlexpr| reverseBytes32($value)) => s!"reverseBytes32({renderExpr value})"
  | `(nlexpr| reverseBytes($value)) => s!"reverseBytes({renderExpr value})"
  | `(nlexpr| sliceBytes($value, $start:num, $stop:num)) =>
    s!"sliceBytes({renderExpr value}, {start.getNat}, {stop.getNat})"
  | `(nlexpr| concatBytes($left, $right)) =>
    s!"concatBytes({renderExpr left}, {renderExpr right})"
  | `(nlexpr| degradeToNative($value)) => s!"degradeToNative({renderExpr value})"
  | `(nlexpr| toBytes32($value)) => s!"toBytes32({renderExpr value})"
  | `(nlexpr| jubjubScalarFromNative($value)) => s!"jubjubScalarFromNative({renderExpr value})"
  | `(nlexpr| jubjubScalarToNative($value)) => s!"jubjubScalarToNative({renderExpr value})"
  | `(nlexpr| jubjubMulGenerator($value)) => s!"jubjubMulGenerator({renderExpr value})"
  | `(nlexpr| jubjubMul($point, $scalar)) => s!"jubjubMul({renderExpr point}, {renderExpr scalar})"
  | `(nlexpr| jubjubAdd($left, $right)) => s!"jubjubAdd({renderExpr left}, {renderExpr right})"
  | `(nlexpr| jubjubNeg($point)) => s!"jubjubNeg({renderExpr point})"
  | `(nlexpr| jubjubX($point)) => s!"jubjubX({renderExpr point})"
  | `(nlexpr| jubjubY($point)) => s!"jubjubY({renderExpr point})"
  | `(nlexpr| jubjubFromCoordinates($x, $y)) =>
    s!"jubjubFromCoordinates({renderExpr x}, {renderExpr y})"
  | `(nlexpr| secp256k1Base($value:num)) => s!"secp256k1Base({value.getNat})"
  | `(nlexpr| secp256k1Scalar($value:num)) => s!"secp256k1Scalar({value.getNat})"
  | `(nlexpr| secp256k1Identity()) => "secp256k1Identity()"
  | `(nlexpr| secp256r1Base($value:num)) => s!"secp256r1Base({value.getNat})"
  | `(nlexpr| secp256r1Scalar($value:num)) => s!"secp256r1Scalar({value.getNat})"
  | `(nlexpr| secp256r1Identity()) => "secp256r1Identity()"
  | `(nlexpr| curve25519Base($value:num)) => s!"curve25519Base({value.getNat})"
  | `(nlexpr| curve25519Scalar($value:num)) => s!"curve25519Scalar({value.getNat})"
  | `(nlexpr| curve25519Identity()) => "curve25519Identity()"
  | `(nlexpr| hashToCurve([$values,*])) =>
    s!"hashToCurve([{String.intercalate ", " (values.getElems.toList.map renderExpr)}])"
  | `(nlexpr| foreignAdd($left, $right)) => s!"foreignAdd({renderExpr left}, {renderExpr right})"
  | `(nlexpr| foreignSub($left, $right)) => s!"foreignSub({renderExpr left}, {renderExpr right})"
  | `(nlexpr| foreignMul($left, $right)) => s!"foreignMul({renderExpr left}, {renderExpr right})"
  | `(nlexpr| foreignNeg($value)) => s!"foreignNeg({renderExpr value})"
  | `(nlexpr| foreignInv($value)) => s!"foreignInv({renderExpr value})"
  | `(nlexpr| curveMul($point, $scalar)) =>
    s!"curveMul({renderExpr point}, {renderExpr scalar})"
  | `(nlexpr| curveMulGenerator($scalar)) => s!"curveMulGenerator({renderExpr scalar})"
  | `(nlexpr| curveX($point)) => s!"curveX({renderExpr point})"
  | `(nlexpr| curveY($point)) => s!"curveY({renderExpr point})"
  | `(nlexpr| curveFromCoordinates($x, $y)) =>
    s!"curveFromCoordinates({renderExpr x}, {renderExpr y})"
  | `(nlexpr| foreignToBytes($value)) => s!"foreignToBytes({renderExpr value})"
  | `(nlexpr| foreignFromBytes($type:nltype, $value)) =>
    s!"foreignFromBytes({renderType type}, {renderExpr value})"
  | `(nlexpr| witness $function:ident($args:nlexpr,*)) =>
    s!"witness {function.getId}({String.intercalate ", " (args.getElems.toList.map renderExpr)})"
  | _ => "<unsupported-expression>"

private partial def disclosedValues (stx : TSyntax `nlexpr) : List String :=
  match stx with
  | `(nlexpr| disclose($value)) => renderExpr value :: disclosedValues value
  | `(nlexpr| let $_:ident := $value:nlexpr in $body:nlexpr) => disclosedValues value ++ disclosedValues body
  | `(nlexpr| assertThen($condition, $body)) => disclosedValues condition ++ disclosedValues body
  | `(nlexpr| add($left, $right)) | `(nlexpr| sub($left, $right))
  | `(nlexpr| mul($left, $right)) | `(nlexpr| eq($left, $right))
  | `(nlexpr| boolAnd($left, $right)) | `(nlexpr| boolOr($left, $right))
  | `(nlexpr| boolXor($left, $right)) =>
    disclosedValues left ++ disclosedValues right
  | `(nlexpr| cast($_:nltype, $value:nlexpr)) => disclosedValues value
  | `(nlexpr| select($condition, $yes, $no)) =>
    disclosedValues condition ++ disclosedValues yes ++ disclosedValues no
  | `(nlexpr| poseidon2($_:num, $left, $right)) => disclosedValues left ++ disclosedValues right
  | `(nlexpr| elementAt($value, $index)) => disclosedValues value ++ disclosedValues index
  | `(nlexpr| persistentHash32($value)) | `(nlexpr| persistentHashNative($value))
  | `(nlexpr| persistentHashPoint($value)) | `(nlexpr| sha512($value))
  | `(nlexpr| keccak256($value)) | `(nlexpr| degradeToNative($value))
  | `(nlexpr| serialize($value, $_:num)) | `(nlexpr| deserialize($_:nltype, $value))
  | `(nlexpr| encode($_:ident, $value)) | `(nlexpr| decode($_:ident, $value))
  | `(nlexpr| field($value, $_:ident))
  | `(nlexpr| enumTag($value))
  | `(nlexpr| toBytes32($value)) | `(nlexpr| reverseBytes32($value))
  | `(nlexpr| reverseBytes($value)) => disclosedValues value
  | `(nlexpr| sliceBytes($value, $_:num, $_:num)) => disclosedValues value
  | `(nlexpr| concatBytes($left, $right)) => disclosedValues left ++ disclosedValues right
  | `(nlexpr| byteAt($value, $_:num)) => disclosedValues value
  | `(nlexpr| persistentHashVector32([$values,*]))
  | `(nlexpr| persistentHashNativeVector([$values,*])) => values.getElems.toList.flatMap disclosedValues
  | `(nlexpr| jubjubScalarFromNative($value))
  | `(nlexpr| jubjubScalarToNative($value))
  | `(nlexpr| jubjubMulGenerator($value))
  | `(nlexpr| jubjubNeg($value))
  | `(nlexpr| jubjubX($value))
  | `(nlexpr| jubjubY($value)) => disclosedValues value
  | `(nlexpr| jubjubMul($point, $scalar)) | `(nlexpr| jubjubAdd($point, $scalar)) =>
    disclosedValues point ++ disclosedValues scalar
  | `(nlexpr| jubjubFromCoordinates($x, $y)) => disclosedValues x ++ disclosedValues y
  | `(nlexpr| hashToCurve([$values,*])) => values.getElems.toList.flatMap disclosedValues
  | `(nlexpr| foreignNeg($value)) | `(nlexpr| foreignInv($value))
  | `(nlexpr| curveMulGenerator($value)) | `(nlexpr| curveX($value))
  | `(nlexpr| curveY($value)) | `(nlexpr| foreignToBytes($value)) => disclosedValues value
  | `(nlexpr| foreignAdd($left, $right)) | `(nlexpr| foreignSub($left, $right))
  | `(nlexpr| foreignMul($left, $right)) | `(nlexpr| curveMul($left, $right))
  | `(nlexpr| curveFromCoordinates($left, $right)) =>
    disclosedValues left ++ disclosedValues right
  | `(nlexpr| foreignFromBytes($_:nltype, $value)) => disclosedValues value
  | `(nlexpr| witness $_:ident($args:nlexpr,*)) => args.getElems.toList.flatMap disclosedValues
  | _ => []

private partial def inlineAssertions (stx : TSyntax `nlexpr) : List String :=
  match stx with
  | `(nlexpr| assertThen($condition, $body)) =>
    renderExpr condition :: (inlineAssertions condition ++ inlineAssertions body)
  | `(nlexpr| let $_:ident := $value:nlexpr in $body:nlexpr) =>
    inlineAssertions value ++ inlineAssertions body
  | `(nlexpr| add($left, $right)) | `(nlexpr| sub($left, $right))
  | `(nlexpr| mul($left, $right)) | `(nlexpr| eq($left, $right))
  | `(nlexpr| boolAnd($left, $right)) | `(nlexpr| boolOr($left, $right))
  | `(nlexpr| boolXor($left, $right)) =>
    inlineAssertions left ++ inlineAssertions right
  | `(nlexpr| cast($_:nltype, $value:nlexpr)) | `(nlexpr| disclose($value)) => inlineAssertions value
  | `(nlexpr| select($condition, $yes, $no)) =>
    inlineAssertions condition ++ inlineAssertions yes ++ inlineAssertions no
  | `(nlexpr| poseidon2($_:num, $left, $right)) => inlineAssertions left ++ inlineAssertions right
  | `(nlexpr| elementAt($value, $index)) => inlineAssertions value ++ inlineAssertions index
  | `(nlexpr| persistentHash32($value)) | `(nlexpr| persistentHashNative($value))
  | `(nlexpr| persistentHashPoint($value)) | `(nlexpr| sha512($value))
  | `(nlexpr| keccak256($value)) | `(nlexpr| degradeToNative($value))
  | `(nlexpr| serialize($value, $_:num)) | `(nlexpr| deserialize($_:nltype, $value))
  | `(nlexpr| encode($_:ident, $value)) | `(nlexpr| decode($_:ident, $value))
  | `(nlexpr| field($value, $_:ident))
  | `(nlexpr| enumTag($value))
  | `(nlexpr| toBytes32($value)) | `(nlexpr| reverseBytes32($value))
  | `(nlexpr| reverseBytes($value)) => inlineAssertions value
  | `(nlexpr| sliceBytes($value, $_:num, $_:num)) => inlineAssertions value
  | `(nlexpr| concatBytes($left, $right)) => inlineAssertions left ++ inlineAssertions right
  | `(nlexpr| byteAt($value, $_:num)) => inlineAssertions value
  | `(nlexpr| persistentHashVector32([$values,*]))
  | `(nlexpr| persistentHashNativeVector([$values,*])) => values.getElems.toList.flatMap inlineAssertions
  | `(nlexpr| jubjubScalarFromNative($value))
  | `(nlexpr| jubjubScalarToNative($value))
  | `(nlexpr| jubjubMulGenerator($value))
  | `(nlexpr| jubjubNeg($value))
  | `(nlexpr| jubjubX($value))
  | `(nlexpr| jubjubY($value)) => inlineAssertions value
  | `(nlexpr| jubjubMul($point, $scalar)) | `(nlexpr| jubjubAdd($point, $scalar)) =>
    inlineAssertions point ++ inlineAssertions scalar
  | `(nlexpr| jubjubFromCoordinates($x, $y)) => inlineAssertions x ++ inlineAssertions y
  | `(nlexpr| hashToCurve([$values,*])) => values.getElems.toList.flatMap inlineAssertions
  | `(nlexpr| foreignNeg($value)) | `(nlexpr| foreignInv($value))
  | `(nlexpr| curveMulGenerator($value)) | `(nlexpr| curveX($value))
  | `(nlexpr| curveY($value)) | `(nlexpr| foreignToBytes($value)) => inlineAssertions value
  | `(nlexpr| foreignAdd($left, $right)) | `(nlexpr| foreignSub($left, $right))
  | `(nlexpr| foreignMul($left, $right)) | `(nlexpr| curveMul($left, $right))
  | `(nlexpr| curveFromCoordinates($left, $right)) =>
    inlineAssertions left ++ inlineAssertions right
  | `(nlexpr| foreignFromBytes($_:nltype, $value)) => inlineAssertions value
  | `(nlexpr| witness $_:ident($args:nlexpr,*)) => args.getElems.toList.flatMap inlineAssertions
  | _ => []

private def commonType (stx : Syntax) (left right : Ty) : CommandElabM Ty := do
  if left == right then return left
  match left, right with
  | .uint m, .uint n => pure (.uint (max m n))
  | .native, .uint _ | .uint _, .native => pure .native
  | _, _ => throwErrorAt stx "readable witness expression type mismatch"

private def coerce (stx : Syntax) (value : Lowered) (target : Ty) : CommandElabM Lowered := do
  let .scalar found := value.type | throwErrorAt stx "Unit cannot be used as a scalar expression"
  if found == target then return value
  match found, target with
  | .uint m, .uint n =>
    unless m ≤ n do throwErrorAt stx "readable witness type narrowing needs an explicit cast"
    pure {value with type := .scalar target, term := .cast target value.term}
  | .uint _, .native => pure {value with type := .scalar .native, term := .cast .native value.term}
  | _, _ => throwErrorAt stx "readable witness expression type mismatch"

private def uniqueWitnesses (signatures : List WitnessSignature) : List WitnessSignature :=
  signatures.foldl (fun acc item => if acc.any (·.name == item.name) then acc else acc ++ [item]) []

private def mergeLowered (type : ResultType) (term : Noctium.Helpers.Term) (values : List Lowered) : Lowered := {
  type, term, before := values.flatMap (·.before),
  signatures := uniqueWitnesses (values.flatMap (·.signatures)),
  witnessNames := values.flatMap (·.witnessNames) |>.eraseDups,
  generatedValidity := values.flatMap (·.generatedValidity) |>.eraseDups
}

private def selectedCodec (name : TSyntax `ident) : ExprM (Helpers.Wire.Codec × String) := do
  let some ((_, codec), index) := (← get).codecs.zipIdx.find? (fun (candidate, _) => candidate.1 == name.getId)
    | throwErrorAt name s!"add codec '{name.getId}' to the circuit's using clause"
  pure (codec, Helpers.Wire.codecName index)

private def lowerProjection (stx : Syntax) (value : Lowered)
    (projection : Types.Projection) : ExprM Lowered := do
  let .composite parent := value.type | throwErrorAt stx "projection requires an aggregate value"
  let composites := (← get).composites
  let span ← spanValue stx
  let child ← match Helpers.projectedType composites span parent projection with
    | .ok child => pure child
    | .error diagnostic => throwErrorAt stx diagnostic.message
  pure {value with type := Helpers.resultTypeOfComposite child, term := .project value.term projection}

private def lowerForeignFieldConstant (stx : Syntax) (kind : Foreign.Kind) (value : Nat) : ExprM Lowered := do
  let encoding ← match Foreign.encodeField kind value with
    | .ok encoding => pure encoding
    | .error message => throwErrorAt stx message
  pure {type := .scalar (.foreign kind), term := .foreignConstant kind encoding}

private partial def lowerExpr (programName callPrefix : String) (env : SurfaceEnv)
    (stx : TSyntax `nlexpr) : ExprM Lowered := do
  match stx with
  | `(nlexpr| $id:ident) =>
    match env.find? (fun value => value.1 == id.getId.toString) with
    | some (_, type, term) => pure {type, term}
    | none => throwErrorAt id s!"unknown readable witness value '{id.getId}'"
  | `(nlexpr| $n:num) =>
    if n.getNat ≥ Field.modulus then throwErrorAt n "Native literal is not canonical"
    pure {type := .scalar .native, term := .native n.getNat}
  | `(nlexpr| true) => pure {type := .scalar .bool, term := .bool _root_.Bool.true}
  | `(nlexpr| false) => pure {type := .scalar .bool, term := .bool _root_.Bool.false}
  | `(nlexpr| uint($n:num)) => do
    match ScalarPolicy.validate (.uint n.getNat) with
    | .error message => throwErrorAt stx message
    | .ok _ => pure {type := .scalar (.uint n.getNat), term := .uint n.getNat n.getNat}
  | `(nlexpr| let $id:ident := $value:nlexpr in $body:nlexpr) => do
    let value ← lowerExpr programName callPrefix env value
    if value.type == .unit then throwErrorAt id "readable witness let cannot bind Unit"
    let localIndex ← get
    modify fun state => {state with nextLet := state.nextLet + 1}
    let internalName := s!"__noctium_let_{localIndex.nextLet}_{id.getId}"
    let ref := Noctium.Helpers.Term.ref internalName
    let body ← lowerExpr programName callPrefix ((id.getId.toString, value.type, ref) :: env) body
    pure
      { body with
        before := value.before ++ [.bind internalName value.type value.term] ++ body.before,
        signatures := uniqueWitnesses (value.signatures ++ body.signatures),
        witnessNames := (value.witnessNames ++ body.witnessNames).eraseDups,
        generatedValidity := (value.generatedValidity ++ body.generatedValidity).eraseDups }
  | `(nlexpr| assertThen($condition, $body)) => do
    unless (← get).allowAssertThen do
      throwErrorAt stx "assertThen is accepted only inside an explicit prove statement"
    let condition ← lowerExpr programName callPrefix env condition
    let condition ← coerce stx condition .bool
    let body ← lowerExpr programName callPrefix env body
    pure
      { body with
        before := condition.before ++ [.assert condition.term] ++ body.before,
        signatures := uniqueWitnesses (condition.signatures ++ body.signatures),
        witnessNames := (condition.witnessNames ++ body.witnessNames).eraseDups,
        generatedValidity := (condition.generatedValidity ++ body.generatedValidity).eraseDups }
  | `(nlexpr| cast($target:nltype, $value:nlexpr)) => do
    let target ← readScalarTy target
    let value ← lowerExpr programName callPrefix env value
    let .scalar source := value.type | throwErrorAt stx "cannot cast Unit"
    if source.isJubjub || target.isJubjub then
      throwErrorAt stx "Jubjub values require an explicitly supported curve route"
    pure {value with
      type := .scalar target,
      term := .cast target value.term,
      generatedValidity := (s!"checked cast {renderExpr stx}") :: value.generatedValidity
    }
  | `(nlexpr| disclose($value)) => do
    let value ← lowerExpr programName callPrefix env value
    pure {value with term := .disclose (← liftM (spanValue stx)) value.term}
  | `(nlexpr| add($left, $right)) => lowerArithmetic programName callPrefix env stx .add left right
  | `(nlexpr| sub($left, $right)) => lowerArithmetic programName callPrefix env stx .sub left right
  | `(nlexpr| mul($left, $right)) => lowerArithmetic programName callPrefix env stx .mul left right
  | `(nlexpr| eq($left, $right)) => do
    let left ← lowerExpr programName callPrefix env left
    let right ← lowerExpr programName callPrefix env right
    let .scalar leftTy := left.type | throwErrorAt stx "eq does not accept Unit"
    let .scalar rightTy := right.type | throwErrorAt stx "eq does not accept Unit"
    let ty ← commonType stx leftTy rightTy
    let left ← coerce stx left ty
    let right ← coerce stx right ty
    pure (mergeLowered (.scalar .bool) (.eq left.term right.term) [left, right])
  | `(nlexpr| boolAnd($left, $right)) => do
    let left ← lowerExpr programName callPrefix env left
    let right ← lowerExpr programName callPrefix env right
    unless left.type == .scalar .bool && right.type == .scalar .bool do
      throwErrorAt stx "boolAnd operands require Bool"
    pure (mergeLowered (.scalar .bool) (.boolAnd left.term right.term) [left, right])
  | `(nlexpr| boolOr($left, $right)) => do
    let left ← lowerExpr programName callPrefix env left
    let right ← lowerExpr programName callPrefix env right
    unless left.type == .scalar .bool && right.type == .scalar .bool do
      throwErrorAt stx "boolOr operands require Bool"
    pure (mergeLowered (.scalar .bool) (.boolOr left.term right.term) [left, right])
  | `(nlexpr| boolXor($left, $right)) => do
    let left ← lowerExpr programName callPrefix env left
    let right ← lowerExpr programName callPrefix env right
    unless left.type == .scalar .bool && right.type == .scalar .bool do
      throwErrorAt stx "boolXor operands require Bool"
    pure (mergeLowered (.scalar .bool) (.boolXor left.term right.term) [left, right])
  | `(nlexpr| select($condition, $yes, $no)) => do
    let condition ← lowerExpr programName callPrefix env condition
    let condition ← coerce stx condition .bool
    let yes ← lowerExpr programName callPrefix env yes
    let no ← lowerExpr programName callPrefix env no
    let .scalar yesTy := yes.type | throwErrorAt stx "select does not accept Unit"
    let .scalar noTy := no.type | throwErrorAt stx "select does not accept Unit"
    let ty ← commonType stx yesTy noTy
    let yes ← coerce stx yes ty
    let no ← coerce stx no ty
    pure (mergeLowered (.scalar ty) (.select condition.term yes.term no.term) [condition, yes, no])
  | `(nlexpr| poseidon2($domain:num, $left, $right)) => do
    let left ← lowerExpr programName callPrefix env left
    let right ← lowerExpr programName callPrefix env right
    let left ← coerce stx left .native
    let right ← coerce stx right .native
    pure (mergeLowered (.scalar .native) (.poseidon2 domain.getNat left.term right.term) [left, right])
  | `(nlexpr| secp256k1Base($value:num)) =>
    lowerForeignFieldConstant stx (.base .secp256k1) value.getNat
  | `(nlexpr| secp256k1Scalar($value:num)) =>
    lowerForeignFieldConstant stx (.scalar .secp256k1) value.getNat
  | `(nlexpr| secp256k1Identity()) =>
    pure {
      type := .scalar (.foreign (.point .secp256k1))
      term := .foreignConstant (.point .secp256k1) (Foreign.identityEncoding .secp256k1)
    }
  | `(nlexpr| secp256r1Base($value:num)) =>
    lowerForeignFieldConstant stx (.base .secp256r1) value.getNat
  | `(nlexpr| secp256r1Scalar($value:num)) =>
    lowerForeignFieldConstant stx (.scalar .secp256r1) value.getNat
  | `(nlexpr| secp256r1Identity()) =>
    pure {
      type := .scalar (.foreign (.point .secp256r1))
      term := .foreignConstant (.point .secp256r1) (Foreign.identityEncoding .secp256r1)
    }
  | `(nlexpr| curve25519Base($value:num)) =>
    lowerForeignFieldConstant stx (.base .curve25519) value.getNat
  | `(nlexpr| curve25519Scalar($value:num)) =>
    lowerForeignFieldConstant stx (.scalar .curve25519) value.getNat
  | `(nlexpr| curve25519Identity()) =>
    pure {
      type := .scalar (.foreign (.point .curve25519))
      term := .foreignConstant (.point .curve25519) (Foreign.identityEncoding .curve25519)
    }
  | `(nlexpr| bytes32($literal:str)) => do
    let bytes := literal.getString.toUTF8.data.toList.map UInt8.toNat
    if bytes.length > 32 then throwErrorAt stx "Bytes32 string literal exceeds 32 UTF-8 bytes"
    pure {type := .scalar (.bytes 32), term := .bytes32Literal (bytes ++ List.replicate (32 - bytes.length) 0)}
  | `(nlexpr| bytes($length:num, $literal:str)) => do
    let length := length.getNat
    if length > Types.defaultLimits.maxVectorLength then
      throwErrorAt stx s!"byte string length exceeds the maximum of {Types.defaultLimits.maxVectorLength}"
    let bytes := literal.getString.toUTF8.data.toList.map UInt8.toNat
    if bytes.length > length then
      throwErrorAt stx s!"byte string literal exceeds its declared length {length}"
    let values := bytes ++ List.replicate (length - bytes.length) 0
    let operation := Noctium.Helpers.BytesOp.bytesLiteral length values
    match operation.signature 0 with
    | .error message => throwErrorAt stx message
    | .ok _ => pure ()
    pure {type := .scalar (.bytes length), term := .bytes operation []}
  | `(nlexpr| byteAt($value, $index:num)) => do
    let value ← lowerExpr programName callPrefix env value
    let .scalar (.bytes length) := value.type
      | throwErrorAt stx "byteAt requires a fixed byte-string value"
    unless index.getNat < length do throwErrorAt stx "byteAt index is outside the byte string"
    pure (mergeLowered (.scalar (.uint 255)) (.bytesAt value.term index.getNat) [value])
  | `(nlexpr| persistentHash32($value)) =>
    lowerBytesOperation programName callPrefix env stx .persistentHash32 [value]
  | `(nlexpr| persistentHashVector32([$values,*])) =>
    lowerBytesOperation programName callPrefix env stx .persistentHashVector32 values.getElems.toList
  | `(nlexpr| persistentHashNative($value)) =>
    lowerBytesOperation programName callPrefix env stx .persistentHashNative [value]
  | `(nlexpr| persistentHashNativeVector([$values,*])) =>
    lowerBytesOperation programName callPrefix env stx .persistentHashNativeVector values.getElems.toList
  | `(nlexpr| persistentHashPoint($point)) =>
    lowerBytesOperation programName callPrefix env stx .persistentHashPoint [point]
  | `(nlexpr| sha512($value)) => do
    let value ← lowerExpr programName callPrefix env value
    let .scalar (.bytes length) := value.type
      | throwErrorAt stx "sha512 requires a fixed byte-string value"
    let operation := Noctium.Helpers.BytesOp.sha512 length
    let (_, result) ← match operation.signature 1 with
      | .error message => throwErrorAt stx message
      | .ok signature => pure signature
    pure (mergeLowered (.scalar result) (.bytes operation [value.term]) [value])
  | `(nlexpr| keccak256($value)) => do
    let value ← lowerExpr programName callPrefix env value
    let .scalar (.bytes length) := value.type
      | throwErrorAt stx "keccak256 requires a fixed byte-string value"
    let operation := Noctium.Helpers.BytesOp.keccak256 length
    let (_, result) ← match operation.signature 1 with
      | .error message => throwErrorAt stx message
      | .ok signature => pure signature
    pure (mergeLowered (.scalar result) (.bytes operation [value.term]) [value])
  | `(nlexpr| reverseBytes32($value)) =>
    lowerBytesOperation programName callPrefix env stx .reverseBytes32 [value]
  | `(nlexpr| reverseBytes($value)) => do
    let value ← lowerExpr programName callPrefix env value
    let .scalar (.bytes length) := value.type
      | throwErrorAt stx "reverseBytes requires a fixed byte-string value"
    let operation := Noctium.Helpers.BytesOp.reverseBytes length
    match operation.signature 1 with
    | .error message => throwErrorAt stx message
    | .ok _ => pure ()
    pure (mergeLowered (.scalar (.bytes length)) (.bytes operation [value.term]) [value])
  | `(nlexpr| sliceBytes($value, $start:num, $stop:num)) => do
    let value ← lowerExpr programName callPrefix env value
    let .scalar (.bytes length) := value.type
      | throwErrorAt stx "sliceBytes requires a fixed byte-string value"
    let operation := Noctium.Helpers.BytesOp.sliceBytes length start.getNat stop.getNat
    match operation.signature 1 with
    | .error message => throwErrorAt stx message
    | .ok _ => pure ()
    let resultLength := stop.getNat - start.getNat
    pure (mergeLowered (.scalar (.bytes resultLength)) (.bytes operation [value.term]) [value])
  | `(nlexpr| concatBytes($left, $right)) => do
    let left ← lowerExpr programName callPrefix env left
    let right ← lowerExpr programName callPrefix env right
    let .scalar (.bytes leftLength) := left.type
      | throwErrorAt stx "concatBytes requires fixed byte-string values"
    let .scalar (.bytes rightLength) := right.type
      | throwErrorAt stx "concatBytes requires fixed byte-string values"
    let operation := Noctium.Helpers.BytesOp.concatBytes leftLength rightLength
    let (_, resultType) ← match operation.signature 2 with
      | .error message => throwErrorAt stx message
      | .ok signature => pure signature
    pure (mergeLowered (.scalar resultType) (.bytes operation [left.term, right.term]) [left, right])
  | `(nlexpr| degradeToNative($value)) =>
    lowerBytesOperation programName callPrefix env stx .degradeToNative [value]
  | `(nlexpr| toBytes32($value)) => do
    let value ← lowerExpr programName callPrefix env value
    let .scalar source := value.type | throwErrorAt stx "toBytes32 does not accept Unit"
    let operation := Noctium.Helpers.BytesOp.toBytes32 source
    match operation.signature 1 with
    | .error message => throwErrorAt stx message
    | .ok _ => pure ()
    pure (mergeLowered (.scalar (.bytes 32)) (.bytes operation [value.term]) [value])
  | `(nlexpr| serialize($value, $length:num)) => do
    let value ← lowerExpr programName callPrefix env value
    let .scalar source := value.type | throwErrorAt stx "serialize requires a scalar or fixed bytes"
    let operation := Noctium.Helpers.BytesOp.serialize source length.getNat
    let (_, result) ← match operation.signature 1 with
      | .ok signature => pure signature
      | .error message => throwErrorAt stx message
    pure (mergeLowered (.scalar result) (.bytes operation [value.term]) [value])
  | `(nlexpr| deserialize($target:nltype, $value)) => do
    let target ← readScalarTy target
    let value ← lowerExpr programName callPrefix env value
    let .scalar (.bytes length) := value.type | throwErrorAt stx "deserialize requires fixed bytes"
    let operation := Noctium.Helpers.BytesOp.deserialize target length
    match operation.signature 1 with
    | .error message => throwErrorAt stx message
    | .ok _ => pure ()
    let result := mergeLowered (.scalar target) (.bytes operation [value.term]) [value]
    pure {result with generatedValidity := s!"checked wire decode {renderExpr stx}" :: result.generatedValidity}
  | `(nlexpr| encode($name:ident, $value)) => do
    let (codec, helper) ← selectedCodec name
    let value ← lowerExpr programName callPrefix env value
    unless value.type == .composite codec.payload do
      throwErrorAt stx s!"encode requires the payload type of codec '{name.getId}'"
    pure (mergeLowered (.scalar (.bytes codec.frameBytes)) (.call (helper ++ "Encode") [value.term]) [value])
  | `(nlexpr| decode($name:ident, $value)) => do
    let (codec, helper) ← selectedCodec name
    let value ← lowerExpr programName callPrefix env value
    unless value.type == .scalar (.bytes codec.frameBytes) do
      throwErrorAt stx s!"decode requires Bytes {codec.frameBytes} for codec '{name.getId}'"
    let result := mergeLowered (.composite codec.payload) (.call (helper ++ "Decode") [value.term]) [value]
    pure {result with generatedValidity := s!"checked wire decode {renderExpr stx}" :: result.generatedValidity}
  | `(nlexpr| field($value, $name:ident)) =>
    lowerProjection stx (← lowerExpr programName callPrefix env value) (.field name.getId.toString)
  | `(nlexpr| elementAt($value, $index)) => do
    let value ← lowerExpr programName callPrefix env value
    if let `(nlexpr| $literal:num) := index then
      let offset := literal.getNat
      let projection ← match value.type with
        | .composite (.tuple _) => pure (Types.Projection.tupleIndex offset)
        | .composite (.vector _ _) => pure (.vectorIndex offset)
        | .composite (.bytes _) => pure (.byteIndex offset)
        | _ => throwErrorAt stx "elementAt requires an aggregate tuple, vector or byte string"
      return ← lowerProjection stx value projection
    let offset ← lowerExpr programName callPrefix env index
    let type ← match Helpers.indexResultType (← spanValue stx) value.type offset.type with
      | .ok type => pure type
      | .error diagnostic => throwErrorAt stx diagnostic.message
    let result := mergeLowered type (.index value.term offset.term) [value, offset]
    let result := {result with generatedValidity := s!"checked vector index {renderExpr index}" :: result.generatedValidity}
    if offset.before.isEmpty then return result
    -- Evaluate the vector before bindings introduced by the index expression.
    let next := (← get).nextLet
    modify fun state => {state with nextLet := state.nextLet + 1}
    let vector := s!"__noctium_index_vector_{next}"
    return { result with
      term := .index (.ref vector) offset.term
      before := value.before ++ [.bind vector value.type value.term] ++ offset.before}
  | `(nlexpr| enumTag($value)) =>
    lowerProjection stx (← lowerExpr programName callPrefix env value) .enumTag
  | `(nlexpr| jubjubScalarFromNative($value)) =>
    lowerCurve programName callPrefix env stx .scalarFromNative [value]
  | `(nlexpr| jubjubScalarToNative($value)) =>
    lowerCurve programName callPrefix env stx .scalarToNative [value]
  | `(nlexpr| jubjubMulGenerator($value)) =>
    lowerCurve programName callPrefix env stx .mulGenerator [value]
  | `(nlexpr| jubjubMul($point, $scalar)) =>
    lowerCurve programName callPrefix env stx .mul [point, scalar]
  | `(nlexpr| jubjubAdd($left, $right)) =>
    lowerCurve programName callPrefix env stx .add [left, right]
  | `(nlexpr| jubjubNeg($point)) => lowerCurve programName callPrefix env stx .neg [point]
  | `(nlexpr| jubjubX($point)) => lowerCurve programName callPrefix env stx .x [point]
  | `(nlexpr| jubjubY($point)) => lowerCurve programName callPrefix env stx .y [point]
  | `(nlexpr| jubjubFromCoordinates($x, $y)) =>
    lowerCurve programName callPrefix env stx .fromCoordinates [x, y]
  | `(nlexpr| hashToCurve([$values,*])) => do
    let arguments := values.getElems.toList
    if arguments.length > Types.defaultLimits.maxVectorLength then
      throwErrorAt stx s!"hashToCurve input count exceeds the maximum of {Types.defaultLimits.maxVectorLength}"
    lowerCurve programName callPrefix env stx (.hashToCurve arguments.length) arguments
  | `(nlexpr| foreignNeg($value)) => lowerForeignUnary programName callPrefix env stx "neg" value
  | `(nlexpr| foreignInv($value)) => lowerForeignUnary programName callPrefix env stx "inv" value
  | `(nlexpr| curveMulGenerator($value)) =>
    lowerForeignUnary programName callPrefix env stx "mulGenerator" value
  | `(nlexpr| curveX($value)) => lowerForeignUnary programName callPrefix env stx "x" value
  | `(nlexpr| curveY($value)) => lowerForeignUnary programName callPrefix env stx "y" value
  | `(nlexpr| foreignAdd($left, $right)) =>
    lowerForeignBinary programName callPrefix env stx "add" left right
  | `(nlexpr| foreignSub($left, $right)) =>
    lowerForeignBinary programName callPrefix env stx "sub" left right
  | `(nlexpr| foreignMul($left, $right)) =>
    lowerForeignBinary programName callPrefix env stx "mul" left right
  | `(nlexpr| curveMul($point, $scalar)) =>
    lowerForeignBinary programName callPrefix env stx "ecMul" point scalar
  | `(nlexpr| curveFromCoordinates($x, $y)) =>
    lowerForeignBinary programName callPrefix env stx "fromCoordinates" x y
  | `(nlexpr| foreignToBytes($value)) => do
    let value ← lowerExpr programName callPrefix env value
    let .scalar (.foreign kind) := value.type
      | throwErrorAt stx "foreignToBytes requires a foreign value"
    let operation := Noctium.Helpers.BytesOp.foreignToBytes kind
    let (expected, result) ← match operation.signature 1 with
      | .ok signature => pure signature
      | .error message => throwErrorAt stx message
    unless expected == [.foreign kind] do throwErrorAt stx "foreignToBytes argument type mismatch"
    pure (mergeLowered (.scalar result) (.bytes operation [value.term]) [value])
  | `(nlexpr| foreignFromBytes($target:nltype, $value)) => do
    let target ← readScalarTy target
    let .foreign kind := target
      | throwErrorAt stx "foreignFromBytes requires a foreign target type"
    let value ← lowerExpr programName callPrefix env value
    let .scalar (.bytes length) := value.type
      | throwErrorAt stx "foreignFromBytes requires a fixed byte string"
    let operation := Noctium.Helpers.BytesOp.foreignFromBytes kind length
    let (expected, result) ← match operation.signature 1 with
      | .ok signature => pure signature
      | .error message => throwErrorAt stx message
    unless expected == [.bytes length] && result == target do
      throwErrorAt stx "foreignFromBytes argument type mismatch"
    let lowered := mergeLowered (.scalar result) (.bytes operation [value.term]) [value]
    pure {lowered with generatedValidity :=
      (lowered.generatedValidity ++
        if let .point _ := kind then ["canonical foreign point decoding"] else []).eraseDups}
  | `(nlexpr| witness $function:ident($args:nlexpr,*)) => do
    let signature ← liftM (witnessSignature function)
    let signatureName := signature.name
    validIdentity function signatureName
    unless signature.parameters.all (fun p => match p.type with
      | .scalar _ => _root_.Bool.true
      | _ => _root_.Bool.false) do
      throwErrorAt function "witness callback parameters must use supported scalar types"
    let supportedResult : _root_.Bool := match signature.result with
      | .scalar _ => _root_.Bool.true
      | .unit => _root_.Bool.true
      | .composite _ => _root_.Bool.false
    if !supportedResult then
      throwErrorAt function "witness callback results require Unit or a supported scalar type"
    unless args.getElems.size == signature.parameters.length do
      throwErrorAt stx s!"witness '{function.getId}' argument count does not match its declaration"
    let mut loweredArgs := []
    for (argument, parameter) in (args.getElems.toList.zip signature.parameters) do
      let value ← lowerExpr programName callPrefix env argument
      let .scalar parameterTy := parameter.type | throwErrorAt function "Unit witness parameters are unsupported"
      let value ← coerce argument value parameterTy
      loweredArgs := loweredArgs ++ [value]
    let callNo ← get
    modify fun state => {state with nextCall := state.nextCall + 1}
    let site := s!"{programName}.call.{callPrefix}.{callNo.nextCall}"
    validIdentity stx site
    let term := .witnessCall site signatureName (loweredArgs.map (·.term))
    let result := signature.result
    pure
      { mergeLowered result term loweredArgs with
        signatures := uniqueWitnesses (signature :: loweredArgs.flatMap (·.signatures)),
        witnessNames := (signatureName :: loweredArgs.flatMap (·.witnessNames)).eraseDups,
        generatedValidity := (loweredArgs.flatMap (·.generatedValidity) ++
          [s!"typed witness reply: {signatureName}"]).eraseDups }
  | _ => throwErrorAt stx "unsupported readable witness expression"
where
  lowerBytesOperation (programName callPrefix : String) (env : SurfaceEnv) (stx : Syntax)
      (operation : Noctium.Helpers.BytesOp) (arguments : List (TSyntax `nlexpr)) : ExprM Lowered := do
    let (expected, result) ← match operation.signature arguments.length with
      | .ok signature => pure signature
      | .error message => throwErrorAt stx message
    let values ← arguments.mapM (lowerExpr programName callPrefix env)
    for (value, expectedType) in values.zip expected do
      let .scalar actualType := value.type | throwErrorAt stx "byte operation argument cannot be Unit"
      unless actualType == expectedType do
        throwErrorAt stx s!"{operation.operationName} argument type mismatch"
    let term := Noctium.Helpers.Term.bytes operation (values.map (·.term))
    pure (mergeLowered (.scalar result) term values)

  lowerCurve (programName callPrefix : String) (env : SurfaceEnv) (stx : Syntax)
      (operation : Noctium.Helpers.CurveOp) (arguments : List (TSyntax `nlexpr)) : ExprM Lowered := do
    if let .hashToCurve arity := operation then
      if arity > Types.defaultLimits.maxVectorLength then
        throwErrorAt stx s!"hashToCurve input count exceeds the maximum of {Types.defaultLimits.maxVectorLength}"
      unless arity == arguments.length do
        throwErrorAt stx "hashToCurve argument count mismatch"
    let (expected, result) := operation.signature
    unless arguments.length == expected.length do
      throwErrorAt stx s!"{operation.operationName} argument count mismatch"
    let values ← arguments.mapM (lowerExpr programName callPrefix env)
    for (value, expectedType) in values.zip expected do
      let .scalar actualType := value.type | throwErrorAt stx "curve operation argument cannot be Unit"
      unless actualType == expectedType do
        throwErrorAt stx s!"{operation.operationName} argument type mismatch"
    let term := Noctium.Helpers.Term.curve operation (values.map (·.term))
    pure { mergeLowered (.scalar result) term values with
      generatedValidity := (values.flatMap (·.generatedValidity) ++
        if operation == .fromCoordinates then ["Jubjub point coordinate validation"] else []).eraseDups }

  lowerForeignUnary (programName callPrefix : String) (env : SurfaceEnv) (stx : Syntax)
      (operationName : String) (valueStx : TSyntax `nlexpr) : ExprM Lowered := do
    let value ← lowerExpr programName callPrefix env valueStx
    let .scalar (.foreign kind) := value.type
      | throwErrorAt stx s!"{operationName} requires a foreign value"
    let operation ← match operationName with
      | "neg" => pure (Foreign.UnaryOp.neg kind)
      | "inv" =>
        match kind.fieldKind? with
        | some field => pure (Foreign.UnaryOp.inv field)
        | none => throwErrorAt stx "foreignInv does not accept points"
      | "mulGenerator" =>
        if let .scalar curve := kind then pure (Foreign.UnaryOp.mulGenerator curve)
        else throwErrorAt stx "curveMulGenerator requires a foreign scalar"
      | "x" =>
        if let .point curve := kind then pure (Foreign.UnaryOp.x curve)
        else throwErrorAt stx "curveX requires a foreign point"
      | "y" =>
        if let .point curve := kind then pure (Foreign.UnaryOp.y curve)
        else throwErrorAt stx "curveY requires a foreign point"
      | _ => throwErrorAt stx "unsupported foreign unary operation"
    finishForeignCurve stx (.foreignUnary operation) [value]

  lowerForeignBinary (programName callPrefix : String) (env : SurfaceEnv) (stx : Syntax)
      (operationName : String) (leftStx rightStx : TSyntax `nlexpr) : ExprM Lowered := do
    let left ← lowerExpr programName callPrefix env leftStx
    let right ← lowerExpr programName callPrefix env rightStx
    let .scalar (.foreign leftKind) := left.type
      | throwErrorAt stx s!"{operationName} requires foreign values"
    let .scalar (.foreign rightKind) := right.type
      | throwErrorAt stx s!"{operationName} requires foreign values"
    let operation ← match operationName with
      | "add" =>
        unless leftKind == rightKind do throwErrorAt stx "foreignAdd requires matching foreign types"
        pure (Foreign.BinaryOp.add leftKind)
      | "sub" =>
        unless leftKind == rightKind do throwErrorAt stx "foreignSub requires matching foreign types"
        pure (Foreign.BinaryOp.sub leftKind)
      | "mul" =>
        unless leftKind == rightKind do throwErrorAt stx "foreignMul requires matching foreign types"
        match leftKind.fieldKind? with
        | some field => pure (Foreign.BinaryOp.mul field)
        | none => throwErrorAt stx "foreignMul does not multiply points"
      | "ecMul" =>
        match leftKind, rightKind with
        | .point curve, .scalar otherCurve =>
          unless curve == otherCurve do throwErrorAt stx "curveMul requires a matching curve scalar"
          pure (Foreign.BinaryOp.ecMul curve)
        | _, _ => throwErrorAt stx "curveMul requires a foreign point and matching scalar"
      | "fromCoordinates" =>
        match leftKind, rightKind with
        | .base curve, .base otherCurve =>
          unless curve == otherCurve do throwErrorAt stx "curveFromCoordinates requires a matching curve family"
          pure (Foreign.BinaryOp.fromCoordinates curve)
        | _, _ => throwErrorAt stx "curveFromCoordinates requires two matching foreign base values"
      | _ => throwErrorAt stx "unsupported foreign binary operation"
    finishForeignCurve stx (.foreignBinary operation) [left, right]

  finishForeignCurve (stx : Syntax) (operation : Noctium.Helpers.CurveOp)
      (values : List Lowered) : ExprM Lowered := do
    let (expected, result) := operation.signature
    unless values.length == expected.length do
      throwErrorAt stx s!"{operation.operationName} argument count mismatch"
    for (value, expectedType) in values.zip expected do
      unless value.type == .scalar expectedType do
        throwErrorAt stx s!"{operation.operationName} argument type mismatch"
    let validity := match operation with
      | .foreignUnary (.inv _) => ["foreign inverse nonzero check"]
      | .foreignUnary (.x _) | .foreignUnary (.y _) => ["foreign point coordinate validity"]
      | .foreignBinary (.fromCoordinates _) => ["foreign point membership validation"]
      | _ => []
    let term := Noctium.Helpers.Term.curve operation (values.map (·.term))
    pure {mergeLowered (.scalar result) term values with
      generatedValidity := (values.flatMap (·.generatedValidity) ++ validity).eraseDups}

  lowerArithmetic (programName callPrefix : String) (env : SurfaceEnv) (stx : Syntax)
      (op : ScalarPolicy.Binary) (leftStx rightStx : TSyntax `nlexpr) : ExprM Lowered := do
    let left ← lowerExpr programName callPrefix env leftStx
    let right ← lowerExpr programName callPrefix env rightStx
    let .scalar leftTy := left.type | throwErrorAt stx "arithmetic does not accept Unit"
    let .scalar rightTy := right.type | throwErrorAt stx "arithmetic does not accept Unit"
    let result ← match ScalarPolicy.infer op leftTy.scalarKind rightTy.scalarKind with
      | .ok (.native) => pure .native
      | .ok (.uint maximum) => pure (.uint maximum)
      | .ok _ => throwErrorAt stx "unsupported scalar arithmetic result"
      | .error message => throwErrorAt stx message
    let left ← match result with
      | .native => coerce stx left .native
      | .uint _ => pure left
      | _ => throwErrorAt stx "unsupported arithmetic result type"
    let right ← match result with
      | .native => coerce stx right .native
      | .uint _ => pure right
      | _ => throwErrorAt stx "unsupported arithmetic result type"
    let term := Noctium.Helpers.Term.binary op left.term right.term
    let underflow := match op, leftTy, rightTy with
      | .sub, .uint _, .uint _ => ["unsigned subtraction underflow"]
      | _, _, _ => []
    pure {
      type := .scalar result, term,
      before := left.before ++ right.before,
      signatures := uniqueWitnesses (left.signatures ++ right.signatures),
      witnessNames := (left.witnessNames ++ right.witnessNames).eraseDups,
      generatedValidity := (left.generatedValidity ++ right.generatedValidity ++ underflow).eraseDups
    }

private def authoringForeignCurveTerm : Foreign.Curve → CommandElabM (TSyntax `term)
  | .secp256k1 => `(Noctium.Foreign.Curve.secp256k1)
  | .secp256r1 => `(Noctium.Foreign.Curve.secp256r1)
  | .curve25519 => `(Noctium.Foreign.Curve.curve25519)

private def authoringForeignKindTerm : Foreign.Kind → CommandElabM (TSyntax `term)
  | .base curve => do
    let curve ← authoringForeignCurveTerm curve
    `(Noctium.Foreign.Kind.base $curve)
  | .scalar curve => do
    let curve ← authoringForeignCurveTerm curve
    `(Noctium.Foreign.Kind.scalar $curve)
  | .point curve => do
    let curve ← authoringForeignCurveTerm curve
    `(Noctium.Foreign.Kind.point $curve)

private def authoringForeignFieldKindTerm : Foreign.FieldKind → CommandElabM (TSyntax `term)
  | .base curve => do
    let curve ← authoringForeignCurveTerm curve
    `(Noctium.Foreign.FieldKind.base $curve)
  | .scalar curve => do
    let curve ← authoringForeignCurveTerm curve
    `(Noctium.Foreign.FieldKind.scalar $curve)

private def authoringForeignUnaryTerm : Foreign.UnaryOp → CommandElabM (TSyntax `term)
  | .neg kind => do
    let kind ← authoringForeignKindTerm kind
    `(Noctium.Foreign.UnaryOp.neg $kind)
  | .inv kind => do
    let kind ← authoringForeignFieldKindTerm kind
    `(Noctium.Foreign.UnaryOp.inv $kind)
  | .mulGenerator curve => do
    let curve ← authoringForeignCurveTerm curve
    `(Noctium.Foreign.UnaryOp.mulGenerator $curve)
  | .x curve => do
    let curve ← authoringForeignCurveTerm curve
    `(Noctium.Foreign.UnaryOp.x $curve)
  | .y curve => do
    let curve ← authoringForeignCurveTerm curve
    `(Noctium.Foreign.UnaryOp.y $curve)

private def authoringForeignBinaryTerm : Foreign.BinaryOp → CommandElabM (TSyntax `term)
  | .add kind => do
    let kind ← authoringForeignKindTerm kind
    `(Noctium.Foreign.BinaryOp.add $kind)
  | .sub kind => do
    let kind ← authoringForeignKindTerm kind
    `(Noctium.Foreign.BinaryOp.sub $kind)
  | .mul kind => do
    let kind ← authoringForeignFieldKindTerm kind
    `(Noctium.Foreign.BinaryOp.mul $kind)
  | .ecMul curve => do
    let curve ← authoringForeignCurveTerm curve
    `(Noctium.Foreign.BinaryOp.ecMul $curve)
  | .fromCoordinates curve => do
    let curve ← authoringForeignCurveTerm curve
    `(Noctium.Foreign.BinaryOp.fromCoordinates $curve)

private partial def termTerm : Noctium.Helpers.Term → CommandElabM (TSyntax `term)
  | .unit => `(Noctium.Helpers.Term.unit)
  | .native value => `(Noctium.Helpers.Term.native $(natTerm value))
  | .bool value => do
    let value ← if value then `(Bool.true) else `(Bool.false)
    `(Noctium.Helpers.Term.bool $value)
  | .uint maximum value => `(Noctium.Helpers.Term.uint $(natTerm maximum) $(natTerm value))
  | .ref name => `(Noctium.Helpers.Term.ref $(stringTerm name))
  | .binary op left right => do
    let op ← match op with
      | .add => `(Noctium.ScalarPolicy.Binary.add)
      | .sub => `(Noctium.ScalarPolicy.Binary.sub)
      | .mul => `(Noctium.ScalarPolicy.Binary.mul)
    `(Noctium.Helpers.Term.binary $op $(← termTerm left) $(← termTerm right))
  | .boolAnd left right => do
    `(Noctium.Helpers.Term.boolAnd $(← termTerm left) $(← termTerm right))
  | .boolOr left right => do
    `(Noctium.Helpers.Term.boolOr $(← termTerm left) $(← termTerm right))
  | .boolXor left right => do
    `(Noctium.Helpers.Term.boolXor $(← termTerm left) $(← termTerm right))
  | .foreignConstant kind encoding => do
    let kind ← match kind with
      | .base .secp256k1 => `(Noctium.Foreign.Kind.base Noctium.Foreign.Curve.secp256k1)
      | .scalar .secp256k1 => `(Noctium.Foreign.Kind.scalar Noctium.Foreign.Curve.secp256k1)
      | .point .secp256k1 => `(Noctium.Foreign.Kind.point Noctium.Foreign.Curve.secp256k1)
      | .base .secp256r1 => `(Noctium.Foreign.Kind.base Noctium.Foreign.Curve.secp256r1)
      | .scalar .secp256r1 => `(Noctium.Foreign.Kind.scalar Noctium.Foreign.Curve.secp256r1)
      | .point .secp256r1 => `(Noctium.Foreign.Kind.point Noctium.Foreign.Curve.secp256r1)
      | .base .curve25519 => `(Noctium.Foreign.Kind.base Noctium.Foreign.Curve.curve25519)
      | .scalar .curve25519 => `(Noctium.Foreign.Kind.scalar Noctium.Foreign.Curve.curve25519)
      | .point .curve25519 => `(Noctium.Foreign.Kind.point Noctium.Foreign.Curve.curve25519)
    let encoding := encoding.map natTerm |>.toArray
    `(Noctium.Helpers.Term.foreignConstant $kind [$encoding,*])
  | .eq left right => do `(Noctium.Helpers.Term.eq $(← termTerm left) $(← termTerm right))
  | .cast ty value => do `(Noctium.Helpers.Term.cast $(← tyTerm ty) $(← termTerm value))
  | .disclose span value => do
    let span ← quoteSpan span
    `(Noctium.Helpers.Term.disclose $span $(← termTerm value))
  | .ite condition yes no => do
    `(Noctium.Helpers.Term.ite $(← termTerm condition) $(← termTerm yes) $(← termTerm no))
  | .select condition yes no => do
    `(Noctium.Helpers.Term.select $(← termTerm condition) $(← termTerm yes) $(← termTerm no))
  | .witnessCall site name args => do
    let args ← args.mapM termTerm
    let args := args.toArray
    `(Noctium.Helpers.Term.witnessCall $(stringTerm site) $(stringTerm name) [$args,*])
  | .call name args => do
    let args := (← args.mapM termTerm).toArray
    `(Noctium.Helpers.Term.call $(stringTerm name) [$args,*])
  | .poseidon2 domain left right => do
    `(Noctium.Helpers.Term.poseidon2 $(natTerm domain) $(← termTerm left) $(← termTerm right))
  | .curve operation arguments => do
    let operation ← match operation with
      | .scalarFromNative => `(Noctium.Helpers.CurveOp.scalarFromNative)
      | .scalarToNative => `(Noctium.Helpers.CurveOp.scalarToNative)
      | .mulGenerator => `(Noctium.Helpers.CurveOp.mulGenerator)
      | .mul => `(Noctium.Helpers.CurveOp.mul)
      | .add => `(Noctium.Helpers.CurveOp.add)
      | .neg => `(Noctium.Helpers.CurveOp.neg)
      | .x => `(Noctium.Helpers.CurveOp.x)
      | .y => `(Noctium.Helpers.CurveOp.y)
      | .fromCoordinates => `(Noctium.Helpers.CurveOp.fromCoordinates)
      | .hashToCurve arity => `(Noctium.Helpers.CurveOp.hashToCurve $(natTerm arity))
      | .foreignUnary foreignOperation => do
        let operation ← authoringForeignUnaryTerm foreignOperation
        `(Noctium.Helpers.CurveOp.foreignUnary $operation)
      | .foreignBinary foreignOperation => do
        let operation ← authoringForeignBinaryTerm foreignOperation
        `(Noctium.Helpers.CurveOp.foreignBinary $operation)
    let arguments ← arguments.mapM termTerm
    let arguments := arguments.toArray
    `(Noctium.Helpers.Term.curve $operation [$arguments,*])
  | .bytes operation arguments => do
    let operation ← match operation with
      | .persistentHash32 => `(Noctium.Helpers.BytesOp.persistentHash32)
      | .persistentHashVector32 => `(Noctium.Helpers.BytesOp.persistentHashVector32)
      | .persistentHashNative => `(Noctium.Helpers.BytesOp.persistentHashNative)
      | .persistentHashNativeVector => `(Noctium.Helpers.BytesOp.persistentHashNativeVector)
      | .persistentHashPoint => `(Noctium.Helpers.BytesOp.persistentHashPoint)
      | .sha512 length => `(Noctium.Helpers.BytesOp.sha512 $(natTerm length))
      | .keccak256 length => `(Noctium.Helpers.BytesOp.keccak256 $(natTerm length))
      | .reverseBytes32 => `(Noctium.Helpers.BytesOp.reverseBytes32)
      | .reverseBytes length => `(Noctium.Helpers.BytesOp.reverseBytes $(natTerm length))
      | .sliceBytes length start stop =>
        `(Noctium.Helpers.BytesOp.sliceBytes $(natTerm length) $(natTerm start) $(natTerm stop))
      | .concatBytes leftLength rightLength =>
        `(Noctium.Helpers.BytesOp.concatBytes $(natTerm leftLength) $(natTerm rightLength))
      | .foreignToBytes kind => do
        let kind ← authoringForeignKindTerm kind
        `(Noctium.Helpers.BytesOp.foreignToBytes $kind)
      | .foreignFromBytes kind length => do
        let kind ← authoringForeignKindTerm kind
        `(Noctium.Helpers.BytesOp.foreignFromBytes $kind $(natTerm length))
      | .degradeToNative => `(Noctium.Helpers.BytesOp.degradeToNative)
      | .toBytes32 source => `(Noctium.Helpers.BytesOp.toBytes32 $(← tyTerm source))
      | .serialize source length =>
        `(Noctium.Helpers.BytesOp.serialize $(← tyTerm source) $(natTerm length))
      | .deserialize target length =>
        `(Noctium.Helpers.BytesOp.deserialize $(← tyTerm target) $(natTerm length))
      | .bytesLiteral length values => do
        let values := values.map natTerm |>.toArray
        `(Noctium.Helpers.BytesOp.bytesLiteral $(natTerm length) [$values,*])
    let arguments ← arguments.mapM termTerm
    let arguments := arguments.toArray
    `(Noctium.Helpers.Term.bytes $operation [$arguments,*])
  | .bytes32Literal values => do
    let values := values.map natTerm |>.toArray
    `(Noctium.Helpers.Term.bytes32Literal [$values,*])
  | .bytesAt value index => do
    `(Noctium.Helpers.Term.bytesAt $(← termTerm value) $(natTerm index))
  | .composite type leaves => do
    let type ← compositeTypeTerm type
    let leaves ← leaves.mapM termTerm
    let leaves := leaves.toArray
    `(Noctium.Helpers.Term.composite $type [$leaves,*])
  | .project value projection => do
    let projection ← match projection with
      | .field name => `(Noctium.Types.Projection.field $(stringTerm name))
      | .tupleIndex index => `(Noctium.Types.Projection.tupleIndex $(natTerm index))
      | .vectorIndex index => `(Noctium.Types.Projection.vectorIndex $(natTerm index))
      | .byteIndex index => `(Noctium.Types.Projection.byteIndex $(natTerm index))
      | .enumTag => `(Noctium.Types.Projection.enumTag)
      | .enumField variant name =>
        `(Noctium.Types.Projection.enumField $(stringTerm variant) $(stringTerm name))
    `(Noctium.Helpers.Term.project $(← termTerm value) $projection)
  | .index value index => do
    `(Noctium.Helpers.Term.index $(← termTerm value) $(← termTerm index))
  | .at span value => do
    let span ← quoteSpan span
    `(Noctium.Helpers.Term.at $span $(← termTerm value))
  | _ => throwError "unsupported generated helper term"

private def statementTerm : Statement → CommandElabM (TSyntax `term)
  | .bind name type value => do
    `(Noctium.Helpers.Statement.bind $(stringTerm name) $(← resultTypeTerm type) $(← termTerm value))
  | .evaluate value => do `(Noctium.Helpers.Statement.evaluate $(← termTerm value))
  | .assert value => do `(Noctium.Helpers.Statement.assert $(← termTerm value))
  | .return value => do
    let value ← match value with
      | none => `(none)
      | some value => `(some $(← termTerm value))
    `(Noctium.Helpers.Statement.«return» $value)
  | .stage capability key ty value => do
    `(Noctium.Helpers.Statement.stage $(stringTerm capability) $(stringTerm key)
      $(← tyTerm ty) $(← termTerm value))
  | .readCell .. => throwError "readable witness source does not support ledger cell reads"
  | .writeCell .. => throwError "readable witness source does not support ledger cell writes"
  | .readMap .. | .readMember .. =>
    throwError "readable witness source does not support ledger map reads"
  | .writeMap .. => throwError "readable witness source does not support ledger map writes"
  | .branch .. => throwError "readable witness source does not support branch statements yet"
  | .forRange .. => throwError "readable witness source does not support unexpanded finite loops"

private def inputTerm (name : String) (ty : Ty) (visibility : Noctium.Visibility)
    (span : SourceSpan) : CommandElabM (TSyntax `term) := do
  let visibility ← if visibility == .public then `(Noctium.Visibility.public)
    else `(Noctium.Visibility.private)
  let span ← quoteSpan span
  let ty ← tyTerm ty
  `(Noctium.Input.mk $(stringTerm name) $ty $visibility $span)

private def observationTerm (metadata : ObservationMetadata) : CommandElabM (TSyntax `term) := do
  let inputs ← metadata.inputs.mapM fun input => do
    let ty ← tyTerm input.ty
    let visibility ← if input.visibility == .public then `(Noctium.Visibility.public)
      else `(Noctium.Visibility.private)
    `(Noctium.Authoring.ObservationInput.mk $(stringTerm input.name) $ty $visibility)
  let inputs := inputs.toArray
  let list (values : List String) := (values.map stringTerm).toArray
  let entryText := stringTerm metadata.entryName
  let reads := list metadata.privateReads
  let stages := list metadata.privateStages
  let witnesses := list metadata.witnessNames
  let proves := list metadata.authoredProves
  let releases := list metadata.explicitReleases
  let validity := list metadata.generatedValidity
  `(Noctium.Authoring.ObservationMetadata.mk $entryText [$inputs,*] [$reads,*] [$stages,*]
    [$witnesses,*] [$proves,*] [$releases,*] [$validity,*])

@[command_elab noctiumPrivateStateCommand] unsafe def elabPrivateState : CommandElab := fun stx => do
  match stx with
  | `(noctium_private_state $name:ident where $fields:noctium_private_field* end) => do
    let schemaName ← lowerSchemaName name
    let mut fieldValues : List PrivateStateField := []
    for fieldStx in fields do
      match fieldStx with
      | `(noctium_private_field| cell $field:ident : $type:nltype) => do
        let ty ← readScalarTy type
        if ty.isJubjub then
          throwErrorAt type "Jubjub private-state cells are not supported by this witness path"
        let key := "noctium/" ++ schemaName ++ "/" ++ field.getId.toString
        let capability := "private_state:" ++ schemaName
        let signatureName := "private_state.read." ++ schemaName ++ "." ++ field.getId.toString ++ ".v1"
        let operation := "private_state.read.v1"
        validIdentity field signatureName
        validIdentity field capability
        let fieldSpan ← spanValue fieldStx
        let signature : WitnessSignature :=
          { name := signatureName,
            operation := operation,
            capability := capability,
            privateKey := some key,
            result := .scalar ty,
            span := fieldSpan }
        fieldValues := fieldValues ++ [PrivateStateField.mk
          field.getId.toString ty key capability signature]
      | _ => throwErrorAt fieldStx "unsupported private-state field"
    let fields := fieldValues
    if !uniqueStrings (fields.map (·.name)) then throwErrorAt name "duplicate private-state field"
    let fullName := (← getCurrNamespace) ++ name.getId
    let generated := generatedName fullName "__privateStateSchema"
    let generatedSyntaxName := generatedName name.getId "__privateStateSchema"
    if (← getEnv).contains generated then throwErrorAt name "private-state schema descriptor already exists"
    let schemaTerm ← do
      let fieldTerms ← fields.mapM quoteField
      let fieldTerms := fieldTerms.toArray
      `(Noctium.Authoring.PrivateStateSchema.mk $(stringTerm schemaName) [$fieldTerms,*])
    elabCommand (← `(def $(mkIdent generatedSyntaxName) : Noctium.Authoring.PrivateStateSchema := $schemaTerm))
    modifyEnv fun env => noctiumPrivateStateRegistry.addEntry env
      {name := schemaName, fields := fields}
  | _ => throwUnsupportedSyntax

@[command_elab noctiumWitnessDeclarationCommand] unsafe def elabWitnessDeclaration : CommandElab := fun stx => do
  match stx with
  | `(noctium_witness $name:ident ($params:noctium_witness_parameter,*) : $result:noctium_witness_result) => do
    let fullName := ((← getCurrNamespace) ++ name.getId).toString
    let signatureName := fullName
    let operation := "noctium.witness." ++ fullName ++ ".v1"
    let capability := fullName
    validIdentity name signatureName
    validIdentity name operation
    validIdentity name capability
    let mut parameters : List WitnessParameter := []
    for parameterStx in params.getElems do
      match parameterStx with
      | `(noctium_witness_parameter| $parameter:ident : $type:nltype) => do
        let ty ← readScalarTy type
        parameters := parameters ++ [{name := parameter.getId.toString, type := .scalar ty}]
      | _ => throwErrorAt parameterStx "unsupported witness parameter"
    let parameterNames := parameters.map (·.name)
    unless uniqueStrings parameterNames do throwErrorAt name "duplicate witness parameter"
    let result ← match result with
      | `(noctium_witness_result| $unitType:ident) => do
        unless unitType.getId == `Unit do
          throwErrorAt unitType "only Unit or a supported scalar witness result is allowed"
        pure .unit
      | `(noctium_witness_result| $type:nltype) => .scalar <$> readScalarTy type
      | _ => throwErrorAt result "unsupported witness result"
    let signatureSpan ← spanValue name
    let signature : WitnessSignature :=
      { name := signatureName,
        operation := operation,
        capability := capability,
        parameters := parameters,
        result := result,
        span := signatureSpan }
    let generated := generatedName ((← getCurrNamespace) ++ name.getId) "__witnessSignature"
    let generatedSyntaxName := generatedName name.getId "__witnessSignature"
    if (← getEnv).contains generated then throwErrorAt name "witness signature already exists"
    let signatureTerm ← quoteSignature signature
    elabCommand (← `(def $(mkIdent generatedSyntaxName) : Noctium.Helpers.WitnessSignature := $signatureTerm))
    modifyEnv fun env => noctiumWitnessSignatureRegistry.addEntry env signature
  | _ => throwUnsupportedSyntax

private def collectExpressionMetadata (metadata : ObservationMetadata) (stx : TSyntax `nlexpr)
    (generated : List String) : ObservationMetadata :=
  { metadata with
    explicitReleases := (metadata.explicitReleases ++ disclosedValues stx).eraseDups,
    authoredProves := (metadata.authoredProves ++ inlineAssertions stx).eraseDups,
    generatedValidity := (metadata.generatedValidity ++ generated).eraseDups }

private def makeReadSignature (field : PrivateStateField) : WitnessSignature :=
  field.signature

@[command_elab noctiumAuthoredWitnessCircuitCommand] unsafe def elabAuthoredWitnessCircuit : CommandElab := fun stx => do
  match stx with
  | `(noctium_witness_circuit $name:ident $[using $usingCodecs:ident,*]?
      where $statements:noctium_witness_statement* end) => do
    let fullName := (← getCurrNamespace) ++ name.getId
    let programName := generatedName fullName "__program"
    let observationName := generatedName fullName "__observation"
    let programSyntaxName := generatedName name.getId "__program"
    let observationSyntaxName := generatedName name.getId "__observation"
    if (← getEnv).contains programName || (← getEnv).contains observationName then
      throwErrorAt name "generated readable witness program name already exists"
    let programNameText := fullName.toString
    validIdentity name programNameText
    let exportName := "noctium.witness-circuit." ++ programNameText ++ ".v1"
    validIdentity name exportName
    let codecNames := (usingCodecs.map (·.getElems)).getD #[]
    let mut codecs : List (Name × Helpers.Wire.Codec) := []
    let mut codecTerms : Array (TSyntax `term) := #[]
    for codecName in codecNames do
      if codecs.any (·.1 == codecName.getId) then
        throwErrorAt codecName "duplicate readable wire codec"
      let source ← liftCoreM <| resolveGlobalConstNoOverload codecName
      let codec ← evalConstCheck Helpers.Wire.Codec ``Helpers.Wire.Codec source
      codecs := codecs ++ [(codecName.getId, codec)]
      codecTerms := codecTerms.push ⟨mkIdent source⟩
    let composites := Helpers.Wire.compositeEnv {} (codecs.map (·.2))
    let exprState : AuthoringExprState := {codecs, composites}
    let mut env : SurfaceEnv := []
    let mut parameters : List Parameter := []
    let mut inputs : List Input := []
    let mut inputObservations : List ObservationInput := []
    let mut witnesses : List WitnessSignature := []
    let mut body : List Statement := []
    let mut privateReads : List String := []
    let mut privateStages : List String := []
    let mut witnessNames : List String := []
    let mut authoredProves : List String := []
    let mut explicitReleases : List String := []
    let mut generatedValidity : List String := []
    let mut outputName := ""
    let mut outputType : ResultType := .unit
    let mut sawOutput := _root_.Bool.false
    let mut authoredOutputs : List AuthoredOutput := []
    let mut logicalAliasBindings : List LogicalAliasBinding := []
    for (statement, ordinal) in statements.toList.zip (List.range statements.size) do
      let isOutput := statement.raw[0].getAtomVal == "output"
      if sawOutput && !isOutput then
        throwErrorAt statement "no statements may follow the circuit outputs"
      match statement with
      | `(noctium_witness_statement| public $id:ident : $type:nltype)
      | `(noctium_witness_statement| private $id:ident : $type:nltype) => do
        let valueName := id.getId.toString
        if env.any (fun value => value.1 == valueName) then throwErrorAt id s!"duplicate readable witness value '{valueName}'"
        let ty ← readScalarTy type
        let visibility := if statement.raw[0].getAtomVal == "public" then Noctium.Visibility.public else Noctium.Visibility.private
        let term := Noctium.Helpers.Term.ref valueName
        env := (valueName, .scalar ty, term) :: env
        parameters := parameters ++ [{name := valueName, ty}]
        inputs := inputs ++ [{name := valueName, ty, visibility, span := ← spanValue statement}]
        inputObservations := inputObservations ++ [{name := valueName, ty, visibility}]
      | `(noctium_witness_statement| read private $fieldPath:ident as $id:ident) => do
        let (schemaName, fieldName) ← splitSchemaField fieldPath
        let sourceField ← privateStateSchema schemaName fieldPath
        let some field := sourceField.fields.find? (·.name == fieldName)
          | throwErrorAt fieldPath "schema '{sourceField.name}' has no field '{fieldName}'"
        let valueName := id.getId.toString
        if env.any (fun value => value.1 == valueName) then throwErrorAt id s!"duplicate readable witness value '{valueName}'"
        let site := s!"{programNameText}.read.{ordinal}"
        validIdentity statement site
        let signature := makeReadSignature field
        witnesses := uniqueWitnesses (witnesses ++ [signature])
        let readTerm := Noctium.Helpers.Term.witnessCall site signature.name []
        body := body ++ [.bind valueName (.scalar field.ty) (.at (← spanValue statement) readTerm)]
        env := (valueName, .scalar field.ty, .ref valueName) :: env
        logicalAliasBindings := logicalAliasBindings ++ [
          {name := valueName, ty := field.ty, source := .call site}]
        privateReads := (privateReads ++ [field.key]).eraseDups
        generatedValidity := (generatedValidity ++ [s!"typed private-state read reply: {field.key}"]).eraseDups
      | `(noctium_witness_statement| witness $function:ident($args:nlexpr,*)) => do
        let callbackExpr ← `(nlexpr| witness $function($args,*))
        let lowered ← (lowerExpr programNameText s!"s{ordinal}" env callbackExpr).run' exprState
        let .unit := lowered.type | throwErrorAt statement "standalone witness statements must call a Unit witness"
        body := body ++ lowered.before ++ [.evaluate lowered.term]
        witnesses := uniqueWitnesses (witnesses ++ lowered.signatures)
        witnessNames := (witnessNames ++ lowered.witnessNames).eraseDups
        generatedValidity := (generatedValidity ++ lowered.generatedValidity).eraseDups
        for argument in args.getElems do
          let observationPart := collectExpressionMetadata {entryName := exportName} argument []
          authoredProves := (authoredProves ++ observationPart.authoredProves).eraseDups
          explicitReleases := (explicitReleases ++ observationPart.explicitReleases).eraseDups
      | `(noctium_witness_statement| let $id:ident $[: $type:nltype]? := $value:nlexpr) => do
        let valueName := id.getId.toString
        if env.any (fun value => value.1 == valueName) then throwErrorAt id s!"duplicate readable witness value '{valueName}'"
        let sourceExpr := value
        let lowered ← (lowerExpr programNameText s!"s{ordinal}" env sourceExpr).run' exprState
        let value ← match type with
          | some annotation => coerce sourceExpr lowered (← readScalarTy annotation)
          | none => do
            if lowered.type == .unit then throwErrorAt id "readable witness let cannot bind Unit"
            pure lowered
        body := body ++ value.before ++ [.bind valueName value.type (.at (← spanValue statement) value.term)]
        env := (valueName, value.type, .ref valueName) :: env
        if let .scalar ty := value.type then
          let aliasSource := match value.term with
            | .witnessCall site .. => LogicalAliasSource.call site
            | .at _ (.witnessCall site ..) => LogicalAliasSource.call site
            | _ => LogicalAliasSource.expression sourceExpr
          logicalAliasBindings := logicalAliasBindings ++ [
            {name := valueName, ty, source := aliasSource}]
        witnesses := uniqueWitnesses (witnesses ++ value.signatures)
        witnessNames := (witnessNames ++ value.witnessNames).eraseDups
        let observationPart := collectExpressionMetadata {entryName := exportName} sourceExpr value.generatedValidity
        authoredProves := (authoredProves ++ observationPart.authoredProves).eraseDups
        explicitReleases := (explicitReleases ++ observationPart.explicitReleases).eraseDups
        generatedValidity := (generatedValidity ++ observationPart.generatedValidity ++ value.witnessNames.map fun witnessName => s!"typed witness reply: {witnessName}").eraseDups
      | `(noctium_witness_statement| prove $predicate:nlexpr) => do
        let predicateStx := predicate
        let lowered ← (lowerExpr programNameText s!"s{ordinal}" env predicateStx).run'
          {exprState with allowAssertThen := _root_.Bool.true}
        let predicate ← coerce predicateStx lowered .bool
        body := body ++ predicate.before ++ [.assert (.at (← spanValue statement) predicate.term)]
        witnesses := uniqueWitnesses (witnesses ++ predicate.signatures)
        witnessNames := (witnessNames ++ predicate.witnessNames).eraseDups
        authoredProves := (authoredProves ++ [renderExpr predicateStx] ++ inlineAssertions predicateStx).eraseDups
        explicitReleases := (explicitReleases ++ disclosedValues predicateStx).eraseDups
        generatedValidity := (generatedValidity ++ predicate.generatedValidity ++ predicate.witnessNames.map fun witnessName => s!"typed witness reply: {witnessName}").eraseDups
      | `(noctium_witness_statement| stage $fieldPath:ident := $value:nlexpr) => do
        let (schemaName, fieldName) ← splitSchemaField fieldPath
        let sourceField ← privateStateSchema schemaName fieldPath
        let some field := sourceField.fields.find? (·.name == fieldName)
          | throwErrorAt fieldPath "schema '{sourceField.name}' has no field '{fieldName}'"
        let sourceExpr := value
        let lowered ← (lowerExpr programNameText s!"s{ordinal}" env sourceExpr).run' exprState
        let value ← coerce sourceExpr lowered field.ty
        body := body ++ value.before ++ [.stage field.capability field.key field.ty (.at (← spanValue statement) value.term)]
        witnesses := uniqueWitnesses (witnesses ++ value.signatures)
        witnessNames := (witnessNames ++ value.witnessNames).eraseDups
        privateStages := (privateStages ++ [field.key]).eraseDups
        let observationPart := collectExpressionMetadata {entryName := exportName} sourceExpr value.generatedValidity
        authoredProves := (authoredProves ++ observationPart.authoredProves).eraseDups
        explicitReleases := (explicitReleases ++ observationPart.explicitReleases).eraseDups
        generatedValidity := (generatedValidity ++ observationPart.generatedValidity ++ [s!"typed staged private-state value: {field.key}"] ++ value.witnessNames.map fun witnessName => s!"typed witness reply: {witnessName}").eraseDups
      | `(noctium_witness_statement| output $id:ident $[: $type:nltype]? := $value:nlexpr) => do
        let valueName := id.getId.toString
        if env.any (fun value => value.1 == valueName) || authoredOutputs.any (·.name == valueName) then
          throwErrorAt id s!"duplicate readable witness output '{valueName}'"
        let sourceExpr := value
        let lowered ← (lowerExpr programNameText s!"s{ordinal}" env sourceExpr).run' exprState
        let outputSpan ← spanValue statement
        let value ← match type with
          | some annotation => coerce sourceExpr lowered (← readScalarTy annotation)
          | none => do
            let .composite _ := lowered.type
              | throwErrorAt id "scalar outputs require a type annotation"
            pure lowered
        let source := match value.term with
          | .witnessCall site .. => LogicalAliasSource.call site
          | .at _ (.witnessCall site ..) => LogicalAliasSource.call site
          | _ => LogicalAliasSource.expression sourceExpr
        authoredOutputs := authoredOutputs ++ [{name := valueName, value, span := outputSpan, ordinal, source}]
        sawOutput := _root_.Bool.true
        witnesses := uniqueWitnesses (witnesses ++ value.signatures)
        witnessNames := (witnessNames ++ value.witnessNames).eraseDups
        let observationPart := collectExpressionMetadata {entryName := exportName} sourceExpr value.generatedValidity
        authoredProves := (authoredProves ++ observationPart.authoredProves).eraseDups
        explicitReleases := (explicitReleases ++ observationPart.explicitReleases).eraseDups
        generatedValidity := (generatedValidity ++ observationPart.generatedValidity ++ value.witnessNames.map fun witnessName => s!"typed witness reply: {witnessName}").eraseDups
      | _ => throwErrorAt statement "unsupported readable witness statement"
    let compositeId := programNameText ++ ".Output"
    let compositeType := Types.CompositeType.structure compositeId
    let grouped := authoredOutputs.length > 1
    let hasAggregate := authoredOutputs.any fun item =>
      match item.value.type with
      | .composite _ => _root_.Bool.true
      | _ => _root_.Bool.false
    let compositeFields : List Types.Field := authoredOutputs.map fun item =>
      {name := item.name, type := item.layoutType, span := item.span}
    let declarationSpan ← spanValue stx
    let compositeEnv : Types.CompositeEnv := if grouped then
      {structures := [{id := compositeId, fields := compositeFields, span := declarationSpan}]}
      else {}
    match authoredOutputs with
    | [] => body := body ++ [.return none]
    | [item] =>
      if let .scalar _ := item.value.type then outputName := item.name
      outputType := item.value.type
      body := body ++ item.value.before ++ [.return (some (.at item.span item.value.term))]
    | _ =>
      outputType := .composite compositeType
      let mut outputReferences := []
      for item in authoredOutputs do
        let bindingName := s!"__noctium_output_{item.ordinal}_{item.name}"
        if env.any (fun item => item.1 == bindingName) || authoredOutputs.any (·.name == bindingName) then
          throwErrorAt stx "generated composite output binding collides with a source name"
        body := body ++ item.value.before ++ [
          .bind bindingName item.value.type (.at item.span item.value.term)]
        let leaves : List Noctium.Helpers.Term ← match item.value.type with
          | .scalar (.bytes length) =>
            pure ((List.range length).map fun index => .cast .native (.bytesAt (.ref bindingName) index))
          | .composite payload => do
            let .ok layout := Types.compileType composites payload
              | throwErrorAt stx s!"invalid aggregate output layout for '{item.name}'"
            match Helpers.Iteration.flattenResult item.span item.value.type
                layout.checked.value (.ref bindingName) with
            | .ok leaves => pure leaves
            | .error diagnostic => throwErrorAt stx diagnostic.message
          | _ => pure [.ref bindingName]
        outputReferences := outputReferences ++ leaves
      body := body ++ [.return (some (.composite compositeType outputReferences))]
    let observation : ObservationMetadata := {
      entryName := exportName,
      inputs := inputObservations,
      privateReads := privateReads,
      privateStages := privateStages,
      witnessNames := witnessNames,
      authoredProves := authoredProves,
      explicitReleases := explicitReleases,
      generatedValidity := generatedValidity
    }
    let declId : DeclarationId := ⟨0, 0⟩
    let declaration : Noctium.Helpers.Declaration :=
      { id := declId,
        name := programNameText,
        parameters := parameters,
        result := outputType,
        body := body,
        span := declarationSpan }
    let exportSpan ← spanValue stx
    let entryExport : Export :=
      { name := exportName,
        target := declId,
        inputs := inputs,
        span := exportSpan }
    let program : Program := {
      declarations := [declaration], exports := [entryExport], composites := compositeEnv, witnesses := witnesses}
    let program ← match Helpers.Wire.attach program (codecs.map (·.2)) with
      | .ok value => pure value
      | .error message => throwErrorAt stx message
    let readTypes := (witnesses.filter (·.operation == "private_state.read.v1")).map (·.result)
    if let some expected := readTypes.head? then
      unless readTypes.all (· == expected) do
        throwErrorAt stx "readable witness circuits currently require private-state fields to share one result type"
    let compiled ← match Witness.compile program exportName programNameText with
      | .error diagnostic => throwErrorAt stx s!"readable witness compilation failed: {diagnostic.message}"
      | .ok compiled => pure compiled
    let mut logicalEnv : List (String × Ty × TSyntax `term) := []
    for input in inputs do
      let value ← `(@Noctium.Expr.ref $(← tyTerm input.ty) $(stringTerm input.name))
      logicalEnv := logicalEnv ++ [(input.name, input.ty, value)]
    let mut logicalOutputAliases : List (String × Ty × Name) := []
    let defineAlias (item : AuthoredOutput) (ty : Ty) (value : TSyntax `term) : CommandElabM Name := do
      let aliasName := generatedName fullName s!"__logicalOutput_{item.ordinal}_{item.name}"
      if (← getEnv).contains aliasName then
        throwErrorAt stx "generated logical output alias name already exists"
      elabCommand (← `(def $(mkIdent aliasName) : Noctium.Expr $(← tyTerm ty) := $value))
      pure aliasName
    for binding in (if grouped && !hasAggregate then logicalAliasBindings else []) do
      if logicalEnv.any (fun alias => alias.1 == binding.name) then
        throwErrorAt stx s!"duplicate logical output alias source '{binding.name}'"
      let value ← match binding.source with
        | .expression source =>
          Noctium.quoteSourceExpression logicalEnv source binding.ty
        | .call site => do
          let some call := compiled.calls.find? (·.site == site)
            | throwErrorAt stx s!"compiled witness call '{site}' is missing its result binding"
          unless call.result == .scalar binding.ty do
            throwErrorAt stx s!"witness call '{site}' does not produce a scalar logical alias"
          let some inputName := call.inputs.head?
            | throwErrorAt stx s!"witness call '{site}' has no scalar result binding"
          `(@Noctium.Expr.ref $(← tyTerm binding.ty) $(stringTerm inputName))
      logicalEnv := logicalEnv ++ [(binding.name, binding.ty, value)]
    if grouped && !hasAggregate then
      for item in authoredOutputs do
        let .scalar fieldType := item.value.type
          | throwErrorAt stx "expected a grouped scalar circuit output"
        let value ← match item.source with
          | .expression expression =>
            Noctium.quoteSourceExpression logicalEnv expression fieldType
          | .call site => do
            let some call := compiled.calls.find? (·.site == site)
              | throwErrorAt stx s!"compiled witness call '{site}' is missing its result binding"
            unless call.result == .scalar fieldType do
              throwErrorAt stx s!"witness call '{site}' does not produce a scalar logical output"
            let some inputName := call.inputs.head?
              | throwErrorAt stx s!"witness call '{site}' has no scalar result binding"
            `(@Noctium.Expr.ref $(← tyTerm fieldType) $(stringTerm inputName))
        let aliasName ← defineAlias item fieldType value
        logicalOutputAliases := logicalOutputAliases ++ [(item.name, fieldType, aliasName)]
    let signatureTerms ← witnesses.mapM quoteSignature
    let signatureTerms := signatureTerms.toArray
    let parameterTerms ← parameters.mapM fun parameter => do
      `( ({ name := $(stringTerm parameter.name), ty := $(← tyTerm parameter.ty) } : Noctium.Helpers.Parameter))
    let parameterTerms := parameterTerms.toArray
    let statementTerms ← body.mapM statementTerm
    let statementTerms := statementTerms.toArray
    let inputTerms ← inputs.mapM fun input => inputTerm input.name input.ty input.visibility input.span
    let inputTerms := inputTerms.toArray
    let declarationSpanTerm ← quoteSpan declaration.span
    let idTerm ← `(Noctium.Helpers.DeclarationId.mk 0 0)
    let declarationResultTerm ← resultTypeTerm declaration.result
    let compositeEnvTerm ← if grouped then do
      let fieldTerms ← compositeFields.mapM fun field => do
        let fieldType ← compositeTypeTerm field.type
        let fieldSpan ← quoteSpan field.span
        `(Noctium.Types.Field.mk $(stringTerm field.name)
          $fieldType $fieldSpan)
      let fieldTerms := fieldTerms.toArray
      let structureSpan ← quoteSpan declarationSpan
      let structureTerm ← `(Noctium.Types.StructDecl.mk $(stringTerm compositeId)
        [$fieldTerms,*] $structureSpan)
      `({ structures := [$structureTerm], enumerations := [] : Noctium.Types.CompositeEnv })
    else
      `({ : Noctium.Types.CompositeEnv })
    let declarationTerm ← `(Noctium.Helpers.Declaration.mk $idTerm $(stringTerm declaration.name)
      [$parameterTerms,*] [] $declarationResultTerm [$statementTerms,*] _root_.Bool.false $declarationSpanTerm)
    let exportSpanTerm ← quoteSpan entryExport.span
    let exportTerm ← `(Noctium.Helpers.Export.mk $(stringTerm entryExport.name) $idTerm
      [$inputTerms,*] [] $exportSpanTerm)
    let programTerm ← `({
      scopes := [{id := 0}]
      declarations := [$declarationTerm]
      exports := [$exportTerm]
      composites := $compositeEnvTerm
      witnesses := [$signatureTerms,*]
      : Noctium.Helpers.Program })
    let programTerm ← if codecTerms.isEmpty then pure programTerm else
      `(match Noctium.Helpers.Wire.attach $programTerm [$codecTerms,*] with
        | .ok program => program
        | .error _ => {})
    let metadataTerm ← observationTerm observation
    elabCommand (← `(def $(mkIdent programSyntaxName) : Noctium.Helpers.Program := $programTerm))
    elabCommand (← `(def $(mkIdent observationSyntaxName) : Noctium.Authoring.ObservationMetadata := $metadataTerm))
    let mut registeredAggregates := []
    if hasAggregate then
      let mut remaining := compiled.circuit.outputs.map (·.name)
      for item in authoredOutputs do
        let .ok layout := Types.compileType program.composites item.layoutType
          | throwErrorAt stx s!"invalid circuit output layout for '{item.name}'"
        let (fields, rest) := remaining.splitAt layout.checked.value.leafCount
        unless fields.length == layout.checked.value.leafCount do
          throwErrorAt stx "circuit output layout exceeds the compiled Native fields"
        remaining := rest
        match item.value.type with
        | .composite payload =>
          let suffix := if grouped then s!"__returnView_{item.ordinal}" else "__returnView"
          let localName := generatedName name.getId suffix
          let fullViewName := generatedName fullName suffix
          if (← getEnv).contains fullViewName then throwErrorAt name "aggregate return view already exists"
          let fieldTerms := (fields.map stringTerm).toArray
          let payload ← compositeTypeTerm payload
          elabCommand (← `(def $(mkIdent localName) : Noctium.ReturnView := {
            name := $(stringTerm item.name)
            environment := $(mkIdent programName).composites
            type := $payload
            fields := [$fieldTerms,*]
          }))
          registeredAggregates := registeredAggregates ++ [(item.name, fullViewName, fields)]
        | .scalar ty =>
          let value ← match ty with
            | .bytes _ => quoteByteLeaves fields
            | _ => do
              let [field] := fields | throwErrorAt stx "expected one Native field for a scalar output"
              let ref ← `(@Noctium.Expr.ref Noctium.Ty.native $(stringTerm field))
              if ty == .native then pure ref else `(Noctium.Expr.cast $(← tyTerm ty) $ref)
          let aliasName ← defineAlias item ty value
          logicalOutputAliases := logicalOutputAliases ++ [(item.name, ty, aliasName)]
        | .unit => throwErrorAt stx "unexpected Unit circuit output"
      unless remaining.isEmpty do
        throwErrorAt stx "circuit output layout did not consume the compiled Native fields"
    Noctium.registerWitnessCircuit name.raw programName exportName outputName
      (some observation.toJson.compress) logicalOutputAliases registeredAggregates
  | _ => throwUnsupportedSyntax

end Noctium
