import Noctium.Frontend.Core

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

declare_syntax_cat noctium_witness_statement
scoped syntax "public" ident ":" nltype : noctium_witness_statement
scoped syntax "private" ident ":" nltype : noctium_witness_statement
scoped syntax "let" ident ":" nltype ":=" nlexpr : noctium_witness_statement
scoped syntax "read" "private" ident "as" ident : noctium_witness_statement
scoped syntax "witness" ident "(" nlexpr,* ")" : noctium_witness_statement
scoped syntax "prove" nlexpr : noctium_witness_statement
scoped syntax "stage" ident ":=" nlexpr : noctium_witness_statement
scoped syntax "output" ident ":" nltype ":=" nlexpr : noctium_witness_statement
scoped syntax (name := noctiumAuthoredWitnessCircuitCommand) "noctium_witness_circuit" ident
  "where" noctium_witness_statement* "end" : command

private abbrev SurfaceEnv := List (String × ResultType × Noctium.Helpers.Term)

private structure Lowered where
  type : ResultType
  term : Noctium.Helpers.Term
  before : List Statement := []
  signatures : List WitnessSignature := []
  witnessNames : List String := []
  generatedValidity : List String := []

private structure AuthoringExprState where
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

private abbrev ExprM := StateT AuthoringExprState CommandElabM

private def stringTerm (value : String) : TSyntax `term := ⟨Syntax.mkStrLit value⟩
private def natTerm (value : Nat) : TSyntax `term := ⟨Syntax.mkNumLit (toString value)⟩

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
  | `(nltype| JubjubScalar) => pure .jubjubScalar
  | `(nltype| JubjubPoint) => pure .jubjubPoint
  | _ => throwErrorAt stx "unsupported readable witness scalar type"

private def tyTerm : Ty → CommandElabM (TSyntax `term)
  | .native => `(Noctium.Ty.native)
  | .bool => `(Noctium.Ty.bool)
  | .uint maximum => `(Noctium.Ty.uint $(natTerm maximum))
  | .bytes length => `(Noctium.Ty.bytes $(natTerm length))
  | .jubjubScalar => `(Noctium.Ty.jubjubScalar)
  | .jubjubPoint => `(Noctium.Ty.jubjubPoint)

private def resultTypeTerm : ResultType → CommandElabM (TSyntax `term)
  | .unit => `(Noctium.Helpers.ResultType.unit)
  | .scalar ty => do `(Noctium.Helpers.ResultType.scalar $(← tyTerm ty))
  | .composite (.structure id) =>
    `(Noctium.Helpers.ResultType.composite (Noctium.Types.CompositeType.structure $(stringTerm id)))
  | .composite _ => throwError "readable witness source supports only synthesized record results"

private def compositeTypeTerm : Types.CompositeType → CommandElabM (TSyntax `term)
  | .structure id => `(Noctium.Types.CompositeType.structure $(stringTerm id))
  | _ => throwError "readable witness source supports only synthesized record types"

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
  | `(nltype| JubjubScalar) => "JubjubScalar"
  | `(nltype| JubjubPoint) => "JubjubPoint"
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
  | `(nlexpr| eq($left, $right)) => s!"eq({renderExpr left}, {renderExpr right})"
  | `(nlexpr| select($condition, $yes, $no)) =>
    s!"select({renderExpr condition}, {renderExpr yes}, {renderExpr no})"
  | `(nlexpr| poseidon2($domain:num, $left, $right)) =>
    s!"poseidon2({domain.getNat}, {renderExpr left}, {renderExpr right})"
  | `(nlexpr| persistentHash32($value)) => s!"persistentHash32({renderExpr value})"
  | `(nlexpr| bytes32($literal:str)) => s!"bytes32({(toJson literal.getString).compress})"
  | `(nlexpr| persistentHashVector32([$values,*])) =>
    s!"persistentHashVector32([{String.intercalate ", " (values.getElems.toList.map renderExpr)}])"
  | `(nlexpr| persistentHashNative($value)) => s!"persistentHashNative({renderExpr value})"
  | `(nlexpr| persistentHashNativeVector([$values,*])) =>
    s!"persistentHashNativeVector([{String.intercalate ", " (values.getElems.toList.map renderExpr)}])"
  | `(nlexpr| persistentHashPoint($point)) => s!"persistentHashPoint({renderExpr point})"
  | `(nlexpr| reverseBytes32($value)) => s!"reverseBytes32({renderExpr value})"
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
  | `(nlexpr| witness $function:ident($args:nlexpr,*)) =>
    s!"witness {function.getId}({String.intercalate ", " (args.getElems.toList.map renderExpr)})"
  | _ => "<unsupported-expression>"

private partial def disclosedValues (stx : TSyntax `nlexpr) : List String :=
  match stx with
  | `(nlexpr| disclose($value)) => renderExpr value :: disclosedValues value
  | `(nlexpr| let $_:ident := $value:nlexpr in $body:nlexpr) => disclosedValues value ++ disclosedValues body
  | `(nlexpr| assertThen($condition, $body)) => disclosedValues condition ++ disclosedValues body
  | `(nlexpr| add($left, $right)) | `(nlexpr| sub($left, $right))
  | `(nlexpr| mul($left, $right)) | `(nlexpr| eq($left, $right)) =>
    disclosedValues left ++ disclosedValues right
  | `(nlexpr| cast($_:nltype, $value:nlexpr)) => disclosedValues value
  | `(nlexpr| select($condition, $yes, $no)) =>
    disclosedValues condition ++ disclosedValues yes ++ disclosedValues no
  | `(nlexpr| poseidon2($_:num, $left, $right)) => disclosedValues left ++ disclosedValues right
  | `(nlexpr| persistentHash32($value)) | `(nlexpr| persistentHashNative($value))
  | `(nlexpr| persistentHashPoint($value)) | `(nlexpr| degradeToNative($value))
  | `(nlexpr| toBytes32($value)) | `(nlexpr| reverseBytes32($value)) => disclosedValues value
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
  | `(nlexpr| witness $_:ident($args:nlexpr,*)) => args.getElems.toList.flatMap disclosedValues
  | _ => []

private partial def inlineAssertions (stx : TSyntax `nlexpr) : List String :=
  match stx with
  | `(nlexpr| assertThen($condition, $body)) =>
    renderExpr condition :: (inlineAssertions condition ++ inlineAssertions body)
  | `(nlexpr| let $_:ident := $value:nlexpr in $body:nlexpr) =>
    inlineAssertions value ++ inlineAssertions body
  | `(nlexpr| add($left, $right)) | `(nlexpr| sub($left, $right))
  | `(nlexpr| mul($left, $right)) | `(nlexpr| eq($left, $right)) =>
    inlineAssertions left ++ inlineAssertions right
  | `(nlexpr| cast($_:nltype, $value:nlexpr)) | `(nlexpr| disclose($value)) => inlineAssertions value
  | `(nlexpr| select($condition, $yes, $no)) =>
    inlineAssertions condition ++ inlineAssertions yes ++ inlineAssertions no
  | `(nlexpr| poseidon2($_:num, $left, $right)) => inlineAssertions left ++ inlineAssertions right
  | `(nlexpr| persistentHash32($value)) | `(nlexpr| persistentHashNative($value))
  | `(nlexpr| persistentHashPoint($value)) | `(nlexpr| degradeToNative($value))
  | `(nlexpr| toBytes32($value)) | `(nlexpr| reverseBytes32($value)) => inlineAssertions value
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
    let .scalar ty := value.type | throwErrorAt id "readable witness let cannot bind Unit"
    let localIndex ← get
    modify fun state => {state with nextLet := state.nextLet + 1}
    let internalName := s!"__noctium_let_{localIndex.nextLet}_{id.getId}"
    let ref := Noctium.Helpers.Term.ref internalName
    let body ← lowerExpr programName callPrefix ((id.getId.toString, .scalar ty, ref) :: env) body
    pure
      { body with
        before := value.before ++ [.bind internalName (.scalar ty) value.term] ++ body.before,
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
  | `(nlexpr| bytes32($literal:str)) => do
    let bytes := literal.getString.toUTF8.data.toList.map UInt8.toNat
    if bytes.length > 32 then throwErrorAt stx "Bytes32 string literal exceeds 32 UTF-8 bytes"
    pure {type := .scalar (.bytes 32), term := .bytes32Literal (bytes ++ List.replicate (32 - bytes.length) 0)}
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
  | `(nlexpr| reverseBytes32($value)) =>
    lowerBytesOperation programName callPrefix env stx .reverseBytes32 [value]
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
  | `(nlexpr| witness $function:ident($args:nlexpr,*)) => do
    let signature ← liftM (witnessSignature function)
    let signatureName := signature.name
    validIdentity function signatureName
    unless signature.parameters.all (fun p => match p.type with
      | .scalar ty => !ty.isBytes || ty == .bytes 32
      | _ => _root_.Bool.false) do
      throwErrorAt function "witness callback parameters must use supported scalar types"
    let supportedResult : _root_.Bool := match signature.result with
      | .scalar ty => !ty.isBytes || ty == .bytes 32
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
      let .scalar actualType := value.type | throwErrorAt stx "Bytes32 operation argument cannot be Unit"
      unless actualType == expectedType do
        throwErrorAt stx s!"{operation.operationName} argument type mismatch"
    let term := Noctium.Helpers.Term.bytes operation (values.map (·.term))
    pure (mergeLowered (.scalar result) term values)

  lowerCurve (programName callPrefix : String) (env : SurfaceEnv) (stx : Syntax)
      (operation : Noctium.Helpers.CurveOp) (arguments : List (TSyntax `nlexpr)) : ExprM Lowered := do
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
  | .eq left right => do `(Noctium.Helpers.Term.eq $(← termTerm left) $(← termTerm right))
  | .cast ty value => do `(Noctium.Helpers.Term.cast $(← tyTerm ty) $(← termTerm value))
  | .disclose span value => do
    let span ← quoteSpan span
    `(Noctium.Helpers.Term.disclose $span $(← termTerm value))
  | .select condition yes no => do
    `(Noctium.Helpers.Term.select $(← termTerm condition) $(← termTerm yes) $(← termTerm no))
  | .witnessCall site name args => do
    let args ← args.mapM termTerm
    let args := args.toArray
    `(Noctium.Helpers.Term.witnessCall $(stringTerm site) $(stringTerm name) [$args,*])
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
      | .reverseBytes32 => `(Noctium.Helpers.BytesOp.reverseBytes32)
      | .degradeToNative => `(Noctium.Helpers.BytesOp.degradeToNative)
      | .toBytes32 source => `(Noctium.Helpers.BytesOp.toBytes32 $(← tyTerm source))
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
  | .branch .. => throwError "readable witness source does not support branch statements yet"

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
  | `(noctium_witness_circuit $name:ident where $statements:noctium_witness_statement* end) => do
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
    let mut authoredOutputs : List
        (String × Ty × Lowered × SourceSpan × Nat × LogicalAliasSource) := []
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
        let lowered ← (lowerExpr programNameText s!"s{ordinal}" env callbackExpr).run' {}
        let .unit := lowered.type | throwErrorAt statement "standalone witness statements must call a Unit witness"
        body := body ++ lowered.before ++ [.evaluate lowered.term]
        witnesses := uniqueWitnesses (witnesses ++ lowered.signatures)
        witnessNames := (witnessNames ++ lowered.witnessNames).eraseDups
        generatedValidity := (generatedValidity ++ lowered.generatedValidity).eraseDups
        for argument in args.getElems do
          let observationPart := collectExpressionMetadata {entryName := exportName} argument []
          authoredProves := (authoredProves ++ observationPart.authoredProves).eraseDups
          explicitReleases := (explicitReleases ++ observationPart.explicitReleases).eraseDups
      | `(noctium_witness_statement| let $id:ident : $type:nltype := $value:nlexpr) => do
        let valueName := id.getId.toString
        if env.any (fun value => value.1 == valueName) then throwErrorAt id s!"duplicate readable witness value '{valueName}'"
        let ty ← readScalarTy type
        let sourceExpr := value
        let lowered ← (lowerExpr programNameText s!"s{ordinal}" env sourceExpr).run' {}
        let value ← coerce sourceExpr lowered ty
        body := body ++ value.before ++ [.bind valueName (.scalar ty) (.at (← spanValue statement) value.term)]
        env := (valueName, .scalar ty, .ref valueName) :: env
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
        let lowered ← (lowerExpr programNameText s!"s{ordinal}" env predicateStx).run' {allowAssertThen := _root_.Bool.true}
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
        let lowered ← (lowerExpr programNameText s!"s{ordinal}" env sourceExpr).run' {}
        let value ← coerce sourceExpr lowered field.ty
        body := body ++ value.before ++ [.stage field.capability field.key field.ty (.at (← spanValue statement) value.term)]
        witnesses := uniqueWitnesses (witnesses ++ value.signatures)
        witnessNames := (witnessNames ++ value.witnessNames).eraseDups
        privateStages := (privateStages ++ [field.key]).eraseDups
        let observationPart := collectExpressionMetadata {entryName := exportName} sourceExpr value.generatedValidity
        authoredProves := (authoredProves ++ observationPart.authoredProves).eraseDups
        explicitReleases := (explicitReleases ++ observationPart.explicitReleases).eraseDups
        generatedValidity := (generatedValidity ++ observationPart.generatedValidity ++ [s!"typed staged private-state value: {field.key}"] ++ value.witnessNames.map fun witnessName => s!"typed witness reply: {witnessName}").eraseDups
      | `(noctium_witness_statement| output $id:ident : $type:nltype := $value:nlexpr) => do
        let valueName := id.getId.toString
        if env.any (fun value => value.1 == valueName) || authoredOutputs.any (fun prior => prior.1 == valueName) then
          throwErrorAt id s!"duplicate readable witness output '{valueName}'"
        let ty ← readScalarTy type
        let sourceExpr := value
        let lowered ← (lowerExpr programNameText s!"s{ordinal}" env sourceExpr).run' {}
        let value ← coerce sourceExpr lowered ty
        let outputSpan ← spanValue statement
        let aliasSource := match value.term with
          | .witnessCall site .. => LogicalAliasSource.call site
          | .at _ (.witnessCall site ..) => LogicalAliasSource.call site
          | _ => LogicalAliasSource.expression sourceExpr
        authoredOutputs := authoredOutputs ++ [
          (valueName, ty, value, outputSpan, ordinal, aliasSource)]
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
    let compositeFields := authoredOutputs.map fun (fieldName, fieldType, _, fieldSpan, _, _) =>
      {name := fieldName,
        type := match fieldType with
          | .bytes length => Types.CompositeType.bytes length
          | _ => Types.CompositeType.scalar fieldType,
        span := fieldSpan : Types.Field}
    let declarationSpan ← spanValue stx
    let compositeEnv : Types.CompositeEnv := if authoredOutputs.length > 1 then
      {structures := [{id := compositeId, fields := compositeFields, span := declarationSpan}]}
      else {}
    if authoredOutputs.isEmpty then
      body := body ++ [.return none]
      outputType := .unit
    else if authoredOutputs.length == 1 then
      let some (fieldName, fieldType, fieldValue, fieldSpan, _, _) := authoredOutputs.head?
        | throwErrorAt stx "readable witness output collection failed"
      outputName := fieldName
      outputType := .scalar fieldType
      body := body ++ fieldValue.before ++ [.return (some (.at fieldSpan fieldValue.term))]
    else
      outputName := ""
      outputType := .composite compositeType
      let mut outputReferences := []
      for (fieldName, fieldType, fieldValue, fieldSpan, ordinal, _) in authoredOutputs do
        let bindingName := s!"__noctium_output_{ordinal}_{fieldName}"
        if env.any (fun item => item.1 == bindingName) || authoredOutputs.any (fun item => item.1 == bindingName) then
          throwErrorAt stx "generated composite output binding collides with a source name"
        body := body ++ fieldValue.before ++ [
          .bind bindingName (.scalar fieldType) (.at fieldSpan fieldValue.term)]
        match fieldType with
        | .bytes length =>
          outputReferences := outputReferences ++ (List.range length).map fun index =>
            .cast .native (.bytesAt (.ref bindingName) index)
        | _ => outputReferences := outputReferences ++ [.ref bindingName]
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
    for binding in logicalAliasBindings do
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
    if authoredOutputs.length > 1 then
      for (fieldName, fieldType, _, fieldSpan, ordinal, source) in authoredOutputs do
        let value ← match source with
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
        let aliasName := generatedName fullName s!"__logicalOutput_{ordinal}_{fieldName}"
        if (← getEnv).contains aliasName then
          throwErrorAt stx "generated logical output alias name already exists"
        elabCommand (← `(def $(mkIdent aliasName) : Noctium.Expr $(← tyTerm fieldType) := $value))
        logicalOutputAliases := logicalOutputAliases ++ [(fieldName, fieldType, aliasName)]
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
    let compositeEnvTerm ← if authoredOutputs.length > 1 then do
      let fieldTerms ← compositeFields.mapM fun field => do
        let fieldType ← match field.type with
          | .scalar ty => `(Noctium.Types.CompositeType.scalar $(← tyTerm ty))
          | .bytes length => `(Noctium.Types.CompositeType.bytes $(natTerm length))
          | _ => throwErrorAt stx "readable witness record outputs require scalar or Bytes32 fields"
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
    let programTerm ← `(Noctium.Helpers.Program.mk [{id := 0}] [$declarationTerm]
      [$exportTerm] $compositeEnvTerm [$signatureTerms,*])
    let metadataTerm ← observationTerm observation
    elabCommand (← `(def $(mkIdent programSyntaxName) : Noctium.Helpers.Program := $programTerm))
    elabCommand (← `(def $(mkIdent observationSyntaxName) : Noctium.Authoring.ObservationMetadata := $metadataTerm))
    Noctium.registerWitnessCircuit name.raw programName exportName outputName
      (some observation.toJson.compress) logicalOutputAliases
  | _ => throwUnsupportedSyntax

end Noctium
