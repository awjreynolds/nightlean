import Noctium.Disclosure
import Noctium.Helpers
import Noctium.Helpers.Specialization
import Noctium.ComponentDisclosure
import Noctium.Control
import Noctium.Witness
import Noctium.Modules
import Noctium.Crypto.Signatures
import Noctium.Backend.Impact
import Lean

namespace Noctium
open Lean Elab Command

/-- Declarations registered through the supported Noctium circuit surface. -/
structure CircuitInfo where
  declName : Name
  inputs : List (String × Ty)
  publicInputs : List (String × Ty)
  outputs : List (String × Ty)
  /-- Logical witness-circuit results retained when a grouped helper result is
  expanded into native leaves. The names point to typed Expr constants. -/
  logicalOutputs : List (String × Ty × Name) := []
  sourceProgram? : Option (Name × String) := none
  /-- Structured ledger bodies are rebuilt from their typed source at export. -/
  stateProgram? : Option (Name × String) := none
  specializationArtifact? : Option String := none
  deriving Inhabited

initialize circuitRegistry : SimplePersistentEnvExtension CircuitInfo (Array CircuitInfo) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }
initialize contractRegistry : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }

initialize controlRegistry : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }

structure WitnessInfo where
  circuitName : Name
  sourceName : Name
  exportName : String
  outputName : String := ""
  observationArtifact? : Option String := none
  deriving Inhabited

/-- Exact source constants registered as Noctium module definitions. -/
structure ModuleSourceInfo where
  sourceName : Name
  definitionName : Name
  deriving Inhabited

/-- A module contract declaration retains only source roots. Compiler checks
re-expand these roots and rebuild their concrete circuits for each invocation. -/
structure ModuleBuildInfo where
  contractName : Name
  requestName : Name
  deriving Inhabited

structure ModuleCircuitBuildInfo where
  source : Modules.ModuleCircuitSource
  declarationName : Name
  programName : Name
  program : Helpers.Program
  circuit : Circuit
  signatureArtifact : Helpers.Specialization.SignatureArtifact

structure ModuleBuildOutput where
  specialized : Modules.SpecializedModule
  contract : Contract
  programs : List (Name × Name × Helpers.Program)
  circuits : List ModuleCircuitBuildInfo

initialize witnessRegistry : SimplePersistentEnvExtension WitnessInfo (Array WitnessInfo) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }

initialize moduleSourceRegistry : SimplePersistentEnvExtension ModuleSourceInfo (Array ModuleSourceInfo) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }

initialize moduleBuildRegistry : SimplePersistentEnvExtension ModuleBuildInfo (Array ModuleBuildInfo) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }

declare_syntax_cat nltype
scoped syntax "Native" : nltype
scoped syntax "Bool" : nltype
scoped syntax "UInt" num : nltype
scoped syntax "UIntRange" num : nltype
scoped syntax "Bytes32" : nltype
scoped syntax "Bytes" num : nltype
scoped syntax "JubjubScalar" : nltype
scoped syntax "JubjubPoint" : nltype
scoped syntax "Secp256k1Base" : nltype
scoped syntax "Secp256k1Scalar" : nltype
scoped syntax "Secp256k1Point" : nltype
scoped syntax "Secp256r1Base" : nltype
scoped syntax "Secp256r1Scalar" : nltype
scoped syntax "Secp256r1Point" : nltype
scoped syntax "Curve25519Base" : nltype
scoped syntax "Curve25519Scalar" : nltype
scoped syntax "Curve25519Point" : nltype

declare_syntax_cat nlexpr
scoped syntax ident : nlexpr
scoped syntax num : nlexpr
scoped syntax "true" : nlexpr
scoped syntax "false" : nlexpr
scoped syntax "let" ident ":=" nlexpr "in" nlexpr : nlexpr
scoped syntax "assertThen(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "add(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "mul(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "sub(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "inv(" nlexpr ")" : nlexpr
scoped syntax "copyValue(" nlexpr ")" : nlexpr
scoped syntax "uint(" num ")" : nlexpr
scoped syntax "cast(" nltype "," nlexpr ")" : nlexpr
scoped syntax "default(" nltype ")" : nlexpr
scoped syntax "disclose(" nlexpr ")" : nlexpr
scoped syntax "boolAnd(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "boolOr(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "boolXor(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "eq(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "select(" nlexpr "," nlexpr "," nlexpr ")" : nlexpr
scoped syntax "poseidon2(" num "," nlexpr "," nlexpr ")" : nlexpr
scoped syntax "persistentHash32(" nlexpr ")" : nlexpr
scoped syntax "sha512(" nlexpr ")" : nlexpr
scoped syntax "keccak256(" nlexpr ")" : nlexpr
scoped syntax "secp256k1EcdsaVerify(" nlexpr "," nlexpr "," nlexpr "," nlexpr ")" : nlexpr
scoped syntax "secp256r1EcdsaVerify(" nlexpr "," nlexpr "," nlexpr "," nlexpr ")" : nlexpr
scoped syntax "jubjubSchnorrVerify(" "[" nlexpr,* "]" "," nlexpr "," nlexpr "," nlexpr ")" : nlexpr
scoped syntax "ed25519Verify(" nlexpr "," nlexpr "," nlexpr "," nlexpr ")" : nlexpr
scoped syntax "secp256k1EthereumAddress(" nlexpr ")" : nlexpr
scoped syntax "reverseBytes32(" nlexpr ")" : nlexpr
scoped syntax "bytes(" num "," str ")" : nlexpr
scoped syntax "reverseBytes(" nlexpr ")" : nlexpr
scoped syntax "sliceBytes(" nlexpr "," num "," num ")" : nlexpr
scoped syntax "concatBytes(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "bytes32(" str ")" : nlexpr
scoped syntax "persistentHashVector32(" "[" nlexpr,* "]" ")" : nlexpr
scoped syntax "persistentHashNative(" nlexpr ")" : nlexpr
scoped syntax "persistentHashNativeVector(" "[" nlexpr,* "]" ")" : nlexpr
scoped syntax "transientHashNativeVector(" "[" nlexpr,* "]" ")" : nlexpr
scoped syntax "persistentHashPoint(" nlexpr ")" : nlexpr
scoped syntax "hashToCurve(" "[" nlexpr,* "]" ")" : nlexpr
scoped syntax "toBytes32(" nlexpr ")" : nlexpr
scoped syntax "fromBytes32(" nltype "," nlexpr ")" : nlexpr
scoped syntax "fromBytes(" nltype "," nlexpr ")" : nlexpr
scoped syntax "byteAt(" nlexpr "," num ")" : nlexpr
scoped syntax "degradeToNative(" nlexpr ")" : nlexpr
scoped syntax "jubjubScalarFromNative(" nlexpr ")" : nlexpr
scoped syntax "jubjubScalarToNative(" nlexpr ")" : nlexpr
scoped syntax "jubjubMulGenerator(" nlexpr ")" : nlexpr
scoped syntax "jubjubMul(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "jubjubAdd(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "jubjubNeg(" nlexpr ")" : nlexpr
scoped syntax "jubjubX(" nlexpr ")" : nlexpr
scoped syntax "jubjubY(" nlexpr ")" : nlexpr
scoped syntax "jubjubFromCoordinates(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "secp256k1Base(" num ")" : nlexpr
scoped syntax "secp256k1Scalar(" num ")" : nlexpr
scoped syntax "secp256k1Identity()" : nlexpr
scoped syntax "secp256r1Base(" num ")" : nlexpr
scoped syntax "secp256r1Scalar(" num ")" : nlexpr
scoped syntax "secp256r1Identity()" : nlexpr
scoped syntax "curve25519Base(" num ")" : nlexpr
scoped syntax "curve25519Scalar(" num ")" : nlexpr
scoped syntax "curve25519Identity()" : nlexpr
scoped syntax "foreignAdd(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "foreignSub(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "foreignMul(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "foreignNeg(" nlexpr ")" : nlexpr
scoped syntax "foreignInv(" nlexpr ")" : nlexpr
scoped syntax "curveMul(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "curveMulGenerator(" nlexpr ")" : nlexpr
scoped syntax "curveX(" nlexpr ")" : nlexpr
scoped syntax "curveY(" nlexpr ")" : nlexpr
scoped syntax "curveFromCoordinates(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "foreignToBytes(" nlexpr ")" : nlexpr
scoped syntax "foreignFromBytes(" nltype "," nlexpr ")" : nlexpr

declare_syntax_cat nlcstmt
scoped syntax "public" ident ":" nltype : nlcstmt
scoped syntax "private" ident ":" nltype : nlcstmt
scoped syntax "let" ident ":" nltype ":=" nlexpr : nlcstmt
scoped syntax "assert" nlexpr : nlcstmt
scoped syntax "output" ident ":" nltype ":=" nlexpr : nlcstmt
scoped syntax (name := circuitCommand) "noctium_circuit" ident "where" nlcstmt* "end" : command

declare_syntax_cat nlstate
scoped syntax "cell" ident ":" nltype : nlstate
scoped syntax "sealed" "cell" ident ":" nltype : nlstate
scoped syntax "sealed" "cell" ident ":" "OpaqueString" : nlstate
declare_syntax_cat nlconstructorparam
scoped syntax ident ":" nltype : nlconstructorparam
scoped syntax ident ":" "OpaqueString" : nlconstructorparam
declare_syntax_cat nlconstructorinit
scoped syntax "initialize" ident ":=" nlexpr : nlconstructorinit
scoped syntax "initialize" ident ":=" str : nlconstructorinit
scoped syntax "constructor" "(" nlconstructorparam,* ")" "where" nlconstructorinit* "end" : nlstate
scoped syntax "map" ident ":" nltype "=>" nltype : nlstate
scoped syntax "counter" ident : nlstate
declare_syntax_cat nlcompositefield
scoped syntax ident ":" nltype : nlcompositefield
scoped syntax "tree" ident ":" nltype "=>" "struct" ident "{" nlcompositefield* "}" : nlstate
scoped syntax "tree" ident ":" nltype "=>" nltype "=>" "struct" ident "{" nlcompositefield* "}" : nlstate
scoped syntax ident ident ":" "struct" ident "{" nlcompositefield* "}" : nlstate
scoped syntax "tree" ident ":" nltype "=>" ident "struct" ident "{" nlcompositefield* "}" : nlstate
scoped syntax "tree" ident ":" nltype "=>" nltype "=>" ident "struct" ident "{" nlcompositefield* "}" : nlstate
scoped syntax "tree" ident ":" nltype "=>" nltype "=>" "Counter" : nlstate
scoped syntax "tree" ident ":" nltype "=>" "Counter" : nlstate
scoped syntax "tree" ident ":" nltype "=>" nltype "=>" nltype : nlstate

declare_syntax_cat nlleaves
scoped syntax "fields(" nlexpr,* ")" : nlleaves

declare_syntax_cat nlpath
scoped syntax ident : nlpath
scoped syntax nlpath "[" nlexpr "]" : nlpath

declare_syntax_cat nlupdate
scoped syntax "claimContractCall" "(" nlexpr "," nlexpr "," nlexpr ")" : nlupdate

declare_syntax_cat nleffect
scoped syntax nlupdate : nleffect
scoped syntax "when" nlexpr nlupdate : nleffect
scoped syntax "read" nlpath "as" ident : nleffect
scoped syntax "member" nlpath "as" ident : nleffect
scoped syntax ident nlpath "as" ident : nleffect
scoped syntax "increment" ident "by" num : nleffect
scoped syntax "increment" ident "[" nlexpr "]" "by" num : nleffect
scoped syntax "increment" ident "[" nlexpr "]" "[" nlexpr "]" "by" num : nleffect
scoped syntax "decrement" ident "by" num : nleffect
scoped syntax "decrement" ident "[" nlexpr "]" "by" num : nleffect
scoped syntax "decrement" ident "[" nlexpr "]" "[" nlexpr "]" "by" num : nleffect
scoped syntax "reset" nlpath : nleffect
scoped syntax "require" nlexpr : nleffect
scoped syntax "absent" ident "[" nlexpr "]" : nleffect
scoped syntax "write" ident ":=" nlexpr : nleffect
scoped syntax "insert" ident "[" nlexpr "]" ":=" nlexpr : nleffect
scoped syntax "insert" ident "[" nlexpr "]" ":=" "emptyMap" : nleffect
scoped syntax "insert" ident "[" nlexpr "]" "[" nlexpr "]" ":=" nlexpr : nleffect
scoped syntax "write" ident "[" nlexpr "]" "[" nlexpr "]" ":=" nlexpr : nleffect
scoped syntax "insert" ident "[" nlexpr "]" ":=" nlleaves : nleffect
scoped syntax "write" ident "[" nlexpr "]" ":=" nlleaves : nleffect
scoped syntax "insert" ident "[" nlexpr "]" "[" nlexpr "]" ":=" nlleaves : nleffect
scoped syntax "write" ident "[" nlexpr "]" "[" nlexpr "]" ":=" nlleaves : nleffect
scoped syntax "pushFront" nlpath ":=" nlleaves : nleffect
scoped syntax "popFront" nlpath : nleffect
scoped syntax "remove" nlpath : nleffect
scoped syntax "when" nlexpr "write" ident ":=" nlexpr : nleffect
scoped syntax "when" nlexpr "insert" ident "[" nlexpr "]" ":=" nlexpr : nleffect
scoped syntax "when" nlexpr "require" nlexpr : nleffect
scoped syntax "when" nlexpr "read" nlpath "as" ident : nleffect
scoped syntax "when" nlexpr "member" nlpath "as" ident : nleffect
scoped syntax "when" nlexpr ident nlpath "as" ident : nleffect
scoped syntax "when" nlexpr "increment" ident "by" num : nleffect
scoped syntax "when" nlexpr "increment" ident "[" nlexpr "]" "by" num : nleffect
scoped syntax "when" nlexpr "increment" ident "[" nlexpr "]" "[" nlexpr "]" "by" num : nleffect
scoped syntax "when" nlexpr "decrement" ident "by" num : nleffect
scoped syntax "when" nlexpr "decrement" ident "[" nlexpr "]" "by" num : nleffect
scoped syntax "when" nlexpr "decrement" ident "[" nlexpr "]" "[" nlexpr "]" "by" num : nleffect
scoped syntax "when" nlexpr "reset" nlpath : nleffect
scoped syntax "when" nlexpr "pushFront" nlpath ":=" nlleaves : nleffect
scoped syntax "when" nlexpr "popFront" nlpath : nleffect
scoped syntax "when" nlexpr "remove" nlpath : nleffect

declare_syntax_cat nlstatement
scoped syntax nleffect : nlstatement
scoped syntax "if" nlexpr "then" "{" nlstatement* "}" "else" "{" nlstatement* "}" : nlstatement

declare_syntax_cat nlreturn
scoped syntax "return" ident ":" nltype ":=" nlexpr : nlreturn

declare_syntax_cat nlentry
scoped syntax "entry" ident "uses" ident "where" nlstatement* nlreturn* "end" : nlentry
scoped syntax "entry" ident "uses" ident ident "[" ident,* "]" "where" nlstatement* nlreturn* "end" : nlentry
scoped syntax "entry" ident "from" ident "entry" str "end" : nlentry
scoped syntax (name := contractCommand) "noctium_contract" ident "where" nlstate* nlentry* "end" : command

open scoped Noctium

private def readTy (stx : TSyntax `nltype) : CommandElabM Ty :=
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
    if length.getNat > Noctium.maxBytesLength then
      throwErrorAt length s!"byte string length exceeds the maximum of {Noctium.maxBytesLength}"
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
  | _ => throwErrorAt stx "unsupported Noctium type"

private def tyTerm : Ty → CommandElabM (TSyntax `term)
  | .native => `(Noctium.Ty.native)
  | .bool => `(Noctium.Ty.bool)
  | .uint maximum => `(Noctium.Ty.uint $(⟨Syntax.mkNumLit (toString maximum)⟩))
  | .bytes len => `(Noctium.Ty.bytes $(⟨Syntax.mkNumLit (toString len)⟩))
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

private def foreignCurveTerm : Foreign.Curve → CommandElabM (TSyntax `term)
  | .secp256k1 => `(Noctium.Foreign.Curve.secp256k1)
  | .secp256r1 => `(Noctium.Foreign.Curve.secp256r1)
  | .curve25519 => `(Noctium.Foreign.Curve.curve25519)

private def foreignKindTerm : Foreign.Kind → CommandElabM (TSyntax `term)
  | .base curve => do
    let curve ← foreignCurveTerm curve
    `(Noctium.Foreign.Kind.base $curve)
  | .scalar curve => do
    let curve ← foreignCurveTerm curve
    `(Noctium.Foreign.Kind.scalar $curve)
  | .point curve => do
    let curve ← foreignCurveTerm curve
    `(Noctium.Foreign.Kind.point $curve)

private def foreignFieldKindTerm : Foreign.FieldKind → CommandElabM (TSyntax `term)
  | .base curve => do
    let curve ← foreignCurveTerm curve
    `(Noctium.Foreign.FieldKind.base $curve)
  | .scalar curve => do
    let curve ← foreignCurveTerm curve
    `(Noctium.Foreign.FieldKind.scalar $curve)

private def foreignUnaryOpTerm : Foreign.UnaryOp → CommandElabM (TSyntax `term)
  | .neg kind => do
    let kind ← foreignKindTerm kind
    `(Noctium.Foreign.UnaryOp.neg $kind)
  | .inv kind => do
    let kind ← foreignFieldKindTerm kind
    `(Noctium.Foreign.UnaryOp.inv $kind)
  | .mulGenerator curve => do
    let curve ← foreignCurveTerm curve
    `(Noctium.Foreign.UnaryOp.mulGenerator $curve)
  | .x curve => do
    let curve ← foreignCurveTerm curve
    `(Noctium.Foreign.UnaryOp.x $curve)
  | .y curve => do
    let curve ← foreignCurveTerm curve
    `(Noctium.Foreign.UnaryOp.y $curve)

private def foreignBinaryOpTerm : Foreign.BinaryOp → CommandElabM (TSyntax `term)
  | .add kind => do
    let kind ← foreignKindTerm kind
    `(Noctium.Foreign.BinaryOp.add $kind)
  | .sub kind => do
    let kind ← foreignKindTerm kind
    `(Noctium.Foreign.BinaryOp.sub $kind)
  | .mul kind => do
    let kind ← foreignFieldKindTerm kind
    `(Noctium.Foreign.BinaryOp.mul $kind)
  | .ecMul curve => do
    let curve ← foreignCurveTerm curve
    `(Noctium.Foreign.BinaryOp.ecMul $curve)
  | .fromCoordinates curve => do
    let curve ← foreignCurveTerm curve
    `(Noctium.Foreign.BinaryOp.fromCoordinates $curve)

private def stringTerm (value : String) : TSyntax `term := ⟨Syntax.mkStrLit value⟩
private def natTerm (value : Nat) : TSyntax `term := ⟨Syntax.mkNumLit (toString value)⟩

private partial def natListTerm : List Nat → CommandElabM (TSyntax `term)
  | [] => `(([] : List Nat))
  | value :: rest => do
    let tail ← natListTerm rest
    `($(natTerm value) :: $tail)

private partial def exprListTerm : List (TSyntax `term) → CommandElabM (TSyntax `term)
  | [] => `(([] : List (Noctium.Expr (Noctium.Ty.bytes 32))))
  | value :: rest => do
    let tail ← exprListTerm rest
    `($value :: $tail)

private partial def pathKeyListTerm : List (TSyntax `term) → CommandElabM (TSyntax `term)
  | [] => `(([] : List Noctium.PathKey))
  | value :: rest => do
    let tail ← pathKeyListTerm rest
    `($value :: $tail)

private partial def stringListTerm : List (TSyntax `term) → CommandElabM (TSyntax `term)
  | [] => `(([] : List String))
  | value :: rest => do
    let tail ← stringListTerm rest
    `($value :: $tail)

private partial def nativeExprListTerm : List (TSyntax `term) → CommandElabM (TSyntax `term)
  | [] => `(([] : List (Noctium.Expr Noctium.Ty.native)))
  | value :: rest => do
    let tail ← nativeExprListTerm rest
    `($value :: $tail)

private def spanTerm (stx : Syntax) : CommandElabM (TSyntax `term) := do
  let fileMap ← getFileMap
  let pos := fileMap.toPosition (stx.getPos?.getD 0)
  let file ← getFileName
  `({ file := $(stringTerm file), line := $(natTerm pos.line),
      column := $(natTerm (pos.column + 1)) : Noctium.SourceSpan })

private abbrev Bindings := List (String × Ty × TSyntax `term)

private def coerceExpression (stx : Syntax) (found target : Ty) (value : TSyntax `term) :
    CommandElabM (TSyntax `term) := do
  if found == target then return value
  match found, target with
  | .uint m, .uint n =>
    unless m ≤ n do throwErrorAt stx "Noctium expression type mismatch; use an explicit narrowing cast"
    `(Noctium.Expr.cast $(← tyTerm target) $value)
  | .uint _, .native => `(Noctium.Expr.cast Noctium.Ty.native $value)
  | _, _ => throwErrorAt stx "Noctium expression type mismatch"

private def commonType (stx : Syntax) (left right : Ty) : CommandElabM Ty := do
  if left == right then return left
  match left, right with
  | .uint m, .uint n => pure (.uint (max m n))
  | .native, .uint _ | .uint _, .native => pure .native
  | _, _ => throwErrorAt stx "Noctium expression type mismatch"

/-- A new partial scalar operation must execute even beneath a total wrapper.
Mark every subtraction conservatively, including total native-field subtraction. -/
private partial def hasPartialScalar (stx : TSyntax `nlexpr) : _root_.Bool :=
  match stx with
  | `(nlexpr| cast($_:nltype, $_:nlexpr)) => Bool.true
  | `(nlexpr| sub($_:nlexpr, $_:nlexpr)) => Bool.true
  | `(nlexpr| inv($_:nlexpr)) => Bool.true
  | `(nlexpr| fromBytes32($_:nltype, $_:nlexpr)) => Bool.true
  | `(nlexpr| fromBytes($_:nltype, $value:nlexpr)) => hasPartialScalar value
  | `(nlexpr| assertThen($_:nlexpr, $_:nlexpr)) => Bool.true
  | `(nlexpr| let $_:ident := $value:nlexpr in $body:nlexpr) =>
    hasPartialScalar value || hasPartialScalar body
  | `(nlexpr| disclose($value)) => hasPartialScalar value
  | `(nlexpr| add($a, $b)) | `(nlexpr| mul($a, $b))
  | `(nlexpr| eq($a, $b)) | `(nlexpr| boolAnd($a, $b))
  | `(nlexpr| boolOr($a, $b)) | `(nlexpr| boolXor($a, $b))
  | `(nlexpr| poseidon2($_:num, $a, $b)) =>
    hasPartialScalar a || hasPartialScalar b
  | `(nlexpr| persistentHash32($value)) => hasPartialScalar value
  | `(nlexpr| sha512($value)) | `(nlexpr| keccak256($value)) => hasPartialScalar value
  | `(nlexpr| bytes($_:num, $_:str)) => Bool.false
  | `(nlexpr| copyValue($value)) | `(nlexpr| reverseBytes($value)) => hasPartialScalar value
  | `(nlexpr| sliceBytes($value, $_:num, $_:num)) => Bool.true
  | `(nlexpr| concatBytes($left, $right)) =>
    hasPartialScalar left || hasPartialScalar right
  | `(nlexpr| reverseBytes32($value)) => hasPartialScalar value
  | `(nlexpr| persistentHashVector32([$values,*])) =>
    values.getElems.toList.any hasPartialScalar
  | `(nlexpr| persistentHashNative($value)) => hasPartialScalar value
  | `(nlexpr| persistentHashNativeVector([$values,*])) =>
    values.getElems.toList.any hasPartialScalar
  | `(nlexpr| transientHashNativeVector([$values,*])) =>
    values.getElems.toList.any hasPartialScalar
  | `(nlexpr| persistentHashPoint($point)) => hasPartialScalar point
  | `(nlexpr| hashToCurve([$values,*])) => Bool.true
  | `(nlexpr| toBytes32($value)) => hasPartialScalar value
  | `(nlexpr| byteAt($value, $_:num)) => hasPartialScalar value
  | `(nlexpr| degradeToNative($value)) => hasPartialScalar value
  | `(nlexpr| jubjubScalarFromNative($value))
  | `(nlexpr| jubjubScalarToNative($value))
  | `(nlexpr| jubjubMulGenerator($value))
  | `(nlexpr| jubjubNeg($value))
  | `(nlexpr| jubjubX($value))
  | `(nlexpr| jubjubY($value)) => hasPartialScalar value
  | `(nlexpr| jubjubMul($point, $scalar))
  | `(nlexpr| jubjubAdd($point, $scalar)) =>
    hasPartialScalar point || hasPartialScalar scalar
  | `(nlexpr| jubjubFromCoordinates($_:nlexpr, $_:nlexpr)) => Bool.true
  | `(nlexpr| foreignAdd($_:nlexpr, $_:nlexpr))
  | `(nlexpr| foreignSub($_:nlexpr, $_:nlexpr))
  | `(nlexpr| foreignMul($_:nlexpr, $_:nlexpr))
  | `(nlexpr| foreignNeg($_:nlexpr))
  | `(nlexpr| foreignInv($_:nlexpr))
  | `(nlexpr| curveMul($_:nlexpr, $_:nlexpr))
  | `(nlexpr| curveMulGenerator($_:nlexpr))
  | `(nlexpr| curveX($_:nlexpr))
  | `(nlexpr| curveY($_:nlexpr))
  | `(nlexpr| curveFromCoordinates($_:nlexpr, $_:nlexpr))
  | `(nlexpr| foreignToBytes($_:nlexpr))
  | `(nlexpr| foreignFromBytes($_:nltype, $_:nlexpr))
  | `(nlexpr| secp256k1EcdsaVerify($_:nlexpr, $_:nlexpr, $_:nlexpr, $_:nlexpr))
  | `(nlexpr| secp256r1EcdsaVerify($_:nlexpr, $_:nlexpr, $_:nlexpr, $_:nlexpr))
  | `(nlexpr| ed25519Verify($_:nlexpr, $_:nlexpr, $_:nlexpr, $_:nlexpr))
  | `(nlexpr| secp256k1EthereumAddress($_:nlexpr)) => Bool.true
  | `(nlexpr| jubjubSchnorrVerify([$messages,*], $_:nlexpr, $_:nlexpr, $_:nlexpr)) => Bool.true
  | `(nlexpr| select($c, $a, $b)) =>
    hasPartialScalar c || hasPartialScalar a || hasPartialScalar b
  | _ => Bool.false

private partial def expression (env : Bindings) (stx : TSyntax `nlexpr) :
    CommandElabM (Ty × TSyntax `term) := do
  match stx with
  | `(nlexpr| $id:ident) =>
    match env.find? (fun p => p.1 == id.getId.toString) with
    | some (_, ty, value) => pure (ty, value)
    | none => throwErrorAt id "unknown Noctium value '{id.getId}'"
  | `(nlexpr| $n:num) => pure (.native, ← `(Noctium.Expr.native $n))
  | `(nlexpr| true) => pure (.bool, ← `(Noctium.Expr.bool Bool.true))
  | `(nlexpr| false) => pure (.bool, ← `(Noctium.Expr.bool Bool.false))
  | `(nlexpr| let $id:ident := $value:nlexpr in $body:nlexpr) => do
    let (valueTy, value) ← expression env value
    let typeTerm ← tyTerm valueTy
    let valueRef ← `(Noctium.Expr.ref (ty := $typeTerm) $(stringTerm id.getId.toString))
    let bodyEnv := (id.getId.toString, valueTy, valueRef) :: env
    let (bodyTy, body) ← expression bodyEnv body
    pure (bodyTy, ← `(Noctium.Expr.letE $(stringTerm id.getId.toString) $value $body))
  | `(nlexpr| assertThen($condition, $body)) => do
    let condition ← expected env condition .bool
    let (bodyTy, body) ← expression env body
    pure (bodyTy, ← `(Noctium.Expr.assertE $condition $body))
  | `(nlexpr| uint($n:num)) =>
    match ScalarPolicy.validate (.uint n.getNat) with
    | .error message => throwErrorAt stx message
    | .ok _ => pure (.uint n.getNat, ← `(Noctium.Expr.uint $n $n))
  | `(nlexpr| cast($target:nltype, $value:nlexpr)) =>
    let target ← readTy target
    let (source, value) ← expression env value
    if target.isJubjub || source.isJubjub || target.isForeign || source.isForeign then
      throwErrorAt stx "curve values require explicit typed conversions"
    pure (target, ← `(Noctium.Expr.cast $(← tyTerm target) $value))
  | `(nlexpr| default($target:nltype)) =>
    let target ← readTy target
    match target with
    | .native => pure (.native, ← `(Noctium.Expr.native 0))
    | .bool => pure (.bool, ← `(Noctium.Expr.bool Bool.false))
    | .uint maximum => pure (target, ← `(Noctium.Expr.uint $(natTerm maximum) 0))
    | .bytes _ => throwErrorAt stx "byte strings have no scalar default expression"
    | .jubjubScalar | .jubjubPoint => throwErrorAt stx "Jubjub values have no generic default expression"
    | .foreign _ => throwErrorAt stx "foreign values have no generic default expression"
  | `(nlexpr| disclose($value)) =>
    let (ty, value) ← expression env value
    pure (ty, ← `(Noctium.Expr.disclose $(← spanTerm stx) $value))
  | `(nlexpr| add($a, $b)) =>
    arithmetic env stx .add a b
  | `(nlexpr| mul($a, $b)) =>
    arithmetic env stx .mul a b
  | `(nlexpr| sub($a, $b)) =>
    arithmetic env stx .sub a b
  | `(nlexpr| inv($value)) => do
    let (ty, value) ← expression env value
    unless ty == .native || ty == .jubjubScalar do
      throwErrorAt stx "inv accepts only Native and JubjubScalar values"
    pure (ty, ← `(Noctium.Expr.inv $value))
  | `(nlexpr| toBytes32($value)) => do
    let (source, value) ← expression env value
    unless source == .native || source == .jubjubScalar || source == .jubjubPoint do
      throwErrorAt stx "toBytes32 accepts only Native, JubjubScalar or JubjubPoint"
    pure (.bytes 32, ← `(Noctium.Expr.toBytes32 $value))
  | `(nlexpr| fromBytes32($target:nltype, $value)) => do
    let target ← readTy target
    unless target == .native || target == .jubjubScalar || target == .jubjubPoint do
      throwErrorAt stx "fromBytes32 supports only Native, JubjubScalar or JubjubPoint"
    let value ← expected env value (.bytes 32)
    pure (target, ← `(Noctium.Expr.fromBytes32 (target := $(← tyTerm target)) $value))
  | `(nlexpr| fromBytes($target:nltype, $value)) => do
    let target ← readTy target
    unless target == .native || target == .jubjubScalar do
      throwErrorAt stx "fromBytes supports only Native and JubjubScalar"
    let (valueTy, value) ← expression env value
    let .bytes length := valueTy
      | throwErrorAt stx "fromBytes requires a Bytes expression"
    if length > maxBytesLength then
      throwErrorAt stx s!"byte string length exceeds the maximum of {maxBytesLength}"
    pure (target, ← `(Noctium.Expr.fromBytes (target := $(← tyTerm target)) $value))
  | `(nlexpr| byteAt($value, $index:num)) => do
    let (valueTy, value) ← expression env value
    let .bytes length := valueTy
      | throwErrorAt stx "byteAt requires a Bytes expression"
    unless index.getNat < length do
      throwErrorAt index s!"byte index must be less than the byte string length {length}"
    pure (.uint 255, ← `(Noctium.Expr.bytesAt $value $(natTerm index.getNat)))
  | `(nlexpr| eq($a, $b)) =>
    let (ta, a) ← expression env a
    let (tb, b) ← expression env b
    if ta.isBytes || tb.isBytes then do
      if ta == .bytes 32 || tb == .bytes 32 then do
        unless ta == .bytes 32 && tb == .bytes 32 do
          throwErrorAt stx "Bytes32 equality requires two Bytes32 expressions"
        let aHigh ← `(Noctium.Expr.bytesField $a 0)
        let bHigh ← `(Noctium.Expr.bytesField $b 0)
        let aLow ← `(Noctium.Expr.bytesField $a 1)
        let bLow ← `(Noctium.Expr.bytesField $b 1)
        let highEqual ← `(Noctium.Expr.eq $aHigh $bHigh)
        let lowEqual ← `(Noctium.Expr.eq $aLow $bLow)
        let falseValue ← `(Noctium.Expr.bool Bool.false)
        pure (.bool, ← `(Noctium.Expr.select $highEqual $lowEqual $falseValue))
      else do
        let .bytes length := ta
          | throwErrorAt stx "byte equality requires two same-length Bytes expressions"
        unless tb == .bytes length do
          throwErrorAt stx "byte equality requires two same-length Bytes expressions"
        if length == 0 then do
          let usedNames := env.map (fun binding => binding.1)
          let mut index := 0
          let mut leftName := s!"$byteEq{index}"
          while usedNames.contains leftName do
            index := index + 1
            leftName := s!"$byteEq{index}"
          index := index + 1
          let mut rightName := s!"$byteEq{index}"
          while usedNames.contains rightName || rightName == leftName do
            index := index + 1
            rightName := s!"$byteEq{index}"
          pure (.bool, ← `(Noctium.Expr.letE $(stringTerm leftName) $a
            (Noctium.Expr.letE $(stringTerm rightName) $b (Noctium.Expr.bool Bool.true))))
        else do
          let mut equal ← `(Noctium.Expr.bool Bool.true)
          for chunk in List.range ((length + 30) / 31) do
            let aField ← `(Noctium.Expr.bytesField $a $(natTerm chunk))
            let bField ← `(Noctium.Expr.bytesField $b $(natTerm chunk))
            let chunkEqual ← `(Noctium.Expr.eq $aField $bField)
            equal ← `(Noctium.Expr.select $chunkEqual $equal (Noctium.Expr.bool Bool.false))
          pure (.bool, equal)
    else do
      let ty ← commonType stx ta tb
      let a ← coerceExpression stx ta ty a
      let b ← coerceExpression stx tb ty b
      pure (.bool, ← `(Noctium.Expr.eq $a $b))
  | `(nlexpr| boolAnd($left, $right)) => do
    let left ← expected env left .bool
    let right ← expected env right .bool
    pure (.bool, ← `(Noctium.Expr.boolAnd $left $right))
  | `(nlexpr| boolOr($left, $right)) => do
    let left ← expected env left .bool
    let right ← expected env right .bool
    pure (.bool, ← `(Noctium.Expr.boolOr $left $right))
  | `(nlexpr| boolXor($left, $right)) => do
    let left ← expected env left .bool
    let right ← expected env right .bool
    pure (.bool, ← `(Noctium.Expr.boolXor $left $right))
  | `(nlexpr| select($c, $a, $b)) =>
    let c ← expected env c .bool
    let (ta, a) ← expression env a
    let (tb, b) ← expression env b
    let ty ← commonType stx ta tb
    let a ← coerceExpression stx ta ty a
    let b ← coerceExpression stx tb ty b
    pure (ty, ← `(Noctium.Expr.select $c $a $b))
  | `(nlexpr| poseidon2($domain:num, $a, $b)) =>
    let a ← expected env a .native
    let b ← expected env b .native
    pure (.native, ← `(Noctium.Expr.poseidon2 $domain $a $b))
  | `(nlexpr| persistentHash32($value)) => do
    let (valueTy, value) ← expression env value
    unless valueTy == .bytes 32 do
      throwErrorAt stx "persistentHash32 requires a Bytes32 expression"
    pure (.bytes 32, ← `(Noctium.Expr.persistentHash32 $value))
  | `(nlexpr| sha512($value)) => do
    let (valueTy, value) ← expression env value
    let .bytes _ := valueTy
      | throwErrorAt stx "sha512 requires a Bytes expression"
    pure (.bytes 64, ← `(Noctium.Expr.sha512 $value))
  | `(nlexpr| keccak256($value)) => do
    let (valueTy, value) ← expression env value
    let .bytes _ := valueTy
      | throwErrorAt stx "keccak256 requires a Bytes expression"
    pure (.bytes 32, ← `(Noctium.Expr.keccak256 $value))
  | `(nlexpr| secp256k1EcdsaVerify($msgHash, $r, $s, $pk)) => do
    let msgHash ← expected env msgHash (.bytes 32)
    let r ← expected env r (.foreign (.scalar .secp256k1))
    let s ← expected env s (.foreign (.scalar .secp256k1))
    let pk ← expected env pk (.foreign (.point .secp256k1))
    pure (.bool, ← `(Noctium.Crypto.secp256k1EcdsaVerify $msgHash $r $s $pk))
  | `(nlexpr| secp256r1EcdsaVerify($msgHash, $r, $s, $pk)) => do
    let msgHash ← expected env msgHash (.bytes 32)
    let r ← expected env r (.foreign (.scalar .secp256r1))
    let s ← expected env s (.foreign (.scalar .secp256r1))
    let pk ← expected env pk (.foreign (.point .secp256r1))
    pure (.bool, ← `(Noctium.Crypto.secp256r1EcdsaVerify $msgHash $r $s $pk))
  | `(nlexpr| jubjubSchnorrVerify([$message,*], $announcement, $response, $pk)) => do
    let sourceMessages := message.getElems.toList
    unless sourceMessages.length + 4 ≤ 1024 do
      throwErrorAt stx "jubjubSchnorrVerify challenge input exceeds 1024 Native fields"
    let messages ← sourceMessages.mapM fun value => expected env value .native
    let messageList ← nativeExprListTerm messages
    let announcement ← expected env announcement .jubjubPoint
    let response ← expected env response .native
    let pk ← expected env pk .jubjubPoint
    pure (.bool, ← `(Noctium.Crypto.jubjubSchnorrVerify $messageList $announcement $response $pk))
  | `(nlexpr| ed25519Verify($message, $r, $s, $pk)) => do
    let (messageTy, message) ← expression env message
    let .bytes length := messageTy
      | throwErrorAt stx "ed25519Verify requires a Bytes message"
    unless length + 64 ≤ 1024 do
      throwErrorAt stx "ed25519Verify input exceeds 1024 bytes"
    let r ← expected env r (.foreign (.point .curve25519))
    let s ← expected env s (.foreign (.scalar .curve25519))
    let pk ← expected env pk (.foreign (.point .curve25519))
    pure (.bool, ← `(Noctium.Crypto.ed25519Verify $message $r $s $pk))
  | `(nlexpr| secp256k1EthereumAddress($pk)) => do
    let pk ← expected env pk (.foreign (.point .secp256k1))
    pure (.bytes 20, ← `(Noctium.Crypto.secp256k1EthereumAddress $pk))
  | `(nlexpr| bytes($length:num, $literal:str)) => do
    let length := length.getNat
    if length > Noctium.maxBytesLength then
      throwErrorAt stx s!"byte string length exceeds the maximum of {Noctium.maxBytesLength}"
    let bytes := literal.getString.toUTF8.data.toList.map UInt8.toNat
    if bytes.length > length then
      throwErrorAt literal s!"byte string literal exceeds its declared length {length}"
    let values ← natListTerm (bytes ++ List.replicate (length - bytes.length) 0)
    pure (.bytes length, ← `(Noctium.Expr.bytesLiteral $(natTerm length) $values))
  | `(nlexpr| copyValue($value)) => do
    let (ty, value) ← expression env value
    pure (ty, ← `(Noctium.Expr.copyValue $value))
  | `(nlexpr| reverseBytes($value)) => do
    let (valueTy, value) ← expression env value
    let .bytes _ := valueTy
      | throwErrorAt stx "reverseBytes requires a Bytes expression"
    pure (valueTy, ← `(Noctium.Expr.reverseBytes $value))
  | `(nlexpr| sliceBytes($value, $start:num, $stop:num)) => do
    let (valueTy, value) ← expression env value
    let .bytes length := valueTy
      | throwErrorAt stx "sliceBytes requires a Bytes expression"
    let start := start.getNat
    let stop := stop.getNat
    unless start ≤ stop && stop ≤ length do
      throwErrorAt stx s!"byte slice bounds must satisfy 0 ≤ start ≤ end ≤ {length}"
    pure (.bytes (stop - start), ← `(Noctium.Expr.sliceBytes $value $(natTerm start) $(natTerm stop)))
  | `(nlexpr| concatBytes($left, $right)) => do
    let (leftTy, left) ← expression env left
    let (rightTy, right) ← expression env right
    let (.bytes leftLength, .bytes rightLength) := (leftTy, rightTy)
      | throwErrorAt stx "concatBytes requires two Bytes expressions"
    let length := leftLength + rightLength
    if length > Noctium.maxBytesLength then
      throwErrorAt stx s!"concatenated byte string length exceeds the maximum of {Noctium.maxBytesLength}"
    pure (.bytes length, ← `(Noctium.Expr.concatBytes $left $right))
  | `(nlexpr| reverseBytes32($value)) => do
    let value ← expected env value (.bytes 32)
    pure (.bytes 32, ← `(Noctium.Expr.reverseBytes32 $value))
  | `(nlexpr| bytes32($literal:str)) => do
    let bytes := literal.getString.toUTF8.data.toList.map UInt8.toNat
    if bytes.length > 32 then throwErrorAt stx "Bytes32 string literal exceeds 32 UTF-8 bytes"
    let padded := bytes ++ List.replicate (32 - bytes.length) 0
    let values ← natListTerm padded
    pure (.bytes 32, ← `(Noctium.Expr.bytes32Literal $values))
  | `(nlexpr| persistentHashVector32([$values,*])) => do
    let expressions ← values.getElems.toList.mapM fun value => do
      let (valueTy, value) ← expression env value
      unless valueTy == .bytes 32 do
        throwErrorAt value "persistentHashVector32 accepts only Bytes32 elements"
      pure value
    unless expressions.length ≥ 1 && expressions.length ≤ 32 do
      throwErrorAt stx "persistentHashVector32 requires 1 to 32 Bytes32 elements"
    let valueList ← exprListTerm expressions
    pure (.bytes 32, ← `(Noctium.Expr.persistentHashVector32 $valueList))
  | `(nlexpr| persistentHashNative($value)) => do
    let (valueTy, value) ← expression env value
    unless valueTy == .native do
      throwErrorAt stx "persistentHashNative requires a Native field expression"
    pure (.bytes 32, ← `(Noctium.Expr.persistentHashNative $value))
  | `(nlexpr| persistentHashNativeVector([$values,*])) => do
    let expressions ← values.getElems.toList.mapM fun value => do
      let (valueTy, value) ← expression env value
      unless valueTy == .native do
        throwErrorAt value "persistentHashNativeVector accepts only Native fields"
      pure value
    unless expressions.length ≥ 1 && expressions.length ≤ 32 do
      throwErrorAt stx "persistentHashNativeVector requires 1 to 32 Native fields"
    let valueList ← nativeExprListTerm expressions
    pure (.bytes 32, ← `(Noctium.Expr.persistentHashNativeVector $valueList))
  | `(nlexpr| transientHashNativeVector([$values,*])) => do
    let sourceValues := values.getElems.toList
    unless sourceValues.length ≤ Types.defaultLimits.maxVectorLength do
      throwErrorAt stx s!"transient hash input count exceeds the maximum of {Types.defaultLimits.maxVectorLength}"
    let values ← sourceValues.mapM fun value => do
      let (valueTy, expression) ← expression env value
      unless valueTy == .native do
        throwErrorAt value "transientHashNativeVector accepts only Native fields"
      pure expression
    let valueList ← nativeExprListTerm values
    pure (.native, ← `(Noctium.Expr.transientHash $valueList))
  | `(nlexpr| persistentHashPoint($point)) => do
    let point ← expected env point .jubjubPoint
    let x ← `(Noctium.Expr.jubjubCoordinate $point 0)
    let y ← `(Noctium.Expr.jubjubCoordinate $point 1)
    let valueList ← nativeExprListTerm [x, y]
    pure (.bytes 32, ← `(Noctium.Expr.persistentHashNativeVector $valueList))
  | `(nlexpr| degradeToNative($value)) => do
    let (valueTy, value) ← expression env value
    unless valueTy == .bytes 32 do
      throwErrorAt stx "degradeToNative requires a Bytes32 expression"
    -- Match the ledger's transient-crypto degradation, which takes field_vec()[1].
    pure (.native, ← `(Noctium.Expr.bytesField $value 1))
  | `(nlexpr| jubjubScalarFromNative($value)) => do
    let value ← expected env value .native
    pure (.jubjubScalar, ← `(Noctium.Expr.jubjubScalarFromNative $value))
  | `(nlexpr| jubjubScalarToNative($value)) => do
    let value ← expected env value .jubjubScalar
    pure (.native, ← `(Noctium.Expr.jubjubScalarToNative $value))
  | `(nlexpr| jubjubMulGenerator($scalar)) => do
    let scalar ← expected env scalar .jubjubScalar
    pure (.jubjubPoint, ← `(Noctium.Expr.jubjubMulGenerator $scalar))
  | `(nlexpr| jubjubMul($point, $scalar)) => do
    let point ← expected env point .jubjubPoint
    let scalar ← expected env scalar .jubjubScalar
    pure (.jubjubPoint, ← `(Noctium.Expr.jubjubMul $point $scalar))
  | `(nlexpr| jubjubAdd($left, $right)) => do
    let left ← expected env left .jubjubPoint
    let right ← expected env right .jubjubPoint
    pure (.jubjubPoint, ← `(Noctium.Expr.jubjubAdd $left $right))
  | `(nlexpr| jubjubNeg($point)) => do
    let point ← expected env point .jubjubPoint
    pure (.jubjubPoint, ← `(Noctium.Expr.jubjubNeg $point))
  | `(nlexpr| jubjubX($point)) => do
    let point ← expected env point .jubjubPoint
    pure (.native, ← `(Noctium.Expr.jubjubCoordinate $point 0))
  | `(nlexpr| jubjubY($point)) => do
    let point ← expected env point .jubjubPoint
    pure (.native, ← `(Noctium.Expr.jubjubCoordinate $point 1))
  | `(nlexpr| jubjubFromCoordinates($x, $y)) => do
    let x ← expected env x .native
    let y ← expected env y .native
    pure (.jubjubPoint, ← `(Noctium.Expr.jubjubFromCoordinates $x $y))
  | `(nlexpr| secp256k1Base($value:num)) => do
    unless value.getNat < Foreign.Curve.baseModulus .secp256k1 do
      throwErrorAt value "Secp256k1Base literal is not canonical"
    pure (.foreign (.base .secp256k1), ← `(Noctium.Expr.foreignBase Noctium.Foreign.Curve.secp256k1 $value))
  | `(nlexpr| secp256k1Scalar($value:num)) => do
    unless value.getNat < Foreign.Curve.scalarModulus .secp256k1 do
      throwErrorAt value "Secp256k1Scalar literal is not canonical"
    pure (.foreign (.scalar .secp256k1), ← `(Noctium.Expr.foreignScalar Noctium.Foreign.Curve.secp256k1 $value))
  | `(nlexpr| secp256k1Identity()) =>
    pure (.foreign (.point .secp256k1), ← `(Noctium.Expr.foreignIdentity Noctium.Foreign.Curve.secp256k1))
  | `(nlexpr| secp256r1Base($value:num)) => do
    unless value.getNat < Foreign.Curve.baseModulus .secp256r1 do
      throwErrorAt value "Secp256r1Base literal is not canonical"
    pure (.foreign (.base .secp256r1), ← `(Noctium.Expr.foreignBase Noctium.Foreign.Curve.secp256r1 $value))
  | `(nlexpr| secp256r1Scalar($value:num)) => do
    unless value.getNat < Foreign.Curve.scalarModulus .secp256r1 do
      throwErrorAt value "Secp256r1Scalar literal is not canonical"
    pure (.foreign (.scalar .secp256r1), ← `(Noctium.Expr.foreignScalar Noctium.Foreign.Curve.secp256r1 $value))
  | `(nlexpr| secp256r1Identity()) =>
    pure (.foreign (.point .secp256r1), ← `(Noctium.Expr.foreignIdentity Noctium.Foreign.Curve.secp256r1))
  | `(nlexpr| curve25519Base($value:num)) => do
    unless value.getNat < Foreign.Curve.baseModulus .curve25519 do
      throwErrorAt value "Curve25519Base literal is not canonical"
    pure (.foreign (.base .curve25519), ← `(Noctium.Expr.foreignBase Noctium.Foreign.Curve.curve25519 $value))
  | `(nlexpr| curve25519Scalar($value:num)) => do
    unless value.getNat < Foreign.Curve.scalarModulus .curve25519 do
      throwErrorAt value "Curve25519Scalar literal is not canonical"
    pure (.foreign (.scalar .curve25519), ← `(Noctium.Expr.foreignScalar Noctium.Foreign.Curve.curve25519 $value))
  | `(nlexpr| curve25519Identity()) =>
    pure (.foreign (.point .curve25519), ← `(Noctium.Expr.foreignIdentity Noctium.Foreign.Curve.curve25519))
  | `(nlexpr| foreignAdd($left, $right)) => do
    let (leftTy, left) ← expression env left
    let (rightTy, right) ← expression env right
    let (.foreign kind, .foreign rightKind) := (leftTy, rightTy)
      | throwErrorAt stx "foreignAdd requires two foreign values"
    unless kind == rightKind do throwErrorAt stx "foreignAdd requires matching curve and role"
    let operation ← foreignBinaryOpTerm (.add kind)
    pure (.foreign kind, ← `(Noctium.Expr.foreignBinary $operation $left $right))
  | `(nlexpr| foreignSub($left, $right)) => do
    let (leftTy, left) ← expression env left
    let (rightTy, right) ← expression env right
    let (.foreign kind, .foreign rightKind) := (leftTy, rightTy)
      | throwErrorAt stx "foreignSub requires two foreign values"
    unless kind == rightKind do throwErrorAt stx "foreignSub requires matching curve and role"
    let operation ← foreignBinaryOpTerm (.sub kind)
    pure (.foreign kind, ← `(Noctium.Expr.foreignBinary $operation $left $right))
  | `(nlexpr| foreignMul($left, $right)) => do
    let (leftTy, left) ← expression env left
    let (rightTy, right) ← expression env right
    let (.foreign kind, .foreign rightKind) := (leftTy, rightTy)
      | throwErrorAt stx "foreignMul requires two foreign field values"
    unless kind == rightKind do throwErrorAt stx "foreignMul requires matching curve and field role"
    let some fieldKind := kind.fieldKind?
      | throwErrorAt stx "foreignMul does not accept point values"
    let operation ← foreignBinaryOpTerm (.mul fieldKind)
    pure (.foreign kind, ← `(Noctium.Expr.foreignBinary $operation $left $right))
  | `(nlexpr| foreignNeg($value)) => do
    let (ty, value) ← expression env value
    let .foreign kind := ty
      | throwErrorAt stx "foreignNeg requires a foreign value"
    let operation ← foreignUnaryOpTerm (.neg kind)
    pure (ty, ← `(Noctium.Expr.foreignUnary $operation $value))
  | `(nlexpr| foreignInv($value)) => do
    let (ty, value) ← expression env value
    let .foreign kind := ty
      | throwErrorAt stx "foreignInv requires a foreign field value"
    let some fieldKind := kind.fieldKind?
      | throwErrorAt stx "foreignInv does not accept point values"
    let operation ← foreignUnaryOpTerm (.inv fieldKind)
    pure (ty, ← `(Noctium.Expr.foreignUnary $operation $value))
  | `(nlexpr| curveMul($point, $scalar)) => do
    let (pointTy, point) ← expression env point
    let (scalarTy, scalar) ← expression env scalar
    let .foreign (.point curve) := pointTy
      | throwErrorAt point "curveMul requires a curve point as its first argument"
    let .foreign (.scalar scalarCurve) := scalarTy
      | throwErrorAt scalar "curveMul requires a matching curve scalar"
    unless curve == scalarCurve do throwErrorAt stx "curveMul requires matching curve families"
    let operation ← foreignBinaryOpTerm (.ecMul curve)
    pure (pointTy, ← `(Noctium.Expr.foreignBinary $operation $point $scalar))
  | `(nlexpr| curveMulGenerator($scalar)) => do
    let (scalarTy, scalar) ← expression env scalar
    let .foreign (.scalar curve) := scalarTy
      | throwErrorAt stx "curveMulGenerator requires a foreign curve scalar"
    let operation ← foreignUnaryOpTerm (.mulGenerator curve)
    pure (.foreign (.point curve), ← `(Noctium.Expr.foreignUnary $operation $scalar))
  | `(nlexpr| curveX($point)) => do
    let (pointTy, point) ← expression env point
    let .foreign (.point curve) := pointTy
      | throwErrorAt stx "curveX requires a foreign curve point"
    let operation ← foreignUnaryOpTerm (.x curve)
    pure (.foreign (.base curve), ← `(Noctium.Expr.foreignUnary $operation $point))
  | `(nlexpr| curveY($point)) => do
    let (pointTy, point) ← expression env point
    let .foreign (.point curve) := pointTy
      | throwErrorAt stx "curveY requires a foreign curve point"
    let operation ← foreignUnaryOpTerm (.y curve)
    pure (.foreign (.base curve), ← `(Noctium.Expr.foreignUnary $operation $point))
  | `(nlexpr| curveFromCoordinates($x, $y)) => do
    let (xTy, x) ← expression env x
    let (yTy, y) ← expression env y
    let (.foreign (.base curve), .foreign (.base yCurve)) := (xTy, yTy)
      | throwErrorAt stx "curveFromCoordinates requires two foreign base-field values"
    unless curve == yCurve do throwErrorAt stx "curveFromCoordinates requires matching curve families"
    let operation ← foreignBinaryOpTerm (.fromCoordinates curve)
    pure (.foreign (.point curve), ← `(Noctium.Expr.foreignBinary $operation $x $y))
  | `(nlexpr| foreignToBytes($value)) => do
    let (valueTy, value) ← expression env value
    let .foreign kind := valueTy
      | throwErrorAt stx "foreignToBytes requires a foreign curve value"
    pure (.bytes kind.byteLength, ← `(Noctium.Expr.foreignToBytes $value))
  | `(nlexpr| foreignFromBytes($target:nltype, $value)) => do
    let target ← readTy target
    let .foreign kind := target
      | throwErrorAt stx "foreignFromBytes target must be a foreign curve type"
    let (valueTy, value) ← expression env value
    let byteLength ← match valueTy with
      | .bytes byteLength => pure byteLength
      | _ => throwErrorAt stx "foreignFromBytes requires a Bytes expression"
    if byteLength > maxBytesLength then
      throwErrorAt stx s!"byte string length exceeds the maximum of {maxBytesLength}"
    if let .point _ := kind then
      unless byteLength == kind.byteLength do
        throwErrorAt stx s!"foreign point decoding requires Bytes {kind.byteLength}"
    let kindTerm ← foreignKindTerm kind
    pure (target, ← `(Noctium.Expr.foreignFromBytes $kindTerm $value))
  | `(nlexpr| hashToCurve([$values,*])) => do
    let sourceValues := values.getElems.toList
    unless sourceValues.length ≤ Types.defaultLimits.maxVectorLength do
      throwErrorAt stx s!"hashToCurve input count exceeds the maximum of {Types.defaultLimits.maxVectorLength}"
    let values ← sourceValues.mapM fun value => expected env value .native
    let valueList ← nativeExprListTerm values
    pure (.jubjubPoint, ← `(Noctium.Expr.hashToCurve $valueList))
  | _ => throwErrorAt stx "unsupported Noctium expression"
where
  expected (env : Bindings) (stx : TSyntax `nlexpr) (ty : Ty) : CommandElabM (TSyntax `term) := do
    if let .uint maximum := ty then
      if let `(nlexpr| $n:num) := stx then
        unless n.getNat ≤ maximum do throwErrorAt stx "unsigned constant exceeds its type"
        return ← `(Noctium.Expr.uint $(natTerm maximum) $n)
    let (found, value) ← expression env stx
    coerceExpression stx found ty value
  arithmetic (env : Bindings) (stx : Syntax) (op : ScalarPolicy.Binary)
      (left right : TSyntax `nlexpr) : CommandElabM (Ty × TSyntax `term) := do
    let (lt, left) ← expression env left
    let (rt, right) ← expression env right
    let result ← match ScalarPolicy.infer op lt.scalarKind rt.scalarKind with
      | .ok result => pure result
      | .error message => throwErrorAt stx message
    match result with
    | .native =>
      let left ← coerceExpression stx lt .native left
      let right ← coerceExpression stx rt .native right
      let term ← match op with
        | .add => `(Noctium.Expr.add $left $right)
        | .sub => `(Noctium.Expr.sub $left $right)
        | .mul => `(Noctium.Expr.mul $left $right)
      pure (.native, term)
    | .uint maximum =>
      let term ← match op with
        | .add => `(Noctium.Expr.uadd $left $right)
        | .sub => `(Noctium.Expr.usub $left $right)
        | .mul => `(Noctium.Expr.umul $left $right)
      pure (.uint maximum, term)
    | .bool => throwErrorAt stx "invalid arithmetic result type"
    | .bytes _ => throwErrorAt stx "Bytes32 does not support arithmetic"
    | .jubjubScalar | .jubjubPoint =>
      throwErrorAt stx "Jubjub values do not support scalar arithmetic"
    | .foreign _ => throwErrorAt stx "foreign values require a qualified curve operation"

private def checkedExpression (env : Bindings) (stx : TSyntax `nlexpr) (ty : Ty) :
    CommandElabM (TSyntax `term) := do
  if let .uint maximum := ty then
    if let `(nlexpr| $n:num) := stx then
      unless n.getNat ≤ maximum do throwErrorAt stx "unsigned constant exceeds its type"
      return ← `(Noctium.Expr.uint $(natTerm maximum) $n)
  let (found, value) ← expression env stx
  coerceExpression stx found ty value

private partial def lowerTreePath (env : Bindings) (schema : LedgerValueType)
    (keys : List (TSyntax `nlexpr)) :
    CommandElabM (List (TSyntax `term) × LedgerValueType) := do
  match schema, keys with
  | value, [] => pure ([], value)
  | .scalar _, _ :: _ => throwError "nested map path continues through a scalar value"
  | .counter, _ :: _ => throwError "nested map path continues through a Counter value"
  | .composite .., _ :: _ => throwError "nested map path continues through a composite value"
  | .«list» .., _ :: _ => throwError "nested map path continues through a list value"
  | .map keyTy child, key :: rest => do
    let lowered ← checkedExpression env key keyTy
    let (tail, result) ← lowerTreePath env child rest
    pure ((← `(Noctium.PathKey.mk $(← tyTerm keyTy) $lowered)) :: tail, result)

private def pathKeysTerm (keys : List (TSyntax `term)) : CommandElabM (TSyntax `term) := do
  let list ← pathKeyListTerm keys
  `(($list : List Noctium.PathKey))

private partial def sourcePathParts (path : TSyntax `nlpath) :
    CommandElabM (TSyntax `ident × List (TSyntax `nlexpr)) := do
  match path with
  | `(nlpath| $storage:ident) => pure (storage, [])
  | `(nlpath| $parent:nlpath[$key:nlexpr]) => do
    let (storage, keys) ← sourcePathParts parent
    pure (storage, keys ++ [key])
  | _ => throwErrorAt path "invalid recursive state path"

private def treeStateSchema (schema : List (String × StateKind)) (storage : TSyntax `ident) :
    CommandElabM LedgerValueType := do
  match schema.lookup storage.getId.toString with
  | some (.tree value) => pure value
  | _ => throwErrorAt storage "nested path requires a declared recursive tree state"

private def lowerListPath (schema : List (String × StateKind)) (env : Bindings)
    (path : TSyntax `nlpath) :
    CommandElabM (TSyntax `ident × TSyntax `term × Types.CompositeType × List String) := do
  let (storage, sourceKeys) ← sourcePathParts path
  unless sourceKeys.length ≤ 13 do
    throwErrorAt path "List paths support at most 13 map keys"
  let treeSchema ← treeStateSchema schema storage
  let (keys, value) ← lowerTreePath env treeSchema sourceKeys
  let .«list» environment type := value
    | throwErrorAt path "List operation path must select a List value"
  let fieldNames ← match LedgerValueType.nativeLeafNames environment type with
    | .ok names => pure names
    | .error message => throwErrorAt path message
  pure (storage, ← pathKeysTerm keys, type, fieldNames)

private def counterPathTerm (env : Bindings) (schema : LedgerValueType)
    (keys : List (TSyntax `nlexpr)) : CommandElabM (TSyntax `term) := do
  let (path, result) ← lowerTreePath env schema keys
  let .counter := result | throwError "Counter operation path must select a Counter value"
  pathKeysTerm path

private def ensureFresh (env : Bindings) (id : TSyntax `ident) : CommandElabM Unit := do
  if env.any (fun p => p.1 == id.getId.toString) then
    throwErrorAt id "duplicate Noctium value '{id.getId}'"

private def failDisclosure (diagnostic : Diagnostic) : CommandElabM Unit :=
  throwError "{diagnostic.span.file}:{diagnostic.span.line}:{diagnostic.span.column}: {diagnostic.message}"

/-- Evaluate only the typed AST definitions constructed by these elaborators. -/
private unsafe def checkGeneratedCircuit (name : Name) : CommandElabM Unit := do
  let value ← evalConstCheck Circuit ``Circuit name
  match Disclosure.circuit value with
  | .ok _ => pure ()
  | .error diagnostic => failDisclosure diagnostic

private unsafe def checkGeneratedContract (name : Name) : CommandElabM Unit := do
  let value ← evalConstCheck Contract ``Contract name
  match value.validate Capabilities.source with
  | .error diagnostic => failDisclosure diagnostic
  | .ok _ =>
    match Disclosure.contract value with
    | .ok _ => pure ()
    | .error diagnostic => failDisclosure diagnostic

@[command_elab circuitCommand] def elabCircuit : CommandElab := fun stx => do
  match stx with
  | `(noctium_circuit $name:ident where $stmts:nlcstmt* end) =>
    let mut env : Bindings := []
    let mut inputs : Array (TSyntax `term) := #[]
    let mut inputInfo := []
    let mut publicInputInfo := []
    let mut outputs : Array (TSyntax `term) := #[]
    let mut outputInfo : List (String × Ty) := []
    let mut constraints : Array (TSyntax `term) := #[]
    for stmt in stmts do
      match stmt with
      | `(nlcstmt| public $id:ident : $ty:nltype)
      | `(nlcstmt| private $id:ident : $ty:nltype) =>
        ensureFresh env id
        let t ← readTy ty
        let tt ← tyTerm t
        let isPublic := stmt.raw[0].getAtomVal == "public"
        let visibility ← if isPublic then `(Noctium.Visibility.public) else `(Noctium.Visibility.private)
        let span ← spanTerm stmt
        inputs := inputs.push (← `({ name := $(stringTerm id.getId.toString), ty := $tt, visibility := $visibility, span := $span : Noctium.Input }))
        env := (id.getId.toString, t, ← `(@Noctium.Expr.ref $tt $(stringTerm id.getId.toString))) :: env
        inputInfo := inputInfo ++ [(id.getId.toString, t)]
        if isPublic then publicInputInfo := publicInputInfo ++ [(id.getId.toString, t)]
      | `(nlcstmt| let $id:ident : $ty:nltype := $value:nlexpr) =>
        ensureFresh env id
        let t ← readTy ty
        let retain := (match t with | .uint _ => Bool.true | _ => Bool.false) || hasPartialScalar value
        let value ← checkedExpression env value t
        if retain then
          -- Equality keeps partial range/underflow checks in unused bindings.
          -- Byte expressions have no equality operator on the source surface, so
          -- retain their evaluation in a typed let whose body is true.
          match t with
          | .bytes _ =>
            constraints := constraints.push
              (← `(Noctium.Expr.letE "$byteRetain" $value (Noctium.Expr.bool Bool.true)))
          | _ =>
            constraints := constraints.push (← `(Noctium.Expr.eq $value $value))
        env := (id.getId.toString, t, value) :: env
      | `(nlcstmt| assert $value:nlexpr) =>
        constraints := constraints.push (← checkedExpression env value .bool)
      | `(nlcstmt| output $id:ident : $ty:nltype := $value:nlexpr) =>
        if outputInfo.any (fun p => p.1 == id.getId.toString) || inputInfo.any (fun p => p.1 == id.getId.toString) then
          throwErrorAt id "duplicate Noctium output '{id.getId}'"
        let t ← readTy ty
        let tt ← tyTerm t
        let value ← checkedExpression env value t
        let span ← spanTerm stmt
        outputs := outputs.push (← `({ name := $(stringTerm id.getId.toString), ty := $tt, value := $value, span := $span : Noctium.Output }))
        outputInfo := outputInfo ++ [(id.getId.toString, t)]
      | _ => throwErrorAt stmt "unsupported Noctium circuit statement"
    let span ← spanTerm stx
    let fullName := (← getCurrNamespace) ++ name.getId
    elabCommand (← `(def $name : Noctium.Circuit := { name := $(stringTerm fullName.toString), inputs := [$inputs,*], outputs := [$outputs,*], constraints := [$constraints,*], span := $span }))
    unsafe checkGeneratedCircuit fullName
    modifyEnv fun e => circuitRegistry.addEntry e {declName := fullName, inputs := inputInfo, publicInputs := publicInputInfo, outputs := outputInfo}
  | _ => throwUnsupportedSyntax

private def addReferences (env : Bindings) (items : List (String × Ty)) : CommandElabM Bindings := do
  let mut env := env
  for (name, ty) in items do
    if env.any (fun p => p.1 == name) then throwError "ambiguous circuit input/output '{name}'"
    env := (name, ty, ← `(@Noctium.Expr.ref $(← tyTerm ty) $(stringTerm name))) :: env
  pure env

/-- Check and quote a source expression against an explicit typed alias
environment. Authoring uses this to retain logical expressions across aggregate
output expansion without adding physical circuit outputs. -/
def quoteSourceExpression (env : List (String × Ty × TSyntax `term))
    (stx : TSyntax `nlexpr) (ty : Ty) : CommandElabM (TSyntax `term) :=
  checkedExpression env stx ty

private def addLogicalReferences (env : Bindings)
    (items : List (String × Ty × Name)) : CommandElabM Bindings := do
  let mut env := env
  for (name, ty, declaration) in items do
    if env.any (fun p => p.1 == name) then
      throwError "ambiguous logical output alias '{name}'"
    let value : TSyntax `term := ⟨mkIdent declaration⟩
    env := (name, ty, value) :: env
  pure env

private def addReferenceAs (env : Bindings) (sourceName internalName : String) (ty : Ty) :
    CommandElabM Bindings := do
  pure ((sourceName, ty, ← `(@Noctium.Expr.ref $(← tyTerm ty) $(stringTerm internalName))) :: env)

private structure EntryEffects where
  env : Bindings
  terms : Array (TSyntax `term) := #[]
  spans : Array (TSyntax `term) := #[]
  guards : Array (TSyntax `term) := #[]
  returns : Array (TSyntax `term) := #[]
  nextLocal : Nat := 0
  usedLocalNames : List String := []

private def explicitEffectGuard (effect : TSyntax `nleffect) : Option (TSyntax `nlexpr) :=
  match effect with
  | `(nleffect| when $condition:nlexpr $update:nlupdate) => some condition
  | `(nleffect| when $condition:nlexpr write $_state:ident := $_value:nlexpr) => some condition
  | `(nleffect| when $condition:nlexpr insert $_state:ident [ $_key:nlexpr ] := $_value:nlexpr) => some condition
  | `(nleffect| when $condition:nlexpr require $_value:nlexpr) => some condition
  | `(nleffect| when $condition:nlexpr read $_path:nlpath as $_dest:ident) => some condition
  | `(nleffect| when $condition:nlexpr member $_path:nlpath as $_dest:ident) => some condition
  | `(nleffect| when $condition:nlexpr $_operation:ident $_path:nlpath as $_dest:ident) => some condition
  | `(nleffect| when $condition:nlexpr increment $_state:ident by $_amount:num) => some condition
  | `(nleffect| when $condition:nlexpr increment $_state:ident [ $_key:nlexpr ] by $_amount:num) => some condition
  | `(nleffect| when $condition:nlexpr increment $_state:ident [ $_owner:nlexpr ] [ $_spender:nlexpr ] by $_amount:num) => some condition
  | `(nleffect| when $condition:nlexpr decrement $_state:ident by $_amount:num) => some condition
  | `(nleffect| when $condition:nlexpr decrement $_state:ident [ $_key:nlexpr ] by $_amount:num) => some condition
  | `(nleffect| when $condition:nlexpr decrement $_state:ident [ $_owner:nlexpr ] [ $_spender:nlexpr ] by $_amount:num) => some condition
  | `(nleffect| when $condition:nlexpr reset $_path:nlpath) => some condition
  | `(nleffect| when $condition:nlexpr pushFront $_path:nlpath := $_payload:nlleaves) => some condition
  | `(nleffect| when $condition:nlexpr popFront $_path:nlpath) => some condition
  | `(nleffect| when $condition:nlexpr remove $_path:nlpath) => some condition
  | _ => none

private def effectGuardTerm (env : Bindings) (parent : Option (TSyntax `term))
    (effect : TSyntax `nleffect) : CommandElabM (TSyntax `term) := do
  let explicit ← match explicitEffectGuard effect with
    | none => pure none
    | some condition => pure (some (← checkedExpression env condition .bool))
  match parent, explicit with
  | none, none => `(none)
  | none, some condition => `(some $condition)
  | some parent, none => `(some $parent)
  | some parent, some condition =>
    `(some (Noctium.Backend.Impact.activityGuardWithin $parent $condition))

private def chooseBranchLocalName (env : Bindings) (used : List String) (next : Nat) :
    String × Nat := Id.run do
  let mut candidateIndex := next
  let mut candidate := s!"noctium_if_local_{candidateIndex}"
  while env.any (fun binding => binding.1 == candidate) || used.contains candidate do
    candidateIndex := candidateIndex + 1
    candidate := s!"noctium_if_local_{candidateIndex}"
  return (candidate, candidateIndex + 1)

private partial def syntaxIdentifiers : Syntax → List String
  | .ident _ _ name _ => [name.toString]
  | .node _ _ children => children.toList.flatMap syntaxIdentifiers
  | _ => []

private def freshReadName (depth : Nat) (state : EntryEffects) (destination : TSyntax `ident) :
    CommandElabM (String × EntryEffects) := do
  ensureFresh state.env destination
  let sourceName := destination.getId.toString
  if depth == 0 then return (sourceName, state)
  let (internalName, nextLocal) :=
    chooseBranchLocalName state.env state.usedLocalNames state.nextLocal
  return (internalName, {state with nextLocal, usedLocalNames := internalName :: state.usedLocalNames})

private def bindReadName (state : EntryEffects) (sourceName internalName : String) (ty : Ty) :
    CommandElabM EntryEffects := do
  let env ← if sourceName == internalName then addReferences state.env [(sourceName, ty)]
    else addReferenceAs state.env sourceName internalName ty
  pure {state with env}

private def elaborateTreeRead (storage destination : TSyntax `ident)
    (keys : List (TSyntax `nlexpr))
    (treeSchema : LedgerValueType) (depth : Nat) (state : EntryEffects) : CommandElabM EntryEffects := do
  let (path, result) ← lowerTreePath state.env treeSchema keys
  let keys ← pathKeysTerm path
  match result with
  | .scalar valueTy => do
    let (readName, updated) ← freshReadName depth state destination
    let term ← `(Noctium.Effect.readPath $(stringTerm storage.getId.toString)
      $(stringTerm readName) $keys $(← tyTerm valueTy))
    let updated := {updated with terms := updated.terms.push term}
    bindReadName updated destination.getId.toString readName valueTy
  | .composite environment (.structure typeId) => do
    let leafNames ← match LedgerValueType.nativeLeafNames environment (.structure typeId) with
      | .ok names => pure names
      | .error message => throwErrorAt destination message
    let (readName, updated) ← freshReadName depth state destination
    let mut updated := updated
    let mut internalNames : List String := []
    for leafName in leafNames do
      let sourceName := destination.getId.toString ++ "_" ++ leafName
      if updated.env.any (fun binding => binding.1 == sourceName) then
        throwErrorAt destination s!"duplicate composite read field {sourceName}"
      let internalName ← if depth == 0 then pure sourceName else do
        let (candidate, nextLocal) := chooseBranchLocalName updated.env
          updated.usedLocalNames updated.nextLocal
        updated := {updated with nextLocal, usedLocalNames := candidate :: updated.usedLocalNames}
        pure candidate
      updated ← bindReadName updated sourceName internalName .native
      internalNames := internalNames ++ [internalName]
    let destinationsRaw ← stringListTerm (internalNames.map stringTerm)
    let destinations ← `(($destinationsRaw : List String))
    let typeTerm ← `(Noctium.Types.CompositeType.structure $(stringTerm typeId))
    let term ← `(Noctium.Effect.readCompositePath
      $(stringTerm storage.getId.toString) $(stringTerm readName) $keys $typeTerm $destinations)
    pure {updated with terms := updated.terms.push term}
  | .composite .. => throwErrorAt destination "native composite ledger reads require a named structure"
  | .map .. => throwErrorAt destination "nested map read must select a scalar or composite value"
  | .«list» .. => throwErrorAt destination "List reads require head or length"
  | .counter => do
    let (readName, updated) ← freshReadName depth state destination
    let pathTerm ← pathKeysTerm path
    let ty := Ty.uint (2 ^ 64 - 1)
    let term ← `(Noctium.Effect.counterRead
      $(stringTerm storage.getId.toString) $(stringTerm readName) $pathTerm)
    let updated := {updated with terms := updated.terms.push term}
    bindReadName updated destination.getId.toString readName ty

private def elaborateCounterAdjust (schema : List (String × StateKind))
    (storage : TSyntax `ident) (keys : List (TSyntax `nlexpr))
    (subtract : _root_.Bool) (amount : TSyntax `num) (state : EntryEffects) : CommandElabM EntryEffects := do
  let value := amount.getNat
  unless value ≤ 2 ^ 32 - 1 do
    throwErrorAt amount "Counter adjustment exceeds the native u32 immediate"
  let treeSchema ← treeStateSchema schema storage
  let path ← counterPathTerm state.env treeSchema keys
  let direction ← if subtract then `(Bool.true) else `(Bool.false)
  let term ← `(Noctium.Effect.counterAdjust
    $(stringTerm storage.getId.toString) $path $direction $(natTerm value))
  pure {state with terms := state.terms.push term}

private def elaborateListLength (schema : List (String × StateKind))
    (path : TSyntax `nlpath) (destinationId : TSyntax `ident)
    (depth : Nat) (state : EntryEffects) : CommandElabM EntryEffects := do
  let (storage, keys, _, _) ← lowerListPath schema state.env path
  let (readName, updated) ← freshReadName depth state destinationId
  let term ← `(Noctium.Effect.listLength
    $(stringTerm storage.getId.toString) $(stringTerm readName) $keys)
  let updated := {updated with terms := updated.terms.push term}
  bindReadName updated destinationId.getId.toString readName (.uint (2 ^ 64 - 1))

private def elaborateListHead (schema : List (String × StateKind))
    (path : TSyntax `nlpath) (destination : TSyntax `ident) (depth : Nat)
    (state : EntryEffects) : CommandElabM EntryEffects := do
  let (storage, keys, type, fieldNames) ← lowerListPath schema state.env path
  let (readName, updated) ← freshReadName depth state destination
  let mut updated := updated
  let mut internalNames : List String := []
  for fieldName in fieldNames do
    let sourceName := destination.getId.toString ++ "_" ++ fieldName
    if updated.env.any (fun binding => binding.1 == sourceName) then
      throwErrorAt destination s!"duplicate List head field {sourceName}"
    let internalName ← if depth == 0 then pure sourceName else do
      let (candidate, nextLocal) := chooseBranchLocalName updated.env
        updated.usedLocalNames updated.nextLocal
      updated := {updated with nextLocal, usedLocalNames := candidate :: updated.usedLocalNames}
      pure candidate
    updated ← bindReadName updated sourceName internalName .native
    internalNames := internalNames ++ [internalName]
  let typeTerm ← match type with
    | .structure id => `(Noctium.Types.CompositeType.structure $(stringTerm id))
    | _ => throwErrorAt path "List head currently requires a named structure"
  let destinationsRaw ← stringListTerm (internalNames.map stringTerm)
  let destinations ← `(($destinationsRaw : List String))
  let term ← `(Noctium.Effect.listHead
    $(stringTerm storage.getId.toString) $(stringTerm readName) $keys $typeTerm $destinations)
  pure {updated with terms := updated.terms.push term}

private def elaborateListPushFront (schema : List (String × StateKind))
    (path : TSyntax `nlpath) (payload : TSyntax `nlleaves)
    (state : EntryEffects) : CommandElabM EntryEffects := do
  let (storage, keys, type, fieldNames) ← lowerListPath schema state.env path
  let values ← match payload with
    | `(nlleaves| fields($items:nlexpr,*)) => pure items.getElems.toList
    | _ => throwErrorAt payload "pushFront expects fields(...)"
  unless values.length == fieldNames.length do
    throwErrorAt payload "pushFront field count does not match its checked List record"
  let values ← values.mapM fun value => checkedExpression state.env value Ty.native
  let typeTerm ← match type with
    | .structure id => `(Noctium.Types.CompositeType.structure $(stringTerm id))
    | _ => throwErrorAt path "pushFront currently requires a named structure"
  let nativeTy ← tyTerm Ty.native
  let valuesRaw ← nativeExprListTerm values
  let valuesTerm ← `(($valuesRaw : List (Noctium.Expr $nativeTy)))
  let term ← `(Noctium.Effect.listPushFront
    $(stringTerm storage.getId.toString) $keys $typeTerm $valuesTerm)
  pure {state with terms := state.terms.push term}

private def elaborateListPopFront (schema : List (String × StateKind))
    (path : TSyntax `nlpath) (state : EntryEffects) : CommandElabM EntryEffects := do
  let (storage, keys, _, _) ← lowerListPath schema state.env path
  let term ← `(Noctium.Effect.listPopFront $(stringTerm storage.getId.toString) $keys)
  pure {state with terms := state.terms.push term}

private def elaborateReset (schema : List (String × StateKind)) (path : TSyntax `nlpath)
    (state : EntryEffects) : CommandElabM EntryEffects := do
  let (storage, sourceKeys) ← sourcePathParts path
  let treeSchema ← treeStateSchema schema storage
  let (keys, value) ← lowerTreePath state.env treeSchema sourceKeys
  let keys ← pathKeysTerm keys
  match value with
  | .counter =>
    let term ← `(Noctium.Effect.counterReset $(stringTerm storage.getId.toString) $keys)
    pure {state with terms := state.terms.push term}
  | .«list» .. => do
    let _ ← lowerListPath schema state.env path
    let term ← `(Noctium.Effect.listReset $(stringTerm storage.getId.toString) $keys)
    pure {state with terms := state.terms.push term}
  | _ => throwErrorAt path "reset requires a Counter or List value"

private def elaborateCompositePathWrite (schema : List (String × StateKind))
    (storage : TSyntax `ident) (keys : List (TSyntax `nlexpr))
    (payload : TSyntax `nlleaves) (state : EntryEffects) : CommandElabM EntryEffects := do
  let treeSchema ← treeStateSchema schema storage
  let (path, result) ← lowerTreePath state.env treeSchema keys
  let (.composite environment type) := result
    | throwErrorAt payload "composite write must select a composite record"
  let fieldNames ← match LedgerValueType.nativeLeafNames environment type with
    | .ok names => pure names
    | .error message => throwErrorAt payload message
  let values ← match payload with
    | `(nlleaves| fields($items:nlexpr,*)) => pure items.getElems.toList
    | _ => throwErrorAt payload "composite write expects fields(...)"
  unless values.length == fieldNames.length do
    throwErrorAt payload "composite write field count does not match its checked layout"
  let lowered ← values.mapM fun value => checkedExpression state.env value Ty.native
  let pathTerm ← pathKeysTerm path
  let nativeTy ← tyTerm Ty.native
  let valueListRaw ← nativeExprListTerm lowered
  let valueList ← `(($valueListRaw : List (Noctium.Expr $nativeTy)))
  let typeTerm ← match type with
    | .structure id => `(Noctium.Types.CompositeType.structure $(stringTerm id))
    | _ => throwErrorAt payload "composite writes currently require a named structure"
  let term ← `(Noctium.Effect.writeCompositePath
    $(stringTerm storage.getId.toString) $pathTerm $typeTerm $valueList)
  pure {state with terms := state.terms.push term}

private def elaborateMapRemove (schema : List (String × StateKind))
    (path : TSyntax `nlpath) (state : EntryEffects) : CommandElabM EntryEffects := do
  let (storage, sourceKeys) ← sourcePathParts path
  let some finalKey := sourceKeys.getLast?
    | throwErrorAt path "remove requires at least one map key"
  let treeSchema ← treeStateSchema schema storage
  let parents := sourceKeys.take (sourceKeys.length - 1)
  let (parentTerms, parentSchema) ← lowerTreePath state.env treeSchema parents
  let .map keyTy _ := parentSchema
    | throwErrorAt path "remove parent path must select a map"
  let loweredFinalKey ← checkedExpression state.env finalKey keyTy
  let finalTerm ← `(Noctium.PathKey.mk $(← tyTerm keyTy) $loweredFinalKey)
  let keys ← pathKeysTerm (parentTerms ++ [finalTerm])
  let term ← `(Noctium.Effect.removePath $(stringTerm storage.getId.toString) $keys)
  pure {state with terms := state.terms.push term}

private def elaborateNamedPathRead (schema : List (String × StateKind))
    (operation : String) (path : TSyntax `nlpath) (destination : TSyntax `ident)
    (depth : Nat) (state : EntryEffects) : CommandElabM EntryEffects := do
  let (storage, sourceKeys) ← sourcePathParts path
  match operation with
  | "length" => elaborateListLength schema path destination depth state
  | "head" => elaborateListHead schema path destination depth state
  | "read" =>
    match schema.lookup storage.getId.toString with
    | some (.cell ty) => do
      unless sourceKeys.isEmpty do
        throwErrorAt path "cell reads do not accept a key path"
      let (readName, updated) ← freshReadName depth state destination
      let term ← `(Noctium.Effect.readCell
        $(stringTerm storage.getId.toString) $(stringTerm readName) $(← tyTerm ty))
      let updated := {updated with terms := updated.terms.push term}
      bindReadName updated destination.getId.toString readName ty
    | some (.map keyTy valueTy) => do
      let [key] := sourceKeys | throwErrorAt path "map reads require exactly one key"
      let (readName, updated) ← freshReadName depth state destination
      let loweredKey ← checkedExpression updated.env key keyTy
      let term ← `(Noctium.Effect.readMap
        $(stringTerm storage.getId.toString) $(stringTerm readName)
        $(← tyTerm keyTy) $(← tyTerm valueTy) $loweredKey)
      let updated := {updated with terms := updated.terms.push term}
      bindReadName updated destination.getId.toString readName valueTy
    | some (.tree treeSchema) =>
      elaborateTreeRead storage destination sourceKeys treeSchema depth state
    | some .opaqueString =>
      throwErrorAt storage "OpaqueString constructor metadata cannot be read by entrypoints"
    | _ => throwErrorAt storage "read requires a declared state cell or recursive tree"
  | "member" =>
    match schema.lookup storage.getId.toString with
    | some (.map keyTy valueTy) => do
      let [key] := sourceKeys | throwErrorAt path "map membership requires exactly one key"
      let (readName, updated) ← freshReadName depth state destination
      let loweredKey ← checkedExpression updated.env key keyTy
      let term ← `(Noctium.Effect.readMember
        $(stringTerm storage.getId.toString) $(stringTerm readName)
        $(← tyTerm keyTy) $(← tyTerm valueTy) $loweredKey)
      let updated := {updated with terms := updated.terms.push term}
      bindReadName updated destination.getId.toString readName .bool
    | some (.tree treeSchema) => do
      unless sourceKeys.length > 0 do
        throwErrorAt path "tree membership requires at least one key"
      let (keys, _) ← lowerTreePath state.env treeSchema sourceKeys
      let (readName, updated) ← freshReadName depth state destination
      let keys ← pathKeysTerm keys
      let term ← `(Noctium.Effect.memberPath
        $(stringTerm storage.getId.toString) $(stringTerm readName) $keys)
      let updated := {updated with terms := updated.terms.push term}
      bindReadName updated destination.getId.toString readName .bool
    | _ => throwErrorAt storage "membership requires a declared state map"
  | _ => throwErrorAt path "unsupported Noctium state query"

private def elaborateEffect (schema : List (String × StateKind))
    (parent : Option (TSyntax `term)) (depth : Nat) (state : EntryEffects)
    (effect : TSyntax `nleffect) : CommandElabM EntryEffects := do
  let guard ← effectGuardTerm state.env parent effect
  let span ← spanTerm effect
  let mut state := {state with
    spans := state.spans.push span
    guards := state.guards.push guard}
  match effect with
  | `(nleffect| $update:nlupdate)
  | `(nleffect| when $_:nlexpr $update:nlupdate) =>
    match update with
    | `(nlupdate| claimContractCall($address:nlexpr, $entryPointHash:nlexpr, $commitment:nlexpr)) => do
      let address ← checkedExpression state.env address (.bytes 32)
      let entryPointHash ← checkedExpression state.env entryPointHash (.bytes 32)
      let commitment ← checkedExpression state.env commitment .native
      let term ← `(Noctium.Effect.claimContractCall $address $entryPointHash $commitment)
      state := {state with terms := state.terms.push term}
    | _ => throwErrorAt update "unsupported Noctium update"
  | `(nleffect| require $value:nlexpr) =>
    let condition ← checkedExpression state.env value .bool
    let term ← `(Noctium.Effect.require $condition)
    state := {state with terms := state.terms.push term}
  | `(nleffect| when $_:nlexpr require $value:nlexpr) =>
    let condition ← checkedExpression state.env value .bool
    let term ← `(Noctium.Effect.require $condition)
    state := {state with terms := state.terms.push term}
  | `(nleffect| read $path:nlpath as $destination:ident)
  | `(nleffect| when $_:nlexpr read $path:nlpath as $destination:ident) =>
    state := ← elaborateNamedPathRead schema "read" path destination depth state
  | `(nleffect| member $path:nlpath as $destination:ident)
  | `(nleffect| when $_:nlexpr member $path:nlpath as $destination:ident) =>
    state := ← elaborateNamedPathRead schema "member" path destination depth state
  | `(nleffect| $operation:ident $path:nlpath as $destination:ident)
  | `(nleffect| when $_:nlexpr $operation:ident $path:nlpath as $destination:ident) =>
    state := ← elaborateNamedPathRead schema operation.getId.toString path destination depth state
  | `(nleffect| write $storage:ident := $value:nlexpr)
  | `(nleffect| when $_:nlexpr write $storage:ident := $value:nlexpr) => do
    let some (.cell ty) := schema.lookup storage.getId.toString
      | throwErrorAt storage "write requires a declared state cell"
    let loweredValue ← checkedExpression state.env value ty
    let term ← `(Noctium.Effect.writeCell
      $(stringTerm storage.getId.toString) $(← tyTerm ty) $loweredValue)
    state := {state with terms := state.terms.push term}
  | `(nleffect| insert $storage:ident [ $key:nlexpr ] := $value:nlexpr)
  | `(nleffect| when $_:nlexpr insert $storage:ident [ $key:nlexpr ] := $value:nlexpr) => do
    let some (.map keyTy valueTy) := schema.lookup storage.getId.toString
      | throwErrorAt storage "insert requires a declared state map"
    let loweredKey ← checkedExpression state.env key keyTy
    let loweredValue ← checkedExpression state.env value valueTy
    let term ← `(Noctium.Effect.writeMap
      $(stringTerm storage.getId.toString) $(← tyTerm keyTy) $(← tyTerm valueTy)
      $loweredKey $loweredValue)
    state := {state with terms := state.terms.push term}
  | `(nleffect| insert $storage:ident [$owner:nlexpr] := emptyMap) => do
    let schema ← treeStateSchema schema storage
    let (path, result) ← lowerTreePath state.env schema [owner]
    let .map _ _ := result | throwErrorAt effect "emptyMap assignment must select a map value"
    let keys ← pathKeysTerm path
    let term ← `(Noctium.Effect.emptyMapPath $(stringTerm storage.getId.toString) $keys)
    state := {state with terms := state.terms.push term}
  | `(nleffect| insert $storage:ident [ $key:nlexpr ] := $payload:nlleaves)
  | `(nleffect| write $storage:ident [ $key:nlexpr ] := $payload:nlleaves) => do
    state ← elaborateCompositePathWrite schema storage [key] payload state
  | `(nleffect| insert $storage:ident [ $owner:nlexpr ] [ $spender:nlexpr ] := $payload:nlleaves)
  | `(nleffect| write $storage:ident [ $owner:nlexpr ] [ $spender:nlexpr ] := $payload:nlleaves) => do
    state ← elaborateCompositePathWrite schema storage [owner, spender] payload state
  | `(nleffect| insert $storage:ident [$owner:nlexpr] [$spender:nlexpr] := $value:nlexpr)
  | `(nleffect| write $storage:ident [$owner:nlexpr] [$spender:nlexpr] := $value:nlexpr) => do
    let schema ← treeStateSchema schema storage
    let (path, result) ← lowerTreePath state.env schema [owner, spender]
    let .scalar ty := result | throwErrorAt effect "nested scalar write must select a scalar value"
    let loweredValue ← checkedExpression state.env value ty
    let keys ← pathKeysTerm path
    let term ← if effect.raw[0].getAtomVal == "insert" then
      `(Noctium.Effect.insertPath $(stringTerm storage.getId.toString) $keys $(← tyTerm ty) $loweredValue)
      else `(Noctium.Effect.writePath $(stringTerm storage.getId.toString) $keys $(← tyTerm ty) $loweredValue)
    state := {state with terms := state.terms.push term}
  | `(nleffect| increment $storage:ident by $amount:num)
  | `(nleffect| when $_:nlexpr increment $storage:ident by $amount:num) =>
    state := ← elaborateCounterAdjust schema storage [] Bool.false amount state
  | `(nleffect| increment $storage:ident [ $key:nlexpr ] by $amount:num)
  | `(nleffect| when $_:nlexpr increment $storage:ident [ $key:nlexpr ] by $amount:num) =>
    state := ← elaborateCounterAdjust schema storage [key] Bool.false amount state
  | `(nleffect| increment $storage:ident [ $owner:nlexpr ] [ $spender:nlexpr ] by $amount:num)
  | `(nleffect| when $_:nlexpr increment $storage:ident [ $owner:nlexpr ] [ $spender:nlexpr ] by $amount:num) =>
    state := ← elaborateCounterAdjust schema storage [owner, spender] Bool.false amount state
  | `(nleffect| decrement $storage:ident by $amount:num)
  | `(nleffect| when $_:nlexpr decrement $storage:ident by $amount:num) =>
    state := ← elaborateCounterAdjust schema storage [] Bool.true amount state
  | `(nleffect| decrement $storage:ident [ $key:nlexpr ] by $amount:num)
  | `(nleffect| when $_:nlexpr decrement $storage:ident [ $key:nlexpr ] by $amount:num) =>
    state := ← elaborateCounterAdjust schema storage [key] Bool.true amount state
  | `(nleffect| decrement $storage:ident [ $owner:nlexpr ] [ $spender:nlexpr ] by $amount:num)
  | `(nleffect| when $_:nlexpr decrement $storage:ident [ $owner:nlexpr ] [ $spender:nlexpr ] by $amount:num) =>
    state := ← elaborateCounterAdjust schema storage [owner, spender] Bool.true amount state
  | `(nleffect| pushFront $path:nlpath := $payload:nlleaves)
  | `(nleffect| when $_:nlexpr pushFront $path:nlpath := $payload:nlleaves) =>
    state := ← elaborateListPushFront schema path payload state
  | `(nleffect| popFront $path:nlpath)
  | `(nleffect| when $_:nlexpr popFront $path:nlpath) =>
    state := ← elaborateListPopFront schema path state
  | `(nleffect| remove $path:nlpath)
  | `(nleffect| when $_:nlexpr remove $path:nlpath) =>
    state := ← elaborateMapRemove schema path state
  | `(nleffect| reset $path:nlpath)
  | `(nleffect| when $_:nlexpr reset $path:nlpath) =>
    state := ← elaborateReset schema path state
  | `(nleffect| absent $storage:ident [ $key:nlexpr ]) => do
    if depth > 0 then throwErrorAt effect "absent queries inside if/else blocks are unsupported"
    let some (.map keyTy _) := schema.lookup storage.getId.toString
      | throwErrorAt storage "absent requires a declared state map"
    let loweredKey ← checkedExpression state.env key keyTy
    let term ← `(Noctium.Effect.requireAbsent
      $(stringTerm storage.getId.toString) $(← tyTerm keyTy) $loweredKey)
    state := {state with terms := state.terms.push term}
  | _ => throwErrorAt effect "unsupported Noctium state effect"
  pure state

private partial def elaborateStatements (schema : List (String × StateKind))
    (parent : Option (TSyntax `term)) (depth : Nat)
    (statements : Array (TSyntax `nlstatement)) (initial : EntryEffects) :
    CommandElabM EntryEffects := do
  let mut state := initial
  for statement in statements do
    match statement with
    | `(nlstatement| $effect:nleffect) =>
      state ← elaborateEffect schema parent depth state effect
    | `(nlstatement| if $condition:nlexpr then { $thenStatements:nlstatement* }
        else { $elseStatements:nlstatement* }) => do
      let condition ← checkedExpression state.env condition .bool
      let parentExpression ← match parent with
        | some expression => pure expression
        | none => `(Noctium.Expr.bool Bool.true)
      let thenPath : Option (TSyntax `term) := some (←
        `(Noctium.Backend.Impact.activityGuardWithin
          $parentExpression $condition))
      let negated ← `(Noctium.Expr.eq $condition (Noctium.Expr.bool Bool.false))
      let elsePath : Option (TSyntax `term) := some (←
        `(Noctium.Backend.Impact.activityGuardWithin
          $parentExpression $negated))
      let branchEnv := state.env
      let afterThen ← elaborateStatements schema thenPath (depth + 1) thenStatements state
      let afterElse ← elaborateStatements schema elsePath (depth + 1) elseStatements
        {afterThen with env := branchEnv}
      state := {afterElse with env := branchEnv}
    | _ => throwErrorAt statement "unsupported Noctium state statement"
  pure state

private def elaborateReturns (statements : Array (TSyntax `nlreturn))
    (initial : EntryEffects) : CommandElabM EntryEffects := do
  let mut state := initial
  let mut labels : List String := []
  for statement in statements do
    match statement with
    | `(nlreturn| return $label:ident : $returnTy:nltype := $value:nlexpr) => do
      let labelName := label.getId.toString
      if labels.contains labelName then
        throwErrorAt label "duplicate entry return label '{labelName}'"
      if state.env.any (fun binding => binding.1 == labelName) then
        throwErrorAt label "entry return label '{labelName}' collides with an input or read binding"
      labels := labelName :: labels
      let ty ← readTy returnTy
      let value ← checkedExpression state.env value ty
      let span ← spanTerm statement
      state := {state with returns := state.returns.push (← `({
        name := $(stringTerm labelName), ty := $(← tyTerm ty), value := $value,
        span := $span : Noctium.Output }))}
    | _ => throwErrorAt statement "unsupported Noctium entry return"
  pure state

private def elaborateNamedRecord (contractName : Name) (record : TSyntax `ident)
    (recordFields : Array (TSyntax `nlcompositefield)) (owner : Syntax) :
    CommandElabM (Types.CompositeEnv × Types.CompositeType × TSyntax `term × TSyntax `term) := do
  let typeId := contractName.toString ++ "." ++ record.getId.toString
  let mut fieldTerms : Array (TSyntax `term) := #[]
  let mut fieldValues : List Noctium.Types.Field := []
  for field in recordFields do
    match field with
    | `(nlcompositefield| $fieldName:ident : $fieldType:nltype) => do
      let fieldTy ← readTy fieldType
      let fieldNameString := fieldName.getId.toString
      fieldValues := fieldValues ++ [{name := fieldNameString, type := .scalar fieldTy}]
      let fieldTyTerm ← tyTerm fieldTy
      let fieldTypeTerm ← `(Noctium.Types.CompositeType.scalar $fieldTyTerm)
      let fieldSpan ← spanTerm field
      fieldTerms := fieldTerms.push (← `({ name := $(stringTerm fieldNameString), type := $fieldTypeTerm, span := $fieldSpan : Noctium.Types.Field }))
    | _ => throwErrorAt field "unsupported composite record field"
  let structSpan ← spanTerm owner
  let structureTerm ← `({ id := $(stringTerm typeId), fields := [$fieldTerms,*], span := $structSpan : Noctium.Types.StructDecl })
  let environmentTerm ← `({ structures := [$structureTerm] : Noctium.Types.CompositeEnv })
  let compositeType := Types.CompositeType.structure typeId
  let compositeTypeTerm ← `(Noctium.Types.CompositeType.structure $(stringTerm typeId))
  let environment : Types.CompositeEnv := {structures := [{id := typeId, fields := fieldValues}]}
  pure (environment, compositeType, environmentTerm, compositeTypeTerm)

private def elaborateConstructor (source : TSyntax `nlstate)
    (schema : List (String × StateKind)) : CommandElabM (TSyntax `term) := do
  let `(nlstate| constructor($parameters:nlconstructorparam,*) where $initializers:nlconstructorinit* end) := source
    | throwErrorAt source "invalid Noctium constructor declaration"
  let mut parameterTerms : Array (TSyntax `term) := #[]
  let mut scalarBindings : Bindings := []
  let mut opaqueParameters : List String := []
  let mut parameterNames : List String := []
  for parameter in parameters.getElems.toList do
    let (name, parameterType, typeTerm) ← match parameter with
      | `(nlconstructorparam| $id:ident : OpaqueString) => do
        let name := id.getId.toString
        pure (name, ConstructorType.opaqueString, ← `(Noctium.ConstructorType.opaqueString))
      | `(nlconstructorparam| $id:ident : $sourceTy:nltype) => do
        let name := id.getId.toString
        let ty ← readTy sourceTy
        pure (name, ConstructorType.scalar ty,
          ← `(Noctium.ConstructorType.scalar $(← tyTerm ty)))
      | _ => throwErrorAt parameter "unsupported constructor parameter"
    if parameterNames.contains name then throwErrorAt parameter s!"duplicate constructor parameter '{name}'"
    parameterNames := name :: parameterNames
    if parameterType == .opaqueString then
      opaqueParameters := name :: opaqueParameters
    else
      let .scalar ty := parameterType | throwErrorAt parameter "invalid scalar constructor parameter"
      let reference ← `(@Noctium.Expr.ref $(← tyTerm ty) $(stringTerm name))
      scalarBindings := (name, ty, reference) :: scalarBindings
    parameterTerms := parameterTerms.push (← `(Noctium.ConstructorParameter.mk $(stringTerm name) $typeTerm))
  let mut initializerTerms : Array (TSyntax `term) := #[]
  let mut initializedNames : List String := []
  for initializer in initializers do
    let (destination, initializerType, initializerValue) ← match initializer with
      | `(nlconstructorinit| initialize $stateName:ident := $value:nlexpr) => do
        let destination := stateName.getId.toString
        match schema.find? (·.1 == destination) with
        | some (_, .opaqueString) =>
          match value with
          | `(nlexpr| $parameter:ident) =>
            let parameterName := parameter.getId.toString
            unless opaqueParameters.contains parameterName do
              throwErrorAt value "OpaqueString initializer must reference an OpaqueString parameter or literal"
            let typeTerm ← `(Noctium.ConstructorType.opaqueString)
            let valueTerm ← `(Noctium.ConstructorValue.opaqueStringParameter $(stringTerm parameterName))
            pure (destination, ConstructorType.opaqueString, (typeTerm, valueTerm))
          | _ => throwErrorAt value "OpaqueString initializer must reference an OpaqueString parameter or literal"
        | some (_, .cell ty) => do
          let expression ← checkedExpression scalarBindings value ty
          let typeTerm ← `(Noctium.ConstructorType.scalar $(← tyTerm ty))
          let valueTerm ← `(Noctium.ConstructorValue.scalar $expression)
          pure (destination, ConstructorType.scalar ty, (typeTerm, valueTerm))
        | some _ => throwErrorAt stateName "constructor initializers must target cells"
        | none => throwErrorAt stateName s!"constructor initializes unknown state '{destination}'"
      | `(nlconstructorinit| initialize $stateName:ident := $literal:str) => do
        let destination := stateName.getId.toString
        match schema.find? (·.1 == destination) with
        | some (_, .opaqueString) => do
          let typeTerm ← `(Noctium.ConstructorType.opaqueString)
          let valueTerm ← `(Noctium.ConstructorValue.opaqueStringLiteral $(stringTerm literal.getString))
          pure (destination, ConstructorType.opaqueString, (typeTerm, valueTerm))
        | some _ => throwErrorAt literal "string literals initialize only OpaqueString cells"
        | none => throwErrorAt stateName s!"constructor initializes unknown state '{destination}'"
      | _ => throwErrorAt initializer "unsupported constructor initializer"
    if initializedNames.contains destination then
      throwErrorAt initializer s!"duplicate constructor initializer for '{destination}'"
    initializedNames := destination :: initializedNames
    let (typeTerm, valueTerm) := initializerValue
    initializerTerms := initializerTerms.push
      (← `(Noctium.ConstructorInitializer.mk $(stringTerm destination) $typeTerm $valueTerm))
  let parameters := parameterTerms
  let initializers := initializerTerms
  `(some ({parameters := [$parameters,*], initializers := [$initializers,*] : Noctium.Constructor}))

@[command_elab contractCommand] unsafe def elabContract : CommandElab := fun stx => do
  match stx with
  | `(noctium_contract $name:ident where $states:nlstate* $entries:nlentry* end) =>
    let mut stateTerms : Array (TSyntax `term) := #[]
    let mut schema : List (String × StateKind) := []
    let mut concreteSchema : List StateDecl := []
    let mut stateDeclarations : Array (TSyntax `nlstate) := #[]
    let mut constructorSyntax? : Option (TSyntax `nlstate) := none
    for state in states do
      match state with
      | `(nlstate| constructor($_:nlconstructorparam,*) where $_:nlconstructorinit* end) =>
        if constructorSyntax?.isSome then throwErrorAt state "duplicate constructor declaration"
        constructorSyntax? := some state
      | _ => stateDeclarations := stateDeclarations.push state
    for state in stateDeclarations do
      let (id, kind, term) ← match state with
        | `(nlstate| sealed cell $id:ident : OpaqueString) =>
          pure (id, StateKind.opaqueString, ← `(Noctium.StateKind.opaqueString))
        | `(nlstate| sealed cell $id:ident : $ty:nltype) => do
          let t ← readTy ty
          pure (id, StateKind.cell t, ← `(Noctium.StateKind.cell $(← tyTerm t)))
        | `(nlstate| cell $id:ident : $ty:nltype) => do
          let t ← readTy ty
          pure (id, StateKind.cell t, ← `(Noctium.StateKind.cell $(← tyTerm t)))
        | `(nlstate| map $id:ident : $key:nltype => $value:nltype) => do
          let k ← readTy key
          let v ← readTy value
          pure (id, StateKind.map k v, ← `(Noctium.StateKind.map $(← tyTerm k) $(← tyTerm v)))
        | `(nlstate| counter $id:ident) =>
          pure (id, StateKind.tree .counter, ← `(Noctium.StateKind.tree Noctium.LedgerValueType.counter))
        | `(nlstate| tree $id:ident : $key:nltype => Counter) => do
          let keyTy ← readTy key
          let keyTerm ← tyTerm keyTy
          let valueSchema := LedgerValueType.map keyTy .counter
          pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree
            (Noctium.LedgerValueType.map $keyTerm Noctium.LedgerValueType.counter)))
        | `(nlstate| tree $id:ident : $outer:nltype => $inner:nltype => Counter) => do
          let outerTy ← readTy outer
          let innerTy ← readTy inner
          let outerTerm ← tyTerm outerTy
          let innerTerm ← tyTerm innerTy
          let valueSchema := LedgerValueType.map outerTy (.map innerTy .counter)
          pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree
            (Noctium.LedgerValueType.map $outerTerm
              (Noctium.LedgerValueType.map $innerTerm Noctium.LedgerValueType.counter))))
        | `(nlstate| tree $id:ident : $key:nltype => struct $record:ident { $recordFields:nlcompositefield* }) => do
          let keyTy ← readTy key
          let contractName := (← getCurrNamespace) ++ name.getId
          let (environment, compositeType, environmentTerm, compositeTypeTerm) ←
            elaborateNamedRecord contractName record recordFields state
          let valueSchema := LedgerValueType.map keyTy (.composite environment compositeType)
          let valueTerm ← `(Noctium.LedgerValueType.map $(← tyTerm keyTy)
            (Noctium.LedgerValueType.composite $environmentTerm $compositeTypeTerm))
          pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree $valueTerm))
        | `(nlstate| tree $id:ident : $outer:nltype => $inner:nltype => struct $record:ident { $recordFields:nlcompositefield* }) => do
          let outerTy ← readTy outer
          let innerTy ← readTy inner
          let contractName := (← getCurrNamespace) ++ name.getId
          let (environment, compositeType, environmentTerm, compositeTypeTerm) ←
            elaborateNamedRecord contractName record recordFields state
          let valueSchema := LedgerValueType.map outerTy
            (.map innerTy (.composite environment compositeType))
          let outerTerm ← tyTerm outerTy
          let innerTerm ← tyTerm innerTy
          let valueTerm ← `(Noctium.LedgerValueType.map $outerTerm
            (Noctium.LedgerValueType.map $innerTerm
              (Noctium.LedgerValueType.composite $environmentTerm $compositeTypeTerm)))
          pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree $valueTerm))
        | `(nlstate| $listKind:ident $id:ident : struct $record:ident { $recordFields:nlcompositefield* }) => do
          unless listKind.getId.toString == "list" do
            throwErrorAt listKind "unsupported recursive List state declaration"
          let contractName := (← getCurrNamespace) ++ name.getId
          let (environment, compositeType, environmentTerm, compositeTypeTerm) ←
            elaborateNamedRecord contractName record recordFields state
          let valueSchema := LedgerValueType.«list» environment compositeType
          let valueTerm ← `(Noctium.LedgerValueType.«list» $environmentTerm $compositeTypeTerm)
          pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree $valueTerm))
        | `(nlstate| tree $id:ident : $key:nltype => $listKind:ident struct $record:ident { $recordFields:nlcompositefield* }) => do
          unless listKind.getId.toString == "List" do
            throwErrorAt listKind "unsupported recursive tree value declaration"
          let keyTy ← readTy key
          let contractName := (← getCurrNamespace) ++ name.getId
          let (environment, compositeType, environmentTerm, compositeTypeTerm) ←
            elaborateNamedRecord contractName record recordFields state
          let valueSchema := LedgerValueType.map keyTy (.«list» environment compositeType)
          let valueTerm ← `(Noctium.LedgerValueType.map $(← tyTerm keyTy)
            (Noctium.LedgerValueType.«list» $environmentTerm $compositeTypeTerm))
          pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree $valueTerm))
        | `(nlstate| tree $id:ident : $outer:nltype => $inner:nltype => $listKind:ident struct $record:ident { $recordFields:nlcompositefield* }) => do
          unless listKind.getId.toString == "List" do
            throwErrorAt listKind "unsupported recursive tree value declaration"
          let outerTy ← readTy outer
          let innerTy ← readTy inner
          let contractName := (← getCurrNamespace) ++ name.getId
          let (environment, compositeType, environmentTerm, compositeTypeTerm) ←
            elaborateNamedRecord contractName record recordFields state
          let valueSchema := LedgerValueType.map outerTy
            (.map innerTy (.«list» environment compositeType))
          let outerTerm ← tyTerm outerTy
          let innerTerm ← tyTerm innerTy
          let valueTerm ← `(Noctium.LedgerValueType.map $outerTerm
            (Noctium.LedgerValueType.map $innerTerm
              (Noctium.LedgerValueType.«list» $environmentTerm $compositeTypeTerm)))
          pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree $valueTerm))
        | `(nlstate| tree $id:ident : $outer:nltype => $inner:nltype => $value:nltype) => do
          let outerTy ← readTy outer
          let innerTy ← readTy inner
          let valueTy ← readTy value
          let valueSchema := LedgerValueType.map outerTy
            (.map innerTy (.scalar valueTy))
          let outerTerm ← tyTerm outerTy
          let innerTerm ← tyTerm innerTy
          let valueTerm ← tyTerm valueTy
          pure (id, StateKind.tree valueSchema, ←
            `(Noctium.StateKind.tree
              (Noctium.LedgerValueType.map $outerTerm
                (Noctium.LedgerValueType.map $innerTerm
                  (Noctium.LedgerValueType.scalar $valueTerm)))))
        | _ => throwErrorAt state "unsupported Noctium state declaration"
      if schema.any (fun p => p.1 == id.getId.toString) then throwErrorAt id "duplicate Noctium state"
      schema := schema ++ [(id.getId.toString, kind)]
      concreteSchema := concreteSchema ++ [{name := id.getId.toString, kind := kind, «sealed» := state.raw[0].getAtomVal == "sealed"}]
      if state.raw[0].getAtomVal == "sealed" then
        stateTerms := stateTerms.push (← `(Noctium.StateDecl.mk $(stringTerm id.getId.toString)
          $term Bool.true $(← spanTerm state)))
      else
        stateTerms := stateTerms.push (← `(Noctium.StateDecl.mk $(stringTerm id.getId.toString)
          $term Bool.false $(← spanTerm state)))
    let constructorTerm ← match constructorSyntax? with
      | none => `(none)
      | some ctor => elaborateConstructor ctor schema
    let mut entryTerms : Array (TSyntax `term) := #[]
    let mut entryNames : List Name := []
    for entryStx in entries do
      match entryStx with
      | `(nlentry| entry $id:ident uses $circuit:ident $argumentKeyword:ident [$args,*] where $statements:nlstatement* $returns:nlreturn* end) =>
        unless argumentKeyword.getId == `arguments do
          throwErrorAt argumentKeyword "expected 'arguments' before the call input list"
        if entryNames.contains id.getId then throwErrorAt id "duplicate Noctium entrypoint"
        entryNames := id.getId :: entryNames
        let registry := circuitRegistry.getState (← getEnv)
        let fullName := (← getCurrNamespace) ++ circuit.getId
        let some info := registry.find? (fun i => i.declName == fullName || i.declName == circuit.getId)
          | throwErrorAt circuit "entrypoint requires a registered Noctium circuit"
        let env ← addReferences [] (info.inputs ++ info.outputs)
        let env ← addLogicalReferences env info.logicalOutputs
        let reserved := statements.toList.flatMap (fun statement => syntaxIdentifiers statement.raw) ++
          returns.toList.flatMap (fun statement => syntaxIdentifiers statement.raw)
        let initial : EntryEffects := {env, usedLocalNames := reserved}
        let lowered ← elaborateStatements schema none 0 statements initial
        let lowered ← elaborateReturns returns lowered
        let circuitTerm := mkIdent info.declName
        let callInputTerms := args.getElems.map fun argument => stringTerm argument.getId.toString
        let entryName := stringTerm id.getId.toString
        let entrySpan ← spanTerm entryStx
        entryTerms := entryTerms.push (← `(Noctium.Entrypoint.mk $entryName $circuitTerm
          [$callInputTerms,*] [$lowered.terms,*] [$lowered.returns,*] [] $entrySpan
          [$lowered.spans,*] [$lowered.guards,*]))
      | `(nlentry| entry $id:ident uses $circuit:ident where $statements:nlstatement* $returns:nlreturn* end) =>
        if entryNames.contains id.getId then throwErrorAt id "duplicate Noctium entrypoint"
        entryNames := id.getId :: entryNames
        let registry := circuitRegistry.getState (← getEnv)
        let fullName := (← getCurrNamespace) ++ circuit.getId
        let some info := registry.find? (fun i => i.declName == fullName || i.declName == circuit.getId)
          | throwErrorAt circuit "entrypoint requires a registered Noctium circuit"
        let env ← addReferences [] (info.inputs ++ info.outputs)
        let env ← addLogicalReferences env info.logicalOutputs
        let reserved := statements.toList.flatMap (fun statement => syntaxIdentifiers statement.raw) ++
          returns.toList.flatMap (fun statement => syntaxIdentifiers statement.raw)
        let initial : EntryEffects := {env, usedLocalNames := reserved}
        let lowered ← elaborateStatements schema none 0 statements initial
        let lowered ← elaborateReturns returns lowered
        let circuitTerm := mkIdent info.declName
        entryTerms := entryTerms.push (← `({ name := $(stringTerm id.getId.toString), circuit := $circuitTerm, effects := [$lowered.terms,*], returns := [$lowered.returns,*], span := $(← spanTerm entryStx), effectSpans := [$lowered.spans,*], effectGuards := [$lowered.guards,*] : Noctium.Entrypoint }))
      | `(nlentry| entry $id:ident from $source:ident entry $exportName:str end) =>
        if entryNames.contains id.getId then throwErrorAt id "duplicate Noctium entrypoint"
        entryNames := id.getId :: entryNames
        let sourceName ← liftCoreM <| resolveGlobalConstNoOverload source
        let program ← evalConstCheck Helpers.Program ``Helpers.Program sourceName
        let value ← match Witness.compileStateEntrypoint program exportName.getString concreteSchema with
          | .ok value => pure value
          | .error diagnostic => failDisclosure diagnostic *> throwError "structured ledger compilation failed"
        let localCircuitName := name.getId ++ id.getId ++ `circuit
        let fullCircuitName := (← getCurrNamespace) ++ localCircuitName
        let circuitId := mkIdent localCircuitName
        let circuitName := stringTerm fullCircuitName.toString
        let sourceTerm := mkIdent sourceName
        elabCommand (← `(def $circuitId : Noctium.Circuit :=
          match Noctium.Witness.compileStateEntrypoint $sourceTerm $exportName [$stateTerms,*] with
          | .ok compiledEntry => {compiledEntry.circuit with name := $circuitName}
          | .error _ => {name := $circuitName}))
        unsafe checkGeneratedCircuit fullCircuitName
        modifyEnv fun env => circuitRegistry.addEntry env {
          declName := fullCircuitName
          inputs := value.circuit.inputs.map fun input => (input.name, input.ty)
          publicInputs := (value.circuit.inputs.filter (·.visibility == .public)).map fun input => (input.name, input.ty)
          outputs := []
          stateProgram? := some (sourceName, exportName.getString)}
        let circuitTerm := mkIdent fullCircuitName
        entryTerms := entryTerms.push (← `(
          match Noctium.Witness.compileStateEntrypoint $sourceTerm $exportName [$stateTerms,*] with
          | .ok compiledEntry => {compiledEntry with name := $(stringTerm id.getId.toString), circuit := $circuitTerm}
          | .error _ => {name := $(stringTerm id.getId.toString), circuit := $circuitTerm}))
      | _ => throwErrorAt entryStx "unsupported Noctium entrypoint"
    let span ← spanTerm stx
    let fullName := (← getCurrNamespace) ++ name.getId
    elabCommand (← `(def $name : Noctium.Contract := Noctium.Contract.mk
      $(stringTerm fullName.toString) [$stateTerms,*] $constructorTerm [$entryTerms,*] $span))
    unsafe checkGeneratedContract fullName
    modifyEnv fun e => contractRegistry.addEntry e fullName
  | _ => throwUnsupportedSyntax

/-- Structured source declarations support forward references and lexical IDs.
The generated value enters exactly the same circuit registry and compiler. -/
scoped syntax (name := helperCircuitCommand) "noctium_helper_circuit" ident
  "from" ident "entry" str : command

open scoped Noctium

@[command_elab helperCircuitCommand] unsafe def elabHelperCircuit : CommandElab := fun stx => do
  match stx with
  | `(noctium_helper_circuit $name:ident from $source:ident entry $exportName:str) =>
    let sourceName ← liftCoreM <| resolveGlobalConstNoOverload source
    let program ← evalConstCheck Helpers.Program ``Helpers.Program sourceName
    match ComponentDisclosure.checkProgram program exportName.getString with
    | .ok _ => pure ()
    | .error diagnostic => failDisclosure diagnostic
    let value ← match Helpers.compile program exportName.getString with
      | .ok value => pure value
      | .error diagnostic => failDisclosure diagnostic *> throwError "helper compilation failed"
    let fullName := (← getCurrNamespace) ++ name.getId
    let sourceTerm := mkIdent sourceName
    elabCommand (← `(def $name : Noctium.Circuit :=
      match Noctium.Helpers.compile $sourceTerm $exportName with
      | .ok value => {value with name := $(stringTerm fullName.toString)}
      | .error _ => {name := $(stringTerm fullName.toString)}))
    checkGeneratedCircuit fullName
    modifyEnv fun env => circuitRegistry.addEntry env {
      declName := fullName
      inputs := value.inputs.map fun input => (input.name, input.ty)
      publicInputs := (value.inputs.filter (·.visibility == .public)).map fun input => (input.name, input.ty)
      outputs := value.outputs.map fun item => (item.name, item.ty)
      sourceProgram? := some (sourceName, exportName.getString)
    }
  | _ => throwUnsupportedSyntax

/-- Compile a generic source export into one registered monomorphic helper program.
The compiler later checks this generated concrete program again. -/
scoped syntax (name := genericHelperCircuitCommand) "noctium_generic_circuit" ident
  "from" ident "entry" str : command

open scoped Noctium

@[command_elab genericHelperCircuitCommand] unsafe def elabGenericHelperCircuit : CommandElab := fun stx => do
  match stx with
  | `(noctium_generic_circuit $name:ident from $source:ident entry $exportName:str) => do
    let sourceName ← liftCoreM <| resolveGlobalConstNoOverload source
    let sourceProgram ← evalConstCheck Helpers.Specialization.Program
      ``Helpers.Specialization.Program sourceName
    let specialized ← match Helpers.Specialization.specialize sourceProgram exportName.getString with
      | .ok result => pure result
      | .error diagnostic => failDisclosure diagnostic *> throwError "generic helper specialization failed"
    match ComponentDisclosure.checkProgram specialized.program specialized.exportName with
    | .ok _ => pure ()
    | .error diagnostic => failDisclosure diagnostic
    let value ← match Helpers.compile specialized.program specialized.exportName with
      | .ok value => pure value
      | .error diagnostic => failDisclosure diagnostic *> throwError "generic helper compilation failed"
    let fullName := (← getCurrNamespace) ++ name.getId.eraseMacroScopes
    let programName := fullName ++ `specializedProgram
    if (← getEnv).contains programName then
      throwErrorAt name "generated specialized program name collides with an existing declaration"
    let sourceTerm := mkIdent sourceName
    let programIdent := mkIdent programName
    elabCommand (← `(def $programIdent : Noctium.Helpers.Program :=
      match Noctium.Helpers.Specialization.specialize $sourceTerm $exportName with
      | .ok result => result.program
      | .error _ => {}))
    let programTerm := mkIdent programName
    elabCommand (← `(def $name : Noctium.Circuit :=
      match Noctium.Helpers.compile $programTerm $exportName with
      | .ok value => {value with name := $(stringTerm fullName.toString)}
      | .error _ => {name := $(stringTerm fullName.toString)}))
    checkGeneratedCircuit fullName
    let signatureText := (Lean.toJson specialized.signatureArtifact).pretty
    modifyEnv fun env => circuitRegistry.addEntry env {
      declName := fullName
      inputs := value.inputs.map fun input => (input.name, input.ty)
      publicInputs := (value.inputs.filter (·.visibility == .public)).map fun input => (input.name, input.ty)
      outputs := value.outputs.map fun item => (item.name, item.ty)
      sourceProgram? := some (programName, specialized.exportName)
      specializationArtifact? := some signatureText
    }
  | _ => throwUnsupportedSyntax

/-- Explicit source spelling for component-aware helper circuits. It compiles
through the same checked helper IR and mandatory origin pass. -/
scoped syntax (name := componentCircuitCommand) "noctium_component_circuit" ident
  "from" ident "entry" str : command

@[command_elab componentCircuitCommand] unsafe def elabComponentCircuit : CommandElab := fun stx => do
  match stx with
  | `(noctium_component_circuit $name:ident from $source:ident entry $exportName:str) =>
    elabHelperCircuit (← `(command| noctium_helper_circuit $name from $source entry $exportName))
  | _ => throwUnsupportedSyntax

/-- Portable host-only execution plans never enter the native circuit registry. -/
scoped syntax (name := controlPlanCommand) "noctium_control" ident
  "from" ident "entry" str : command

open scoped Noctium

@[command_elab controlPlanCommand] unsafe def elabControlPlan : CommandElab := fun stx => do
  match stx with
  | `(noctium_control $name:ident from $source:ident entry $exportName:str) =>
    let sourceName ← liftCoreM <| resolveGlobalConstNoOverload source
    let program ← evalConstCheck Helpers.Program ``Helpers.Program sourceName
    match Control.compile program exportName.getString with
    | .error diagnostic => throwErrorAt stx diagnostic.message
    | .ok _ => pure ()
    let sourceTerm := mkIdent sourceName
    elabCommand (← `(def $name : Lean.Json :=
      match Noctium.Control.compile $sourceTerm $exportName with
      | .ok value => value
      | .error _ => Lean.Json.null))
    let fullName := (← getCurrNamespace) ++ name.getId
    modifyEnv fun env => controlRegistry.addEntry env fullName
  | _ => throwUnsupportedSyntax

scoped syntax (name := witnessCircuitCommand) "noctium_witness_circuit" ident
  "from" ident "entry" str : command

/-- Share checked registration between generated authoring programs and explicit IR sources. -/
unsafe def registerWitnessCircuit (name : Syntax) (sourceName : Name) (exportName : String)
    (outputName : String := "") (observationArtifact? : Option String := none)
    (logicalOutputs : List (String × Ty × Name) := []) : CommandElabM Unit := do
    let program ← evalConstCheck Helpers.Program ``Helpers.Program sourceName
    let fullName := (← getCurrNamespace) ++ name.getId
    let compiled ← match Witness.compile program exportName fullName.toString outputName with
      | .ok value => pure value
      | .error diagnostic => failDisclosure diagnostic *> throwError "typed witness compilation failed"
    let sourceTerm := mkIdent sourceName
    let fullNameTerm := stringTerm fullName.toString
    let exportNameTerm := stringTerm exportName
    let outputNameTerm := stringTerm outputName
    let name : TSyntax `ident := ⟨name⟩
    elabCommand (← `(def $name : Noctium.Circuit :=
      match Noctium.Witness.compile $sourceTerm $exportNameTerm $fullNameTerm $outputNameTerm with
      | .ok value => value.circuit
      | .error _ => {name := $fullNameTerm, inputs := [], outputs := [], constraints := []}))
    unsafe checkGeneratedCircuit fullName
    modifyEnv fun env => circuitRegistry.addEntry env {
      declName := fullName,
      inputs := compiled.circuit.inputs.map fun input => (input.name, input.ty),
      publicInputs := (compiled.circuit.inputs.filter (·.visibility == .public)).map fun input => (input.name, input.ty),
      outputs := compiled.circuit.outputs.map fun value => (value.name, value.ty),
      logicalOutputs,
      sourceProgram? := some (sourceName, exportName)}
    modifyEnv fun env => witnessRegistry.addEntry env {
      circuitName := fullName, sourceName, exportName, outputName, observationArtifact?}

@[command_elab witnessCircuitCommand] unsafe def elabWitnessCircuit : CommandElab := fun stx => do
  match stx with
  | `(noctium_witness_circuit $name:ident from $source:ident entry $exportName:str) =>
    let sourceName ← liftCoreM <| resolveGlobalConstNoOverload source
    registerWitnessCircuit name sourceName exportName.getString
  | _ => throwUnsupportedSyntax

private def moduleProgramDeclName (contractName : Name) (ordinal : Nat) : Name :=
  contractName ++ Name.str .anonymous ("__moduleProgram_" ++ toString ordinal)

private def moduleCircuitDeclName (contractName : Name) (outputName : String) : Name :=
  contractName ++ Name.str .anonymous "__moduleCircuit" ++ Name.str .anonymous outputName

private def moduleCapabilities : Capabilities := {
  typedBoolean := Bool.true
  poseidon2 := Bool.true
  persistentHash32 := Bool.true
  persistentHashVector32 := Bool.true
  persistentHashNative := Bool.true
  sha512 := Bool.true
  keccak256 := Bool.true
  bytes32Conversions := Bool.true
  hashToCurve := Bool.true
  jubjub := Bool.true
  foreignValues := Bool.true
  foreignArithmetic := Bool.true
  foreignByteConversions := Bool.true
  stateCells := Bool.true
  stateMaps := Bool.true}

/-- Re-read every registered module definition constant before expansion. -/
unsafe def moduleRegistryForBuild : CommandElabM Modules.Registry := do
  let mut registry : Modules.Registry := {}
  for info in moduleSourceRegistry.getState (← getEnv) do
    let definition ← evalConstCheck Modules.Definition ``Modules.Definition info.definitionName
    registry ← match registry.register info.sourceName definition with
      | .ok value => pure value
      | .error diagnostic => failDisclosure diagnostic *> throwError "module registration failed"
  pure registry

/-- Re-expand a registered module root from exact source constants. This is
called by both elaboration and the compiler's mandatory source checks. -/
unsafe def rebuildModuleBuild (buildInfo : ModuleBuildInfo) : CommandElabM ModuleBuildOutput := do
  let registry ← moduleRegistryForBuild
  let request ← evalConstCheck Modules.Request ``Modules.Request buildInfo.requestName
  let expansion ← match Modules.expand registry request.sourceName request.arguments with
    | .ok value => pure value
    | .error diagnostic => failDisclosure diagnostic *> throwError "module expansion failed"
  let plan ← match expansion.contractPlan expansion.root with
    | .ok value => pure value
    | .error diagnostic => failDisclosure diagnostic *> throwError "module contract planning failed"
  let groups ← match plan.specializationGroups with
    | .ok value => pure value
    | .error diagnostic => failDisclosure diagnostic *> throwError "module specialization planning failed"
  let mut sources : List (Name × Helpers.Specialization.Program) := []
  for group in groups do
    let source ← evalConstCheck Helpers.Specialization.Program
      ``Helpers.Specialization.Program group.sourceProgram
    sources := sources ++ [(group.sourceProgram, source)]
  let specialized ← match plan.specializeWithSources {} sources with
    | .ok value => pure value
    | .error diagnostic => failDisclosure diagnostic *> throwError "module helper specialization failed"
  let mut programs : List (Name × Name × Helpers.Program) := []
  let mut ordinal := 0
  for (sourceName, batch) in specialized.batches do
    let programName := moduleProgramDeclName buildInfo.contractName ordinal
    programs := programs ++ [(sourceName, programName, batch.program)]
    ordinal := ordinal + 1
  let mut circuitInfos : List ModuleCircuitBuildInfo := []
  let mut circuitValues : List Circuit := []
  for source in plan.circuits do
    let some (_, programName, program) := programs.find? (·.1 == source.source.program)
      | throwError "module source program was not specialized"
    match ComponentDisclosure.checkProgram program source.outputName with
    | .ok _ => pure ()
    | .error diagnostic => failDisclosure diagnostic
    let circuit ← match source.kind with
      | .witness => do
        match Witness.compile program source.outputName source.outputName with
        | .ok compiled => pure compiled.circuit
        | .error diagnostic => failDisclosure diagnostic *> throwError "module witness compilation failed"
      | .circuit =>
        match Helpers.compile program source.outputName with
        | .ok compiled => pure compiled
        | .error diagnostic => failDisclosure diagnostic *> throwError "module circuit compilation failed"
      | _ => throwError "module circuit plan contains a non-circuit member"
    match Disclosure.circuit circuit with
    | .ok _ => pure ()
    | .error diagnostic => failDisclosure diagnostic
    let some (_, batch) := specialized.batches.find? (·.1 == source.source.program)
      | throwError "module specialization batch was not retained"
    let some signatureArtifact := batch.signatureArtifactFor source.outputName
      | throwError "module specialization signature is missing"
    let declarationName := moduleCircuitDeclName buildInfo.contractName source.outputName
    circuitInfos := circuitInfos ++ [{
      source
      declarationName
      programName
      program
      circuit
      signatureArtifact}]
    circuitValues := circuitValues ++ [circuit]
  let contract ← match plan.assembleContract buildInfo.contractName.toString circuitValues with
    | .ok value => pure value
    | .error diagnostic => failDisclosure diagnostic *> throwError "module contract assembly failed"
  match contract.validate moduleCapabilities with
  | .ok _ => pure ()
  | .error diagnostic => failDisclosure diagnostic
  match Disclosure.contract contract with
  | .ok _ => pure ()
  | .error diagnostic => failDisclosure diagnostic
  pure {specialized, contract, programs, circuits := circuitInfos}

private partial def nameTerm : Name → CommandElabM (TSyntax `term)
  | .anonymous => `(Lean.Name.anonymous)
  | .str parent component => do
    let parentTerm ← nameTerm parent
    `(Lean.Name.str $parentTerm $(stringTerm component))
  | .num parent value => do
    let parentTerm ← nameTerm parent
    `(Lean.Name.num $parentTerm $(natTerm value))

private def moduleRegistryTerm : CommandElabM (TSyntax `term) := do
  let infos := moduleSourceRegistry.getState (← getEnv)
  let entries ← infos.toList.toArray.mapM fun info => do
    let sourceName ← nameTerm info.sourceName
    let definition := mkIdent info.definitionName
    `( ({sourceName := $sourceName, definition := $definition : Noctium.Modules.Registered}) )
  let modules ← `(([$entries,*] : List Noctium.Modules.Registered))
  `({modules := $modules : Noctium.Modules.Registry})

private def moduleSourceProgramsTerm (specialized : Modules.SpecializedModule) :
    CommandElabM (TSyntax `term) := do
  let entries ← specialized.batches.toArray.mapM fun (sourceName, _) => do
    let sourceNameTerm ← nameTerm sourceName
    let source := mkIdent sourceName
    `(($sourceNameTerm, $source))
  `(([$entries,*] : List (Lean.Name × Noctium.Helpers.Specialization.Program)))

private def moduleSpecializeTerm (buildInfo : ModuleBuildInfo)
    (specialized : Modules.SpecializedModule) : CommandElabM (TSyntax `term) := do
  let registry ← moduleRegistryTerm
  let request := mkIdent buildInfo.requestName
  let sources ← moduleSourceProgramsTerm specialized
  `(Noctium.Modules.specializeRequestWithSources {} {} $registry $request $sources)

private def moduleProgramBodyTerm (specializeTerm : TSyntax `term) (sourceName : Name) :
    CommandElabM (TSyntax `term) := do
  let sourceNameTerm ← nameTerm sourceName
  `(match ($specializeTerm) with
    | .ok specialized =>
      match specialized.findBatch $sourceNameTerm with
      | some batch => batch.program
      | none => ({} : Noctium.Helpers.Program)
    | .error _ => ({} : Noctium.Helpers.Program))

private def moduleCircuitBodyTerm (source : Modules.ModuleCircuitSource)
    (programName : Name) : CommandElabM (TSyntax `term) := do
  let program := mkIdent programName
  let outputName := stringTerm source.outputName
  match source.kind with
  | .witness =>
    `(match Noctium.Witness.compile $program $outputName $outputName with
      | .ok value => value.circuit
      | .error _ => {name := $outputName, inputs := [], outputs := [], constraints := []})
  | .circuit =>
    `(match Noctium.Helpers.compile $program $outputName with
      | .ok value => value
      | .error _ => {name := $outputName, inputs := [], outputs := [], constraints := []})
  | _ => throwError "module circuit source has an invalid member kind"

scoped syntax (name := moduleSourceCommand) "noctium_module" "from" ident : command

open scoped Noctium

@[command_elab moduleSourceCommand] unsafe def elabModuleSource : CommandElab := fun stx => do
  match stx with
  | `(noctium_module from $source:ident) => do
    let sourceName ← liftCoreM <| resolveGlobalConstNoOverload source
    if moduleSourceRegistry.getState (← getEnv) |>.any (·.sourceName == sourceName) then
      throwErrorAt source "Noctium module source identity is already registered"
    let definition ← evalConstCheck Modules.Definition ``Modules.Definition sourceName
    match Modules.registerDefinition sourceName definition with
    | .error diagnostic => failDisclosure diagnostic
    | .ok _ => pure ()
    modifyEnv fun env => moduleSourceRegistry.addEntry env {
      sourceName
      definitionName := sourceName}
  | _ => throwUnsupportedSyntax

scoped syntax (name := moduleContractCommand) "noctium_module_contract" ident
  "from" ident : command

@[command_elab moduleContractCommand] unsafe def elabModuleContract : CommandElab := fun stx => do
  match stx with
  | `(noctium_module_contract $name:ident from $requestSource:ident) => do
    let requestName ← liftCoreM <| resolveGlobalConstNoOverload requestSource
    let fullName := (← getCurrNamespace) ++ name.getId.eraseMacroScopes
    if (← getEnv).contains fullName then
      throwErrorAt name "generated module contract name collides with an existing declaration"
    let buildInfo : ModuleBuildInfo := {contractName := fullName, requestName}
    let builtModule ← rebuildModuleBuild buildInfo
    let specializeTerm ← moduleSpecializeTerm buildInfo builtModule.specialized
    for (sourceName, programName, _) in builtModule.programs do
      let programIdent := mkIdent programName
      if (← getEnv).contains programName then
        throwErrorAt name "generated module program name collides with an existing declaration"
      let body ← moduleProgramBodyTerm specializeTerm sourceName
      elabCommand (← `(def $programIdent : Noctium.Helpers.Program := $body))
    for circuitInfo in builtModule.circuits do
      let circuitIdent := mkIdent circuitInfo.declarationName
      if (← getEnv).contains circuitInfo.declarationName then
        throwErrorAt name "generated module circuit name collides with an existing declaration"
      let body ← moduleCircuitBodyTerm circuitInfo.source circuitInfo.programName
      elabCommand (← `(def $circuitIdent : Noctium.Circuit := $body))
      unsafe checkGeneratedCircuit circuitInfo.declarationName
      let signatureText := (Lean.toJson circuitInfo.signatureArtifact).pretty
      modifyEnv fun env => circuitRegistry.addEntry env {
        declName := circuitInfo.declarationName
        inputs := circuitInfo.circuit.inputs.map fun input => (input.name, input.ty)
        publicInputs := (circuitInfo.circuit.inputs.filter (·.visibility == .public)).map
          fun input => (input.name, input.ty)
        outputs := circuitInfo.circuit.outputs.map fun item => (item.name, item.ty)
        sourceProgram? := some (circuitInfo.programName, circuitInfo.source.outputName)
        specializationArtifact? := some signatureText}
      if circuitInfo.source.kind == .witness then
        modifyEnv fun env => witnessRegistry.addEntry env {
          circuitName := Name.str .anonymous circuitInfo.source.outputName
          sourceName := circuitInfo.programName
          exportName := circuitInfo.source.outputName}
    let circuitTerms := builtModule.circuits.toArray.map fun circuitInfo => mkIdent circuitInfo.declarationName
    let contractNameText := stringTerm fullName.toString
    let contractIdent := mkIdent fullName
    let contractBody ← `(match ($specializeTerm) with
      | .ok specialized =>
        match specialized.plan.assembleContract $contractNameText [$circuitTerms,*] with
        | .ok contract => contract
        | .error _ => {name := $contractNameText : Noctium.Contract}
      | .error _ => {name := $contractNameText : Noctium.Contract})
    elabCommand (← `(def $contractIdent : Noctium.Contract := $contractBody))
    unsafe checkGeneratedContract fullName
    modifyEnv fun env => contractRegistry.addEntry env fullName
    modifyEnv fun env => moduleBuildRegistry.addEntry env buildInfo
  | _ => throwUnsupportedSyntax

end Noctium
