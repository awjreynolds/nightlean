import Noctium.Frontend
import Noctium.Backend.Zkir
import Noctium.Target
import Noctium.Types.ValueSchema

namespace Noctium.Compiler
open Lean Elab Command

private def sourceCapabilities : Capabilities := Capabilities.source

private def typeName : Ty → String
  | .native => "Native"
  | .bool => "Bool"
  | .uint maximum => s!"UIntRange<{maximum + 1}>"
  | .bytes byteLength => s!"Bytes<{byteLength}>"
  | .jubjubScalar => "JubjubScalar"
  | .jubjubPoint => "JubjubPoint"

private def expressionJson : Expr ty → Json
  | .native n => Json.mkObj [("native", toJson (toString n))]
  | .bool b => Json.mkObj [("bool", toJson b)]
  | .uint maximum value => Json.mkObj [("uint", Json.mkObj [
      ("maximum", toJson (toString maximum)), ("value", toJson (toString value))])]
  | .bytesField value index => Json.mkObj [("bytesField", Json.mkObj [
      ("value", expressionJson value), ("index", toJson index)])]
  | .bytesAt value index => Json.mkObj [("byteAt", Json.mkObj [
      ("value", expressionJson value), ("index", toJson index)])]
  | .bytesLiteral length values => Json.mkObj [("tag", toJson ("bytesLiteral" : String)),
      ("length", toJson length), ("values", toJson values)]
  | .reverseBytes (length := length) value => Json.mkObj [
      ("tag", toJson ("reverseBytes" : String)), ("length", toJson length),
      ("value", expressionJson value)]
  | .sliceBytes (length := length) value start stop => Json.mkObj [
      ("tag", toJson ("sliceBytes" : String)), ("length", toJson length),
      ("value", expressionJson value), ("start", toJson start), ("end", toJson stop)]
  | .concatBytes (leftLength := leftLength) (rightLength := rightLength) left right =>
      Json.mkObj [("tag", toJson ("concatBytes" : String)),
        ("leftLength", toJson leftLength), ("rightLength", toJson rightLength),
        ("left", expressionJson left), ("right", expressionJson right)]
  | .sha512 (length := length) value => Json.mkObj [
      ("tag", toJson ("sha512" : String)), ("length", toJson length),
      ("value", expressionJson value)]
  | .keccak256 (length := length) value => Json.mkObj [
      ("tag", toJson ("keccak256" : String)), ("length", toJson length),
      ("value", expressionJson value)]
  | .reverseBytes32 value => Json.mkObj [("tag", toJson ("reverseBytes32" : String)),
      ("value", expressionJson value)]
  | .persistentHash32 value => Json.mkObj [("tag", toJson ("persistentHash32" : String)),
      ("value", expressionJson value)]
  | .bytes32Literal values => Json.mkObj [("tag", toJson ("bytes32Literal" : String)),
      ("values", toJson values)]
  | .persistentHashVector32 values => Json.mkObj [("tag", toJson ("persistentHashVector32" : String)),
      ("values", toJson (values.map expressionJson))]
  | .persistentHashNative value => Json.mkObj [("tag", toJson ("persistentHashNative" : String)),
      ("value", expressionJson value)]
  | .persistentHashNativeVector values => Json.mkObj [("tag", toJson ("persistentHashNativeVector" : String)),
      ("values", toJson (values.map expressionJson))]
  | .toBytes32 value => Json.mkObj [("tag", toJson ("toBytes32" : String)),
      ("value", expressionJson value)]
  | .fromBytes32 (target := target) value => Json.mkObj [("tag", toJson ("fromBytes32" : String)),
      ("type", toJson (typeName target)), ("value", expressionJson value)]
  | .jubjubScalarFromNative value => Json.mkObj [("tag", toJson ("jubjubScalarFromNative" : String)),
      ("value", expressionJson value)]
  | .jubjubScalarToNative value => Json.mkObj [("tag", toJson ("jubjubScalarToNative" : String)),
      ("value", expressionJson value)]
  | .jubjubMulGenerator scalar => Json.mkObj [("tag", toJson ("jubjubMulGenerator" : String)),
      ("scalar", expressionJson scalar)]
  | .jubjubMul point scalar => Json.mkObj [("tag", toJson ("jubjubMul" : String)),
      ("point", expressionJson point), ("scalar", expressionJson scalar)]
  | .jubjubAdd left right => Json.mkObj [("tag", toJson ("jubjubAdd" : String)),
      ("left", expressionJson left), ("right", expressionJson right)]
  | .jubjubNeg point => Json.mkObj [("tag", toJson ("jubjubNeg" : String)),
      ("point", expressionJson point)]
  | .jubjubCoordinate point index => Json.mkObj [("tag", toJson ("jubjubCoordinate" : String)),
      ("point", expressionJson point), ("index", toJson index)]
  | .jubjubFromCoordinates x y => Json.mkObj [("tag", toJson ("jubjubFromCoordinates" : String)),
      ("x", expressionJson x), ("y", expressionJson y)]
  | .boolAnd left right => Json.mkObj [("tag", toJson ("boolAnd" : String)),
      ("left", expressionJson left), ("right", expressionJson right)]
  | .boolOr left right => Json.mkObj [("tag", toJson ("boolOr" : String)),
      ("left", expressionJson left), ("right", expressionJson right)]
  | .boolXor left right => Json.mkObj [("tag", toJson ("boolXor" : String)),
      ("left", expressionJson left), ("right", expressionJson right)]
  | .ref name => Json.mkObj [("ref", toJson name)]
  | .add a b => Json.mkObj [("add", toJson [expressionJson a, expressionJson b])]
  | .mul a b => Json.mkObj [("mul", toJson [expressionJson a, expressionJson b])]
  | .sub a b => Json.mkObj [("sub", toJson [expressionJson a, expressionJson b])]
  | .uadd a b => Json.mkObj [("uadd", toJson [expressionJson a, expressionJson b])]
  | .usub a b => Json.mkObj [("usub", toJson [expressionJson a, expressionJson b])]
  | .umul a b => Json.mkObj [("umul", toJson [expressionJson a, expressionJson b])]
  | .inv value => Json.mkObj [("tag", toJson ("inv" : String)), ("value", expressionJson value)]
  | .cast target value => Json.mkObj [("cast", Json.mkObj [
      ("type", toJson (typeName target)), ("value", expressionJson value)])]
  | .letE name value body => Json.mkObj [("let", Json.mkObj [
      ("name", toJson name), ("value", expressionJson value), ("body", expressionJson body)])]
  | .assertE condition body => Json.mkObj [("assertThen", toJson [expressionJson condition, expressionJson body])]
  | .disclose _ value => expressionJson value
  | .eq a b => Json.mkObj [("eq", toJson [expressionJson a, expressionJson b])]
  | .select c a b => Json.mkObj [("select", toJson [expressionJson c, expressionJson a, expressionJson b])]
  | .poseidon2 domain a b => Json.mkObj [("poseidon2", Json.mkObj [
      ("domain", toJson (toString domain)), ("args", toJson [expressionJson a, expressionJson b])])]

/-- Symbolic source expressions for the native runtime. Values are AST constants or references,
never an execution witness. Decimal field constants avoid JavaScript number truncation. -/
private def nativeExpressionJson : Expr ty → Json
  | .native n => Json.mkObj [("tag", toJson ("constant" : String)), ("value", toJson (toString n))]
  | .bool b => Json.mkObj [("tag", toJson ("bool" : String)), ("value", toJson b)]
  | .uint maximum value => Json.mkObj [("tag", toJson ("uint" : String)),
      ("maximum", toJson (toString maximum)), ("value", toJson (toString value))]
  | .bytesField value index => Json.mkObj [("tag", toJson ("bytesField" : String)),
      ("value", nativeExpressionJson value), ("index", toJson index)]
  | .bytesAt value index => Json.mkObj [("tag", toJson ("byteAt" : String)),
      ("value", nativeExpressionJson value), ("index", toJson index)]
  | .bytesLiteral length values => Json.mkObj [("tag", toJson ("bytesLiteral" : String)),
      ("length", toJson length), ("values", toJson values)]
  | .reverseBytes (length := length) value => Json.mkObj [
      ("tag", toJson ("reverseBytes" : String)), ("length", toJson length),
      ("value", nativeExpressionJson value)]
  | .sliceBytes (length := length) value start stop => Json.mkObj [
      ("tag", toJson ("sliceBytes" : String)), ("length", toJson length),
      ("value", nativeExpressionJson value), ("start", toJson start), ("end", toJson stop)]
  | .concatBytes (leftLength := leftLength) (rightLength := rightLength) left right =>
      Json.mkObj [("tag", toJson ("concatBytes" : String)),
        ("leftLength", toJson leftLength), ("rightLength", toJson rightLength),
        ("left", nativeExpressionJson left), ("right", nativeExpressionJson right)]
  | .sha512 (length := length) value => Json.mkObj [
      ("tag", toJson ("sha512" : String)), ("length", toJson length),
      ("value", nativeExpressionJson value)]
  | .keccak256 (length := length) value => Json.mkObj [
      ("tag", toJson ("keccak256" : String)), ("length", toJson length),
      ("value", nativeExpressionJson value)]
  | .reverseBytes32 value => Json.mkObj [("tag", toJson ("reverseBytes32" : String)),
      ("value", nativeExpressionJson value)]
  | .persistentHash32 value => Json.mkObj [("tag", toJson ("persistentHash32" : String)),
      ("value", nativeExpressionJson value)]
  | .bytes32Literal values => Json.mkObj [("tag", toJson ("bytes32Literal" : String)),
      ("values", toJson values)]
  | .persistentHashVector32 values => Json.mkObj [("tag", toJson ("persistentHashVector32" : String)),
      ("values", toJson (values.map nativeExpressionJson))]
  | .persistentHashNative value => Json.mkObj [("tag", toJson ("persistentHashNative" : String)),
      ("value", nativeExpressionJson value)]
  | .persistentHashNativeVector values => Json.mkObj [("tag", toJson ("persistentHashNativeVector" : String)),
      ("values", toJson (values.map nativeExpressionJson))]
  | .toBytes32 value => Json.mkObj [("tag", toJson ("toBytes32" : String)),
      ("value", nativeExpressionJson value)]
  | .fromBytes32 (target := target) value => Json.mkObj [("tag", toJson ("fromBytes32" : String)),
      ("type", toJson (typeName target)), ("value", nativeExpressionJson value)]
  | .jubjubScalarFromNative value => Json.mkObj [("tag", toJson ("jubjubScalarFromNative" : String)),
      ("value", nativeExpressionJson value)]
  | .jubjubScalarToNative value => Json.mkObj [("tag", toJson ("jubjubScalarToNative" : String)),
      ("value", nativeExpressionJson value)]
  | .jubjubMulGenerator scalar => Json.mkObj [("tag", toJson ("jubjubMulGenerator" : String)),
      ("scalar", nativeExpressionJson scalar)]
  | .jubjubMul point scalar => Json.mkObj [("tag", toJson ("jubjubMul" : String)),
      ("point", nativeExpressionJson point), ("scalar", nativeExpressionJson scalar)]
  | .jubjubAdd left right => Json.mkObj [("tag", toJson ("jubjubAdd" : String)),
      ("left", nativeExpressionJson left), ("right", nativeExpressionJson right)]
  | .jubjubNeg point => Json.mkObj [("tag", toJson ("jubjubNeg" : String)),
      ("point", nativeExpressionJson point)]
  | .jubjubCoordinate point index => Json.mkObj [("tag", toJson ("jubjubCoordinate" : String)),
      ("point", nativeExpressionJson point), ("index", toJson index)]
  | .jubjubFromCoordinates x y => Json.mkObj [("tag", toJson ("jubjubFromCoordinates" : String)),
      ("x", nativeExpressionJson x), ("y", nativeExpressionJson y)]
  | .boolAnd left right => Json.mkObj [("tag", toJson ("boolAnd" : String)),
      ("left", nativeExpressionJson left), ("right", nativeExpressionJson right)]
  | .boolOr left right => Json.mkObj [("tag", toJson ("boolOr" : String)),
      ("left", nativeExpressionJson left), ("right", nativeExpressionJson right)]
  | .boolXor left right => Json.mkObj [("tag", toJson ("boolXor" : String)),
      ("left", nativeExpressionJson left), ("right", nativeExpressionJson right)]
  | .ref name => Json.mkObj [("tag", toJson ("reference" : String)), ("name", toJson name)]
  | .add a b => binary "add" (nativeExpressionJson a) (nativeExpressionJson b)
  | .mul a b => binary "mul" (nativeExpressionJson a) (nativeExpressionJson b)
  | .sub a b => binary "sub" (nativeExpressionJson a) (nativeExpressionJson b)
  | .uadd (m := m) (n := n) a b => unsigned "uadd" (m + n) (nativeExpressionJson a) (nativeExpressionJson b)
  | .usub (m := m) a b => unsigned "usub" m (nativeExpressionJson a) (nativeExpressionJson b)
  | .umul (m := m) (n := n) a b => unsigned "umul" (m * n) (nativeExpressionJson a) (nativeExpressionJson b)
  | .inv value => Json.mkObj [("tag", toJson ("inv" : String)), ("value", nativeExpressionJson value)]
  | .cast target value => Json.mkObj [("tag", toJson ("cast" : String)),
      ("type", toJson (typeName target)), ("value", nativeExpressionJson value)]
  | .letE name value body => Json.mkObj [("tag", toJson ("let" : String)),
      ("name", toJson name), ("value", nativeExpressionJson value), ("body", nativeExpressionJson body)]
  | .assertE condition body => Json.mkObj [("tag", toJson ("assertThen" : String)),
      ("condition", nativeExpressionJson condition), ("body", nativeExpressionJson body)]
  | .disclose _ value => nativeExpressionJson value
  | .eq a b => binary "eq" (nativeExpressionJson a) (nativeExpressionJson b)
  | .select c a b => Json.mkObj [("tag", toJson ("select" : String)),
      ("condition", nativeExpressionJson c), ("yes", nativeExpressionJson a), ("no", nativeExpressionJson b)]
  | .poseidon2 domain a b => Json.mkObj [("tag", toJson ("poseidon2" : String)),
      ("domain", toJson (toString domain)), ("left", nativeExpressionJson a), ("right", nativeExpressionJson b)]
where
  binary (tag : String) (left right : Json) : Json :=
    Json.mkObj [("tag", toJson tag), ("left", left), ("right", right)]
  unsigned (tag : String) (maximum : Nat) (left right : Json) : Json :=
    Json.mkObj [("tag", toJson tag), ("maximum", toJson (toString maximum)),
      ("left", left), ("right", right)]

private def alignedJson (value : Backend.Impact.Aligned) : List (String × Json) :=
  match value with
  | .field expression => [("alignment", toJson ("field" : String)), ("expression", nativeExpressionJson expression)]
  | .bit b => [("alignment", toJson ("bit" : String)), ("expression", nativeExpressionJson (.bool b))]
  | .bitExpr expression => [("alignment", toJson ("bit" : String)), ("expression", nativeExpressionJson expression)]
  | .bytes32 expression => [("alignment", toJson ("bytes32" : String)), ("expression", nativeExpressionJson expression)]
  | .nativeFields expressions => [("alignment", toJson ("nativeFields" : String)),
      ("expressions", toJson (expressions.map nativeExpressionJson))]
  | .counter expression => [("alignment", toJson ("u64" : String)),
      ("expression", nativeExpressionJson expression)]

private def alignedExpressionJson (value : Backend.Impact.Aligned) : Json :=
  match value with
  | .field expression => nativeExpressionJson expression
  | .bit value => nativeExpressionJson (.bool value)
  | .bitExpr expression => nativeExpressionJson expression
  | .bytes32 expression => nativeExpressionJson expression
  | .nativeFields expressions => toJson (expressions.map nativeExpressionJson)
  | .counter expression => nativeExpressionJson expression

private def operationJsonBare : Backend.Impact.Op → Json
  | .dup => Json.mkObj [("op", toJson ("dup" : String))]
  | .index slot pushPath => Json.mkObj [("op", toJson ("index" : String)),
      ("slot", toJson slot), ("pushPath", toJson pushPath)]
  | .mapIndex slot key => Json.mkObj [("op", toJson ("index" : String)),
      ("slot", toJson slot), ("pushPath", toJson Bool.false),
      ("key", alignedExpressionJson key)]
  | .indexPath slot pushPath keys => Json.mkObj [
      ("op", toJson ("indexPath" : String)), ("slot", toJson slot),
      ("pushPath", toJson pushPath),
      ("keys", toJson (keys.map fun key => Json.mkObj (alignedJson key)))]
  | .push value storage => Json.mkObj ([("op", toJson ("push" : String)), ("storage", toJson storage)] ++ alignedJson value)
  | .newMap => Json.mkObj [("op", toJson ("new" : String))]
  | .popeq value => Json.mkObj ([("op", toJson ("popeq" : String))] ++ alignedJson value)
  | .pushFields schema expressions storage => Json.mkObj [
      ("op", toJson ("pushFields" : String)), ("storage", toJson storage),
      ("expressions", toJson (expressions.map nativeExpressionJson)), ("schema", schema)]
  | .popeqFields schema expressions => Json.mkObj [
      ("op", toJson ("popeqFields" : String)),
      ("expressions", toJson (expressions.map nativeExpressionJson)), ("schema", schema)]
  | .member => Json.mkObj [("op", toJson ("member" : String))]
  | .insert n => Json.mkObj [("op", toJson ("insert" : String)), ("n", toJson n)]
  | .addImmediate amount => Json.mkObj [("op", toJson ("addImmediate" : String)), ("amount", toJson amount)]
  | .subImmediate amount => Json.mkObj [("op", toJson ("subImmediate" : String)), ("amount", toJson amount)]
  | .listLength slot keys expression => Json.mkObj [
      ("op", toJson ("listLength" : String)), ("slot", toJson slot),
      ("keys", toJson (keys.map fun key => Json.mkObj (alignedJson key))),
      ("expression", nativeExpressionJson expression)]
  | .listHead slot keys schema expressions => Json.mkObj [
      ("op", toJson ("listHead" : String)), ("slot", toJson slot),
      ("keys", toJson (keys.map fun key => Json.mkObj (alignedJson key))),
      ("schema", schema), ("expressions", toJson (expressions.map nativeExpressionJson))]
  | .listPushFront slot keys schema expressions => Json.mkObj [
      ("op", toJson ("listPushFront" : String)), ("slot", toJson slot),
      ("keys", toJson (keys.map fun key => Json.mkObj (alignedJson key))),
      ("schema", schema), ("expressions", toJson (expressions.map nativeExpressionJson))]
  | .listPopFront slot keys => Json.mkObj [
      ("op", toJson ("listPopFront" : String)), ("slot", toJson slot),
      ("keys", toJson (keys.map fun key => Json.mkObj (alignedJson key)))]
  | .listReset slot keys => Json.mkObj [
      ("op", toJson ("listReset" : String)), ("slot", toJson slot),
      ("keys", toJson (keys.map fun key => Json.mkObj (alignedJson key)))]
  | .mapRemove slot keys => Json.mkObj [
      ("op", toJson ("mapRemove" : String)), ("slot", toJson slot),
      ("keys", toJson (keys.map fun key => Json.mkObj (alignedJson key)))]

private def operationJson (activityGuard : Option (Expr .bool))
    (operation : Backend.Impact.Op) : Json :=
  let encoded := operationJsonBare operation
  match activityGuard with
  | none => encoded
  | some guard => Json.mkObj [
      ("op", toJson ("guarded" : String)),
      ("guard", nativeExpressionJson guard),
      ("operation", encoded)]

private def effectJson : Effect → Json
  | .readCell state destination ty => Json.mkObj [("op", toJson ("readCell" : String)),
      ("state", toJson state), ("destination", toJson destination), ("type", toJson (typeName ty))]
  | .readMap state destination _ ty key => Json.mkObj [("op", toJson ("readMap" : String)),
      ("state", toJson state), ("destination", toJson destination), ("type", toJson (typeName ty)),
      ("key", expressionJson key)]
  | .readMember state destination _ _ key => Json.mkObj [("op", toJson ("readMember" : String)),
      ("state", toJson state), ("destination", toJson destination),
      ("type", toJson (typeName .bool)), ("key", expressionJson key)]
  | .require condition => Json.mkObj [("op", toJson ("require" : String)), ("condition", expressionJson condition)]
  | .writeCell state _ value => Json.mkObj [("op", toJson ("writeCell" : String)),
      ("state", toJson state), ("value", expressionJson value)]
  | .writeMap state _ _ key value => Json.mkObj [("op", toJson ("writeMap" : String)),
      ("state", toJson state), ("key", expressionJson key), ("value", expressionJson value)]
  | .requireAbsent state _ key => Json.mkObj [("op", toJson ("requireAbsent" : String)),
      ("state", toJson state), ("key", expressionJson key)]
  | .readPath state destination keys ty => Json.mkObj [
      ("op", toJson ("readPath" : String)), ("state", toJson state),
      ("destination", toJson destination), ("type", toJson (typeName ty)),
      ("keys", toJson (keys.map fun key => match key with
        | .mk _ value => expressionJson value))]
  | .memberPath state destination keys => Json.mkObj [
      ("op", toJson ("memberPath" : String)), ("state", toJson state),
      ("destination", toJson destination),
      ("keys", toJson (keys.map fun key => match key with
        | .mk _ value => expressionJson value))]
  | .counterRead state destination keys => Json.mkObj [
      ("op", toJson ("counterRead" : String)), ("state", toJson state),
      ("destination", toJson destination),
      ("keys", toJson (keys.map fun key => match key with
        | .mk _ value => expressionJson value))]
  | .counterAdjust state keys subtract amount => Json.mkObj [
      ("op", toJson ("counterAdjust" : String)), ("state", toJson state),
      ("keys", toJson (keys.map fun key => match key with
        | .mk _ value => expressionJson value)),
      ("subtract", toJson subtract), ("amount", toJson amount)]
  | .counterReset state keys => Json.mkObj [
      ("op", toJson ("counterReset" : String)), ("state", toJson state),
      ("keys", toJson (keys.map fun key => match key with
        | .mk _ value => expressionJson value))]
  | .listLength state destination keys => Json.mkObj [
      ("op", toJson ("listLength" : String)), ("state", toJson state),
      ("destination", toJson destination), ("type", toJson (typeName (.uint (2 ^ 64 - 1)))),
      ("keys", toJson (keys.map fun key => match key with
        | .mk _ value => expressionJson value))]
  | .listHead state destination keys _ destinations => Json.mkObj [
      ("op", toJson ("listHead" : String)), ("state", toJson state),
      ("destination", toJson destination),
      ("keys", toJson (keys.map fun key => match key with
        | .mk _ value => expressionJson value)),
      ("destinations", toJson destinations)]
  | .listPushFront state keys _ values => Json.mkObj [
      ("op", toJson ("listPushFront" : String)), ("state", toJson state),
      ("keys", toJson (keys.map fun key => match key with
        | .mk _ value => expressionJson value)),
      ("values", toJson (values.map expressionJson))]
  | .listPopFront state keys => Json.mkObj [
      ("op", toJson ("listPopFront" : String)), ("state", toJson state),
      ("keys", toJson (keys.map fun key => match key with
        | .mk _ value => expressionJson value))]
  | .listReset state keys => Json.mkObj [
      ("op", toJson ("listReset" : String)), ("state", toJson state),
      ("keys", toJson (keys.map fun key => match key with
        | .mk _ value => expressionJson value))]
  | .insertPath state keys _ value => Json.mkObj [
      ("op", toJson ("insertPath" : String)), ("state", toJson state),
      ("keys", toJson (keys.map fun key => match key with
        | .mk _ value => expressionJson value)), ("value", expressionJson value)]
  | .writePath state keys _ value => Json.mkObj [
      ("op", toJson ("writePath" : String)), ("state", toJson state),
      ("keys", toJson (keys.map fun key => match key with
        | .mk _ value => expressionJson value)), ("value", expressionJson value)]
  | .readCompositePath state destination keys _ destinations => Json.mkObj [
        ("op", toJson ("readCompositePath" : String)), ("state", toJson state),
        ("destination", toJson destination), ("destinations", toJson destinations),
        ("keys", toJson (keys.map fun key => match key with
          | .mk _ value => expressionJson value))]
  | .writeCompositePath state keys _ values => Json.mkObj [
      ("op", toJson ("writeCompositePath" : String)), ("state", toJson state),
      ("keys", toJson (keys.map fun key => match key with
        | .mk _ value => expressionJson value)),
      ("values", toJson (values.map expressionJson))]
  | .emptyMapPath state keys => Json.mkObj [
      ("op", toJson ("emptyMapPath" : String)), ("state", toJson state),
      ("keys", toJson (keys.map fun key => match key with
        | .mk _ value => expressionJson value))]
  | .removePath state keys => Json.mkObj [
      ("op", toJson ("removePath" : String)), ("state", toJson state),
      ("keys", toJson (keys.map fun key => match key with
        | .mk _ value => expressionJson value))]

private def guardedEffectJson (guard : Option (Expr .bool)) (effect : Effect) : Json :=
  let encoded := effectJson effect
  match guard with
  | none => encoded
  | some condition => Json.mkObj [
      ("op", toJson ("guarded" : String)),
      ("guard", expressionJson condition),
      ("effect", encoded)]

private def stateJson (state : StateDecl) : Json :=
  let compositeSchema (environment : Types.CompositeEnv) (type : Types.CompositeType) : Json :=
    match Types.compileType environment type with
    | .error _ => Json.null
    | .ok compiled => (Types.schemaJson compiled).toOption.getD Json.null
  let rec treeJson : LedgerValueType → Json
    | .scalar ty => Json.mkObj [("scalar", toJson (typeName ty))]
    | .map keyTy value => Json.mkObj [("map", toJson [toJson (typeName keyTy), treeJson value])]
    | .composite environment type => Json.mkObj [("composite", compositeSchema environment type)]
    | .list environment type => Json.mkObj [("list", Json.mkObj [
        ("composite", compositeSchema environment type)])]
    | .counter => Json.mkObj [("counter", toJson Bool.true)]
  let kind := match state.kind with
    | .cell ty => Json.mkObj [("cell", toJson (typeName ty))]
    | .map kt vt => Json.mkObj [("map", toJson [typeName kt, typeName vt])]
    | .tree value => Json.mkObj [("tree", treeJson value)]
    | .opaqueString => Json.mkObj [("opaqueString", toJson Bool.true)]
  Json.mkObj ([("name", toJson state.name), ("kind", kind)] ++
    (if state.sealed then [("sealed", toJson Bool.true)] else []))

private def constructorTypeName : ConstructorType → String
  | .scalar ty => typeName ty
  | .opaqueString => "OpaqueString"

private def constructorValueJson : ConstructorValue → Json
  | .scalar value => Json.mkObj [
      ("kind", toJson ("scalarExpression" : String)),
      ("expression", nativeExpressionJson value)]
  | .opaqueStringParameter name => Json.mkObj [
      ("kind", toJson ("opaqueStringParameter" : String)),
      ("name", toJson name)]
  | .opaqueStringLiteral value => Json.mkObj [
      ("kind", toJson ("opaqueStringLiteral" : String)),
      ("value", toJson value)]

private def constructorJson (ctor : Constructor) : Json := Json.mkObj [
  ("parameters", toJson (ctor.parameters.map fun parameter => Json.mkObj [
    ("name", toJson parameter.name), ("type", toJson (constructorTypeName parameter.type))])),
  ("initializers", toJson (ctor.initializers.map fun initializer => Json.mkObj [
    ("state", toJson initializer.state),
    ("type", toJson (constructorTypeName initializer.type)),
    ("value", constructorValueJson initializer.value)]))]

private def circuitSchemaJson (name : Name) (circuit : Circuit) : Json :=
  Json.mkObj [("name", toJson name.toString), ("file", toJson (name.toString ++ ".zkir")),
    ("inputs", toJson (circuit.inputs.map fun input => Json.mkObj [
      ("name", toJson input.name), ("type", toJson (typeName input.ty)),
      ("visibility", toJson (if input.visibility == .«public» then "public" else "private"))])),
    ("outputs", toJson (circuit.outputs.map fun out => Json.mkObj [
      ("name", toJson out.name), ("type", toJson (typeName out.ty)),
      ("visibility", toJson ("public" : String)), ("expression", nativeExpressionJson out.value)])),
    ("constraints", toJson (circuit.constraints.map nativeExpressionJson))]

private def failDiagnostic (d : Diagnostic) : CommandElabM α :=
  throwError "{d.span.file}:{d.span.line}:{d.span.column}: {d.message}"

/-- Rebuild module roots from their registered source constants for each
compiler inspection. Generated declarations remain convenient names for users,
but their cached values do not authorize compilation. -/
private unsafe def rebuildModuleOutputs : CommandElabM (Array (Name × ModuleBuildOutput)) := do
  let env ← getEnv
  let mut outputs := #[]
  for info in moduleBuildRegistry.getState env do
    unless env.isImportedConst info.contractName do
      outputs := outputs.push (info.contractName, ← rebuildModuleBuild info)
  return outputs

private def moduleCircuitFor (outputs : Array (Name × ModuleBuildOutput)) (name : Name) :
    Option ModuleCircuitBuildInfo :=
  outputs.toList.flatMap (·.2.circuits) |>.find? (·.declarationName == name)

private def moduleWitnessProgramFor (outputs : Array (Name × ModuleBuildOutput))
    (info : WitnessInfo) : Option Helpers.Program := do
  let circuit ← outputs.toList.flatMap (·.2.circuits) |>.find? fun item =>
    item.source.kind == .witness && item.programName == info.sourceName &&
      item.source.outputName == info.exportName
  pure circuit.program

/-- Evaluate only definitions generated and registered by the Noctium elaborators. -/
private unsafe def registeredCircuits (moduleOutputs : Array (Name × ModuleBuildOutput)) :
    CommandElabM (Array (Name × Circuit)) := do
  let env ← getEnv
  let mut circuits := #[]
  for info in circuitRegistry.getState env do
    unless env.isImportedConst info.declName do
      let moduleCircuit := moduleCircuitFor moduleOutputs info.declName
      if moduleCircuit.isNone then
        if let some (sourceName, exportName) := info.sourceProgram? then
          let program ← evalConstCheck Helpers.Program ``Helpers.Program sourceName
          match ComponentDisclosure.checkProgram program exportName with
          | .ok _ => pure ()
          | .error d => failDiagnostic d
      if let some text := info.specializationArtifact? then
        match Helpers.Specialization.parseSignatureArtifactText text with
        | .ok _ => pure ()
        | .error message => throwError "invalid generic specialization signature artifact: {message}"
      let circuit ← match moduleCircuit with
        | some fresh => pure fresh.circuit
        | none => evalConstCheck Circuit ``Circuit info.declName
      match circuit.validate sourceCapabilities with
      | .error d => failDiagnostic d
      | .ok _ =>
        match Disclosure.circuit circuit with
        | .error d => failDiagnostic d
        | .ok _ => circuits := circuits.push (info.declName, circuit)
  return circuits

private unsafe def registeredContracts (moduleOutputs : Array (Name × ModuleBuildOutput)) :
    CommandElabM (Array (Name × Contract)) := do
  let env ← getEnv
  let mut contracts := #[]
  for name in contractRegistry.getState env do
    unless env.isImportedConst name do
      let contract ← match moduleOutputs.toList.find? (·.1 == name) with
        | some (_, rebuilt) => pure rebuilt.contract
        | none => evalConstCheck Contract ``Contract name
      match contract.validate sourceCapabilities with
      | .error d => failDiagnostic d
      | .ok _ =>
        match Disclosure.contract contract with
        | .error d => failDiagnostic d
        | .ok _ => contracts := contracts.push (name, contract)
  return contracts

private def artifactName (name : Name) : String := name.toString

private def validateArtifactStem (text : String) : CommandElabM Unit := do
  if text.contains '/' || text.contains '\\' || (text.splitOn "..").length > 1 then
    throwError "declaration name is not a safe artifact filename: {text}"

private def validateArtifactName (name : Name) : CommandElabM Unit :=
  validateArtifactStem (artifactName name)

private def nativeCircuitFile (contract : Name) (ep : Entrypoint) : String :=
  artifactName contract ++ "." ++ ep.name ++ ".zkir"

private def nativePlanFile (contract : Name) (ep : Entrypoint) : String :=
  artifactName contract ++ "." ++ ep.name ++ ".impact.json"

/-- The exact symbolic plan tree written by the compiler. This pure function
also gives proof modules a kernel-visible artifact boundary. -/
def nativePlanJson (profile : TargetProfile) (contractName : Name)
    (state : List StateDecl) (ctor : Option Constructor)
    (ep : Entrypoint) (plan : Backend.Impact.Plan) : Json := Id.run do
  let targetPlanFields := if profile.name == TargetProfile.selected321.name then [
    ("target", toJson profile.name), ("targetProfile", toJson profile)
  ] else []
  let returnFields := if ep.returns.isEmpty then [] else [
    ("returns", toJson (ep.returns.map fun returned => Json.mkObj [
      ("name", toJson returned.name), ("type", toJson (typeName returned.ty)),
      ("visibility", toJson ("public" : String)),
      ("expression", nativeExpressionJson returned.value)]))]
  let constructorFields := match ctor with
    | none => []
    | some value => [("constructor", constructorJson value)]
  return Json.mkObj ([
    ("schemaVersion", toJson (1 : Nat))] ++ targetPlanFields ++ [
    ("contractName", toJson contractName.toString),
    ("entrypoint", toJson ep.name), ("nativeCircuitFile", toJson (nativeCircuitFile contractName ep)),
    ("state", toJson (state.map stateJson)),
    ("circuit", circuitSchemaJson ep.circuit.name.toName ep.circuit),
    ("operations", toJson (plan.operations.zipIdx.map fun (operation, index) =>
      operationJson (plan.activityGuards[index]?.getD none) operation)),
    ] ++ constructorFields ++ returnFields ++ [
    ("reads", toJson (plan.reads.map fun item => Json.mkObj ([
      ("name", toJson item.name),
      ("type", toJson (if item.schema.isSome then "Composite" else typeName item.ty))] ++
      (match item.schema with
        | none => []
        | some schema => [
            ("components", toJson (item.components.map fun (name, ty) => Json.mkObj [
              ("name", toJson name), ("type", toJson (typeName ty))])),
            ("schema", schema)]) ++
      (match item.guard with
        | none => []
        | some guard => [("guard", nativeExpressionJson guard)])))),
    ("guards", toJson (plan.guards.map nativeExpressionJson))])

private unsafe def inspectWithModules (moduleOutputs : Array (Name × ModuleBuildOutput)) :
    CommandElabM (Array (Name × Circuit) × Array (Name × Contract)) := do
  if (← get).messages.hasErrors then
    throwError "cannot export Noctium artifacts after source elaboration errors"
  let circuits ← registeredCircuits moduleOutputs
  let contracts ← registeredContracts moduleOutputs
  let sourceEnv ← getEnv
  let controls := (controlRegistry.getState sourceEnv).filter (!sourceEnv.isImportedConst ·)
  if circuits.isEmpty && controls.isEmpty then throwError "source contains no Noctium circuit declarations"
  for name in controls do validateArtifactName name
  for (name, _) in circuits do validateArtifactName name
  for (name, contract) in contracts do
    validateArtifactName name
    for ep in contract.entrypoints do
      validateArtifactStem ep.name
      unless circuits.any (fun (_, circuit) => circuit.name == ep.circuit.name) do
        throwError "contract entrypoint references imported circuit '{ep.circuit.name}'; include its source declaration in this compilation unit"
  return (circuits, contracts)

private unsafe def inspect : CommandElabM (Array (Name × Circuit) × Array (Name × Contract)) := do
  let moduleOutputs ← rebuildModuleOutputs
  inspectWithModules moduleOutputs

elab "#noctium_check" : command => do
  let (circuits, contracts) ← unsafe inspect
  logInfo m!"checked {circuits.size} circuit(s), {contracts.size} contract(s); target integration unqualified"

private unsafe def checkTarget (profile : TargetProfile) : CommandElabM Unit := do
  let (circuits, contracts) ← unsafe inspect
  logInfo m!"checked {circuits.size} circuit(s), {contracts.size} contract(s); target {profile.name} ({profile.qualification})"

private def parseTargetProfile (source : String) : CommandElabM TargetProfile := do
  match TargetProfile.parse source with
  | .ok profile => pure profile
  | .error message => throwError "invalid target profile: {message}"

elab "#noctium_check_target" profileJson:str : command => do
  let profile ← parseTargetProfile profileJson.getString
  unsafe checkTarget profile

private def compileArtifacts (directory : String) (profile : TargetProfile) : CommandElabM Unit := do
  let moduleOutputs ← unsafe rebuildModuleOutputs
  let (circuits, contracts) ← unsafe inspectWithModules moduleOutputs
  -- Lower everything before creating output files. Unsupported circuits cannot leave partial output.
  let mut lowered := #[]
  let sourceEnv ← getEnv
  let controls := (controlRegistry.getState sourceEnv).filter (!sourceEnv.isImportedConst ·)
  let witnesses := (witnessRegistry.getState sourceEnv).filter (!sourceEnv.isImportedConst ·.circuitName)
  let mut witnessMetadata : Array Json := #[]
  for name in controls do
    validateArtifactName name
    let plan ← unsafe evalConstCheck Json ``Lean.Json name
    lowered := lowered.push (artifactName name ++ ".control.json", plan.pretty)
  for (name, circuit) in circuits do
    match Backend.Zkir.lowerCircuit circuit with
    | .error d => failDiagnostic d
    | .ok json => lowered := lowered.push (artifactName name ++ ".zkir", json.pretty)
  for (name, _) in circuits do
    let some info := circuitRegistry.getState (← getEnv) |>.find? (·.declName == name)
      | throwError "missing circuit registry entry for '{name}'"
    if let some fresh := moduleCircuitFor moduleOutputs name then
      lowered := lowered.push (artifactName name ++ ".specialization.json",
        (Lean.toJson fresh.signatureArtifact).pretty)
    else if let some text := info.specializationArtifact? then
      let artifact ← match Helpers.Specialization.parseSignatureArtifactText text with
        | .ok artifact => pure artifact
        | .error message => throwError "invalid generic specialization signature artifact: {message}"
      lowered := lowered.push (artifactName name ++ ".specialization.json", (Lean.toJson artifact).pretty)
  for info in witnesses do
    let program ← match moduleWitnessProgramFor moduleOutputs info with
      | some fresh => pure fresh
      | none => unsafe evalConstCheck Helpers.Program ``Helpers.Program info.sourceName
    let compiled ← match Witness.compile program info.exportName info.circuitName.toString info.outputName with
      | .ok value => pure value
      | .error diagnostic => failDiagnostic diagnostic
    let witnessPrefix := artifactName info.circuitName
    lowered := lowered.push (witnessPrefix ++ ".witness.json", compiled.binding.compress)
    lowered := lowered.push (witnessPrefix ++ ".witness.control.json", compiled.plan.pretty)
    if let some text := info.observationArtifact? then
      let observation ← match Json.parse text with
        | .ok value => pure value
        | .error message => throwError "invalid source observation artifact: {message}"
      lowered := lowered.push (witnessPrefix ++ ".observations.json", observation.pretty)
    witnessMetadata := witnessMetadata.push (Json.mkObj [("circuit", toJson info.circuitName.toString),
      ("bindingFile", toJson (witnessPrefix ++ ".witness.json")), ("controlFile", toJson (witnessPrefix ++ ".witness.control.json")),
      ("target", toJson ("standalone" : String)), ("nativeWitnessQualified", toJson Bool.false)])
  for (name, contract) in contracts do
    match Contract.validate sourceCapabilities contract with
    | .error diagnostic => failDiagnostic diagnostic
    | .ok _ => pure ()
    for ep in contract.entrypoints do
      let ep := Passes.pruneEntrypoint ep
      let plan ← match Backend.Impact.lower contract.state ep with
        | .error d => failDiagnostic d
        | .ok plan => pure plan
      match Backend.Zkir.lowerEntrypoint contract.state ep with
      | .error d => failDiagnostic d
      | .ok json =>
        lowered := lowered.push (nativeCircuitFile name ep, json.pretty)
        if let some info := witnesses.find? (·.circuitName.toString == ep.circuit.name) then
          let program ← match moduleWitnessProgramFor moduleOutputs info with
            | some fresh => pure fresh
            | none => unsafe evalConstCheck Helpers.Program ``Helpers.Program info.sourceName
          let compiled ← match Witness.compile program info.exportName info.circuitName.toString info.outputName with
            | .ok value => pure value
            | .error diagnostic => failDiagnostic diagnostic
          let compiled ← match Witness.bindEntrypoint compiled json name.toString ep.name
              (nativeCircuitFile name ep) profile.name
              ((plan.reads.drop (Backend.Impact.publicInputReadCount ep.circuit.inputs)).flatMap (·.bindings)) with
            | .ok value => pure value
            | .error diagnostic => failDiagnostic diagnostic
          let witnessPrefix := artifactName name ++ "." ++ ep.name
          lowered := lowered.push (witnessPrefix ++ ".witness.json", compiled.binding.compress)
          lowered := lowered.push (witnessPrefix ++ ".witness.control.json", compiled.plan.pretty)
          witnessMetadata := witnessMetadata.push (Json.mkObj [("circuit", toJson ep.circuit.name),
            ("bindingFile", toJson (witnessPrefix ++ ".witness.json")), ("controlFile", toJson (witnessPrefix ++ ".witness.control.json")),
            ("target", toJson ("entrypoint" : String)), ("contract", toJson name.toString),
            ("entrypoint", toJson ep.name), ("nativeWitnessQualified", toJson Bool.false)])
      let planJson := nativePlanJson profile name contract.state contract.constructor ep plan
      lowered := lowered.push (nativePlanFile name ep, planJson.pretty)
  unless uniqueNames (lowered.toList.map (·.1)) do
    throwError "generated artifact filenames collide; rename the circuit or contract entrypoint"
  let contractMetadata := contracts.map fun (name, contract) =>
    let entrypoints := contract.entrypoints.map fun ep => Json.mkObj ([
      ("name", toJson ep.name), ("circuit", toJson ep.circuit.name),
      ("nativeCircuitFile", toJson (nativeCircuitFile name ep)),
      ("nativePlanFile", toJson (nativePlanFile name ep)),
      ("nativeCircuitQualified", toJson Bool.false),
      ("effects", toJson (ep.effects.zipIdx.map fun (effect, index) =>
        guardedEffectJson (ep.effectGuards[index]?.getD none) effect))] ++
      (if ep.returns.isEmpty then [] else [
        ("returns", toJson (ep.returns.map fun returned => Json.mkObj [
          ("name", toJson returned.name), ("type", toJson (typeName returned.ty)),
          ("visibility", toJson ("public" : String)),
          ("expression", nativeExpressionJson returned.value)]))]))
    let constructorFields := match contract.constructor with
      | none => []
      | some ctor => [("constructor", constructorJson ctor)]
    Json.mkObj ([
      ("name", toJson name.toString),
      ("state", toJson (contract.state.map stateJson)),
      ("entrypoints", toJson entrypoints)] ++ constructorFields)
  let controlFields := if controls.isEmpty then [] else [
    ("hostControlPlans", toJson (controls.toList.map fun name => Json.mkObj [
      ("name", toJson name.toString), ("file", toJson (artifactName name ++ ".control.json")),
      ("nativeGuardQualified", toJson Bool.false)]))]
  let witnessFields := if witnessMetadata.isEmpty then [] else [("hostWitnessPlans", Json.arr witnessMetadata)]
  let metadata := Json.mkObj ([
    ("schemaVersion", toJson (1 : Nat)), ("target", toJson profile.name),
    ("targetProfile", toJson profile),
    ("qualification", toJson ("unqualified-relation-and-state-description" : String)),
    ("deployable", toJson Bool.false),
    ("contracts", Json.arr contractMetadata),
    ("circuits", toJson (circuits.map fun (name, circuit) => circuitSchemaJson name circuit))] ++ controlFields ++ witnessFields)
  let path : System.FilePath := directory
  liftIO <| IO.FS.createDirAll path
  for (name, content) in lowered do
    liftIO <| IO.FS.writeFile (path / name) (content ++ "\n")
  liftIO <| IO.FS.writeFile (path / "noctium.json") (metadata.pretty ++ "\n")
  let nativeCount : Nat := contracts.foldl (fun total (_, contract) => total + contract.entrypoints.length) 0
  if controls.isEmpty then
    logInfo m!"emitted {circuits.size} circuit relation(s), {nativeCount} native entrypoint relation(s), and state metadata to {path}; not a deployable contract bundle"
  else
    logInfo m!"emitted {controls.size} host-only control plan(s), {circuits.size} circuit relation(s), and {nativeCount} native entrypoint relation(s) to {path}; structured native guards unavailable"

elab "#noctium_compile" directory:str : command =>
  compileArtifacts directory.getString TargetProfile.sourceBaseline

elab "#noctium_compile_target" directory:str profileJson:str : command => do
  let profile ← parseTargetProfile profileJson.getString
  compileArtifacts directory.getString profile

end Noctium.Compiler
