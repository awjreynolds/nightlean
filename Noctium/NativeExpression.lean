import Lean
import Noctium.IR

namespace Noctium.NativeExpression
open Lean

def typeName : Ty → String
  | .native => "Native"
  | .bool => "Bool"
  | .uint maximum => s!"UIntRange<{maximum + 1}>"
  | .bytes byteLength => s!"Bytes<{byteLength}>"
  | .jubjubScalar => "JubjubScalar"
  | .jubjubPoint => "JubjubPoint"
  | .foreign kind => kind.sourceName

def foreignConstantJson (kind : Foreign.Kind) (value : kind.Denote) : Json :=
  Json.mkObj [
    ("tag", toJson ("foreignConstant" : String)),
    ("type", toJson kind.sourceName),
    ("encoding", toJson ((Foreign.encodeValue kind value).toOption.getD [] |>.map toString))]

private def nativeExpressionJson : Expr ty → Json
  | .copyValue value => nativeExpressionJson value
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
  | .transientHash values => Json.mkObj [("tag", toJson ("transientHash" : String)),
      ("values", toJson (values.map nativeExpressionJson))]
  | .toBytes32 value => Json.mkObj [("tag", toJson ("toBytes32" : String)),
      ("value", nativeExpressionJson value)]
  | .fromBytes32 (target := target) value => Json.mkObj [("tag", toJson ("fromBytes32" : String)),
      ("type", toJson (typeName target)), ("value", nativeExpressionJson value)]
  | .fromBytes (target := target) (length := length) value => Json.mkObj [
      ("tag", toJson ("fromBytes" : String)), ("type", toJson (typeName target)),
      ("length", toJson length), ("value", nativeExpressionJson value)]
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
  | .hashToCurve values => Json.mkObj [("tag", toJson ("hashToCurve" : String)),
      ("values", toJson (values.map nativeExpressionJson))]
  | .foreignBase curve value => foreignConstantJson (.base curve) value
  | .foreignScalar curve value => foreignConstantJson (.scalar curve) value
  | .foreignIdentity curve => foreignConstantJson (.point curve) .identity
  | .foreignEncodedField (kind := kind) value index => Json.mkObj [
      ("tag", toJson ("foreignEncodedField" : String)),
      ("value", nativeExpressionJson value), ("index", toJson index)]
  | .foreignUnary operation value => Json.mkObj [
      ("tag", toJson ("foreignUnary" : String)),
      ("operation", toJson operation.name), ("value", nativeExpressionJson value)]
  | .foreignBinary operation left right => Json.mkObj [
      ("tag", toJson ("foreignBinary" : String)),
      ("operation", toJson operation.name),
      ("left", nativeExpressionJson left), ("right", nativeExpressionJson right)]
  | .foreignToBytes value => Json.mkObj [
      ("tag", toJson ("foreignToBytes" : String)), ("value", nativeExpressionJson value)]
  | .foreignFromBytes (kind := kind) (length := length) value => Json.mkObj [
      ("tag", toJson ("foreignFromBytes" : String)),
      ("type", toJson kind.sourceName), ("length", toJson length),
      ("value", nativeExpressionJson value)]
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

/-- Symbolic source expressions for the native runtime. Values are AST constants or references,
never an execution witness. Decimal field constants avoid JavaScript number truncation. -/
def toJson {ty : Ty} (value : Expr ty) : Json := nativeExpressionJson value

end Noctium.NativeExpression
