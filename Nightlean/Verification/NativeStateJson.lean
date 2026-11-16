import Lean
import Nightlean.Verification.NativeState

namespace Nightlean.Verification.NativeStateJson
open Lean NativeRelation NativeState

inductive SymbolicOp where
  | push (value : Operand) (storage : _root_.Bool)
  | popeq (value : Operand) (alignment : Alignment)
  | dup
  | index (slot : Nat) (path : _root_.Bool)
  | member
  | insert (levels : Nat)
  deriving Repr, DecidableEq

def SymbolicOp.instantiate (w : Assignment) : SymbolicOp → Op
  | .push value storage => .push (field (value.read w)) storage
  | .popeq value alignment => .popeq ⟨alignment, value.read w⟩
  | .dup => .dup
  | .index slot path => .index slot path
  | .member => .member
  | .insert n => .insert n

private def ensure (condition : _root_.Bool) (message : String) : Except String Unit :=
  if condition then pure () else throw message
private def exactFields (json : Json) (fields : List String) : Except String Unit := do
  let actual := (← json.getObj?).toList.map Prod.fst
  ensure (actual.length == fields.length && actual.all fields.contains && fields.all actual.contains)
    "unexpected plan fields"
private def str (json : Json) (name : String) : Except String String :=
  (json.getObjVal? name).bind Json.getStr?

/-- Fuel-bounded structural JSON equality avoids Lean.Json's opaque partial
BEq implementation in kernel certificates. Exhausted fuel rejects. -/
private def sameJson : Nat → Json → Json → _root_.Bool
  | 0, _, _ => false
  | _ + 1, .null, .null => true
  | _ + 1, .bool a, .bool b => a == b
  | _ + 1, .str a, .str b => a == b
  | _ + 1, .num a, .num b => a.mantissa == b.mantissa && a.exponent == b.exponent
  | fuel + 1, .arr a, .arr b => a.size == b.size && (a.toList.zip b.toList).all (fun p => sameJson fuel p.1 p.2)
  | fuel + 1, .obj a, .obj b =>
    let left := a.toList
    let right := b.toList
    left.length == right.length && (left.zip right).all (fun p => p.1.1 == p.2.1 && sameJson fuel p.1.2 p.2.2)
  | _, _, _ => false

private def naturalField (json : Json) (name : String) : Except String Nat := do
  match ← json.getObjVal? name with
  | .num number =>
    ensure (number.exponent == 0) "native plan index must be an integer"
    match number.mantissa with
    | .ofNat n => pure n
    | .negSucc _ => throw "native plan index must be nonnegative"
  | _ => throw "native plan index must be a number"

private def expression (json : Json) : Except String Operand := do
  let tag ← str json "tag"
  if tag == "reference" then
    exactFields json ["tag", "name"]
    let name ← str json "name"
    let target ← match name with
      | "root" => pure "%input_root"
      | "campaign" => pure "%input_campaign"
      | "suppliedNullifier" | "nullifier" => pure "%input_suppliedNullifier"
      | "storedRoot" => pure "%input_storedRoot"
      | "storedCampaign" => pure "%input_storedCampaign"
      | _ => throw "unsupported claim plan reference"
    return .reference target
  if tag == "bool" then
    exactFields json ["tag", "value"]
    return .immediate (bit (← (← json.getObjVal? "value").getBool?))
  -- The actual storage write is the native encoding of source Bool.true.
  exactFields json ["tag", "condition", "yes", "no"]
  ensure (sameJson 1000 json (Json.mkObj [
    ("tag", toJson ("select" : String)),
    ("condition", Json.mkObj [("tag", toJson ("bool" : String)), ("value", toJson true)]),
    ("yes", Json.mkObj [("tag", toJson ("constant" : String)), ("value", toJson ("1" : String))]),
    ("no", Json.mkObj [("tag", toJson ("constant" : String)), ("value", toJson ("0" : String))])]))
      "unsupported claim storage expression"
  return .immediate one

private def operation (json : Json) : Except String SymbolicOp := do
  match ← str json "op" with
  | "push" =>
    exactFields json ["op", "alignment", "expression", "storage"]
    ensure ((← str json "alignment") == "field") "unsupported push alignment"
    return .push (← expression (← json.getObjVal? "expression"))
      (← (← json.getObjVal? "storage").getBool?)
  | "popeq" =>
    exactFields json ["op", "alignment", "expression"]
    let alignment ← match ← str json "alignment" with
      | "field" => pure Alignment.field
      | "bit" => pure Alignment.bit
      | _ => throw "unsupported read alignment"
    return .popeq (← expression (← json.getObjVal? "expression")) alignment
  | "dup" => exactFields json ["op"]; return .dup
  | "index" =>
    exactFields json ["op", "slot", "pushPath"]
    return .index (← naturalField json "slot")
      (← (← json.getObjVal? "pushPath").getBool?)
  | "member" => exactFields json ["op"]; return .member
  | "insert" =>
    exactFields json ["op", "n"]
    return .insert (← naturalField json "n")
  | _ => throw "unsupported claim VM operation"

private def reference (name : String) : Json :=
  Json.mkObj [("tag", toJson ("reference" : String)), ("name", toJson name)]
private def equality (left right : Json) : Json :=
  Json.mkObj [("tag", toJson ("eq" : String)), ("left", left), ("right", right)]

def schema : Json := Json.arr #[
  Json.mkObj [("name", toJson ("acceptedRoot" : String)), ("kind", Json.mkObj [("cell", toJson ("Native" : String))])],
  Json.mkObj [("name", toJson ("campaignId" : String)), ("kind", Json.mkObj [("cell", toJson ("Native" : String))])],
  Json.mkObj [("name", toJson ("spent" : String)), ("kind", Json.mkObj [("map", toJson (["Native", "Bool"] : List String))])]]
def reads : Json := Json.arr ((["root", "campaign", "suppliedNullifier", "storedRoot", "storedCampaign"].map
  (fun name => Json.mkObj [("name", toJson name), ("type", toJson ("Native" : String))]) ++
  [Json.mkObj [("name", toJson ("_nightlean_absence_5" : String)), ("type", toJson ("Bool" : String))]]).toArray)
def guards : Json := Json.arr #[
  equality (reference "storedRoot") (reference "root"),
  equality (reference "storedCampaign") (reference "campaign"),
  equality (reference "_nightlean_absence_5")
    (Json.mkObj [("tag", toJson ("bool" : String)), ("value", toJson false)])]

/-- Decode the semantic plan fields and check their exact schema/read/guard
layout. Target profile and descriptive circuit metadata are carried as JSON,
not treated as authenticated build or implementation evidence. -/
def decode (json : Json) : Except String (List SymbolicOp) := do
  exactFields json ["targetProfile", "target", "state", "schemaVersion", "reads", "operations",
    "nativeCircuitFile", "guards", "entrypoint", "contractName", "circuit"]
  ensure ((← naturalField json "schemaVersion") == 1) "unsupported plan schema version"
  ensure ((← str json "target") == "midnight-ledger-9-zkir-3.2.1") "unexpected target"
  ensure ((← str json "contractName") == "PrivateClaim" && (← str json "entrypoint") == "claim" &&
    (← str json "nativeCircuitFile") == "PrivateClaim.claim.zkir") "unexpected claim artifact identity"
  ensure (sameJson 1000 (← json.getObjVal? "state") schema) "unexpected native state slots"
  ensure (sameJson 1000 (← json.getObjVal? "reads") reads) "unexpected ordered native read declarations"
  ensure (sameJson 1000 (← json.getObjVal? "guards") guards) "unexpected state requirements"
  (← (← json.getObjVal? "operations").getArr?).toList.mapM operation

end Nightlean.Verification.NativeStateJson
