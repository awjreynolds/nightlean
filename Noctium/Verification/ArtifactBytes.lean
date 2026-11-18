import Lean

namespace Noctium.Verification.ArtifactBytes
open Lean

/-- Exact public file bytes. No UTF-8 conversion or whitespace normalization
occurs before the checked parser. This parser qualifies an ASCII JSON subset. -/
abbrev Bytes := List UInt8

def maxBytes : Nat := 65536
def maxDepth : Nat := 64
def numberLimit : Nat := 18446744073709551616

private def whitespace (byte : UInt8) : Bool :=
  byte == 32 || byte == 9 || byte == 10 || byte == 13

private def trim : Bytes → Bytes
  | [] => []
  | byte :: rest => if whitespace byte then trim rest else byte :: rest

private def digit (byte : UInt8) : Bool := 48 ≤ byte.toNat && byte.toNat ≤ 57
private def hex (byte : UInt8) : Option Nat :=
  let n := byte.toNat
  if 48 ≤ n && n ≤ 57 then some (n - 48)
  else if 65 ≤ n && n ≤ 70 then some (n - 55)
  else if 97 ≤ n && n ≤ 102 then some (n - 87)
  else none

private def escape : Bytes → Except String (Char × Bytes)
  | 34 :: rest => pure ('"', rest)
  | 92 :: rest => pure ('\\', rest)
  | 47 :: rest => pure ('/', rest)
  | 98 :: rest => pure (Char.ofNat 8, rest)
  | 102 :: rest => pure (Char.ofNat 12, rest)
  | 110 :: rest => pure ('\n', rest)
  | 114 :: rest => pure ('\r', rest)
  | 116 :: rest => pure ('\t', rest)
  | 117 :: a :: b :: c :: d :: rest => do
    let some a := hex a | throw "invalid JSON Unicode escape"
    let some b := hex b | throw "invalid JSON Unicode escape"
    let some c := hex c | throw "invalid JSON Unicode escape"
    let some d := hex d | throw "invalid JSON Unicode escape"
    let code := a * 4096 + b * 256 + c * 16 + d
    if code ≤ 127 then pure (Char.ofNat code, rest)
    else throw "only ASCII JSON strings are qualified"
  | _ => throw "invalid JSON escape"

private def string : Nat → Bytes → List Char → Except String (String × Bytes)
  | 0, _, _ => throw "JSON string fuel exhausted"
  | _ + 1, [], _ => throw "unterminated JSON string"
  | fuel + 1, byte :: rest, chars =>
    if byte == 34 then pure (String.ofList chars.reverse, rest)
    else if byte == 92 then do
      let (char, remaining) ← escape rest
      string fuel remaining (char :: chars)
    else if 32 ≤ byte.toNat && byte.toNat ≤ 127 then
      string fuel rest (Char.ofNat byte.toNat :: chars)
    else throw "unescaped control or unsupported non-ASCII JSON byte"

private def natural : Nat → Bytes → Nat → Except String (Nat × Bytes)
  | 0, _, _ => throw "JSON integer fuel exhausted"
  | _ + 1, [], n => pure (n, [])
  | fuel + 1, byte :: rest, n =>
    if digit byte then
      let next := n * 10 + byte.toNat - 48
      if next < numberLimit then natural fuel rest next else throw "JSON integer exceeds qualified UInt64 range"
    else pure (n, byte :: rest)

private def number (fuel : Nat) : Bytes → Except String (Json × Bytes)
  | [] => throw "missing JSON integer"
  | first :: rest => do
    if first == 48 then
      if rest.head?.any digit then throw "leading zero in JSON integer"
      else pure (toJson (0 : Nat), rest)
    else if digit first then
      let (n, remaining) ← natural fuel rest (first.toNat - 48)
      pure (toJson n, remaining)
    else throw "only nonnegative JSON integers are qualified"

private def literal (token : Bytes) (value : Json) (input : Bytes) : Except String (Json × Bytes) :=
  if token.isPrefixOf input then pure (value, input.drop token.length)
  else throw "invalid JSON literal"

mutual
  private def value : Nat → Nat → Bytes → Except String (Json × Bytes)
    | 0, _, _ => throw "JSON value fuel exhausted"
    | fuel + 1, depth, input =>
      match trim input with
      | [] => throw "missing JSON value"
      | 123 :: rest => if depth == 0 then throw "JSON nesting exceeds qualified bound" else object fuel (depth - 1) rest [] true
      | 91 :: rest => if depth == 0 then throw "JSON nesting exceeds qualified bound" else array fuel (depth - 1) rest [] true
      | 34 :: rest => do
        let (text, remaining) ← string fuel rest []
        pure (.str text, remaining)
      | 110 :: rest => literal [117, 108, 108] .null rest
      | 116 :: rest => literal [114, 117, 101] (.bool true) rest
      | 102 :: rest => literal [97, 108, 115, 101] (.bool false) rest
      | input => number fuel input

  private def array : Nat → Nat → Bytes → List Json → Bool → Except String (Json × Bytes)
    | 0, _, _, _, _ => throw "JSON array fuel exhausted"
    | fuel + 1, depth, input, values, allowEmpty => do
      let input := trim input
      if input.head? == some 93 then
        if allowEmpty then pure (.arr values.reverse.toArray, input.tail)
        else throw "trailing JSON array comma"
      else
        let (item, remaining) ← value fuel depth input
        match trim remaining with
        | 93 :: rest => pure (.arr (item :: values).reverse.toArray, rest)
        | 44 :: rest => array fuel depth rest (item :: values) false
        | _ => throw "missing JSON array delimiter"

  private def object : Nat → Nat → Bytes → List (String × Json) → Bool → Except String (Json × Bytes)
    | 0, _, _, _, _ => throw "JSON object fuel exhausted"
    | fuel + 1, depth, input, fields, allowEmpty => do
      match trim input with
      | 125 :: rest =>
        if allowEmpty then pure (Json.mkObj fields.reverse, rest)
        else throw "trailing JSON object comma"
      | 34 :: rest =>
        let (key, remaining) ← string fuel rest []
        if fields.any (fun pair => pair.1 == key) then throw "duplicate JSON object key"
        let 58 :: remaining := trim remaining | throw "missing JSON object colon"
        let (item, remaining) ← value fuel depth remaining
        match trim remaining with
        | 125 :: rest => pure (Json.mkObj ((key, item) :: fields).reverse, rest)
        | 44 :: rest => object fuel depth rest ((key, item) :: fields) false
        | _ => throw "missing JSON object delimiter"
      | _ => throw "missing JSON object string key"
end

/-- Total, bounded, exact byte-to-JSON semantics for the qualified subset.
Unsupported integer/string forms fail closed. Complete consumption is required. -/
def parse (bytes : Bytes) : Except String Json := do
  if bytes.length > maxBytes then throw "JSON artifact exceeds qualified byte bound"
  let (result, remaining) ← value (bytes.length + 1) maxDepth bytes
  if (trim remaining).isEmpty then pure result else throw "trailing JSON artifact bytes"

def tree (bytes : Bytes) : Json := (parse bytes).toOption.getD .null

/-- A successful downstream translation validator implies exact parsing to its
selected tree, without trusting an external byte-to-tree quotation. -/
theorem validated_tree {α : Type} (decode : Json → Except String α) (bytes : Bytes) (expected : α)
    (valid : (parse bytes).bind decode = .ok expected) :
    parse bytes = .ok (tree bytes) ∧ decode (tree bytes) = .ok expected := by
  cases parsed : parse bytes with
  | error message => rw [parsed] at valid; contradiction
  | ok json =>
    rw [parsed] at valid
    have selected : tree bytes = json := by rw [tree, parsed]; rfl
    rw [selected]
    exact ⟨rfl, valid⟩

end Noctium.Verification.ArtifactBytes
