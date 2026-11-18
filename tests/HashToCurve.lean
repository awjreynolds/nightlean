import Noctium.Frontend
import Noctium.Disclosure
import Noctium.Backend.NativeProducer

open scoped Noctium
open Noctium
open Lean
open Noctium.Backend.Native

noctium_circuit hashCurveInputs where
  private left : Native
  private right : Native
  private enabled : Bool
  let emptyComputed : JubjubPoint := assertThen(enabled, hashToCurve([]))
  let oneComputed : JubjubPoint := hashToCurve([left])
  let domainComputed : JubjubPoint := hashToCurve([17, left, right])
  let scalarComputed : JubjubScalar := jubjubScalarFromNative(right)
  let composedComputed : JubjubPoint := jubjubAdd(domainComputed,
    jubjubMulGenerator(scalarComputed))
  let encodedComputed : Bytes32 := toBytes32(composedComputed)
  output emptyPointValue : JubjubPoint := disclose(emptyComputed)
  output onePointValue : JubjubPoint := disclose(oneComputed)
  output domainPointValue : JubjubPoint := disclose(domainComputed)
  output composedPointValue : JubjubPoint := disclose(composedComputed)
  output encodedPointValue : Bytes32 := disclose(encodedComputed)
  output scalarValue : JubjubScalar := disclose(scalarComputed)
end

noctium_contract HashToCurve where
  entry inspect uses hashCurveInputs where
    return emptyPoint : JubjubPoint := disclose(emptyPointValue)
    return onePoint : JubjubPoint := disclose(onePointValue)
    return domainPoint : JubjubPoint := disclose(domainPointValue)
    return composedPoint : JubjubPoint := disclose(composedPointValue)
    return encodedPoint : Bytes32 := disclose(encodedPointValue)
    return scalarResult : JubjubScalar := disclose(scalarValue)
  end
end

private def hashToCurveEvalContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => pure 0
  jubjub := {
    pointValid := fun _ => pure ()
    hashToCurve := fun values => pure (values.length, values.headD 0)
  }
}

private def invalidHashToCurvePointContext : EvalContext := {
  hashToCurveEvalContext with jubjub := {
    hashToCurveEvalContext.jubjub with
    pointValid := fun _ => .error "invalid hash_to_curve point"
    hashToCurve := fun _ => pure (0, 0)
  }
}

private def unavailableHashToCurveContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => pure 0
}

#guard match (Expr.hashToCurve []).eval hashToCurveEvalContext [] with
  | .ok (0, 0) => _root_.Bool.true
  | _ => _root_.Bool.false
#guard match (Expr.hashToCurve [.native 17, .native 9]).eval hashToCurveEvalContext [] with
  | .ok (2, 17) => _root_.Bool.true
  | _ => _root_.Bool.false
#guard match (Expr.hashToCurve [.native 9, .native 17]).eval hashToCurveEvalContext [] with
  | .ok (2, 9) => _root_.Bool.true
  | _ => _root_.Bool.false
#guard match (Expr.assertE (.bool Bool.false) (Expr.hashToCurve [])).eval
    hashToCurveEvalContext [] with
  | .error "helper assertion failed" => _root_.Bool.true
  | _ => _root_.Bool.false
#guard match (Expr.hashToCurve []).eval unavailableHashToCurveContext [] with
  | .error "qualified hash_to_curve oracle is unavailable" => _root_.Bool.true
  | _ => _root_.Bool.false
#guard match (Expr.hashToCurve []).eval invalidHashToCurvePointContext [] with
  | .error "invalid hash_to_curve point" => _root_.Bool.true
  | _ => _root_.Bool.false
#guard match (Expr.hashToCurve [Expr.native Field.modulus]).eval hashToCurveEvalContext [] with
  | .error "noncanonical native constant" => _root_.Bool.true
  | _ => _root_.Bool.false

#guard match (Expr.hashToCurve [.native 1]).validate
    {Capabilities.source with hashToCurve := _root_.Bool.false} [] with
  | .error "target lacks qualified hash_to_curve support" => _root_.Bool.true
  | _ => _root_.Bool.false
#guard match (Expr.hashToCurve [.native 1]).validate
    {Capabilities.source with jubjub := _root_.Bool.false} [] with
  | .error "target lacks qualified Jubjub support" => _root_.Bool.true
  | _ => _root_.Bool.false
#guard match (Expr.hashToCurve
    (List.replicate (Types.defaultLimits.maxVectorLength + 1) (.native 0))).validate
    Capabilities.source [] with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false

#guard match Disclosure.circuit {
  name := "undisclosedHashToCurve"
  inputs := [{name := "secret", ty := .native, visibility := .private}]
  outputs := [{name := "point", ty := .jubjubPoint, value := (Expr.hashToCurve [Expr.ref "secret"])}]
} with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false

/-- error: Noctium expression type mismatch -/
#guard_msgs in
noctium_circuit invalidHashToCurveInput where
  private enabled : Bool
  output point : JubjubPoint := hashToCurve([enabled])
end

private def hashToCurveProducerState (names : List String)
    (types : List NativeValueType) (extra : List (String × Json) := []) : Except String State := do
  unless names.length == types.length do throw "hash_to_curve fixture input mismatch"
  let expected : Expected := {
    mode := .relation, inputs := [], groups := [], returns := [], assertions := [], bounds := []}
  let definitions := (names.zip types).map fun (name, valueType) =>
    (name, ({term := .input name, maximum := 1, valueType} : Fact))
  let state : State := {definitions := definitions}
  let instruction := Json.mkObj <| [
    ("op", toJson ("hash_to_curve" : String)), ("inputs", toJson names),
    ("output", toJson ("%point" : String))] ++ extra
  validateInstruction expected state instruction

private def hashToCurveProducerFact (names : List String)
    (types : List NativeValueType) : Option Fact :=
  match hashToCurveProducerState names types with
  | .ok state => state.definitions.lookup "%point"
  | .error _ => none

#guard hashToCurveProducerState [] [] |>.isOk
#guard hashToCurveProducerState ["%left"] [.native] |>.isOk
#guard hashToCurveProducerState ["%domain", "%left", "%right"]
  [.native, .native, .native] |>.isOk
#guard !(hashToCurveProducerState ["%bool"] [.bool] |>.isOk)
#guard !(hashToCurveProducerState ["%bytes"] [.bytes32] |>.isOk)
#guard !(hashToCurveProducerState ["%scalar"] [.jubjubScalar] |>.isOk)
#guard !(hashToCurveProducerState ["%point"] [.jubjubPoint] |>.isOk)
#guard !(hashToCurveProducerState ["%left"] [.native] [("extra", toJson Bool.true)] |>.isOk)
#guard !(hashToCurveProducerState
  ((List.range (Types.defaultLimits.maxVectorLength + 1)).map fun index => s!"%field{index}")
  (List.replicate (Types.defaultLimits.maxVectorLength + 1) .native) |>.isOk)
#guard match hashToCurveProducerFact ["%left", "%right"] [.native, .native] with
  | some fact => fact.valueType == .jubjubPoint && fact.term == hashToCurveTerm [
      .input "%left", .input "%right"]
  | none => _root_.Bool.false
#guard match (hashToCurveProducerFact ["%left", "%right"] [.native, .native],
    hashToCurveProducerFact ["%right", "%left"] [.native, .native]) with
  | (some leftFirst, some rightFirst) => leftFirst.term != rightFirst.term
  | _ => _root_.Bool.false
