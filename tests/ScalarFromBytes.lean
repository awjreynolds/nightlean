import Noctium.Frontend
import Noctium.Disclosure

open scoped Noctium
open Noctium

noctium_circuit scalarByteValues where
  private wide64 : Bytes 64
  private maximum1024 : Bytes 1024
  private empty0 : Bytes 0
  private nativeEnabled : Bool
  private scalarEnabled : Bool
  let first32 : Bytes32 := sliceBytes(wide64, 0, 32)
  assert eq(fromBytes(Native, first32), fromBytes32(Native, first32))
  assert eq(fromBytes(JubjubScalar, first32), fromBytes32(JubjubScalar, first32))
  output decodedNative64 : Native := disclose(fromBytes(Native, wide64))
  output decodedScalar64 : Native := disclose(jubjubScalarToNative(fromBytes(JubjubScalar, wide64)))
  output decodedNative1024 : Native := disclose(fromBytes(Native, maximum1024))
  output decodedScalar1024 : Native := disclose(jubjubScalarToNative(fromBytes(JubjubScalar, maximum1024)))
  output decodedEmptyNative : Native := disclose(fromBytes(Native, assertThen(nativeEnabled, empty0)))
  output decodedEmptyScalar : Native := disclose(jubjubScalarToNative(fromBytes(JubjubScalar,
    assertThen(scalarEnabled, empty0))))
end

noctium_contract ScalarFromBytes where
  entry decode uses scalarByteValues where
    return native64 : Native := decodedNative64
    return scalar64 : Native := decodedScalar64
    return native1024 : Native := decodedNative1024
    return scalar1024 : Native := decodedScalar1024
    return emptyNative : Native := decodedEmptyNative
    return emptyScalar : Native := decodedEmptyScalar
  end
end

private def scalarBytesContext : EvalContext :=
  {modulus := Field.modulus, poseidon2 := fun _ _ _ => pure 0}

private def full64 : Expr (.bytes 64) := .bytesLiteral 64 (List.replicate 64 255)
private def full64Integer : Nat := 2 ^ 512 - 1

#guard match (Expr.fromBytes (target := .native) full64).eval scalarBytesContext [] with
  | .ok value => value == full64Integer % Field.modulus
  | .error _ => Bool.false
#guard match (Expr.fromBytes (target := .jubjubScalar) full64).eval scalarBytesContext [] with
  | .ok value => value == full64Integer % Jubjub.scalarOrder
  | .error _ => Bool.false
#guard full64Integer % Jubjub.scalarOrder !=
  (full64Integer % Field.modulus) % Jubjub.scalarOrder

#guard match (Expr.fromBytes (target := .native)
    (.bytesLiteral 1024 (List.replicate 1024 0))).validate Capabilities.source [] with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match (Expr.fromBytes (target := .native)
    (.bytesLiteral 1025 (List.replicate 1025 0))).validate Capabilities.source [] with
  | .error message => message == "byte string length exceeds the maximum of 1024"
  | .ok _ => Bool.false

#guard match (Expr.fromBytes (target := .bool) (.bytesLiteral 1 [1])).validate
    Capabilities.source [] with
  | .error message => message == "fromBytes supports only Native and JubjubScalar"
  | .ok _ => Bool.false

private def undisclosedEmptyDecode : Circuit := {
  name := "undisclosedEmptyDecode"
  inputs := [{name := "secretEmpty", ty := .bytes 0, visibility := .private}]
  outputs := [{name := "decoded", ty := .native, value := .fromBytes (length := 0) (.ref "secretEmpty")}]
}

#guard match Disclosure.circuit undisclosedEmptyDecode with
  | .error diagnostic => diagnostic.message.startsWith "undisclosed private parameter"
  | .ok _ => Bool.false
