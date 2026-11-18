import Noctium.Frontend
import Noctium.Disclosure

open scoped Noctium
open Noctium

noctium_circuit transientHashValues where
  private a : Native
  private b : Native
  private c : Native
  private d : Native
  private e : Native
  private enabled : Bool
  assert eq(poseidon2(7, a, b), transientHashNativeVector([7, a, b]))
  output emptyHash : Native := transientHashNativeVector([])
  output singleHash : Native := disclose(transientHashNativeVector([a]))
  output legacyHash : Native := disclose(poseidon2(7, a, b))
  output tripleHash : Native := disclose(transientHashNativeVector([7, a, b]))
  output orderedHash : Native := disclose(transientHashNativeVector([a, b, c, d, e]))
  output checkedHash : Native := disclose(transientHashNativeVector([assertThen(enabled, a), b, c, d, e]))
end

noctium_contract TransientHash where
  entry hash uses transientHashValues where
    return empty : Native := emptyHash
    return single : Native := singleHash
    return legacy : Native := legacyHash
    return triple : Native := tripleHash
    return ordered : Native := orderedHash
    return checked : Native := checkedHash
  end
end

private def noHashOracle : EvalContext :=
  {modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "legacy oracle unavailable"}

#guard match (Expr.transientHash []).eval noHashOracle [] with
  | .error _ => Bool.true
  | .ok _ => Bool.false

#guard match (Expr.transientHash (List.replicate 1024 (.native 0))).validate
    Capabilities.source [] with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match (Expr.transientHash (List.replicate 1025 (.native 0))).validate
    Capabilities.source [] with
  | .error _ => Bool.true
  | .ok _ => Bool.false

#guard match (Expr.transientHash [.native 0]).validate
    {Capabilities.source with poseidon2 := _root_.Bool.false} [] with
  | .error _ => Bool.true
  | .ok _ => Bool.false

private def undisclosedVector : Circuit := {
  name := "undisclosedVector"
  inputs := [{name := "secret", ty := .native, visibility := .private}]
  outputs := [{name := "digest", ty := .native, value := .transientHash [.ref "secret"]}]
}

#guard match Disclosure.circuit undisclosedVector with
  | .error diagnostic => diagnostic.message.startsWith "undisclosed private parameter"
  | .ok _ => Bool.false
