import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit issue69CompositeMap where
  private account : Bytes32
  private c1x : Native
  private c1y : Native
  private c2x : Native
  private c2y : Native
end

noctium_contract Issue69CompositeMap where
  tree balances : Bytes32 => struct Ciphertext4 {
    c1x : Native
    c1y : Native
    c2x : Native
    c2y : Native
  }
  entry update uses issue69CompositeMap where
    member balances[disclose(account)] as present
    when eq(present, true) read balances[disclose(account)] as before
    write balances[disclose(account)] := fields(disclose(c1x), disclose(c1y), disclose(c2x), disclose(c2y))
    read balances[disclose(account)] as observed
    require eq(observed_c1x, c1x)
    require eq(observed_c1y, c1y)
    require eq(observed_c2x, c2x)
    require eq(observed_c2y, c2y)
  end
end

private def issue69CompositeEntry : Entrypoint :=
  match Issue69CompositeMap.entrypoints with
  | ep :: _ => ep
  | _ => {name := "missing", circuit := {name := "missing"}}

#guard match Backend.Zkir.lowerEntrypoint Issue69CompositeMap.state issue69CompositeEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

private def issue69MissingFieldDisclosure : Entrypoint :=
  {issue69CompositeEntry with effects := issue69CompositeEntry.effects.map fun effect =>
    match effect with
    | .writeCompositePath state keys type values =>
      .writeCompositePath state keys type (values.take 3 ++ [.mk .native (.ref "c2y")])
    | other => other}

#guard match Disclosure.entrypoint issue69MissingFieldDisclosure with
  | .error _ => Bool.true
  | .ok _ => Bool.false
