import Noctium.Frontend

open scoped Noctium

noctium_circuit callClaimInput where
  public target : Bytes32
  public entryHash : Bytes32
  public enabled : Bool
  private opening : Native
  private argument : Native
  private expectedBalance : Native
  private expectedCount : UInt 64
  private expectedEnabled : Bool
end

noctium_contract NativeCallClaims where
  cell marker : Native
  entry claim uses callClaimInput where
    if enabled then {
      claimContractCall(target, entryHash,
        disclose(transientHashNativeVector([
          opening, argument, expectedBalance,
          cast(Native, expectedCount), cast(Native, expectedEnabled)])))
    } else {}
    return didClaim : Bool := enabled
  end
end

private def claimEntry : Noctium.Entrypoint :=
  match NativeCallClaims.entrypoints with
  | found :: _ => found
  | [] => {name := "missing", circuit := {name := "missing"}}

private def privateClaimInputRejects (name : String) : _root_.Bool :=
  let checked := {claimEntry with returns := [], circuit := {claimEntry.circuit with
    inputs := claimEntry.circuit.inputs.map fun input =>
      if input.name == name then {input with visibility := .private} else input}}
  !(Noctium.Disclosure.entrypoint checked).isOk

#guard privateClaimInputRejects "target"
#guard privateClaimInputRejects "entryHash"
#guard privateClaimInputRejects "enabled"

private def unapprovedCommitment : Noctium.Entrypoint :=
  {claimEntry with effects := claimEntry.effects.map fun
    | .claimContractCall address entryHash (.disclose _ commitment) =>
      .claimContractCall address entryHash commitment
    | effect => effect}

#guard !(Noctium.Disclosure.entrypoint unapprovedCommitment).isOk
