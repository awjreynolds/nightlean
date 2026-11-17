import Nightlean.Backend.Impact
import Nightlean.Backend.Zkir
import Noctium.Frontend

open scoped Noctium

noctium_circuit nestedEscrowUpdate where
  private owner : Bytes32
  private spender : Bytes32
  private ownerC1x : Native
  private ownerC1y : Native
  private ownerC2x : Native
  private ownerC2y : Native
  private spenderC1x : Native
  private spenderC1y : Native
  private spenderC2x : Native
  private spenderC2y : Native
  private memoX : Native
  private memoY : Native
  private memoAmount : Native
end

noctium_contract NestedEscrow where
  tree escrow : Bytes32 => Bytes32 => struct EscrowRecord {
    ownerC1x : Native
    ownerC1y : Native
    ownerC2x : Native
    ownerC2y : Native
    spenderC1x : Native
    spenderC1y : Native
    spenderC2x : Native
    spenderC2y : Native
    memoX : Native
    memoY : Native
    memoAmount : Native
  }
  entry update uses nestedEscrowUpdate where
    member escrow[disclose(owner)] as ownerPresent
    if eq(ownerPresent, false) then {
      insert escrow[disclose(owner)] := emptyMap
    } else {
    }
    member escrow[disclose(owner)][disclose(spender)] as recordPresent
    when eq(recordPresent, true) read escrow[disclose(owner)][disclose(spender)] as before
    write escrow[disclose(owner)][disclose(spender)] := fields(
      disclose(ownerC1x), disclose(ownerC1y), disclose(ownerC2x), disclose(ownerC2y),
      disclose(spenderC1x), disclose(spenderC1y), disclose(spenderC2x), disclose(spenderC2y),
      disclose(memoX), disclose(memoY), disclose(memoAmount))
    read escrow[disclose(owner)][disclose(spender)] as observed
    require eq(observed_ownerC1x, ownerC1x)
    require eq(observed_ownerC1y, ownerC1y)
    require eq(observed_ownerC2x, ownerC2x)
    require eq(observed_ownerC2y, ownerC2y)
    require eq(observed_spenderC1x, spenderC1x)
    require eq(observed_spenderC1y, spenderC1y)
    require eq(observed_spenderC2x, spenderC2x)
    require eq(observed_spenderC2y, spenderC2y)
    require eq(observed_memoX, memoX)
    require eq(observed_memoY, memoY)
    require eq(observed_memoAmount, memoAmount)
  end
end

private def nestedEscrowEntry : Noctium.Entrypoint :=
  match NestedEscrow.entrypoints with
  | ep :: _ => ep
  | _ => {name := "missing", circuit := {name := "missing"}}

#guard match Nightlean.Backend.Impact.lower NestedEscrow.state nestedEscrowEntry with
  | .ok plan =>
      plan.reads.any (·.name == "ownerPresent") &&
      plan.reads.any (·.name == "recordPresent") &&
      plan.reads.any (·.name == "observed") &&
      plan.operations.any (fun op => match op with | .newMap => _root_.Bool.true | _ => _root_.Bool.false)
  | .error _ => _root_.Bool.false

#guard match Nightlean.Backend.Zkir.lowerEntrypoint NestedEscrow.state nestedEscrowEntry with
  | .ok _ => _root_.Bool.true
  | .error _ => _root_.Bool.false
