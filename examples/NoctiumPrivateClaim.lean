import Noctium.Frontend
open scoped Noctium

/- Current authoring example. This teaching copy has no inherited proof or deployment
qualification. `private` below means a circuit witness input, not persisted wallet
state. Ledger cells and the spent map are public.

Two-level claim fixture. The path depth is a workload parameter. Domain tags
1/2/3 are Noctium application choices, not Midnight protocol constants. -/
namespace NoctiumExamples

noctium_circuit claimRelation where
  public root : Native
  public campaign : Native
  public suppliedNullifier : Native
  private secret : Native
  private sibling0 : Native
  private sibling1 : Native
  private direction0 : Bool
  private direction1 : Bool
  let leaf : Native := poseidon2(1, secret, campaign)
  let left0 : Native := select(direction0, sibling0, leaf)
  let right0 : Native := select(direction0, leaf, sibling0)
  let node0 : Native := poseidon2(2, left0, right0)
  let left1 : Native := select(direction1, sibling1, node0)
  let right1 : Native := select(direction1, node0, sibling1)
  let computedRoot : Native := poseidon2(2, left1, right1)
  let computedNullifier : Native := poseidon2(3, secret, campaign)
  assert eq(disclose(computedRoot), root)
  assert eq(disclose(computedNullifier), suppliedNullifier)
  output nullifier : Native := disclose(computedNullifier)
end

noctium_contract PrivateClaim where
  cell acceptedRoot : Native
  cell campaignId : Native
  map spent : Native => Bool
  entry claim uses claimRelation where
    read acceptedRoot as storedRoot
    require eq(storedRoot, root)
    read campaignId as storedCampaign
    require eq(storedCampaign, campaign)
    absent spent[nullifier]
    insert spent[nullifier] := true
  end
end

end NoctiumExamples
