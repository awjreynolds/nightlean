import Noctium.Frontend

open scoped Noctium

private def pairWire : Noctium.Helpers.Wire.Codec := {
  payload := .structure "ContractInterfaceComposition.Pair"
  frameBytes := 2
  composites := {structures := [{id := "ContractInterfaceComposition.Pair", fields := [
    {name := "amount", type := .scalar (.uint 255)},
    {name := "accepted", type := .scalar .bool}
  ]}]}
}

noctium_witness_circuit inspectPair using pairWire where
  private request : Payload pairWire
  output pair := disclose(request)
end

noctium_interface PairClaimInterface where
  entry claim accepts [
    payload := fields(amount : UInt 8, accepted : Bool)
  ] yields [
    receipt := fields(amount : UInt 8, accepted : Bool)
  ]
end

noctium_contract PairInterfaceTarget where
  cell calls : UInt 8

  entry claim uses inspectPair arguments [request] where
    write calls := 1
    return pair
  end
end

noctium_implements PairInterfaceTarget implements PairClaimInterface

noctium_circuit pairClaimInputs where
  private opening : Native
  private requestAmount : UInt 8
  private requestAccepted : Bool
  private expectedAmount : UInt 8
  private expectedAccepted : Bool
end

noctium_contract PairInterfaceCaller where
  cell route : Bytes32
  cell calls : UInt 8

  entry claim uses pairClaimInputs where
    read route as target
    claimContractCall(target, disclose(callCommitment(PairInterfaceTarget,
      PairClaimInterface, "claim", opening,
      [payload := fields(requestAmount, requestAccepted)],
      [receipt := fields(expectedAmount, expectedAccepted)])))
    write calls := 1
  end
end

noctium_interface WrongPairClaimInterface where
  entry claim accepts [
    payload := fields(amount : UInt 8, accepted : Bool)
  ] yields [
    receipt := fields(amount : UInt 16, accepted : Bool)
  ]
end

/-- does not match interface -/
#guard_msgs (substring := true) in
noctium_implements PairInterfaceTarget implements WrongPairClaimInterface
