import Noctium.Frontend
import Noctium.Backend.Impact

open scoped Noctium

noctium_circuit metadataCircuit where
  output ready : Bool := true
end

noctium_contract ConstructorMetadata where
  sealed cell name : OpaqueString
  sealed cell symbol : OpaqueString
  sealed cell decimals : UInt 8
  sealed cell initialized : Bool
  sealed cell version : OpaqueString
  cell supply : UInt 64
  constructor(name_ : OpaqueString, symbol_ : OpaqueString, decimals_ : UInt 8) where
    initialize name := name_
    initialize symbol := symbol_
    initialize decimals := decimals_
    initialize initialized := true
    initialize version := "v1"
  end
  entry inspect uses metadataCircuit where
    read decimals as observedDecimals
    return decimalsResult : UInt 8 := observedDecimals
  end
end

private def invalidSealedWrite : Noctium.Entrypoint := {
  name := "invalidSealedWrite"
  circuit := metadataCircuit
  effects := [.writeCell "decimals" (.uint 255) (.uint 255 1)]
  effectGuards := [some (.bool Bool.false)]
}

#guard match invalidSealedWrite.validate Noctium.Capabilities.source ConstructorMetadata.state with
  | .error diagnostic => diagnostic.message == "sealed state 'decimals' cannot be written by an entrypoint"
  | .ok _ => Bool.false

#guard match ConstructorMetadata.validate Noctium.Capabilities.source with
  | .ok _ => _root_.Bool.true
  | .error _ => _root_.Bool.false
