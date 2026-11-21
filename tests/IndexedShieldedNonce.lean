import Noctium.Frontend
import Noctium.Disclosure

open scoped Noctium
open Noctium

noctium_circuit indexedNonceInputs where
  private index : UInt 128
  private nonce : Bytes32
  output evolvedNonce : Bytes32 := disclose(shieldedIndexedNonce(index, nonce))
end

noctium_contract IndexedShieldedNonce where
  entry evolve uses indexedNonceInputs where
    return result : Bytes32 := evolvedNonce
  end
end

#guard match IndexedShieldedNonce.entrypoints with
  | [item] => item.name == "evolve" &&
      (item.validate Capabilities.source IndexedShieldedNonce.state).isOk
  | _ => Bool.false

#guard match IndexedShieldedNonce.entrypoints with
  | [item] => (Disclosure.entrypoint item).isOk
  | _ => Bool.false

section SourceFailures

/-- Noctium expression type mismatch -/
#guard_msgs (substring := true) in
noctium_circuit indexedNonceRejectsWideIndex where
  private index : UInt 129
  private nonce : Bytes32
  output evolvedNonce : Bytes32 := disclose(shieldedIndexedNonce(index, nonce))
end

/-- Noctium expression type mismatch -/
#guard_msgs (substring := true) in
noctium_circuit indexedNonceRejectsNarrowNonce where
  private index : UInt 128
  private nonce : Bytes 31
  output evolvedNonce : Bytes32 := disclose(shieldedIndexedNonce(index, nonce))
end

/-- undisclosed private parameter 'index' -/
#guard_msgs (substring := true) in
noctium_circuit indexedNonceRequiresDisclosure where
  private index : UInt 128
  private nonce : Bytes32
  output evolvedNonce : Bytes32 := shieldedIndexedNonce(index, nonce)
end

end SourceFailures
