import Noctium.Frontend

open scoped Noctium
open Noctium.Helpers

namespace StandardEvents

def helperSpendProgram : Program := {
  declarations := [
    {id := ⟨0, 0⟩, name := "emitSpend", parameters := [⟨"nullifier", .bytes 32⟩],
      result := .unit, body := [
        .emitEvent .shieldedSpend (.disclose {} (.ref "nullifier")),
        .return none]},
    {id := ⟨0, 1⟩, name := "main",
      parameters := [⟨"active", .bool⟩, ⟨"nullifier", .bytes 32⟩],
      result := .unit, body := [
        .emitEvent .paused (.bytes (.bytesLiteral 0 []) []),
        .branch (.ref "active") [
          .evaluate (.call "emitSpend" [.ref "nullifier"])] [],
        .emitEvent .unpaused (.bytes (.bytesLiteral 0 []) []),
        .return none]}]
  exports := [{name := "logHelperSpend", target := ⟨0, 1⟩, inputs := [
    {name := "active", ty := .bool, visibility := .public},
    {name := "nullifier", ty := .bytes 32, visibility := .private}]}]
}

noctium_circuit spendInputs where
  public active : Bool
  private nullifier : Bytes 32
end

noctium_circuit catalogInputs where
  private commitment : Bytes 32
  public domain : Bytes 32
  private ciphertext : Bytes 512
  public memo : Bytes 256
  public value : UInt 128
end

noctium_contract Token where
  entry logSpend uses spendInputs where
    emitEvent(Paused)
    when active emitEvent(ShieldedSpend, nullifier := disclose(nullifier))
    emitEvent(Unpaused)
  end

  entry logCatalog uses catalogInputs where
    emitEvent(ShieldedSpend, nullifier := disclose(commitment))
    emitEvent(ShieldedReceive, commitment := disclose(commitment), hasCiphertext := true,
      ciphertext := disclose(ciphertext), hasContractAddress := false, contractAddress := domain)
    emitEvent(ShieldedMint, commitment := disclose(commitment), domainSep := domain,
      hasAmount := true, amount := value)
    emitEvent(ShieldedBurn, nullifier := domain, hasAmount := true, amount := value)
    emitEvent(UnshieldedSpend, isUser := true, userKey := disclose(commitment),
      contractAddress := domain, domainSep := domain, tokenType := disclose(commitment), amount := value)
    emitEvent(UnshieldedReceive, isUser := false, userKey := disclose(commitment),
      contractAddress := domain, domainSep := domain, tokenType := disclose(commitment), amount := value)
    emitEvent(UnshieldedMint, domainSep := domain, tokenType := disclose(commitment), amount := value)
    emitEvent(UnshieldedBurn, isUser := true, userKey := disclose(commitment),
      contractAddress := domain, tokenType := disclose(commitment), amount := value)
    emitEvent(Paused)
    emitEvent(Unpaused)
    emitEvent(Misc, payload := memo, name := domain)
  end

  entry logHelperSpend from helperSpendProgram entry "logHelperSpend" end
end

private def privateEventGuard : Program := {helperSpendProgram with exports := [
  {name := "logHelperSpend", target := ⟨0, 1⟩, inputs := [
    {name := "active", ty := .bool, visibility := .private},
    {name := "nullifier", ty := .bytes 32, visibility := .private}]}]}

private def removeEventPayloadDisclosure (declaration : Declaration) : Declaration :=
  if declaration.name == "emitSpend" then
    {declaration with body := [.emitEvent .shieldedSpend (.ref "nullifier"), .return none]}
  else declaration

private def undisclosedEventPayload : Program := {helperSpendProgram with
  declarations := List.map removeEventPayloadDisclosure helperSpendProgram.declarations}

#guard match Noctium.Helpers.compileEntrypoint privateEventGuard "logHelperSpend" with
  | .error diagnostic => (diagnostic.message.splitOn "undisclosed private control").length > 1
  | .ok _ => Bool.false

#guard match Noctium.Helpers.compileEntrypoint undisclosedEventPayload "logHelperSpend" with
  | .error diagnostic => (diagnostic.message.splitOn "undisclosed private").length > 1
  | .ok _ => Bool.false

end StandardEvents
