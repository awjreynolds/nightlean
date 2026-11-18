import Noctium.Witness.Ledger

open Noctium.Helpers

private def ledgerProgram : Program := {
  ledger := [
    {name := "balance", kind := .cell .native},
    {name := "balances", kind := .map .native .native}]
  witnesses := [{
    name := "quote",
    operation := "oracle.quote.v1",
    capability := "oracle",
    result := .scalar .native}]
  declarations := [{
    id := ⟨0, 0⟩,
    name := "update",
    result := .unit,
    body := [
      .readCell "balance" "before" .native,
      .writeCell "balance" .native (.witnessCall "quote-site" "quote" []),
      .branch (.bool true) [
        .readMap "balances" "amount" .native .native (.native 3),
        .readMember "balances" "present" .native .native (.native 3),
        .writeMap "balances" .native .native (.native 4) (.ref "amount")] [],
      .return none]}]
  exports := [{name := "update", target := ⟨0, 0⟩}]
}

private def countLedger : List Statement → Nat
  | [] => 0
  | .branch _ yes no :: rest =>
      countLedger yes + countLedger no + countLedger rest
  | .readCell .. :: rest => 1 + countLedger rest
  | .writeCell .. :: rest => 1 + countLedger rest
  | .readMap .. :: rest => 1 + countLedger rest
  | .readMember .. :: rest => 1 + countLedger rest
  | .writeMap .. :: rest => 1 + countLedger rest
  | _ :: rest => countLedger rest

private def countExternalQuote (body : List Statement) : Nat :=
  ((reprStr body).splitOn "quote-site").length - 1

private def countReadEqualities : List Statement → Nat
  | [] => 0
  | .branch _ yes no :: rest =>
      countReadEqualities yes + countReadEqualities no + countReadEqualities rest
  | .assert (.eq (.ref _) (.ref _)) :: rest => 1 + countReadEqualities rest
  | _ :: rest => countReadEqualities rest

private def validLedgerSignatures (signatures : List WitnessSignature) : Bool :=
  signatures.all fun signature =>
    (signature.name.splitOn "noctium_ledger_signature_").length > 1 &&
      signature.capability == "noctium.ledger" &&
      (signature.operation == "noctium.ledger.read.v1" ||
        signature.operation == "noctium.ledger.write.v1")

private def transformPasses : Bool := match Noctium.Witness.Ledger.transform ledgerProgram with
  | .error _ => false
  | .ok transformed => match transformed.host.declarations, transformed.native.declarations with
    | [hostDeclaration], [nativeDeclaration] =>
        let hostBody := hostDeclaration.body
        let nativeBody := nativeDeclaration.body
        transformed.calls.length == 5 &&
        countLedger hostBody == 0 && countLedger nativeBody == 5 &&
        countReadEqualities nativeBody == 3 &&
        countExternalQuote hostBody == 1 && countExternalQuote nativeBody == 1 &&
        validLedgerSignatures (transformed.host.witnesses.drop 1) &&
        (transformed.calls.find? (·.kind == "readMember")).isSome &&
        (transformed.calls.find? (·.kind == "writeMap")).isSome
    | _, _ => false

#guard transformPasses
