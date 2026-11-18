import Noctium.Frontend
import Noctium.Witness

open scoped Noctium
open Noctium Noctium.Helpers

private def echoSignature (name operation capability : String) (ty : Ty) : WitnessSignature := {
  name
  operation
  capability
  parameters := [{name := "value", type := .scalar ty}]
  result := .scalar ty}

def structuredTypedCellLedger : List StateDecl := [
  {name := "bytes33", kind := .cell (.bytes 33)},
  {name := "empty", kind := .cell (.bytes 0)},
  {name := "jubjubScalar", kind := .cell .jubjubScalar},
  {name := "jubjubPoint", kind := .cell .jubjubPoint},
  {name := "secp256k1Base", kind := .cell (.foreign (.base .secp256k1))},
  {name := "registry", kind := .map (.bytes 32) (.bytes 33)}]

private def copyCell (ordinal : Nat) (name state site provider : String) (ty : Ty) : Declaration := {
  id := ⟨0, ordinal⟩
  name
  result := .unit
  body := [
    .readCell state "before" ty,
    .bind "echoed" (.scalar ty) (.witnessCall site provider [.ref "before"]),
    .writeCell state ty (.disclose {} (.ref "echoed")),
    .return none]}

private def copyRegistry : Declaration := {
  id := ⟨0, 6⟩
  name := "copyRegistry"
  parameters := [⟨"registryKey", .bytes 32⟩]
  result := .unit
  body := [
    .readMap "registry" "before" (.bytes 32) (.bytes 33) (.ref "registryKey"),
    .bind "echoed" (.scalar (.bytes 33))
      (.witnessCall "echo-registry-bytes33" "echoBytes33" [.ref "before"]),
    .writeMap "registry" (.bytes 32) (.bytes 33) (.ref "registryKey")
      (.disclose {} (.ref "echoed")),
    .return none]}

def structuredTypedCellProgram : Program := {
  ledger := structuredTypedCellLedger
  witnesses := [
    echoSignature "echoBytes33" "noctium.echo.bytes33.v1" "echo.bytes33" (.bytes 33),
    echoSignature "echoBytes0" "noctium.echo.bytes0.v1" "echo.bytes0" (.bytes 0),
    echoSignature "echoJubjubScalar" "noctium.echo.jubjub-scalar.v1" "echo.jubjub-scalar" .jubjubScalar,
    echoSignature "echoJubjubPoint" "noctium.echo.jubjub-point.v1" "echo.jubjub-point" .jubjubPoint,
    echoSignature "echoSecp256k1Base" "noctium.echo.secp256k1-base.v1" "echo.secp256k1-base"
      (.foreign (.base .secp256k1))]
  declarations := [{
    id := ⟨0, 0⟩
    name := "update"
    parameters := [⟨"enabled", .bool⟩, ⟨"registryKey", .bytes 32⟩]
    result := .unit
    body := [
      .branch (.disclose {} (.ref "enabled")) [
        .evaluate (.call "copyBytes33" []),
        .evaluate (.call "copyBytes0" []),
        .evaluate (.call "copyJubjubScalar" []),
        .evaluate (.call "copyJubjubPoint" []),
        .evaluate (.call "copySecp256k1Base" []),
        .evaluate (.call "copyRegistry" [.ref "registryKey"])] [],
      .return none]}] ++ [
    copyCell 1 "copyBytes33" "bytes33" "echo-bytes33" "echoBytes33" (.bytes 33),
    copyCell 2 "copyBytes0" "empty" "echo-bytes0" "echoBytes0" (.bytes 0),
    copyCell 3 "copyJubjubScalar" "jubjubScalar" "echo-jubjub-scalar" "echoJubjubScalar" .jubjubScalar,
    copyCell 4 "copyJubjubPoint" "jubjubPoint" "echo-jubjub-point" "echoJubjubPoint" .jubjubPoint,
    copyCell 5 "copySecp256k1Base" "secp256k1Base" "echo-secp256k1-base" "echoSecp256k1Base"
      (.foreign (.base .secp256k1)),
    copyRegistry]
  exports := [{name := "update", target := ⟨0, 0⟩, inputs := [
    {name := "enabled", ty := .bool, visibility := .private},
    {name := "registryKey", ty := .bytes 32, visibility := .public}]}]}

noctium_contract StructuredTypedCells where
  cell bytes33 : Bytes 33
  cell empty : Bytes 0
  cell jubjubScalar : JubjubScalar
  cell jubjubPoint : JubjubPoint
  cell secp256k1Base : Secp256k1Base
  map registry : Bytes32 => Bytes 33
  entry update from structuredTypedCellProgram entry "update" end
end

#guard (Helpers.compileHostedEntrypointForWithLimits {} structuredTypedCellProgram
  "update" StructuredTypedCells.state).isOk

#guard (Witness.compileLedger structuredTypedCellProgram "update" StructuredTypedCells.state).isOk

#guard match Helpers.compileHostedEntrypointForWithLimits {} structuredTypedCellProgram
    "update" StructuredTypedCells.state with
  | .ok hosted => hosted.calls.map (·.result) == [
      .scalar (.bytes 33), .scalar (.bytes 0), .scalar .jubjubScalar,
      .scalar .jubjubPoint, .scalar (.foreign (.base .secp256k1)),
      .scalar (.bytes 33)]
  | .error _ => _root_.Bool.false

private def undisclosedTypedWrite : Program := {
  ledger := structuredTypedCellLedger
  declarations := [{
    id := ⟨0, 0⟩
    name := "writePrivate"
    parameters := [⟨"secret", .bytes 33⟩]
    result := .unit
    body := [.writeCell "bytes33" (.bytes 33) (.ref "secret"), .return none]}]
  exports := [{name := "writePrivate", target := ⟨0, 0⟩, inputs := [
    {name := "secret", ty := .bytes 33, visibility := .private}]}]}

#guard !(Helpers.compileHostedEntrypointForWithLimits {} undisclosedTypedWrite
  "writePrivate" structuredTypedCellLedger).isOk

private def wrongTypedCell : Program := {
  structuredTypedCellProgram with declarations := structuredTypedCellProgram.declarations.map fun declaration =>
    if declaration.name == "copyBytes33" then
      {declaration with body := [
        .readCell "bytes33" "before" .bool,
        .return none]}
    else declaration}

#guard !(Helpers.compileHostedEntrypointForWithLimits {} wrongTypedCell
  "update" structuredTypedCellLedger).isOk
