import Lean

namespace Nightlean

/-- Components are pinned independently. Producer format and binary release are distinct. -/
structure TargetProfile where
  schemaVersion : Nat
  name : String
  ledger : String
  zkir : String
  circuits : String
  zkStdlib : String
  proofServer : String
  onchainRuntime : String
  qualification : String
  deriving Repr, BEq, Lean.FromJson, Lean.ToJson

def TargetProfile.sourceBaseline : TargetProfile := {
  schemaVersion := 1
  name := "midnight-ledger-9"
  ledger := "9.1.0.1"
  zkir := "3.2.0"
  circuits := "7.3.0"
  zkStdlib := "2.4.0"
  proofServer := "9.0.0"
  onchainRuntime := "4.0.1"
  qualification := "source-baseline-unqualified"
}

def TargetProfile.validate (profile : TargetProfile) : Except String TargetProfile := do
  unless profile.schemaVersion == 1 do
    throw "unsupported target profile schema version"
  unless profile.name == "midnight-ledger-9" do
    throw "unsupported target profile name"
  unless profile.ledger == "9.1.0.1" && profile.zkir == "3.2.0" &&
      profile.circuits == "7.3.0" && profile.zkStdlib == "2.4.0" &&
      profile.proofServer == "9.0.0" && profile.onchainRuntime == "4.0.1" do
    throw "target component versions do not match the ledger 9 source baseline"
  unless profile.qualification == "source-baseline-unqualified" do
    throw "target qualification must be source-baseline-unqualified until integration qualifies the profile"
  return profile

def TargetProfile.parse (source : String) : Except String TargetProfile := do
  let json ← Lean.Json.parse source
  let profile : TargetProfile ← Lean.fromJson? json
  profile.validate

def TargetProfile.load (path : System.FilePath) : IO (Except String TargetProfile) := do
  try
    return TargetProfile.parse (← IO.FS.readFile path)
  catch _ =>
    return .error s!"cannot read target manifest '{path}'"

end Nightlean
