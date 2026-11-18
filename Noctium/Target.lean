import Lean

namespace Noctium

/-- The upstream source identity used by the selected native toolchain profile. -/
structure NativeSourcePin where
  repository : String
  tag : String
  revision : String
  declaredCrateVersion : String
  reportedCliVersion : String
  deriving Repr, BEq, Lean.FromJson, Lean.ToJson

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
  nativeSource : Option NativeSourcePin := none
  deriving Repr, BEq

namespace TargetProfile

/-- Source baseline retained for the default 3.2.0 output. -/
def sourceBaseline : TargetProfile := {
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

def native321Source : NativeSourcePin := {
  repository := "https://github.com/midnightntwrk/midnight-zkir"
  tag := "zkir-3.2.1"
  revision := "7a51b3385bbf4bce3604df87a7c70867c9ab43c0"
  declaredCrateVersion := "3.2.0"
  reportedCliVersion := "midnight-zkir 3.2.0"
}

def selected321 : TargetProfile := {
  schemaVersion := 1
  name := "midnight-ledger-9-zkir-3.2.1"
  ledger := "9.1.0.1"
  zkir := "3.2.1"
  circuits := "7.3.0"
  zkStdlib := "2.4.0"
  proofServer := "9.0.0"
  onchainRuntime := "4.0.1"
  qualification := "selected-native-subset-qualified"
  nativeSource := some native321Source
}

end TargetProfile

instance : Lean.FromJson TargetProfile where
  fromJson? json := do
    let schemaVersion ← json.getObjValAs? Nat "schemaVersion"
    let name ← json.getObjValAs? String "name"
    let ledger ← json.getObjValAs? String "ledger"
    let zkir ← json.getObjValAs? String "zkir"
    let circuits ← json.getObjValAs? String "circuits"
    let zkStdlib ← json.getObjValAs? String "zkStdlib"
    let proofServer ← json.getObjValAs? String "proofServer"
    let onchainRuntime ← json.getObjValAs? String "onchainRuntime"
    let qualification ← json.getObjValAs? String "qualification"
    let nativeSource ← match json.getObjVal? "nativeSource" with
      | .ok .null => pure none
      | .ok value => some <$> Lean.fromJson? value
      | .error _ => pure none
    return {
      schemaVersion, name, ledger, zkir, circuits, zkStdlib, proofServer,
      onchainRuntime, qualification, nativeSource
    }

instance : Lean.ToJson TargetProfile where
  toJson profile := Lean.Json.mkObj <| [
    ("schemaVersion", Lean.toJson profile.schemaVersion),
    ("name", Lean.toJson profile.name),
    ("ledger", Lean.toJson profile.ledger),
    ("zkir", Lean.toJson profile.zkir),
    ("circuits", Lean.toJson profile.circuits),
    ("zkStdlib", Lean.toJson profile.zkStdlib),
    ("proofServer", Lean.toJson profile.proofServer),
    ("onchainRuntime", Lean.toJson profile.onchainRuntime),
    ("qualification", Lean.toJson profile.qualification)
  ] ++ profile.nativeSource.toList.map fun source => ("nativeSource", Lean.toJson source)

def TargetProfile.validate (profile : TargetProfile) : Except String TargetProfile := do
  unless profile.schemaVersion == 1 do
    throw "unsupported target profile schema version"
  unless profile.ledger == "9.1.0.1" && profile.circuits == "7.3.0" &&
      profile.zkStdlib == "2.4.0" && profile.proofServer == "9.0.0" &&
      profile.onchainRuntime == "4.0.1" do
    throw "target component versions do not match a supported ledger 9 profile"
  if profile.name == "midnight-ledger-9" then
    unless profile.zkir == "3.2.0" do
      throw "target component versions do not match the ledger 9 source baseline"
    unless profile.qualification == "source-baseline-unqualified" do
      throw "target qualification must be source-baseline-unqualified for the default profile"
    unless profile.nativeSource.isNone do
      throw "the default target profile cannot declare a native source pin"
  else if profile.name == "midnight-ledger-9-zkir-3.2.1" then
    unless profile.zkir == "3.2.1" do
      throw "target component versions do not match the selected ZKIR 3.2.1 profile"
    unless profile.qualification == "selected-native-subset-qualified" do
      throw "target qualification must be selected-native-subset-qualified for ZKIR 3.2.1"
    unless profile.nativeSource == some TargetProfile.native321Source do
      throw "ZKIR 3.2.1 requires the pinned midnight-zkir source identity"
  else
    throw "unsupported target profile name"
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

end Noctium
