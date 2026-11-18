import Noctium.Target

open Lean Noctium

private def accepts (profile : TargetProfile) : Bool :=
  match profile.validate with
  | .ok _ => true
  | .error _ => false

private def parsesAs (source : String) (expected : TargetProfile) : Bool :=
  match TargetProfile.parse source with
  | .ok profile => profile == expected
  | .error _ => false

private def rejectsJson (profile : TargetProfile) : Bool :=
  match TargetProfile.parse (Lean.toJson profile).compress with
  | .ok _ => false
  | .error _ => true

private def defaultJson := (Lean.toJson TargetProfile.sourceBaseline).compress
private def selectedJson := (Lean.toJson TargetProfile.selected321).compress

#guard defaultJson == "{\"circuits\":\"7.3.0\",\"ledger\":\"9.1.0.1\",\"name\":\"midnight-ledger-9\",\"onchainRuntime\":\"4.0.1\",\"proofServer\":\"9.0.0\",\"qualification\":\"source-baseline-unqualified\",\"schemaVersion\":1,\"zkStdlib\":\"2.4.0\",\"zkir\":\"3.2.0\"}"
#guard parsesAs defaultJson TargetProfile.sourceBaseline
#guard parsesAs selectedJson TargetProfile.selected321
#guard accepts TargetProfile.sourceBaseline
#guard accepts TargetProfile.selected321

#guard !accepts { TargetProfile.selected321 with name := "midnight-ledger-9" }
#guard rejectsJson { TargetProfile.selected321 with name := "midnight-ledger-9" }
#guard !accepts { TargetProfile.selected321 with zkir := "3.2.0" }
#guard rejectsJson { TargetProfile.selected321 with zkir := "3.2.0" }
#guard !accepts { TargetProfile.selected321 with name := "midnight-ledger-9", zkir := "3.2.0" }
#guard !accepts { TargetProfile.selected321 with nativeSource := some { TargetProfile.native321Source with tag := "zkir-3.2.0" } }
#guard rejectsJson { TargetProfile.selected321 with nativeSource := some { TargetProfile.native321Source with tag := "zkir-3.2.0" } }
#guard !accepts { TargetProfile.selected321 with nativeSource := some { TargetProfile.native321Source with revision := "0000000000000000000000000000000000000000" } }
#guard rejectsJson { TargetProfile.selected321 with nativeSource := some { TargetProfile.native321Source with revision := "0000000000000000000000000000000000000000" } }
#guard !accepts { TargetProfile.sourceBaseline with nativeSource := some TargetProfile.native321Source }
#guard rejectsJson { TargetProfile.sourceBaseline with nativeSource := some TargetProfile.native321Source }
#guard !accepts { TargetProfile.selected321 with qualification := "native-claim-localnet-qualified-only" }

def main : IO Unit := do
  let defaultProfile ← TargetProfile.load "profiles/midnight-ledger-9.json"
  match defaultProfile with
  | .ok profile => unless profile == TargetProfile.sourceBaseline do
      throw (IO.userError "default target profile changed")
  | .error message => throw (IO.userError message)
  let selectedProfile ← TargetProfile.load "profiles/midnight-ledger-9-zkir-3.2.1-target.json"
  match selectedProfile with
  | .ok profile => unless profile == TargetProfile.selected321 do
      throw (IO.userError "selected ZKIR 3.2.1 profile does not match the pinned schema")
  | .error message => throw (IO.userError message)
  let historical ← TargetProfile.load "profiles/midnight-ledger-9-zkir-3.2.1.json"
  match historical with
  | .ok _ => throw (IO.userError "historical experimental qualification record must not be selectable")
  | .error _ => pure ()
