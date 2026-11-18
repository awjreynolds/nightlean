import Noctium.Verification.ArtifactBytes
import Noctium.Verification.NativeRelationJson
import Noctium.Verification.NativeStateJson
import Noctium.Verification.NativePrivacy

namespace Noctium.Verification.ArtifactCertificate
open ArtifactBytes NativeRelation NativeStateJson NativePrivacy

def decodeProgram (bytes : Bytes) : Except String Program := (parse bytes).bind NativeRelationJson.decode
def decodePlan (bytes : Bytes) : Except String (List SymbolicOp) := (parse bytes).bind NativeStateJson.decode

structure Profile where
  schemaVersion : Nat
  name : String
  ledger : String
  zkir : String
  circuits : String
  zkStdlib : String
  proofServer : String
  onchainRuntime : String
  qualification : String
  repository : String
  tag : String
  revision : String
  declaredCrateVersion : String
  reportedCliVersion : String
  deriving DecidableEq

def selectedProfile : Profile := ⟨1, "midnight-ledger-9-zkir-3.2.1", "9.1.0.1", "3.2.1", "7.3.0", "2.4.0",
  "9.0.0", "4.0.1", "selected-native-subset-qualified", "https://github.com/midnightntwrk/midnight-zkir",
  "zkir-3.2.1", "7a51b3385bbf4bce3604df87a7c70867c9ab43c0", "3.2.0", "midnight-zkir 3.2.0"⟩

private def fields (json : Lean.Json) (expected : List String) : Except String Unit := do
  let found := (← json.getObj?).toList.map Prod.fst
  if found.length == expected.length && found.all expected.contains && expected.all found.contains then pure ()
  else throw "unexpected selected-profile fields"
private def text (json : Lean.Json) (name : String) : Except String String :=
  (json.getObjVal? name).bind Lean.Json.getStr?

def profile (json : Lean.Json) : Except String Profile := do
  fields json ["schemaVersion", "name", "ledger", "zkir", "circuits", "zkStdlib", "proofServer",
    "onchainRuntime", "qualification", "nativeSource"]
  let schema ← json.getObjVal? "schemaVersion"
  let .num n := schema | throw "selected-profile schema is not an integer"
  if n.exponent != 0 then throw "selected-profile schema is not an integer"
  let .ofNat schemaVersion := n.mantissa | throw "selected-profile schema is negative"
  let native ← json.getObjVal? "nativeSource"
  fields native ["repository", "tag", "revision", "declaredCrateVersion", "reportedCliVersion"]
  return ⟨schemaVersion, ← text json "name", ← text json "ledger", ← text json "zkir", ← text json "circuits",
    ← text json "zkStdlib", ← text json "proofServer", ← text json "onchainRuntime", ← text json "qualification",
    ← text native "repository", ← text native "tag", ← text native "revision", ← text native "declaredCrateVersion",
    ← text native "reportedCliVersion"⟩

def decodeProfile (bytes : Bytes) : Except String Profile := (parse bytes).bind profile

/-- Named native-parser agreement for the exact finite artifact set. This is
an implementation premise, never presented as a Lean proof of Rust/serde. -/
structure NativeParserAgreement (nativeParse : Bytes → Except String Lean.Json) (artifacts : List Bytes) : Prop where
  agrees : ∀ bytes ∈ artifacts, ∀ json, parse bytes = .ok json → nativeParse bytes = .ok json

/-- Public build identities only. No invocation witness, state initialization
secret or provider data belongs in this certificate. Hash values are identifiers
checked externally against independently trusted build inputs. -/
structure BuildIdentity where
  sourceCommit : String
  sourceTree : String
  sourceClosureSha256 : String
  sourcePolicy : String
  nativePolicy : String
  theoremClosureSha256 : String
  trustedModelSha256 : String
  toolchainSha256 : String
  profileBytes : Bytes
  importProducts : List (String × String)
  compilerProductSha256 : String
  deriving DecidableEq

/-- The authority is an external expected value, never inferred from candidate
manifest claims. The trusted data checker must independently match this entire
value, including exact expected artifacts, before accepting a certificate. -/
structure Authority where
  build : BuildIdentity
  planBytes : Bytes
  callBytes : Bytes
  standaloneBytes : Bytes
  deriving DecidableEq

/-- Authentication means equality to the independently supplied authority.
The external checker checks the provenance of that authority through immutable
sources, pinned tools/imports and separate reproducible builds. -/
def Authenticated (authority : Authority) (build : BuildIdentity) (sourceIdentity : String)
    (planBytes callBytes : Bytes) : Prop :=
  build = authority.build ∧ sourceIdentity = authority.build.sourceCommit ∧
    planBytes = authority.planBytes ∧ callBytes = authority.callBytes

/-- Concrete parser/authority composition for the existing native privacy
interface. Neither byte parsing nor build identity is a self-declared True. -/
theorem exact_binding (authority : Authority) (build : BuildIdentity) (sourceIdentity : String)
    (planBytes callBytes : Bytes)
    (planValid : ∃ symbols, decodePlan planBytes = .ok symbols)
    (callValid : ∃ program, decodeProgram callBytes = .ok program)
    (authenticated : Authenticated authority build sourceIdentity planBytes callBytes) :
    ExactArtifactBinding Bytes BuildIdentity sourceIdentity planBytes callBytes
      (tree planBytes) (tree callBytes) build parse (Authenticated authority) := by
  obtain ⟨symbols, hp⟩ := planValid
  obtain ⟨program, hc⟩ := callValid
  exact ⟨(validated_tree NativeStateJson.decode planBytes symbols hp).1,
    (validated_tree NativeRelationJson.decode callBytes program hc).1, authenticated⟩

end Noctium.Verification.ArtifactCertificate
