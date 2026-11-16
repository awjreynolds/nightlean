import Nightlean.Verification.ArtifactCertificate
import Lean.Replay
import LeanExport.Parse

open Lean Nightlean.Verification Nightlean.Verification.ArtifactCertificate

private def load (path : System.FilePath) : IO LeanExport.ExportedEnv := do
  unless (← path.metadata).byteSize ≤ 96 * 1024 * 1024 do throw <| IO.userError "export_limit"
  IO.FS.withFile path .read fun handle => LeanExport.parseStream (.ofHandle handle)

private def name (text : String) : IO Name := do
  let some parsed := Syntax.decodeNameLit ("`" ++ text) | throw <| IO.userError "invalid_name"
  if parsed.isAnonymous then throw <| IO.userError "invalid_name"
  return parsed

private def replay (model candidate : Std.HashMap Name ConstantInfo) : IO Environment := do
  let mut merged := candidate
  for (root, trusted) in model.toList do
    if let some supplied := candidate[root]? then
      unless supplied == trusted do throw <| IO.userError s!"model_declaration_mismatch: {root}"
    merged := merged.insert root trusted
  let primitives := [`Quot.mk, `Quot.lift, `Quot.ind]
  let checked ← (← mkEmptyEnvironment).toKernelEnv.replay (primitives.foldl (fun m n => m.erase n) merged)
  for root in `Quot :: primitives do
    if let some supplied := merged[root]? then
      unless checked.find? root == some supplied do throw <| IO.userError "quotient_declaration_mismatch"
  return .ofKernelEnv checked

private def equality (env : Environment) (left right : Lean.Expr) (error : String) : IO Unit := do
  match Kernel.check env {} left, Kernel.check env {} right with
  | .ok leftType, .ok rightType =>
    match Kernel.isDefEq env {} leftType rightType, Kernel.isDefEq env {} left right with
    | .ok true, .ok true => pure ()
    | _, _ => throw <| IO.userError error
  | _, _ => throw <| IO.userError s!"ill_typed_expected_identity: {error}"

private def listTerm (type : Lean.Expr) (items : List Lean.Expr) : Lean.Expr :=
  items.foldr (fun item tail => mkApp3 (mkConst ``List.cons [Level.zero]) type item tail)
    (mkApp (mkConst ``List.nil [Level.zero]) type)

/-- The trusted checker constructs literals directly from separately read files.
It does not evaluate a candidate constant through native code or evalConstCheck. -/
private def bytesTerm (path : System.FilePath) : IO Lean.Expr := do
  let bytes ← IO.FS.readBinFile path
  unless bytes.size ≤ ArtifactBytes.maxBytes do throw <| IO.userError "artifact_byte_limit"
  pure <| listTerm (mkConst ``UInt8) (bytes.toList.map fun b => mkApp (mkConst ``UInt8.ofNat) (mkNatLit b.toNat))

private def field (json : Json) (key : String) : IO Json :=
  match json.getObjVal? key with
  | .ok value => pure value
  | .error _ => throw <| IO.userError s!"missing_authority_field: {key}"
private def text (json : Json) (key : String) : IO String := do
  match (← field json key).getStr? with
  | .ok value => pure value
  | .error _ => throw <| IO.userError s!"invalid_authority_string: {key}"

private def authorityTerm (authority : Json) (directory : System.FilePath) : IO Lean.Expr := do
  let build ← field authority "build"
  let imports ← field build "importProducts"
  let .ok imports := imports.getArr? | throw <| IO.userError "invalid_import_identities"
  let mut pairs := []
  for item in imports do
    let .ok pair := item.getArr? | throw <| IO.userError "invalid_import_identity"
    unless pair.size == 2 do throw <| IO.userError "invalid_import_identity"
    let .ok path := pair[0]!.getStr? | throw <| IO.userError "invalid_import_path"
    let .ok digest := pair[1]!.getStr? | throw <| IO.userError "invalid_import_digest"
    pairs := pairs ++ [mkApp4 (mkConst ``Prod.mk [Level.zero,Level.zero]) (mkConst ``String) (mkConst ``String)
      (mkStrLit path) (mkStrLit digest)]
  let pairType := mkApp2 (mkConst ``Prod [Level.zero,Level.zero]) (mkConst ``String) (mkConst ``String)
  let mut values := #[]
  for key in ["sourceCommit", "sourceTree", "sourceClosureSha256", "sourcePolicy", "nativePolicy",
      "theoremClosureSha256", "trustedModelSha256", "toolchainSha256"] do
    values := values.push (mkStrLit (← text build key))
  values := values.push (← bytesTerm (directory / "target-profile.json"))
  values := values.push (listTerm pairType pairs)
  values := values.push (mkStrLit (← text build "compilerProductSha256"))
  let buildTerm := mkAppN (mkConst ``BuildIdentity.mk) values
  pure <| mkApp4 (mkConst ``Authority.mk) buildTerm
    (← bytesTerm (directory / "PrivateClaim.claim.impact.json"))
    (← bytesTerm (directory / "PrivateClaim.claim.zkir"))
    (← bytesTerm (directory / "claimRelation.zkir"))

private def proof (env : Environment) (root : Name) (expected : Lean.Expr) : IO (Array Name) := do
  let some info := env.toKernelEnv.find? root | throw <| IO.userError s!"missing_required_proof: {root}"
  unless info.levelParams.isEmpty do throw <| IO.userError "polymorphic_certificate"
  equality env info.type expected s!"wrong_required_statement: {root}"
  match Audit.axiomsIn env root with
  | .ok found => pure found
  | .error message => throw <| IO.userError message

def main (args : List String) : IO UInt32 := do
  try
    let [modelPath, proofPath, authorityPath, expectedDirectory, candidateDirectory] := args
      | throw <| IO.userError "usage: AuditArtifactExport MODEL PROOFS TRUSTED_AUTHORITY EXPECTED_ARTIFACTS CANDIDATE_ARTIFACTS"
    let model ← load modelPath
    let candidate ← load proofPath
    let authorityBytes ← IO.FS.readFile authorityPath
    let .ok authority := Json.parse authorityBytes | throw <| IO.userError "invalid_trusted_authority"
    for root in Audit.approvedAxioms ++ [``ArtifactBytes.parse, ``Authenticated, ``selectedProfile,
        ← name "Nightlean.PrivateClaimArtifacts.Certified",
        ← name "Nightlean.PrivateClaimArtifacts.FunctionalPreservation",
        ← name "Nightlean.PrivateClaimArtifacts.EligibleCompleteness",
        ← name "Nightlean.PrivateClaimNativePrivacy.NativePrivacyObligation",
        ← name "Nightlean.PrivateClaimNativePrivacy.policy",
        ← name "Nightlean.PrivateClaimNativePrivacy.actualObserve",
        ← name "Nightlean.PrivateClaimVerification.policy"] do
      unless model.constMap.contains root do throw <| IO.userError s!"missing_trusted_model_root: {root}"
    let environment ← replay model.constMap candidate.constMap
    let certificateNamespace := "PrivateClaimArtifactCertificate."
    let authorityName ← name (certificateNamespace ++ "authority")
    let buildName ← name (certificateNamespace ++ "build")
    let sourceName ← name (certificateNamespace ++ "sourceIdentity")
    let expectedAuthority ← authorityTerm authority expectedDirectory
    equality environment (mkConst authorityName) expectedAuthority "external_authority_mismatch"
    equality environment (mkConst buildName) (mkApp (mkConst ``Authority.build) expectedAuthority) "external_build_mismatch"
    equality environment (mkConst sourceName) (mkStrLit (← text (← field authority "build") "sourceCommit")) "external_source_mismatch"
    for (constant, file) in [("standaloneBytes", "claimRelation.zkir"), ("planBytes", "PrivateClaim.claim.impact.json"),
        ("callBytes", "PrivateClaim.claim.zkir"), ("profileBytes", "target-profile.json")] do
      equality environment (mkConst (← name (certificateNamespace ++ constant)))
        (← bytesTerm (System.FilePath.mk candidateDirectory / file)) s!"retained_byte_mismatch: {file}"
      equality environment (← bytesTerm (System.FilePath.mk candidateDirectory / file))
        (← bytesTerm (System.FilePath.mk expectedDirectory / file)) s!"trusted_build_byte_mismatch: {file}"
    let certified ← name "Nightlean.PrivateClaimArtifacts.Certified"
    let required := mkAppN (mkConst certified) #[mkConst authorityName, mkConst buildName, mkConst sourceName,
      mkConst (← name (certificateNamespace ++ "standaloneBytes")), mkConst (← name (certificateNamespace ++ "planBytes")),
      mkConst (← name (certificateNamespace ++ "callBytes")), mkConst (← name (certificateNamespace ++ "profileBytes"))]
    let mut axioms ← proof environment (← name (certificateNamespace ++ "certified")) required
    for (policyText, proofText, role) in [("Nightlean.PrivateClaimVerification.policy", "Nightlean.PrivateClaimVerification.functional", Audit.Role.functional),
        ("Nightlean.PrivateClaimVerification.policy", "Nightlean.PrivateClaimVerification.privacy", Audit.Role.privacy)] do
      match Audit.check environment (← name policyText) (← name proofText) role with
      | .ok registration => axioms := axioms ++ registration.axioms
      | .error error => throw <| IO.userError error
    let nativePolicy ← name "Nightlean.PrivateClaimNativePrivacy.policy"
    let nativeObligation ← name "Nightlean.PrivateClaimNativePrivacy.NativePrivacyObligation"
    axioms := axioms ++ (← proof environment (← name "Nightlean.PrivateClaimNativePrivacy.privacy")
      (mkApp (mkConst nativeObligation) (mkConst nativePolicy)))
    let expectedBinding := mkAppN (mkConst ``NativePrivacy.ExactArtifactBinding) #[
      mkConst ``ArtifactBytes.Bytes, mkConst ``BuildIdentity, mkConst sourceName,
      mkConst (← name (certificateNamespace ++ "planBytes")), mkConst (← name (certificateNamespace ++ "callBytes")),
      mkApp (mkConst ``ArtifactBytes.tree) (mkConst (← name (certificateNamespace ++ "planBytes"))),
      mkApp (mkConst ``ArtifactBytes.tree) (mkConst (← name (certificateNamespace ++ "callBytes"))),
      mkConst buildName, mkConst ``ArtifactBytes.parse, mkApp (mkConst ``Authenticated) (mkConst authorityName)]
    axioms := axioms ++ (← proof environment (← name (certificateNamespace ++ "binding")) expectedBinding)
    let functionalObligation ← name "Nightlean.PrivateClaimArtifacts.FunctionalPreservation"
    let functionalExpected := mkApp2 (mkConst functionalObligation)
      (mkApp (mkConst ``ArtifactBytes.tree) (mkConst (← name (certificateNamespace ++ "planBytes"))))
      (mkApp (mkConst ``ArtifactBytes.tree) (mkConst (← name (certificateNamespace ++ "callBytes"))))
    axioms := axioms ++ (← proof environment (← name (certificateNamespace ++ "functional")) functionalExpected)
    let completeObligation ← name "Nightlean.PrivateClaimArtifacts.EligibleCompleteness"
    let completeExpected := mkApp2 (mkConst completeObligation)
      (mkApp (mkConst ``ArtifactBytes.tree) (mkConst (← name (certificateNamespace ++ "planBytes"))))
      (mkApp (mkConst ``ArtifactBytes.tree) (mkConst (← name (certificateNamespace ++ "callBytes"))))
    axioms := axioms ++ (← proof environment (← name (certificateNamespace ++ "complete")) completeExpected)
    let privacyObligation ← name "Nightlean.PrivateClaimNativePrivacy.DecodedPrivacyObligation"
    let privacyExpected := mkApp2 (mkConst privacyObligation)
      (mkApp (mkConst ``ArtifactBytes.tree) (mkConst (← name (certificateNamespace ++ "planBytes"))))
      (mkApp (mkConst ``ArtifactBytes.tree) (mkConst (← name (certificateNamespace ++ "callBytes"))))
    axioms := axioms ++ (← proof environment (← name (certificateNamespace ++ "privacy")) privacyExpected)
    IO.println <| (Json.mkObj [
      ("status", toJson ("exact-retained-artifact-bytes-and-scoped-privacy-checked" : String)),
      ("retainedBytesKernelMatched", toJson true), ("externalAuthorityKernelMatched", toJson true),
      ("sourceFunctionalChecked", toJson true), ("sourcePrivacyChecked", toJson true), ("nativePrivacyChecked", toJson true),
      ("concreteBytePrivacyCompositionChecked", toJson true), ("concreteByteFunctionalPreservationChecked", toJson true), ("eligibleSourceCompletenessChecked", toJson true),
      ("axioms", toJson ((axioms.toList.eraseDups.mergeSort Name.lt).map Name.toString)),
      ("specificationReviewVerified", toJson false), ("deployedIdentityAuthenticated", toJson false),
      ("compiledContractVerified", toJson false)]).compress
    return 0
  catch error =>
    IO.eprintln <| (Json.mkObj [("status", toJson ("rejected" : String)), ("error", toJson (toString error))]).compress
    return 1
