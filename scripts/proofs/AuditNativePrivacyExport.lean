import Noctium.Verification.NativePrivacy
import Lean.Replay
import LeanExport.Parse

open Lean Noctium.Verification

private def load (path : System.FilePath) : IO LeanExport.ExportedEnv := do
  unless (← path.metadata).byteSize ≤ 64 * 1024 * 1024 do throw <| IO.userError "export_limit"
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

private def equality (env : Environment) (left right : Lean.Expr) (error : String) : IO Unit :=
  match Kernel.isDefEq env {} left right with
  | .ok true => pure ()
  | _ => throw <| IO.userError error

private def checked (env : Environment) (policy proof obligation : Name) : IO (Array Name) := do
  let some policyInfo := env.toKernelEnv.find? policy | throw <| IO.userError "unknown_policy"
  unless policyInfo.levelParams.isEmpty do throw <| IO.userError "polymorphic_policy"
  equality env policyInfo.type (mkConst ``NativePrivacy.Policy) "wrong_policy_type"
  let some proofInfo := env.toKernelEnv.find? proof | throw <| IO.userError "missing_native_privacy_proof"
  unless proofInfo.levelParams.isEmpty do throw <| IO.userError "polymorphic_proof"
  equality env proofInfo.type (mkApp (mkConst obligation) (mkConst policy)) "wrong_native_privacy_obligation"
  match Audit.axiomsIn env proof with
  | .ok axioms => pure axioms
  | .error message => throw <| IO.userError message

def main (args : List String) : IO UInt32 := do
  try
    let [modelPath, proofPath, policyText, proofText] := args
      | throw <| IO.userError "usage: AuditNativePrivacyExport MODEL PROOFS POLICY NATIVE_PRIVACY_PROOF"
    let model ← load modelPath
    let candidate ← load proofPath
    let policy ← name policyText
    let proof ← name proofText
    let obligation ← name "Noctium.PrivateClaimNativePrivacy.NativePrivacyObligation"
    let expectedPolicy ← name "Noctium.PrivateClaimNativePrivacy.policy"
    let sourcePolicy ← name "Noctium.PrivateClaimVerification.policy"
    let observer ← name "Noctium.PrivateClaimNativePrivacy.observe"
    for root in Audit.approvedAxioms ++ [policy, expectedPolicy, sourcePolicy, obligation, observer] do
      unless model.constMap.contains root do throw <| IO.userError s!"missing_trusted_model_root: {root}"
    let environment ← replay model.constMap candidate.constMap
    let mut axioms ← checked environment policy proof obligation
    for (sourceProof, role) in [("Noctium.PrivateClaimVerification.functional", Audit.Role.functional),
        ("Noctium.PrivateClaimVerification.privacy", Audit.Role.privacy)] do
      match Audit.check environment sourcePolicy (← name sourceProof) role with
      | .ok registration => axioms := axioms ++ registration.axioms
      | .error message => throw <| IO.userError message
    equality environment (mkConst policy) (mkConst expectedPolicy) "wrong_exact_native_policy"
    equality environment (mkApp (mkConst ``NativePrivacy.Policy.source) (mkConst policy))
      (mkConst sourcePolicy) "wrong_source_policy"
    equality environment (mkApp (mkConst ``NativePrivacy.Policy.scope) (mkConst policy))
      (mkConst ``ObservationScope.successfulOnly) "wrong_privacy_scope"
    equality environment (mkApp (mkConst ``NativePrivacy.Policy.observer) (mkConst policy))
      (mkConst ``NativePrivacy.ObserverIdentity.successfulClaimPublicTranscriptV1) "wrong_native_observer"
    IO.println <| (Json.mkObj [
      ("status", toJson ("native-scoped-privacy-checked" : String)),
      ("nativePrivacyChecked", toJson true), ("sourceFunctionalChecked", toJson true), ("sourcePrivacyChecked", toJson true), ("policy", toJson policyText), ("privacyProof", toJson proofText),
      ("sourcePolicy", toJson sourcePolicy.toString),
      ("observer", toJson ("successfulClaimPublicTranscriptV1" : String)),
      ("scope", toJson ("successful-valid-executions-only" : String)),
      ("axioms", toJson ((axioms.toList.eraseDups.mergeSort Name.lt).map Name.toString)),
      ("exactArtifactByteBuildBindingVerified", toJson false),
      ("proofByteZeroKnowledgeProved", toJson false),
      ("compiledContractVerified", toJson false)]).compress
    return 0
  catch error =>
    IO.eprintln <| (Json.mkObj [("status", toJson ("rejected" : String)), ("error", toJson (toString error))]).compress
    return 1
