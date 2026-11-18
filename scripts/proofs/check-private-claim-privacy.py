#!/usr/bin/env python3
"""Audit actual PrivateClaim native two-run privacy under the exact successful-only policy."""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import runpy
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
STATE = runpy.run_path(str(ROOT / "scripts/proofs/check-private-claim-state.py"))
run = STATE["run"]
NS = "Noctium.PrivateClaimNativePrivacy"
FIXTURES = "Noctium.PrivateClaimPrivacyFixtures"
ROOTS = [f"{NS}.{name}" for name in ["privacy", "exact_source_policy", "exact_source_scope", "no_private_release",
    "source_privacy_from_native", "native_observer_equal", "bound_native_privacy", "decoded_bound_privacy",
    "native_progress", "different_private_fixture_pair", "symmetric_path_flip", "symmetric_eligible_native_pair",
    "wrong_scope_rejected", "exact_artifact_composition"]] + [f"{FIXTURES}.{name}" for name in [
    "authorized_release_privacy", "release_is_not_no_release_privacy", "successful_scope_has_failure_counterexample",
    "direct_leak_rejected", "hash_leak_rejected", "query_leak_rejected", "constant_under_private_control_rejected",
    "direct_payloads_differ", "activity_masks_differ", "private_query_keys_differ", "equal_hash_release_does_not_identify_secret"]]
MODEL_ROOTS = [f"{NS}.{name}" for name in ["policy", "NativePrivacyObligation", "observe", "actualObserve",
    "bindingView", "BindingAgrees", "allOutcomesPolicy"]] + ["Noctium.PrivateClaimVerification.policy",
    "Noctium.Verification.FunctionalObligation", "Noctium.Verification.PrivacyObligation",
    "propext", "Classical.choice", "Quot.sound"]


def certificate_source(plan: object, call: object, namespace: str) -> str:
    base = STATE["certificate_source"](plan, call, namespace).replace(
        "import proofs.PrivateClaimNativeState", "import proofs.PrivateClaimPrivacyFixtures")
    return base + f'''
namespace {namespace}
open Noctium.PrivateClaimNativePrivacy
theorem nativePrivacy : DecodedPrivacyObligation planJson callJson :=
  decoded_obligation planJson callJson planDecoded callDecoded
theorem exactPolicy : NativePrivacyObligation policy := privacy
#print axioms nativePrivacy
#print axioms exactPolicy
end {namespace}
'''


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=ROOT / ".noctium/audits/private-claim-privacy")
    parser.add_argument("--native-checker", type=Path)
    parser.add_argument("--trusted-model-export", type=Path)
    parser.add_argument("--trusted-model-sha256")
    args = parser.parse_args()
    if bool(args.trusted_model_export) != bool(args.trusted_model_sha256):
        parser.error("trusted model export and SHA256 must be supplied together")
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    run(["lake", "build", "noctium", "Noctium.Verification.NativePrivacy", "Noctium.Verification.NativeStateJson",
         "Noctium.Verification.NativeRelationJson", "Noctium.Claim", "Noctium.Backend.Zkir", "Noctium.Frontend", "Noctium.Compiler"])
    run(["lake", "env", "lean", "scripts/proofs/AuditNativePrivacyExport.lean"])
    with tempfile.TemporaryDirectory(prefix="noctium-claim-privacy-") as directory:
        scratch = Path(directory)
        imports = scratch / "imports"
        source_root = scratch / "source"
        for child in ["examples", "proofs", "tests"]:
            (imports / child).mkdir(parents=True)
            (source_root / child).mkdir(parents=True)
        # Freeze built library imports so another reversible build cannot remove
        # or replace a dependency halfway through this fresh proof audit.
        for library in (ROOT / ".lake/build/lib/lean").rglob("*.olean"):
            relative = library.relative_to(ROOT / ".lake/build/lib/lean")
            target = imports / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(library, target)
        env = dict(os.environ, LEAN_PATH=str(imports))

        def build(source: str, contents: str | None = None, negative: bool = False) -> str:
            command = ["lake", "env", "lean", "-D", "Elab.async=false", "-o",
                       str(imports / Path(source).with_suffix(".olean"))]
            if contents is None:
                command.append(source)
            elif (ROOT / source).exists():
                # Preserve the original relative source filename and spans while
                # changing only the candidate term in source/observer regressions.
                command += ["--stdin", source]
            else:
                candidate = source_root / source
                candidate.write_text(contents)
                command += ["--root", str(source_root), str(candidate)]
            result = subprocess.run(command, cwd=ROOT, env=env,
                                    input=contents if contents is not None and (ROOT / source).exists() else None,
                                    capture_output=True, text=True, timeout=240)
            if negative:
                assert result.returncode and "error:" in result.stdout, result.stdout + result.stderr
                assert "unknown module" not in result.stdout and "unknown identifier" not in result.stdout
            else:
                assert result.returncode == 0, str(command) + "\n" + result.stdout + result.stderr
            return result.stdout + result.stderr

        for source in ["examples/PrivateClaim.lean", "proofs/PrivateClaim.lean", "proofs/PrivateClaimVerification.lean",
                       "proofs/PrivateClaimLowering.lean", "proofs/PrivateClaimNativeState.lean",
                       "proofs/PrivateClaimNativePrivacy.lean", "tests/Verification.lean", "proofs/PrivateClaimPrivacyFixtures.lean"]:
            report = build(source)
            if source.endswith("PrivateClaimNativePrivacy.lean"):
                (output / "direct-axioms.txt").write_text(report)
        emitted = output / "emitted"
        run([str(ROOT / ".lake/build/bin/noctium"), "compile", "examples/PrivateClaim.lean", "--target",
             "profiles/midnight-ledger-9-zkir-3.2.1-target.json", "--output", str(emitted)])
        plan_bytes = (emitted / "PrivateClaim.claim.impact.json").read_bytes()
        call_bytes = (emitted / "PrivateClaim.claim.zkir").read_bytes()
        plan, call = STATE["strict_json_bytes"](plan_bytes), STATE["strict_json_bytes"](call_bytes)
        assert len(plan["operations"]) == 21 and len(call["instructions"]) == 55

        def certificate(p: object, c: object, namespace: str, negative: str | None = None) -> None:
            contents = certificate_source(p, c, namespace)
            (output / (namespace + ".lean")).write_text(contents)
            report = build(f"proofs/{namespace}.lean", contents, negative=negative is not None)
            if negative:
                marker = "some " + ("symbolicPlan" if negative == "plan" else "callProgram") + " := by decide +kernel"
                line = next(i for i, text in enumerate(contents.splitlines(), 1) if marker in text)
                assert f"{namespace}.lean:{line}:" in report and "decide" in report, report
                assert "theorems cannot use" not in report
                (output / (namespace + ".rejection.txt")).write_text(report)
            else:
                (output / "certificate-axioms.txt").write_text(report)

        certificate(plan, call, "PrivateClaimPrivacyCertificate")
        mutants = []
        for name, edit in [
            ("DirectPublicOutput", lambda c: c["instructions"][-1].update(vals=["%input_secret"])),
            ("PrivateHashPublicPayload", lambda c: next(i for i in c["instructions"] if i["op"] == "impact")["inputs"].append("%v0")),
            ("PrivateActivityGuard", lambda c: next(i for i in c["instructions"] if i["op"] == "impact").update(guard="%input_direction0")),
        ]:
            changed = copy.deepcopy(call)
            edit(changed)
            certificate(plan, changed, name + "PrivacyCertificate", negative="call")
            mutants.append(name)
        changed_plan = copy.deepcopy(plan)
        changed_plan["operations"][14]["expression"]["name"] = "secret"
        certificate(changed_plan, call, "PrivateQueryKeyPrivacyCertificate", negative="plan")
        mutants.append("PrivateQueryKey")
        for name, proof in [
            ("WrongScope", "allOutcomesPolicy"),
            ("WrongRelease", "{policy with source := {policy.source with privacy := {scope := .successfulOnly, releases := .declared (fun _ => [])}}}"),
        ]:
            contents = f'''import proofs.PrivateClaimNativePrivacy
open Noctium Noctium.Verification Noctium.PrivateClaimNativePrivacy
example : NativePrivacyObligation ({proof}) := privacy
'''
            report = build(f"proofs/{name}Privacy.lean", contents, negative=True)
            assert "Type mismatch" in report, report
            (output / (name + ".rejection.txt")).write_text(report)
        contents = '''import proofs.PrivateClaimNativePrivacy
open Noctium.PrivateClaimNativePrivacy
example : NativePrivacyObligation policy := Noctium.PrivateClaimVerification.functional
'''
        report = build("proofs/FunctionalOnlyPrivacy.lean", contents, negative=True)
        assert "Type mismatch" in report, report
        (output / "FunctionalOnly.rejection.txt").write_text(report)

        def export(module: str, roots: list[str], filename: str) -> Path:
            result = run(["lake", "env", "leanexport", module, "--", *roots], env)
            path = output / filename
            path.write_text(result.stdout)
            return path

        baseline = export("proofs.PrivateClaimNativePrivacy", MODEL_ROOTS, "baseline-model.ndjson")
        proof_roots = ROOTS + ["Noctium.PrivateClaimVerification.functional", "Noctium.PrivateClaimVerification.privacy"] + [
            "PrivateClaimPrivacyCertificate." + item for item in ["planDecoded", "callDecoded", "nativePrivacy", "exactPolicy"]]
        proof = export("proofs.PrivateClaimPrivacyCertificate", proof_roots, "proof-closure.ndjson")
        axioms = STATE["exported_axioms"](proof)
        replay = run(["lake", "env", "leanchecker", "--from-export", str(proof)])
        (output / "kernel-replay.txt").write_text(replay.stdout + replay.stderr)
        model = output / "trusted-model.ndjson"
        model_bytes = args.trusted_model_export.read_bytes() if args.trusted_model_export else baseline.read_bytes()
        assert len(model_bytes) <= 64 * 1024 * 1024
        model.write_bytes(model_bytes)
        pin = args.trusted_model_sha256 or hashlib.sha256(model_bytes).hexdigest()
        assert hashlib.sha256(model_bytes).hexdigest() == pin, "model_pin_mismatch"
        (output / "trusted-model.sha256").write_text(pin + "\n")

        def audit(candidate: Path, policy: str = f"{NS}.policy", proof_name: str = f"{NS}.privacy", error: str | None = None) -> dict:
            clean_env = os.environ.copy()
            clean_env.pop("LEAN_PATH", None)
            checked = subprocess.run(["lake", "env", "lean", "--run", "scripts/proofs/AuditNativePrivacyExport.lean",
                                      str(model), str(candidate), policy, proof_name], cwd=ROOT, env=clean_env,
                                     text=True, capture_output=True, timeout=240)
            if error:
                assert checked.returncode and error in checked.stderr, checked.stdout + checked.stderr
                return json.loads(checked.stderr)
            assert checked.returncode == 0, checked.stdout + checked.stderr
            result = json.loads(checked.stdout)
            assert result["nativePrivacyChecked"] and result["sourceFunctionalChecked"] and result["sourcePrivacyChecked"]
            return result

        accepted = audit(proof)
        (output / "audit.json").write_text(json.dumps(accepted, indent=2, sort_keys=True) + "\n")
        for name, policy_name, proof_name, error in [
            ("WrongScope", f"{NS}.allOutcomesPolicy", f"{NS}.privacy", "wrong_native_privacy_obligation"),
            ("FunctionalOnly", f"{NS}.policy", "Noctium.PrivateClaimVerification.functional", "wrong_native_privacy_obligation"),
        ]:
            rejection = audit(proof, policy_name, proof_name, error)
            (output / (name + "-audit-rejection.json")).write_text(json.dumps(rejection, indent=2) + "\n")
        original = (ROOT / "proofs/PrivateClaimNativePrivacy.lean").read_text()
        marker = "⟨view, queries (operations w), binding view⟩"
        assert original.count(marker) == 1
        build("proofs/PrivateClaimNativePrivacy.lean", original.replace(marker, "⟨view, [], binding view⟩"))
        observer_mutant = export("proofs.PrivateClaimNativePrivacy", [f"{NS}.privacy"], "changed-observer.ndjson")
        rejection = audit(observer_mutant, error="model_declaration_mismatch:")
        (output / "changed-observer-rejection.json").write_text(json.dumps(rejection, indent=2) + "\n")
        build("proofs/PrivateClaimNativePrivacy.lean")
        source = (ROOT / "examples/PrivateClaim.lean").read_text()
        marker = "    require eq(storedRoot, root)\n"
        assert source.count(marker) == 1
        build("examples/PrivateClaim.lean", source.replace(marker, ""))
        stale = export("proofs.PrivateClaimNativePrivacy", [f"{NS}.privacy"], "changed-source-stale-proof.ndjson")
        rejection = audit(stale, error="model_declaration_mismatch:")
        (output / "changed-source-rejection.json").write_text(json.dumps(rejection, indent=2) + "\n")
        if args.native_checker:
            native = run(["node", "tests/private-claim-privacy-checker.mjs", str(args.native_checker.resolve()),
                          str(emitted / "PrivateClaim.claim.impact.json"), str(emitted / "PrivateClaim.claim.zkir")])
            (output / "native-checker.json").write_text(native.stdout)
        summary = {"status": "formal-privacy-package-passed-exact-byte-build-integration-pending", "issue58Complete": False,
            "policy": f"{NS}.policy", "privacyProof": f"{NS}.privacy", "sourcePolicy": "Noctium.PrivateClaimVerification.policy",
            "observer": "successfulClaimPublicTranscriptV1", "scope": "successful-valid-executions-only",
            "observables": ["declared public root/campaign/nullifier", "return nullifier", "public before/after state",
                "six aligned reads", "public read scalars", "ordered opcode payloads and query paths", "all-active mask",
                "empty communication commitment", "real bound proof statement under explicit binding agreement"],
            "excludedObservables": ["rejected outcomes", "termination", "timing and resources", "proof bytes", "host/provider access", "host logs"],
            "hostPremise": "shared parent public context and communication randomness; real proof-phase binding agrees with the public binding view",
            "nativeImplementationAgreementRequired": True, "hashAgreementRequired": True, "proofByteZeroKnowledgeProved": False,
            "sourceSha256": hashlib.sha256((ROOT / "examples/PrivateClaim.lean").read_bytes()).hexdigest(),
            "planSha256": hashlib.sha256(plan_bytes).hexdigest(), "callSha256": hashlib.sha256(call_bytes).hexdigest(),
            "trustedModelSha256": pin, "externalModelSupplied": bool(args.trusted_model_export), "specificationReviewVerified": False,
            "proofExportSha256": hashlib.sha256(proof.read_bytes()).hexdigest(), "axioms": axioms, "kernelReplayed": True,
            "artifactMutantsRejected": mutants, "policyMutantsRejected": ["WrongScope", "WrongRelease", "FunctionalOnly"],
            "changedObserverRejected": True, "staleChangedSourceRejected": True, "nativeSamplesChecked": bool(args.native_checker),
            "symmetricPathDifferentPrivateWitnesses": True, "byteParserCorrespondenceProved": False,
            "compilerBuildAuthenticated": False, "deployedIdentityAuthenticated": False, "compiledContractVerified": False,
            "remainingRequiredLinks": ["issue56 exact UTF-8 bytes and authenticated build integration", "issue57 deployed key/operation identity"],
            "retainedArtifacts": str(output)}
        if (ROOT / "privacy-snapshot.json").exists():
            snapshot = json.loads((ROOT / "privacy-snapshot.json").read_text())
            snapshot["overlaySha256"] = {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
                                         for name in snapshot["overlayFiles"]}
            summary["snapshot"] = snapshot
        (output / "summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
        print(json.dumps(summary, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
