#!/usr/bin/env python3
"""Fresh actual-source proof exports, exact-policy auditing and stale-source negatives."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
NS = "Nightlean.PrivateClaimVerification"
MODULE = "proofs.PrivateClaimVerification"
MODEL_ROOTS = ["Nightlean.Verification.FunctionalObligation", "Nightlean.Verification.PrivacyObligation",
               f"{NS}.policy", "PrivateClaimAuditNegative.wrongPolicy", "propext", "Classical.choice", "Quot.sound"]


def run(args: list[str], env: dict[str, str] | None = None, stdin: str | None = None) -> str:
    result = subprocess.run(args, cwd=ROOT, env=env, input=stdin, capture_output=True, text=True, timeout=240)
    if result.returncode:
        raise AssertionError(f"command failed: {args}\n{result.stdout}\n{result.stderr}")
    return result.stdout


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=ROOT / ".nightlean/audits/private-claim-source")
    parser.add_argument("--trusted-model-export", type=Path)
    parser.add_argument("--trusted-model-sha256")
    args = parser.parse_args()
    if bool(args.trusted_model_export) != bool(args.trusted_model_sha256):
        parser.error("external model export and SHA256 must be supplied together")
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    run(["lake", "build", "Nightlean.Verification.ExportAudit"])
    with tempfile.TemporaryDirectory(prefix="nightlean-private-claim-audit-") as directory:
        scratch = Path(directory)
        imports = scratch / "imports"
        for subdir in ["examples", "proofs"]:
            (imports / subdir).mkdir(parents=True)
        environment = os.environ.copy()
        environment["LEAN_PATH"] = str(imports)

        def build(path: str, source: str | None = None) -> str:
            command = ["lake", "env", "lean", "-D", "Elab.async=false", "-o", str(imports / Path(path).with_suffix(".olean"))]
            if source is not None and not (ROOT / path).exists():
                candidate = scratch / "source" / path
                candidate.parent.mkdir(parents=True, exist_ok=True)
                candidate.write_text(source)
                command += ["--root", str(scratch / "source"), str(candidate)]
                return run(command, environment)
            command += (["--stdin", path] if source is not None else [path])
            return run(command, environment, source)

        def export(filename: str, roots: list[str], module: str = MODULE) -> Path:
            contents = run(["lake", "env", "leanexport", module, "--", *roots], environment)
            destination = output / filename
            destination.write_text(contents)
            return destination

        build("examples/PrivateClaim.lean")
        build("proofs/PrivateClaim.lean")
        report = build("proofs/PrivateClaimVerification.lean")
        (output / "direct-axioms.txt").write_text(report)
        assert report.count("depends on axioms: [propext, Classical.choice, Quot.sound]") == 2, report
        negative = '''import proofs.PrivateClaimVerification
open Nightlean Nightlean.Verification Nightlean.PrivateClaimVerification
namespace PrivateClaimAuditNegative
def wrongPolicy : AuditPolicy :=
  {policy with subject := {subject with specification := {specification with postcondition := fun _ _ _ _ _ => True}}}
end PrivateClaimAuditNegative
'''
        build("proofs/PrivateClaimAuditNegative.lean", negative)
        baseline = export("baseline-model.ndjson", MODEL_ROOTS, "proofs.PrivateClaimAuditNegative")
        proof = export("proofs.ndjson", [f"{NS}.functional", f"{NS}.privacy"])
        # Retain reviewed input bytes before the external driver reads them. A local
        # regression baseline is not an independent review of the business specification.
        model = output / "trusted-model.ndjson"
        model.write_bytes(args.trusted_model_export.read_bytes() if args.trusted_model_export else baseline.read_bytes())
        pin = args.trusted_model_sha256 or hashlib.sha256(model.read_bytes()).hexdigest()
        (output / "trusted-model.sha256").write_text(pin + "\n")

        def audit(candidate: Path, expected_error: str | None = None, policy: str = f"{NS}.policy") -> dict:
            command = ["python3", "scripts/proofs/audit-source-proof.py", "--model-export", str(model),
                       "--proof-export", str(candidate), "--trusted-model-sha256", pin,
                       "--policy", policy, "--functional-proof", f"{NS}.functional", "--privacy-proof", f"{NS}.privacy"]
            checked = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=240)
            result = json.loads(checked.stdout)
            if expected_error:
                assert checked.returncode != 0 and expected_error in result["error"], result
            else:
                assert checked.returncode == 0, result
                assert result["compiledContractVerified"] is False, result
                assert result["sourceFunctionalChecked"] and result["sourcePrivacyChecked"], result
                assert set(result["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"}, result
            return result

        accepted = audit(proof)
        (output / "audit.json").write_text(json.dumps(accepted, indent=2, sort_keys=True) + "\n")
        run(["lake", "env", "leanchecker", "--from-export", str(proof)])
        if not args.trusted_model_export:
            wrong_policy = audit(proof, "wrong_obligation", "PrivateClaimAuditNegative.wrongPolicy")
            (output / "wrong-policy-rejection.json").write_text(json.dumps(wrong_policy, indent=2) + "\n")
        # Deliberately stale proof objects plus a freshly compiled changed actual
        # source relation. Exact retained-model identity must reject before replay.
        source = (ROOT / "examples/PrivateClaim.lean").read_text()
        guard = "    require eq(storedRoot, root)\n"
        assert source.count(guard) == 1
        build("examples/PrivateClaim.lean", source.replace(guard, ""))
        changed = export("changed-source-stale-proofs.ndjson", [f"{NS}.functional", f"{NS}.privacy"])
        rejected = audit(changed, "model_declaration_mismatch: PrivateClaim")
        (output / "changed-source-rejection.json").write_text(json.dumps(rejected, indent=2) + "\n")
        summary = {"status": "passed", "scope": "actual PrivateClaim source functional and successful-only privacy obligations",
                   "modelSha256": pin, "externalModelSupplied": bool(args.trusted_model_export),
                   "specificationReviewVerified": False, "compiledContractVerified": False,
                   "retainedArtifacts": str(output), "axioms": accepted["axioms"]}
        (output / "summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
        print(json.dumps(summary, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
