#!/usr/bin/env python3
"""Exercise issue-66 role types, fresh replay and adversarial export gates."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
SOUNDNESS = "Noctium.Verification.GenericStateAcceptedSoundness.accepted_entrypoint_run_sound"
COMPLETENESS = "Noctium.Verification.GenericStateConverseCompleteness.accepted_entrypoint_run_complete"
FIXTURE = "GenericStateAuditFixtures"
LIMIT = 128 * 1024 * 1024


def command(args: list[str], env: dict[str, str] | None = None) -> str:
    result = subprocess.run(args, cwd=ROOT, env=env, capture_output=True,
                            text=True, timeout=300, check=False)
    if result.returncode or result.stderr:
        raise AssertionError(f"command failed: {args}\n{result.stdout}\n{result.stderr}")
    return result.stdout


def export(path: Path, module: str, roots: list[str], env: dict[str, str]) -> None:
    with path.open("wb") as handle:
        result = subprocess.run(
            ["lake", "env", "leanexport", module, "--", *roots],
            cwd=ROOT, env=env, stdout=handle, stderr=subprocess.PIPE,
            timeout=300, check=False,
        )
    if result.returncode or result.stderr or path.stat().st_size == 0:
        raise AssertionError(
            f"export failed: {module} {roots}, exit={result.returncode}, "
            f"stderr={result.stderr.decode(errors='replace')}"
        )


def digest(path: Path) -> str:
    with path.open("rb") as handle:
        return hashlib.file_digest(handle, "sha256").hexdigest()


def tamper_role_value(source: Path, target: Path) -> None:
    """Keep a parseable role declaration but change its proof before merging."""
    name_index = None
    changed = False
    with source.open("rb") as reader, target.open("wb") as writer:
        for line in reader:
            item = json.loads(line)
            spelling = item.get("str")
            if spelling and spelling.get("str") == "accepted_entrypoint_run_sound":
                name_index = item["in"]
            theorem = item.get("thm")
            if theorem and theorem.get("name") == name_index:
                if changed or theorem["value"] < 2:
                    raise AssertionError("invalid_role_mutation")
                theorem["value"] -= 1
                line = (json.dumps(item, separators=(",", ":")) + "\n").encode()
                changed = True
            writer.write(line)
    if not changed:
        raise AssertionError("missing_role_mutation")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--trusted-model-export", type=Path)
    parser.add_argument("--trusted-model-sha256")
    args = parser.parse_args()
    if bool(args.trusted_model_export) != bool(args.trusted_model_sha256):
        parser.error("external model and digest must be supplied together")
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    command(["lake", "build", "Noctium.Verification.GenericStateProofRoles",
             "Noctium.Verification.GenericStateExportAudit"])
    with tempfile.TemporaryDirectory(prefix="noctium-generic-state-audit-") as directory:
        scratch = Path(directory)
        source = scratch / "source" / f"{FIXTURE}.lean"
        imports = scratch / "imports"
        source.parent.mkdir()
        imports.mkdir()
        source.write_text(f'''import Noctium.Verification.GenericStateProofRoles
import Lean
namespace {FIXTURE}
open Lean Elab Command in
run_cmd do
  for (name, root) in [(`{FIXTURE}.soundness, `{SOUNDNESS}), (`{FIXTURE}.completeness, `{COMPLETENESS})] do
    let some info := (← getEnv).find? root | throwError "missing role"
    liftCoreM <| addDecl (.thmDecl {{name := name, levelParams := info.levelParams, type := info.type, value := mkConst root}})
  let some info := (← getEnv).find? `{SOUNDNESS} | throwError "missing soundness"
  let rec weaken (type : Lean.Expr) : Lean.Expr × Lean.Expr :=
    match type with
    | .forallE name domain body binder =>
      let (rest, proof) := weaken body
      (.forallE name domain rest binder, .lam name domain proof binder)
    | _ => (mkConst ``True, mkConst ``True.intro)
  let (weakType, weakProof) := weaken info.type
  liftCoreM <| addDecl (.thmDecl {{name := `{FIXTURE}.weakened, levelParams := info.levelParams, type := weakType, value := weakProof}})
  liftCoreM <| addDecl (.axiomDecl {{name := `{FIXTURE}.forbiddenAxiom, levelParams := info.levelParams, type := info.type, isUnsafe := false}})
  liftCoreM <| addDecl (.thmDecl {{name := `{FIXTURE}.forgedSoundness, levelParams := info.levelParams, type := info.type, value := mkConst `{FIXTURE}.forbiddenAxiom}})
theorem wrong : True := True.intro
end {FIXTURE}
''')
        environment = os.environ.copy()
        environment["LEAN_PATH"] = str(imports)
        command(["lake", "env", "lean", "-D", "Elab.async=false",
                 "--root", str(source.parent), "-o",
                 str(imports / f"{FIXTURE}.olean"), str(source)], environment)

        baseline = output / "baseline-model.ndjson"
        export(baseline, "Noctium.Verification.GenericStateProofRoles",
               [SOUNDNESS, COMPLETENESS, "propext", "Classical.choice", "Quot.sound"],
               environment)
        trusted = args.trusted_model_export or baseline
        pin = args.trusted_model_sha256 or digest(trusted)
        (output / "trusted-model.sha256").write_text(pin + "\n")
        positive = output / "proofs.ndjson"
        export(positive, FIXTURE, [f"{FIXTURE}.soundness", f"{FIXTURE}.completeness"],
               environment)

        def audit(proofs: Path, *, soundness: str = f"{FIXTURE}.soundness",
                  completeness: str = f"{FIXTURE}.completeness",
                  model: Path = trusted, model_pin: str = pin,
                  expected_error: str | None = None) -> dict:
            checked = subprocess.run(
                ["python3", "scripts/proofs/audit-generic-state-proof.py",
                 "--model-export", str(model), "--proof-export", str(proofs),
                 "--trusted-model-sha256", model_pin,
                 "--soundness-proof", soundness,
                 "--completeness-proof", completeness],
                cwd=ROOT, capture_output=True, text=True, timeout=360, check=False,
            )
            result = json.loads(checked.stdout)
            if expected_error is not None:
                assert checked.returncode != 0 and expected_error in result["error"], result
            else:
                assert checked.returncode == 0, result
                assert result["status"] == "generic-native-state-proofs-checked", result
                assert set(result["axioms"]) <= {
                    "propext", "Classical.choice", "Quot.sound"
                }, result
                assert result["freshKernelReplay"] is True, result
                assert result["wholeCompilerVerified"] is False, result
                assert result["chainAcceptanceVerified"] is False, result
            return result

        reports = {"accepted": audit(positive)}
        reports["swapped"] = audit(positive, soundness=f"{FIXTURE}.completeness",
                                    completeness=f"{FIXTURE}.soundness",
                                    expected_error="wrong_statement: soundness")
        wrong = output / "wrong-statement.ndjson"
        export(wrong, FIXTURE, [f"{FIXTURE}.wrong", f"{FIXTURE}.completeness"],
               environment)
        reports["wrong"] = audit(wrong, soundness=f"{FIXTURE}.wrong",
                                  expected_error="wrong_statement: soundness")
        missing = output / "missing-completeness.ndjson"
        export(missing, FIXTURE, [f"{FIXTURE}.soundness"], environment)
        reports["missing"] = audit(missing, expected_error="missing_proof: completeness")
        weak = output / "weakened.ndjson"
        export(weak, FIXTURE, [f"{FIXTURE}.weakened", f"{FIXTURE}.completeness"],
               environment)
        reports["weakened"] = audit(weak, soundness=f"{FIXTURE}.weakened",
                                    expected_error="wrong_statement: soundness")
        forged = output / "forbidden-axiom.ndjson"
        export(forged, FIXTURE, [f"{FIXTURE}.forgedSoundness", f"{FIXTURE}.completeness"],
               environment)
        reports["forgedAxiom"] = audit(forged, soundness=f"{FIXTURE}.forgedSoundness",
                                       expected_error="forbidden_axiom")
        reports["wrongPin"] = audit(positive, model_pin="0" * 64,
                                    expected_error="model_pin_mismatch")
        oversized = scratch / "oversized.ndjson"
        with oversized.open("wb") as handle:
            handle.truncate(LIMIT + 1)
        reports["oversized"] = audit(oversized, expected_error="export_limit")
        fifo = scratch / "candidate.fifo"
        os.mkfifo(fifo)
        reports["fifo"] = audit(fifo, expected_error="export_not_regular_file")
        symlink = scratch / "candidate-link.ndjson"
        symlink.symlink_to(positive)
        symlink_result = audit(symlink, expected_error="symbolic links")
        reports["symlink"] = symlink_result
        malformed = scratch / "malformed.ndjson"
        malformed.write_bytes(b"not-a-lean-export\n")
        reports["malformedPrefix"] = audit(
            positive, model=malformed, model_pin=digest(malformed),
            expected_error="missing_trusted_model_root")
        changed = scratch / "changed-model.ndjson"
        tamper_role_value(trusted, changed)
        reports["modelMismatch"] = audit(
            positive, model=changed, model_pin=digest(changed),
            expected_error="model_declaration_mismatch")
        summary = {
            "status": "passed",
            "scope": "generic native state proof roles and data-only replay boundary",
            "externalReviewedModelProvided": bool(args.trusted_model_export),
            "trustedModelSha256": pin,
            "soundnessRole": SOUNDNESS,
            "completenessRole": COMPLETENESS,
            "rejections": sorted(k for k in reports if k != "accepted"),
            "wholeCompilerVerified": False,
            "chainAcceptanceVerified": False,
            "reports": reports,
        }
        (output / "summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
        print(json.dumps(summary, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
