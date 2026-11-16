#!/usr/bin/env python3
"""Check data exports against an independently trusted model pin. Standard library only."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile


MAX_EXPORT_BYTES = 64 * 1024 * 1024
ROOT = Path(__file__).resolve().parents[2]


def retained_file(path: Path) -> bytes:
    with path.open("rb") as handle:
        if os.fstat(handle.fileno()).st_size > MAX_EXPORT_BYTES:
            raise ValueError("export_limit")
        contents = handle.read(MAX_EXPORT_BYTES + 1)
    if len(contents) > MAX_EXPORT_BYTES:
        raise ValueError("export_limit")
    return contents


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--model-export", type=Path, required=True)
    parser.add_argument("--proof-export", type=Path, required=True)
    parser.add_argument("--trusted-model-sha256", required=True)
    parser.add_argument("--policy", required=True)
    parser.add_argument("--functional-proof", required=True)
    parser.add_argument("--privacy-proof")
    args = parser.parse_args()
    try:
        if not re.fullmatch("[0-9a-f]{64}", args.trusted_model_sha256):
            raise ValueError("invalid_model_pin")
        model = retained_file(args.model_export)
        proof = retained_file(args.proof_export)
        model_digest = hashlib.sha256(model).hexdigest()
        if model_digest != args.trusted_model_sha256:
            raise ValueError("model_pin_mismatch")
        # Retain both inputs before checking. The checker never reopens caller paths.
        with tempfile.TemporaryDirectory(prefix="nightlean-proof-audit-") as directory:
            scratch = Path(directory)
            model_path, proof_path = scratch / "model.ndjson", scratch / "proof.ndjson"
            model_path.write_bytes(model)
            proof_path.write_bytes(proof)
            command = [
                "lake", "env", "lean", "--run", "scripts/proofs/AuditExport.lean",
                str(model_path), str(proof_path), args.policy, args.functional_proof,
            ]
            if args.privacy_proof:
                command.append(args.privacy_proof)
            environment = os.environ.copy()
            environment.pop("LEAN_PATH", None)
            environment.pop("LEAN_SRC_PATH", None)
            checked = subprocess.run(
                command, cwd=ROOT, env=environment, capture_output=True, text=True,
                timeout=180, check=False,
            )
        if checked.returncode:
            try:
                error = json.loads(checked.stderr)["error"]
            except (ValueError, KeyError, TypeError):
                error = "trusted_export_checker_failed"
            raise ValueError(error)
        result = json.loads(checked.stdout)
        if result.get("compiledContractVerified") is not False:
            raise ValueError("unexpected_checker_status")
        result["trustedModelSha256"] = model_digest
        result["proofExportSha256"] = hashlib.sha256(proof).hexdigest()
        result["externalModelPinChecked"] = True
        result.pop("externalModelPinRequired", None)
        print(json.dumps(result, sort_keys=True))
        return 0
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print(json.dumps({"status": "rejected", "error": str(error)}))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
