#!/usr/bin/env python3
"""The public proof audit controllers require assertion checks."""

import json
from pathlib import Path
import subprocess
import sys


root = Path(__file__).resolve().parents[1]
for name in ("artifacts", "deployment"):
    script = root / "scripts" / "proofs" / f"check-private-claim-{name}.py"
    subprocess.run([sys.executable, str(script), "--help"], capture_output=True, check=True)
    optimized = subprocess.run(
        [sys.executable, "-O", str(script), "--help"], capture_output=True, text=True,
        check=False,
    )
    if optimized.returncode != 1 or json.loads(optimized.stdout) != {
        "status": "rejected",
        "error": "optimized_python_is_not_qualified",
    }:
        raise SystemExit(f"{name} audit did not reject disabled assertions")
