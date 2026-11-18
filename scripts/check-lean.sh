#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

# Build every library module before checking standalone test imports.
python3 - <<'PY'
from pathlib import Path
import subprocess

modules = sorted(".".join(path.with_suffix("").parts) for path in Path("Noctium").rglob("*.lean"))
subprocess.run(["lake", "build", "Noctium", "noctium", "noctium", *modules], check=True)
for source in sorted(Path("tests").glob("*.lean")):
    print(f"Checking {source}", flush=True)
    subprocess.run(["lake", "env", "lean", str(source)], check=True)
PY

lake exe noctium check examples/PrivateClaim.lean
scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT
lake exe noctium compile examples/PrivateClaim.lean --output "$scratch/claim"
bash scripts/proofs/check-private-claim.sh
bash tests/component-disclosure-cli.sh
