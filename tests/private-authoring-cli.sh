#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
cli="$PWD/.lake/build/bin/noctium"
scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT

"$cli" compile examples/PrivateStateCounter.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json --output "$scratch/generated"
for fixture in runtime/tests/fixtures/private-authoring/321/*; do
  test -f "$fixture" || continue
  cmp "$fixture" "$scratch/generated/${fixture##*/}"
done

profile=profiles/midnight-ledger-9-zkir-3.2.1-target.json
"$cli" compile examples/PrivateStateCounter.lean --target "$profile" \
  --emit ledger --emit witness --output "$scratch/ledger"
test ! -e "$scratch/generated/bindings"
test ! -e "$scratch/ledger/bindings"
"$cli" compile examples/PrivateStateCounter.lean --target "$profile" \
  --emit ledger --emit witness --bindings rust --output "$scratch/rust"
binding=bindings/rust/NoctiumExamples.PrivateStateCounter.advance.rs
cmp "runtime/tests/fixtures/private-authoring/321/$binding" "$scratch/rust/$binding"
if "$cli" compile examples/PrivateStateCounter.lean --target "$profile" \
  --emit ledger --output "$scratch/missing-witness" > "$scratch/error" 2>&1; then
  echo "expected a hosted ledger entrypoint to require its witness artifacts" >&2
  exit 1
fi
grep -F 'requires --emit witness' "$scratch/error" > /dev/null
test ! -e "$scratch/missing-witness"
if "$cli" compile examples/PrivateStateCounter.lean --bindings kotlin \
  --output "$scratch/unsupported-host" > "$scratch/error" 2>&1; then
  echo "expected an unsupported binding target to fail" >&2
  exit 1
fi
grep -F "unsupported binding target 'kotlin'" "$scratch/error" > /dev/null
test ! -e "$scratch/unsupported-host"

python3 - "$scratch/generated" "$scratch/ledger" "$scratch/rust" "$binding" <<'PY'
import json
import sys
from pathlib import Path

full, selected, rust = map(Path, sys.argv[1:4])
rust_binding = sys.argv[4]
entry = "NoctiumExamples.PrivateStateCounter.advance"
expected = {
    entry + ".zkir": "ledger",
    entry + ".impact.json": "ledger",
    entry + ".witness.json": "witness",
    entry + ".witness.control.json": "witness",
}
assert {path.name for path in selected.iterdir()} == set(expected) | {"noctium.json"}
meta = json.loads((selected / "noctium.json").read_text())
assert meta["schemaVersion"] == 2
assert {row["file"]: row["role"] for row in meta["artifacts"]} == expected
for name in expected:
    if name.endswith(".impact.json"):
        plan = json.loads((selected / name).read_text())
        original = json.loads((full / name).read_text())
        assert meta["circuits"] == [plan["circuit"]]
        del original["circuit"]["file"]
        assert plan == original
    else:
        assert (selected / name).read_bytes() == (full / name).read_bytes()
    assert (selected / name).read_bytes() == (rust / name).read_bytes()
rust_meta = json.loads((rust / "noctium.json").read_text())
assert {str(path.relative_to(rust)) for path in rust.rglob("*") if path.is_file()} == set(expected) | {"noctium.json", rust_binding}
assert {row["file"]: row["role"] for row in rust_meta["artifacts"]} == {**expected, rust_binding: "rustBinding"}
PY

cat > "$scratch/private-release.lean" <<'LEAN'
import Noctium.Frontend
open scoped Noctium
def ordinaryLeanUnit : Unit := ()
noctium_witness noop() : Unit
noctium_witness_circuit unitCall where
  witness noop()
end
noctium_private_state Wallet where
  cell saved : UInt 8
end
noctium_witness_circuit leak where
  read private Wallet.saved as previous
  output leaked : UInt 8 := previous
end
LEAN
if "$cli" compile "$scratch/private-release.lean" --output "$scratch/rejected" > "$scratch/error" 2>&1; then
  echo "private state reached a public output without disclose" >&2
  exit 1
fi
grep -F "public output" "$scratch/error" > /dev/null
test ! -e "$scratch/rejected"

sed 's/:= previous/:= disclose(previous)/' "$scratch/private-release.lean" > "$scratch/approved-release.lean"
"$cli" compile "$scratch/approved-release.lean" --output "$scratch/approved"
python3 - "$scratch/generated/NoctiumExamples.advance.observations.json" "$scratch/approved/leak.observations.json" "$scratch/generated" <<'PY'
import json
import sys
from pathlib import Path

with open(sys.argv[1]) as stream:
    counter = json.load(stream)
assert counter["privateReads"] == ["noctium/NoctiumExamples.Wallet/saved"]
assert counter["privateStages"] == ["noctium/NoctiumExamples.Wallet/saved"]
assert counter["witnessNames"] == ["NoctiumExamples.nextValue"]
assert len(counter["authoredProves"]) == 2
assert not counter["explicitReleases"]
assert any("cast" in condition for condition in counter["generatedValidity"])
with open(sys.argv[2]) as stream:
    release = json.load(stream)
assert release["explicitReleases"] == ["previous"]
root = Path(sys.argv[3])
with (root / "NoctiumExamples.PrivateStateCounter.advance.witness.json").open() as stream:
    bound = json.load(stream)
assert bound["ledgerInputs"] == [{"name":"current", "type":"UIntRange<256>", "visibility":"public"}]
assert all(value["name"] != "current" for value in bound["circuitInputs"])
with (root / "NoctiumExamples.advance.witness.json").open() as stream:
    standalone = json.load(stream)
assert "ledgerInputs" not in standalone
PY
echo "readable private state source checks passed"
