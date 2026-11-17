#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
cli="$PWD/.lake/build/bin/noctium"
scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT

"$cli" compile examples/PrivateStateCounter.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json --output "$scratch/generated"
for fixture in runtime/tests/fixtures/private-authoring/321/*; do
  cmp "$fixture" "$scratch/generated/${fixture##*/}"
done

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
python3 - "$scratch/generated/NoctiumExamples.advance.observations.json" "$scratch/approved/leak.observations.json" <<'PY'
import json
import sys

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
PY
echo "readable private state source checks passed"
