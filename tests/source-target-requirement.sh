#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
cli="$PWD/.lake/build/bin/noctium"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT

cat > "$scratch/TargetRequirement.lean" <<'LEAN'
import Noctium.Frontend
open scoped Noctium

set_option noctium.requiredTarget "midnight-ledger-9-zkir-3.2.1"

noctium_circuit targetRequirement where
  output result : Native := 7
end
LEAN
source="$scratch/TargetRequirement.lean"
target=profiles/midnight-ledger-9-zkir-3.2.1-target.json
"$cli" check "$source" --target "$target"
"$cli" compile "$source" --target "$target" --emit standalone --output "$scratch/matched"
test -s "$scratch/matched/targetRequirement.zkir"

if "$cli" check "$source" > "$scratch/check-error" 2>&1; then
  exit 1
fi
if "$cli" compile "$source" --output "$scratch/mismatched" > "$scratch/compile-error" 2>&1; then
  exit 1
fi
for operation in check compile; do
  grep -F "requires target 'midnight-ledger-9-zkir-3.2.1', selected 'midnight-ledger-9'" \
    "$scratch/$operation-error" > /dev/null
done
test ! -e "$scratch/mismatched"

sed 's/midnight-ledger-9-zkir-3.2.1/unknown-profile/' "$source" > "$scratch/Unknown.lean"
if "$cli" check "$scratch/Unknown.lean" --target "$target" > "$scratch/unknown-error" 2>&1; then
  exit 1
fi
grep -F "unknown Noctium source target requirement 'unknown-profile'" "$scratch/unknown-error" > /dev/null
