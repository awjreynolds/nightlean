#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."
cli="$PWD/.lake/build/bin/noctium"
scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT

expect_failure() {
  if "$@" > "$scratch/stdout" 2> "$scratch/stderr"; then
    echo "expected command failure: $*" >&2
    exit 1
  fi
}

"$cli" --version
"$cli" check examples/PrivateClaim.lean
"$cli" compile examples/PrivateClaim.lean --output "$scratch/first"
"$cli" compile examples/PrivateClaim.lean --output "$scratch/second"
diff -r "$scratch/first" "$scratch/second"
test -f "$scratch/first/claimRelation.zkir"
test -f "$scratch/first/PrivateClaim.claim.zkir"
test -f "$scratch/first/PrivateClaim.claim.impact.json"
test -f "$scratch/first/noctium.json"
grep -F '"deployable": false' "$scratch/first/noctium.json" > /dev/null
grep -F '"ledger": "9.1.0.1"' "$scratch/first/noctium.json" > /dev/null
grep -F '"nativeCircuitFile": "PrivateClaim.claim.zkir"' "$scratch/first/noctium.json" > /dev/null
grep -F '"nativeCircuitQualified": false' "$scratch/first/noctium.json" > /dev/null
grep -F '"nativePlanFile": "PrivateClaim.claim.impact.json"' "$scratch/first/noctium.json" > /dev/null
lake env lean --run tests/Impact.lean --zkir > "$scratch/reference.zkir"
node --input-type=module - "$scratch/first/PrivateClaim.claim.zkir" "$scratch/reference.zkir" <<'JS'
import { readFileSync } from 'node:fs';
import { deepStrictEqual } from 'node:assert';
const [generated, reference] = process.argv.slice(2).map(path => JSON.parse(readFileSync(path, 'utf8')));
deepStrictEqual(generated, reference, 'Lean source entrypoint differs from the native reference fixture');
deepStrictEqual(generated.do_communications_commitment, true);
JS
node --input-type=module - "$scratch/first/PrivateClaim.claim.impact.json" <<'JS'
import { readFileSync } from 'node:fs';
import { deepStrictEqual, ok } from 'node:assert';
const plan = JSON.parse(readFileSync(process.argv[2], 'utf8'));
deepStrictEqual(plan.schemaVersion, 1);
deepStrictEqual(plan.contractName, 'PrivateClaim');
deepStrictEqual(plan.entrypoint, 'claim');
deepStrictEqual(plan.nativeCircuitFile, 'PrivateClaim.claim.zkir');
deepStrictEqual(plan.operations[0], { op: 'push', storage: false, alignment: 'field', expression: { tag: 'reference', name: 'root' } });
deepStrictEqual(plan.circuit.inputs.find(value => value.name === 'secret').visibility, 'private');
deepStrictEqual(plan.circuit.outputs[0].expression, { tag: 'reference', name: 'suppliedNullifier' });
ok(plan.circuit.constraints.length > 0);
deepStrictEqual(plan.reads.map(value => value.name), ['root', 'campaign', 'suppliedNullifier', 'storedRoot', 'storedCampaign', '_noctium_absence_5']);
JS

cat > "$scratch/later-error.lean" <<'LEAN'
import Noctium.Frontend
open scoped Noctium
noctium_circuit valid where
  public value : Native
  output result : Native := value
end
noctium_circuit invalid where
  private secret : Native
  assert secret
end
LEAN
expect_failure "$cli" compile "$scratch/later-error.lean" --output "$scratch/later-output"
grep -F 'Noctium expression type mismatch' "$scratch/stdout" > /dev/null
test ! -e "$scratch/later-output"

cat > "$scratch/traversal.lean" <<'LEAN'
import Noctium.Frontend
open scoped Noctium
noctium_circuit «../escape» where
  public value : Native
  output result : Native := value
end
LEAN
expect_failure "$cli" compile "$scratch/traversal.lean" --output "$scratch/traversal-output"
grep -F 'not a safe artifact filename' "$scratch/stdout" > /dev/null
test ! -e "$scratch/traversal-output"
test ! -e "$scratch/escape.zkir"

cat > "$scratch/entry-traversal.lean" <<'LEAN'
import Noctium.Frontend
open scoped Noctium
noctium_circuit relation where
  public value : Native
  output result : Native := value
end
noctium_contract SafeContract where
  entry «../escape» uses relation where
  end
end
LEAN
expect_failure "$cli" compile "$scratch/entry-traversal.lean" --output "$scratch/entry-traversal-output"
grep -F 'not a safe artifact filename' "$scratch/stdout" > /dev/null
test ! -e "$scratch/entry-traversal-output"

cat > "$scratch/collision.lean" <<'LEAN'
import Noctium.Frontend
open scoped Noctium
namespace Collision
noctium_circuit claim where
  public value : Native
  output result : Native := value
end
end Collision
noctium_contract Collision where
  entry claim uses Collision.claim where
  end
end
LEAN
expect_failure "$cli" compile "$scratch/collision.lean" --output "$scratch/collision-output"
grep -F 'artifact filenames collide' "$scratch/stdout" > /dev/null
test ! -e "$scratch/collision-output"

cat > "$scratch/imported.lean" <<'LEAN'
import examples.PrivateClaim
import Noctium.Frontend
open scoped Noctium
noctium_circuit localRelation where
  public value : Native
  output result : Native := value
end
noctium_contract ImportedCircuitContract where
  entry claim uses claimRelation where
  end
end
LEAN
# Build the fixture only in the temporary directory, leaving the checkout unchanged.
lake env lean -o "$scratch/PrivateClaim.olean" examples/PrivateClaim.lean
# The source's import resolves through a temporary package path rather than the source tree.
mkdir -p "$scratch/imports/examples"
cp "$scratch/PrivateClaim.olean" "$scratch/imports/examples/PrivateClaim.olean"
expect_failure env LEAN_PATH="$scratch/imports:${LEAN_PATH:-}" "$cli" compile "$scratch/imported.lean" --output "$scratch/imported-output"
grep -F 'references imported circuit' "$scratch/stdout" > /dev/null
test ! -e "$scratch/imported-output"

cat > "$scratch/empty.lean" <<'LEAN'
import Noctium.Frontend
LEAN
expect_failure "$cli" check "$scratch/empty.lean"
expect_failure "$cli" check "$scratch/missing.lean"
expect_failure "$cli" check examples/PrivateClaim.lean --target "$scratch/missing.json"
expect_failure "$cli" check examples/PrivateClaim.lean --adapter compact
expect_failure "$cli" compile examples/PrivateClaim.lean --adapter unknown
expect_failure "$cli" compile examples/PrivateClaim.lean --adapter compact --output "$scratch/removed-adapter"
grep -F "unexpected argument '--adapter'" "$scratch/stderr" > /dev/null
test ! -e "$scratch/removed-adapter"
test -z "$(find "$scratch/first" -type f -name '*.compact' -print)"
echo "CLI conformance checks passed"
