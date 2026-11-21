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
mkdir "$scratch/second"
"$cli" compile examples/PrivateClaim.lean --output "$scratch/second/"
expect_failure "$cli" compile examples/BoundedScalars.lean --output "$scratch/first"
grep -F 'must be a new or empty directory' "$scratch/stderr" > /dev/null
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

cat > "$scratch/early-exit.lean" <<'LEAN'
import Noctium.Frontend
run_cmd liftM (IO.Process.exit 0 : IO Unit)
LEAN
expect_failure "$cli" compile "$scratch/early-exit.lean" --output "$scratch/early-output"
grep -F 'Lean exited before producing Noctium artifacts' "$scratch/stderr" > /dev/null
test ! -e "$scratch/early-output"
test -z "$(find "$scratch" -maxdepth 1 -type d -name '.noctium-*' -print)"

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

mkdir -p "$scratch/imports"
cat > "$scratch/imports/ImportedCircuitLibrary.lean" <<'LEAN'
import Noctium.Frontend
open scoped Noctium
namespace ImportedCircuitLibrary
noctium_circuit claimRelation where
  public value : Native
  output result : Native := value
end
noctium_circuit unusedRelation where
  public value : Native
  output result : Native := value
end
end ImportedCircuitLibrary
LEAN
# Compile the imported source into a separate Lean module, as normal import
# resolution requires. The Noctium CLI then consumes one registered circuit.
lake env lean --root="$scratch/imports" -o "$scratch/imports/ImportedCircuitLibrary.olean" \
  "$scratch/imports/ImportedCircuitLibrary.lean"

cat > "$scratch/imported.lean" <<'LEAN'
import ImportedCircuitLibrary
import Noctium.Frontend
open scoped Noctium
noctium_contract ImportedCircuitContract where
  cell total : Native
  entry claim uses ImportedCircuitLibrary.claimRelation where
    write total := result
  end
end
LEAN
env LEAN_PATH="$scratch/imports:$PWD/.lake/build/lib/lean" \
  "$cli" compile "$scratch/imported.lean" --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --output "$scratch/imported-output"
test -f "$scratch/imported-output/ImportedCircuitLibrary.claimRelation.zkir"
test -f "$scratch/imported-output/ImportedCircuitContract.claim.impact.json"
test ! -e "$scratch/imported-output/ImportedCircuitLibrary.unusedRelation.zkir"
{
  cat "$scratch/imports/ImportedCircuitLibrary.lean"
  sed -n '/^noctium_contract /,$p' "$scratch/imported.lean"
} > "$scratch/combined.lean"
"$cli" compile "$scratch/combined.lean" --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --output "$scratch/combined-output"
cmp "$scratch/imported-output/ImportedCircuitContract.claim.zkir" \
  "$scratch/combined-output/ImportedCircuitContract.claim.zkir"
node - "$scratch/imported-output/noctium.json" <<'JS'
const fs = require('node:fs');
const manifest = JSON.parse(fs.readFileSync(process.argv[2], 'utf8'));
if (manifest.circuits.length !== 1 ||
    manifest.circuits[0].name !== 'ImportedCircuitLibrary.claimRelation') {
  throw new Error('compiler did not emit only the explicitly selected imported circuit');
}
const [contract] = manifest.contracts;
if (contract.name !== 'ImportedCircuitContract' ||
    contract.entrypoints[0].circuit !== 'ImportedCircuitLibrary.claimRelation') {
  throw new Error('imported circuit identity changed in the compiled contract');
}
if (contract.entrypoints[0].nativeCircuitQualified !== false || manifest.deployable !== false) {
  throw new Error('imported source proof provenance was overstated');
}
JS

cat > "$scratch/unresolved-imported.lean" <<'LEAN'
import ImportedCircuitLibrary
import Noctium.Frontend
open scoped Noctium
noctium_contract UnresolvedImportedCircuitContract where
  entry claim uses ImportedCircuitLibrary.missingRelation where
  end
end
LEAN
expect_failure env LEAN_PATH="$scratch/imports:$PWD/.lake/build/lib/lean" \
  "$cli" compile "$scratch/unresolved-imported.lean" --output "$scratch/unresolved-imported-output"
grep -F 'entrypoint requires a registered Noctium circuit' "$scratch/stdout" > /dev/null
test ! -e "$scratch/unresolved-imported-output"

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
