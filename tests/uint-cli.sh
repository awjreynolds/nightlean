#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
cli="$PWD/.lake/build/bin/nightlean"
scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT

"$cli" compile examples/BoundedScalars.lean --output "$scratch/first"
"$cli" compile examples/BoundedScalars.lean --output "$scratch/second"
diff -r "$scratch/first" "$scratch/second"

node --input-type=module - "$scratch/first" <<'JS'
import {readFileSync} from 'node:fs';
import {join} from 'node:path';
import {deepStrictEqual, ok} from 'node:assert/strict';
const directory = process.argv[2];
const plan = JSON.parse(readFileSync(join(directory, 'BoundedScalars.apply.impact.json')));
const circuit = JSON.parse(readFileSync(join(directory, 'BoundedScalars.apply.zkir')));
deepStrictEqual(plan.circuit.inputs.map(value => value.type), ['UIntRange<511>', 'UIntRange<256>', 'UIntRange<256>']);
deepStrictEqual(plan.state[0].kind, {cell: 'UIntRange<511>'});
deepStrictEqual(plan.circuit.constraints[0].left.tag, 'uadd');
deepStrictEqual(plan.circuit.constraints[0].left.maximum, '510');
ok(circuit.instructions.some(value => value.op === 'constrain_bits' && value.bits === 8));
ok(circuit.instructions.some(value => value.op === 'less_than' && value.bits === 9));
ok(circuit.instructions.every(value => value.op !== 'sub'));
deepStrictEqual(circuit.instructions.filter(value => value.op === 'output').length, 1);
deepStrictEqual(circuit.instructions.at(-1).op, 'output');
JS

cat > "$scratch/invalid.lean" <<'LEAN'
import Nightlean.Frontend
open scoped Nightlean
nightlean_circuit bad where
  private unused : UInt 249
end
LEAN
if "$cli" compile "$scratch/invalid.lean" --output "$scratch/invalid-output" > "$scratch/error" 2>&1; then
  echo 'oversized unsigned type compiled' >&2
  exit 1
fi
grep -F 'unsigned width exceeds target maximum' "$scratch/error" > /dev/null
test ! -e "$scratch/invalid-output"

"$cli" compile examples/PrivateClaim.lean --output "$scratch/claim"
node --input-type=module - "$scratch/claim/PrivateClaim.claim.zkir" <<'JS'
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {deepStrictEqual} from 'node:assert/strict';
deepStrictEqual(createHash('sha256').update(readFileSync(process.argv[2])).digest('hex'),
  'c569dd887fdf6aa3bdd2c8e2358985657ad3612eb72e0eb16f28682bb2b2b81c');
JS
echo 'Unsigned CLI conformance passed'
