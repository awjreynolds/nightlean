#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT

lake exe noctium compile tests/component-disclosure/authorized.lean --output "$scratch/authorized"
node --input-type=module - "$scratch/authorized" <<'JS'
import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {join} from 'node:path';

const directory = process.argv[2];
const metadata = JSON.parse(await readFile(join(directory, 'nightlean.json'), 'utf8'));
assert.equal(metadata.circuits.length, 1);
const circuit = metadata.circuits[0];
assert.deepEqual(circuit.inputs.map(input => input.name), [
  'payload.balance', 'payload.nonce', '$helper4'
]);
assert.ok(circuit.inputs.every(input => input.visibility === 'private'));
assert.deepEqual(circuit.outputs.map(output => output.name), ['result.balance', 'result.nonce']);
assert.ok(circuit.outputs.every(output => output.visibility === 'public'));
const relation = JSON.parse(await readFile(join(directory, 'componentRelease.zkir'), 'utf8'));
assert.equal(relation.instructions.filter(instruction => instruction.op === 'private_input').length, 3);
assert.equal(relation.instructions.at(-1).op, 'output');
JS

if lake exe noctium compile tests/component-disclosure/unauthorized.lean --output "$scratch/unauthorized" > "$scratch/reject.log" 2>&1; then
  cat "$scratch/reject.log" >&2
  echo 'unauthorized component disclosure compiled' >&2
  exit 1
fi
grep -F "private parameter 'payload.balance'" "$scratch/reject.log" >/dev/null
test ! -e "$scratch/unauthorized"

if lake exe noctium compile tests/component-disclosure/unauthorized-private-state.lean \
    --output "$scratch/private-state" > "$scratch/private-state-reject.log" 2>&1; then
  cat "$scratch/private-state-reject.log" >&2
  echo 'undisclosed private-state aggregate compiled' >&2
  exit 1
fi
grep -F "private-state read 'account.balance'" "$scratch/private-state-reject.log" >/dev/null
test ! -e "$scratch/private-state"
echo 'Component disclosure source compilation checks passed'
