#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
lake env lean tests/Modules.lean
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
lake exe noctium compile tests/modules/Native.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --output "$scratch/first"
lake exe noctium compile tests/modules/Native.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --output "$scratch/second"
diff -r "$scratch/first" "$scratch/second"
node - "$scratch/first/noctium.json" <<'JS'
const fs = require('node:fs');
const manifest = JSON.parse(fs.readFileSync(process.argv[2], 'utf8'));
const [contract] = manifest.contracts;
if (manifest.contracts.length !== 1 || contract.entrypoints.length !== 3) {
  throw new Error('expected one module contract with three exported entrypoints');
}
if (contract.state.length !== 2) {
  throw new Error(`expected two canonical state fields, found ${contract.state.length}`);
}
const stateTypes = contract.state.map(state => state.kind.cell).sort();
if (stateTypes.join(',') !== 'Native,UIntRange<256>') {
  throw new Error(`generic state types were not substituted: ${stateTypes.join(',')}`);
}
const entries = Object.fromEntries(contract.entrypoints.map(entry => [entry.name, entry]));
const field = name => entries[name].effects.find(effect => effect.op === 'writeCell')?.state;
if (entries.firstUpdate.circuit !== entries.againUpdate.circuit ||
    field('firstUpdate') !== field('againUpdate')) {
  throw new Error('re-export aliases did not reuse circuit and state identities');
}
if (entries.differentUpdate.circuit === entries.firstUpdate.circuit ||
    field('differentUpdate') === field('firstUpdate')) {
  throw new Error('different generic arguments reused a circuit or state identity');
}
JS
echo 'Module expansion and source CLI checks passed'
