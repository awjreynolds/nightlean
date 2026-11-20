import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {
  CompactTypeJubjubPoint, CompactTypeSecp256k1Scalar,
  createCircuitContext, createConstructorContext, dummyContractAddress,
} from '@midnight-ntwrk/compact-runtime';
import {Contract, ledger} from './compact/contract/index.js';

const contract = new Contract({});
const wallet = '00'.repeat(32);
const initial = await contract.initialState(createConstructorContext(null, wallet));
const curve = {point: {x: 0n, y: 1n}, scalar: 0n};
const call = await contract.circuits.append(createCircuitContext({
  circuitId: 'append', contractAddress: dummyContractAddress(), coinPublicKeyOrZswapState: wallet,
  contractState: initial.currentContractState.data, privateState: null,
}), curve);
const tree = ledger(call.context.callContext.currentQueryContext.state).leaves;
const found = tree.findPathForLeaf(curve);
assert.ok(found);
assert.deepEqual(found, tree.pathForLeaf(0n, curve));
const parts = [[CompactTypeJubjubPoint, curve.point], [CompactTypeSecp256k1Scalar, curve.scalar]];
const alignment = parts.flatMap(([type]) => type.alignment());
const atoms = parts.flatMap(([type, value]) => type.toValue(value)).map(atom => Array.from(atom));
const hash = createHash('sha256').update('mdn:lh');
for (const [i, atom] of atoms.entries()) {
  const bytes = Buffer.alloc(alignment[i].value.length ?? 32);
  bytes.set(atom);
  hash.update(bytes);
}
console.log(JSON.stringify([{
  leaf: {kind: 'fab', value: {value: atoms, alignment}},
  leafHash: hash.digest('hex'),
  root: tree.root().field.toString(),
}]));
