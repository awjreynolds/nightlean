import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {
  createCircuitContext, createConstructorContext, dummyContractAddress,
} from '@midnight-ntwrk/compact-runtime';
import { Contract, ledger } from './compact/contract/index.js';

const contract = new Contract({});
const walletKey = '00'.repeat(32);
const { currentContractState } = await contract.initialState(createConstructorContext(null, walletKey));
let state = currentContractState.data;
const invoke = (entry, ...args) => contract.circuits[entry](createCircuitContext({
  circuitId: entry, contractAddress: dummyContractAddress(),
  coinPublicKeyOrZswapState: walletKey, contractState: state, privateState: null,
}), ...args);
const leaf = {tag: new Uint8Array([12, 0, 0]), details: [true, 258n, 0]};
const changed = {...leaf, details: [true, 259n, 0]};
const first = await invoke('append', leaf);
const ordinary = ledger(first.context.callContext.currentQueryContext.state).claims;
assert.deepEqual(ordinary.findPathForLeaf(leaf), ordinary.pathForLeaf(0n, leaf));
const firstInsert = {
  leafHash: createHash('sha256').update('mdn:lh').update(Buffer.from([12, 0, 0, 1, 2, 1, 0])).digest('hex'),
  root: ordinary.root().field.toString(),
};

const call = await invoke('setHistoricIndex', leaf);
state = call.context.callContext.currentQueryContext.state;
const tree = ledger(state).archives;
const found = tree.findPathForLeaf(leaf);
assert.ok(found);
assert.deepEqual(found, tree.pathForLeaf(3n, leaf));
assert.equal(tree.findPathForLeaf(changed), undefined);
const replacement = tree.pathForLeaf(3n, changed);
const snapshotRoot = tree.root().field;
const candidateRoot = (await invoke('typedPathRoot', replacement)).result;
assert.equal((await invoke('typedPathRoot', found)).result, snapshotRoot);
assert.notEqual(candidateRoot, snapshotRoot);
console.log(JSON.stringify({
  firstInsert,
  snapshotRoot: snapshotRoot.toString(),
  candidateRoot: candidateRoot.toString(),
  steps: replacement.path.map(({sibling, goes_left}) => ({
    sibling: sibling.field.toString(), goesLeft: goes_left,
  })),
}));
