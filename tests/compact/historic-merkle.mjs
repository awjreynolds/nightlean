import assert from 'node:assert/strict';
import {
  createCircuitContext, createConstructorContext, dummyContractAddress,
} from '@midnight-ntwrk/compact-runtime';
import { Contract, ledger } from './compact/contract/index.js';

const contract = new Contract({});
const walletKey = '00'.repeat(32);
const { currentContractState } = await contract.initialState(createConstructorContext(null, walletKey));
let state = currentContractState.data;
const invoke = (entrypoint, ...args) => contract.circuits[entrypoint](createCircuitContext({
  circuitId: entrypoint, contractAddress: dummyContractAddress(),
  coinPublicKeyOrZswapState: walletKey, contractState: state, privateState: null,
}), ...args);
const nextState = ({ context }) => context.callContext.currentQueryContext.state;
const view = () => ledger(state).claims;
const currentRoot = () => view().root().field;
const contains = async (field) => (await invoke('checkDigest', {field})).result;
const history = () => [...view().history()].map(({field}) => field);
const sortedHistory = () => history().sort((left, right) => left < right ? -1 : left > right ? 1 : 0);
assert.equal(currentRoot(), 0n);
assert.equal(await contains(0n), true);
assert.deepEqual(history(), [0n]);
const initial = state;
const nextRoot = 17029979906787068148615464077443109129720490673751283300379954364685288014954n;
const leaf = new Uint8Array(32).fill(1);
assert.equal((await invoke('appendAndCheck', leaf, {field: nextRoot})).result, true);
assert.equal((await invoke('appendAndCheck', leaf, {field: 0n})).result, true);
assert.equal((await invoke('appendAndCheck', leaf, {field: 1n})).result, false);
state = nextState(await invoke('writeFieldIndex', 3n, 256n));
const sparseTip = currentRoot();
assert.equal(view().firstFree(), 4n);
assert.equal(await contains(0n), true);
state = nextState(await invoke('clearHistory'));
assert.deepEqual(history(), [sparseTip]);
state = nextState(await invoke('resetTree'));
assert.deepEqual(history(), [0n]);
state = initial;
const expected = [0n];
const steps = [];
const cases = [
  ['appendHash', [new Uint8Array(32).fill(1)], 1n],
  ['appendField', [256n], 2n],
  ['writeHashIndex', [3n, new Uint8Array(32).fill(2)], 4n],
  ['writeFieldIndex', [0n, 0n], 4n],
];
for (const [operation, args, cursor] of cases) {
  const before = state;
  state = nextState(await invoke(operation, ...args));
  const root = currentRoot();
  assert.equal(view().firstFree(), cursor);
  assert.equal((await invoke('fullStatus')).result, cursor === 4n);
  if (operation === 'writeFieldIndex') {
    const saved = state;
    const savedHistory = new Set(history());
    state = before;
    state = nextState(await invoke('restoreDefaultField', args[0]));
    assert.equal(currentRoot(), root);
    assert.equal(view().firstFree(), cursor);
  assert.equal((await invoke('fullStatus')).result, cursor === 4n);
    assert.deepEqual(new Set(history()), savedHistory);
    state = saved;
  }
  expected.push(root);
  assert.deepEqual(new Set(history()), new Set(expected));
  for (const digest of expected) assert.equal(await contains(digest), true);
  steps.push({operation, cursor, root});
}

await assert.rejects(async () => invoke('writeHashIndex', 4n, new Uint8Array(32)));
const tip = currentRoot();
const historyBeforeClear = sortedHistory().map(String);
state = nextState(await invoke('clearHistory'));
assert.equal(currentRoot(), tip);
assert.equal(view().firstFree(), 4n);
assert.deepEqual(history(), [tip]);
assert.equal(await contains(tip), true);
assert.equal(await contains(0n), false);
assert.equal(await contains(expected[1]), false);
const historyAfterClear = sortedHistory().map(String);
state = nextState(await invoke('resetTree'));
assert.equal(currentRoot(), 0n);
assert.equal(view().firstFree(), 0n);
assert.deepEqual(history(), [0n]);
assert.equal(await contains(0n), true);
assert.equal(await contains(tip), false);
const historyAfterReset = sortedHistory().map(String);

console.log(JSON.stringify({
  steps, sparseTip, history: {beforeClear: historyBeforeClear,
    afterClear: historyAfterClear, afterReset: historyAfterReset},
}, (_, value) => typeof value === 'bigint' ? value.toString() : value));
