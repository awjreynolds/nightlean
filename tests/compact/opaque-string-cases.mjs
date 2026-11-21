import assert from 'node:assert/strict';
import { createCircuitContext, createConstructorContext, dummyContractAddress } from '@midnight-ntwrk/compact-runtime';
import { Contract, ledger } from './compact/contract/index.js';

const contract = new Contract({});
const wallet = '00'.repeat(32);
const text = 'é\0λ';
const trailingNul = 'é\0';
const normalForm = /aligned value is not in normal form \(has trailing zero bytes\)/;
const construct = async (value) => contract.initialState(createConstructorContext(null, wallet), value);
const { currentContractState } = await construct(text);
assert.equal(ledger(currentContractState.data).initialized, text);
const empty = await construct('');
assert.equal(ledger(empty.currentContractState.data).initialized, '');
await assert.rejects(() => construct(trailingNul), normalForm);

const contextFor = (circuitId, contractState = currentContractState.data) => createCircuitContext({
  circuitId, contractAddress: dummyContractAddress(), coinPublicKeyOrZswapState: wallet,
  contractState, privateState: null,
});
const key = new Uint8Array(32).fill(2);
const stored = await contract.circuits.store(contextFor('store'), key, text);
const next = stored.context.callContext.currentQueryContext.state;
assert.equal(ledger(next).strings.lookup(key), text);
assert.equal((await contract.circuits.read(contextFor('read', next), key)).result, text);
await assert.rejects(() => contract.circuits.store(contextFor('store'), key, trailingNul), normalForm);
