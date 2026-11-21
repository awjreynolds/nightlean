import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { createCircuitContext, createConstructorContext } from '@midnight-ntwrk/compact-runtime';
import { Contract, ledger } from './compact/contract/index.js';

const contract = new Contract({});
const wallet = '00'.repeat(32);
const own = '09'.repeat(32);
const coin = { color: new Uint8Array(32).fill(1), nonce: new Uint8Array(32).fill(2), value: 5n };
const { currentContractState } = await contract.initialState(createConstructorContext(null, wallet));
const view = (state) => {
  const { coinSlot, coinSet, coinList } = ledger(state);
  return { coinSlot, coinSet: [...coinSet], coinList: [...coinList] };
};
const initial = view(currentContractState.data);
const contextFor = (entry) => createCircuitContext({
  circuitId: entry, contractAddress: own, coinPublicKeyOrZswapState: wallet,
  contractState: currentContractState.data, privateState: null,
});
const receipt = { impact: {} };

for (const [entry, field] of [['putInCell', 'coinSlot'], ['putInSet', 'coinSet'], ['putInList', 'coinList']]) {
  const unbooked = contextFor(entry);
  await assert.rejects(contract.circuits[entry](unbooked, coin, false), /Coin commitment not found/);
  assert.deepEqual(view(unbooked.callContext.currentQueryContext.state), initial);

  const { context } = await contract.circuits[entry](contextFor(entry), coin, true);
  const query = context.callContext.currentQueryContext;
  const zswap = context.callContext.currentZswapLocalState;
  assert.equal(zswap.currentIndex, 1n);
  assert.equal(zswap.outputs.length, 1);
  assert.deepEqual(zswap.outputs[0].coinInfo, coin);
  assert.equal(query.effects.claimedShieldedReceives.length, 1);
  const qualified = { ...coin, mt_index: 0n };
  assert.deepEqual(view(query.state), { ...initial, [field]: field === 'coinSlot' ? qualified : [qualified] });

  const artifact = new URL(`./compact/zkir/${entry}.zkir`, import.meta.url);
  const relation = JSON.parse(await readFile(artifact, 'utf8'));
  const impact = relation.instructions.filter(({ op }) => op === 'impact');
  const qualifiedLookup = impact.findIndex(({ inputs }) => inputs[0] === '0x61');
  assert.ok(qualifiedLookup > 0);
  assert.deepEqual(impact[qualifiedLookup].inputs, ['0x61', '0x01', '0x01', '0x01', '-0x01']);
  const [commitment, lookup, fields, swap, concatenate] = impact.slice(qualifiedLookup - 1, qualifiedLookup + 4);
  assert.equal(commitment.guard, '0x01');
  assert.equal(lookup.guard, '0x01');
  assert.deepEqual(commitment.inputs, ['0x10', '0x01', '0x01', '0x20', '%hash.17', '%hash.16']);
  assert.deepEqual(fields.inputs, [
    '0x10', '0x01', '0x03', '0x20', '0x20', '0x10', '%coin.0', '%coin.1', '%coin.2', '%coin.3', '%coin.4',
  ]);
  assert.deepEqual(swap.inputs, ['0x40']);
  assert.deepEqual(concatenate.inputs, ['0x17', '0x5b']);
  receipt.impact[entry] = impact;
}

console.log(JSON.stringify(receipt, null, 2));
