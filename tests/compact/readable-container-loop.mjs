import assert from 'node:assert/strict';
import { createCircuitContext, createConstructorContext, dummyContractAddress } from '@midnight-ntwrk/compact-runtime';
import { Contract, ledger } from './compact/contract/index.js';

const wallet = '00'.repeat(32);
const initial = { total: 0n };
for (const invalid of [false, true]) {
  const trace = [];
  const contract = new Contract({
    containerBytes: ({ privateState }) => {
      trace.push('bytes');
      return [privateState, Uint8Array.from([4, 5])];
    },
    emptyContainer: ({ privateState }) => {
      trace.push('empty');
      return [privateState, new Uint8Array(0)];
    },
    previous: ({ privateState }) => {
      trace.push(`read:${privateState.total}`);
      return [privateState, privateState.total];
    },
    containerStep: ({ privateState }, item, before) => {
      trace.push(`step:${item}:${before}`);
      const next = item + before - (invalid && item === 5n ? 1n : 0n);
      return [{ ...privateState, total: next }, next];
    },
  });
  const { currentContractState } = await contract.initialState(createConstructorContext(initial, wallet));
  const context = createCircuitContext({
    circuitId: 'update', contractAddress: dummyContractAddress(), coinPublicKeyOrZswapState: wallet,
    contractState: currentContractState.data, privateState: initial,
  });
  const run = () => contract.circuits.update(context, 9n);
  const beforeEmpty = ['bytes', 'read:0', 'step:4:0', 'read:4', 'step:5:4'];
  if (invalid) {
    await assert.rejects(async () => run(), /invalid step/);
    assert.deepEqual(trace, beforeEmpty);
    continue;
  }
  const { result, context: next } = await run();
  const total = ledger(next.callContext.currentQueryContext.state).total;
  assert.equal(result, 9n);
  assert.equal(total, 9n);
  assert.equal(next.callContext.currentPrivateState.total, 9n);
  assert.deepEqual(trace, [...beforeEmpty, 'empty', 'read:9']);
  console.log(JSON.stringify({ result: String(result), total: String(total), trace }));
}
