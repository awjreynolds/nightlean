import assert from 'node:assert/strict';
import { createCircuitContext, createConstructorContext } from '@midnight-ntwrk/compact-runtime';
import { Contract } from './compact/contract/index.js';

const contract = new Contract({});
const wallet = '00'.repeat(32);
const own = '09'.repeat(32);
const color = Uint8Array.from({ length: 32 }, (_, index) => index + 1);
const token = { tag: 'unshielded', raw: Buffer.from(color).toString('hex') };
const { currentContractState } = await contract.initialState(createConstructorContext(null, wallet));

for (const [isContract, byte, selfCredit] of [[true, 9, true], [true, 23, false], [false, 9, false]]) {
  const recipient = new Uint8Array(32).fill(byte);
  const { context } = await contract.circuits.transfer(createCircuitContext({
    circuitId: 'transfer', contractAddress: own, coinPublicKeyOrZswapState: wallet,
    contractState: currentContractState.data, privateState: null,
  }), color, 7n, isContract, recipient);
  const effects = context.callContext.currentQueryContext.effects;
  const target = { tag: isContract ? 'contract' : 'user', address: Buffer.from(recipient).toString('hex') };
  assert.deepEqual([...effects.unshieldedInputs], selfCredit ? [[token, 7n]] : []);
  assert.deepEqual([...effects.unshieldedOutputs], [[token, 7n]]);
  assert.deepEqual([...effects.claimedUnshieldedSpends], [[[token, target], 7n]]);
}
