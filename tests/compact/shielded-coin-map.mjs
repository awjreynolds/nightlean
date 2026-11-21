import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/shielded-coin-map.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const version = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(version, /^0\.36\.1 \(7fa3a117c/, `expected pinned Compact 0.36.1 compiler, got ${version}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/ShieldedCoinMap.compact');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'shielded-coin-map-'));

try {
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtimeUrl = pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href;
  const contractUrl = pathToFileURL(join(generated, 'contract/index.js')).href;
  const { createCircuitContext, createConstructorContext, dummyContractAddress } = await import(runtimeUrl);
  const { Contract, ledger } = await import(contractUrl);
  const contract = new Contract({});
  const walletKey = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(createConstructorContext(null, walletKey));
  const contextFor = (contractState, circuitId = 'tip', zswapState = walletKey) => createCircuitContext({
    circuitId,
    contractAddress: dummyContractAddress(),
    coinPublicKeyOrZswapState: zswapState,
    contractState,
    privateState: null,
  });

  const coin = {
    color: new Uint8Array(32).fill(1),
    nonce: new Uint8Array(32).fill(2),
    value: 5n,
  };
  const storeOnlyContext = contextFor(currentContractState.data);
  await assert.rejects(
    contract.circuits.storeWithoutReceive(storeOnlyContext, coin),
    /Coin commitment not found\. Check the coin has been received/,
  );
  assert.deepEqual(storeOnlyContext.callContext.currentQueryContext.effects.claimedShieldedReceives, []);
  assert.deepEqual([...ledger(storeOnlyContext.callContext.currentQueryContext.state).pot], []);

  const { result, context } = await contract.circuits.tip(contextFor(currentContractState.data), coin);
  assert.deepEqual(result, []);

  const query = context.callContext.currentQueryContext;
  const effects = query.effects;
  assert.equal(effects.claimedShieldedReceives.length, 1);
  assert.deepEqual(effects.claimedShieldedSpends, []);

  const zswap = context.callContext.currentZswapLocalState;
  assert.equal(zswap.currentIndex, 1n);
  assert.deepEqual(zswap.inputs, []);
  assert.equal(zswap.outputs.length, 1);
  assert.deepEqual(zswap.outputs[0].coinInfo, coin);
  assert.equal(zswap.outputs[0].recipient.is_left, false);
  assert.deepEqual(zswap.outputs[0].recipient.right.bytes, new Uint8Array(32));

  assert.deepEqual([...ledger(query.state).pot], [[coin.nonce, {
    nonce: coin.nonce,
    color: coin.color,
    value: coin.value,
    mt_index: 0n,
  }]]);

  const replayContext = contextFor(query.state);
  await assert.rejects(contract.circuits.tip(replayContext, coin), /coin nonce already received/);
  assert.deepEqual(replayContext.callContext.currentQueryContext.effects.claimedShieldedReceives, []);
  console.log('Shielded coin map: missing-output rejection, receive effect, self-directed output, mt_index qualification, and duplicate rejection matched');

  const recipient = { bytes: new Uint8Array(32).fill(3) };
  const { context: spent } = await contract.circuits.withdraw(
    contextFor(query.state, 'withdraw'), coin.nonce, recipient,
  );
  const afterSpend = spent.callContext.currentQueryContext;
  const transfer = spent.callContext.currentZswapLocalState;
  assert.deepEqual([...ledger(afterSpend.state).pot], []);
  assert.equal(transfer.inputs.length, 1);
  assert.equal(transfer.outputs.length, 1);
  assert.deepEqual(afterSpend.effects.claimedNullifiers, [
    'd119520f9cd70fb3b835e7421773629b1991e38d642ff9b6b69eb9ed1bf86c24',
  ]);
  assert.deepEqual(afterSpend.effects.claimedShieldedSpends, [
    '800f1c60e2b9e9da8e987cc2d31713904daa9920005e1490aeab9366f24eb149',
  ]);
  assert.deepEqual(afterSpend.effects.claimedShieldedReceives, []);
  const [output] = transfer.outputs;
  assert.deepEqual(output.coinInfo.color, coin.color);
  assert.equal(output.coinInfo.value, coin.value);
  assert.equal(Buffer.from(output.coinInfo.nonce).toString('hex'),
    '92411b27a7fe195f0f94f46bab957487031cb2702b4e6015adebe924fe246500');
  assert.equal(output.recipient.is_left, true);
  assert.deepEqual(output.recipient.left, recipient);
  await assert.rejects(
    contract.circuits.withdraw(contextFor(afterSpend.state, 'withdraw'), coin.nonce, recipient),
    /coin nonce missing/,
  );
  console.log('Shielded whole-coin spend: exact claims, recipient output, Map removal, and replay rejection matched');

  const split = await contract.circuits.withdrawPartial(
    contextFor(query.state, 'withdrawPartial'), coin.nonce, recipient, 2n,
  );
  const splitQuery = split.context.callContext.currentQueryContext;
  const splitOffer = split.context.callContext.currentZswapLocalState;
  const [recipientOutput, changeOutput] = splitOffer.outputs;
  assert.equal(splitOffer.inputs.length, 1);
  assert.equal(splitOffer.outputs.length, 2);
  assert.equal(splitOffer.currentIndex, 2n);
  assert.deepEqual(splitQuery.effects.claimedNullifiers, afterSpend.effects.claimedNullifiers);
  const changeCommitment = 'ac1f3bb1ec93068af7810556a541cd2fbd3eb3e8e1c4336a7e5a72ee403405c2';
  assert.deepEqual(splitQuery.effects.claimedShieldedSpends, [
    'ed1aadafa7d1883bc63e45853fc4b51f21fb99c6ae68c8de9a256cbc3ac299c7',
    changeCommitment,
  ]);
  assert.deepEqual(splitQuery.effects.claimedShieldedReceives, [changeCommitment]);
  assert.equal(recipientOutput.coinInfo.value, 2n);
  assert.deepEqual(recipientOutput.coinInfo.color, coin.color);
  assert.deepEqual(recipientOutput.coinInfo.nonce, output.coinInfo.nonce);
  assert.equal(recipientOutput.recipient.is_left, true);
  assert.deepEqual(recipientOutput.recipient.left, recipient);
  assert.equal(changeOutput.coinInfo.value, 3n);
  assert.deepEqual(changeOutput.coinInfo.color, coin.color);
  assert.equal(Buffer.from(changeOutput.coinInfo.nonce).toString('hex'),
    '0283a70d7732a940d63ebf3957495f2549236d165e604aa67a59d7eb746f4b00');
  assert.equal(changeOutput.recipient.is_left, false);
  assert.deepEqual(changeOutput.recipient.right.bytes, new Uint8Array(32));
  assert.deepEqual([...ledger(splitQuery.state).pot], [[changeOutput.coinInfo.nonce, {
    ...changeOutput.coinInfo,
    mt_index: 1n,
  }]]);
  await assert.rejects(
    contract.circuits.withdrawPartial(
      contextFor(splitQuery.state, 'withdrawPartial'), coin.nonce, recipient, 2n,
    ),
    /coin nonce missing/,
  );
  for (const amount of [0n, 5n, 6n]) {
    await assert.rejects(
      contract.circuits.withdrawPartial(
        contextFor(query.state, 'withdrawPartial'), coin.nonce, recipient, amount,
      ),
      /partial send must leave change/,
    );
  }
  console.log('Shielded partial spend: exact claims, 2+3 outputs, qualified change Map row, amount bounds, and replay rejection matched');

  const second = { ...coin, nonce: new Uint8Array(32).fill(7), value: 7n };
  const seedSecond = async (value) => {
    const { context: seeded } = await contract.circuits.tip(contextFor(query.state, 'tip', {
      coinPublicKey: walletKey, currentIndex: 1n, inputs: [], outputs: [],
    }), value);
    return seeded.callContext.currentQueryContext.state;
  };
  const mergeFrom = (state, firstNonce = coin.nonce, secondNonce = second.nonce) =>
    contract.circuits.mergeFinalized(contextFor(state, 'mergeFinalized', {
      coinPublicKey: walletKey, currentIndex: 2n, inputs: [], outputs: [],
    }), firstNonce, secondNonce);
  const mergeInputState = await seedSecond(second);
  const { context: merged } = await mergeFrom(mergeInputState);
  const mergeQuery = merged.callContext.currentQueryContext;
  const mergeOffer = merged.callContext.currentZswapLocalState;
  assert.deepEqual(mergeOffer.inputs, [{ ...coin, mt_index: 0n }, { ...second, mt_index: 1n }]);
  assert.equal(mergeOffer.outputs.length, 1);
  const [mergedOutput] = mergeOffer.outputs;
  assert.deepEqual(mergedOutput.coinInfo, { ...coin, nonce: output.coinInfo.nonce, value: 12n });
  assert.equal(mergedOutput.recipient.is_left, false);
  assert.deepEqual(mergedOutput.recipient.right.bytes, new Uint8Array(32));
  assert.deepEqual([...ledger(mergeQuery.state).pot], [[mergedOutput.coinInfo.nonce, {
    ...mergedOutput.coinInfo, mt_index: 2n,
  }]]);
  const mergeEffects = mergeQuery.effects;
  const outputCommitment = '54e30984c10454b1dd9077e45a0fadf79074373d4de8d5e58cca795864b6c9e5';
  const nullifiers = [...mergeEffects.claimedNullifiers].sort();
  assert.deepEqual(mergeEffects.claimedShieldedReceives, [outputCommitment]);
  assert.deepEqual(mergeEffects.claimedShieldedSpends, mergeEffects.claimedShieldedReceives);
  assert.deepEqual(nullifiers, [
    'c37e0e4fcb94a95c0ecb7e49b0c797f80e52c12cb0cd39c1ed2924749b1e3f08',
    afterSpend.effects.claimedNullifiers[0],
  ]);
  await assert.rejects(mergeFrom(mergeInputState, coin.nonce, coin.nonce), /merge inputs must be distinct/);
  await assert.rejects(mergeFrom(mergeQuery.state), /merge input missing/);
  await assert.rejects(mergeFrom(await seedSecond({ ...second, color: new Uint8Array(32).fill(8) })),
    /Can only merge coins of the same color/);
  // The pinned JS booking codec limits the output amount to UInt64 even though the source field is UInt128.
  await assert.rejects(mergeFrom(await seedSecond({ ...second, value: (1n << 64n) - 1n })),
    /expected UnsignedInteger\[<=18446744073709551615\]/);
  console.log(JSON.stringify({
    fixture: 'merge-finalized',
    nonce: Buffer.from(mergedOutput.coinInfo.nonce).toString('hex'),
    value: mergedOutput.coinInfo.value.toString(),
    outputCommitment,
    nullifiers,
  }));

  const destination = { bytes: new Uint8Array(32).fill(4) };
  const selector = new Uint8Array(32).fill(5);
  const { context: relayed } = await contract.circuits.relayImmediate(
    contextFor(currentContractState.data, 'relayImmediate'),
    coin,
    destination,
    selector,
    7n,
  );
  const relayQuery = relayed.callContext.currentQueryContext;
  const relayOffer = relayed.callContext.currentZswapLocalState;
  assert.deepEqual(relayQuery.effects.claimedShieldedReceives, [
    '84a93c4d7971bb71252e9b01a8cc75f4daffdcac90c25c3d3ea484a1b6eae3a0',
  ]);
  assert.deepEqual(relayQuery.effects.claimedShieldedSpends, [
    '142498ccc64b0b945dbabf4804b879f555b3e1eefe9251b9d6e4abaad1ca5a0b',
  ]);
  assert.deepEqual(relayQuery.effects.claimedNullifiers, afterSpend.effects.claimedNullifiers);
  const [call] = relayQuery.effects.claimedContractCalls;
  assert.equal(relayQuery.effects.claimedContractCalls.length, 1);
  assert.deepEqual(call.slice(0, 3), [0n, '04'.repeat(32), '05'.repeat(32)]);
  assert.equal(Buffer.from(call[3]).toString('hex'),
    '732e3d03df361e56dbd2b33ff35904092faafe3124f3c1e7cd36b3ac4c9f56f242');
  assert.deepEqual(relayOffer.inputs, [{ ...coin, mt_index: 0n }]);
  assert.equal(relayOffer.outputs.length, 2);
  const [selfOutput, destinationOutput] = relayOffer.outputs;
  assert.deepEqual(selfOutput.coinInfo, coin);
  assert.equal(selfOutput.recipient.is_left, false);
  assert.deepEqual(selfOutput.recipient.right.bytes, new Uint8Array(32));
  assert.deepEqual(destinationOutput.coinInfo, { ...coin, nonce: output.coinInfo.nonce });
  assert.equal(destinationOutput.recipient.is_left, false);
  assert.deepEqual(destinationOutput.recipient.right, destination);
  assert.deepEqual([...ledger(relayQuery.state).pot], []);
  console.log('Immediate shielded relay: exact claims, transient pairing, and full-value destination output matched');
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
