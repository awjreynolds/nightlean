import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/merge-coin-immediate.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/,
  `expected pinned Compact compiler, got ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(root, 'tests/compact/MergeCoinImmediate.compact');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'merge-coin-immediate-'));

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
  const contractAddress = dummyContractAddress();
  const contractAddressBytes = new Uint8Array(32);
  const { currentContractState } = await contract.initialState(createConstructorContext(null, walletKey));
  const contextFor = (state, circuitId) => createCircuitContext({
    circuitId,
    contractAddress,
    coinPublicKeyOrZswapState: walletKey,
    contractState: state,
    privateState: null,
  });

  const color = new Uint8Array(32).fill(0x41);
  const finalized = { color, nonce: new Uint8Array(32).fill(0x42), value: 5n };
  const seeded = await contract.circuits.seed(contextFor(currentContractState.data, 'seed'), finalized);
  const seedQuery = seeded.context.callContext.currentQueryContext;
  const seededZswap = seeded.context.callContext.currentZswapLocalState;
  assert.deepEqual(seededZswap.inputs, []);
  assert.equal(seededZswap.outputs.length, 1);
  assert.deepEqual(seededZswap.outputs[0].coinInfo, finalized);
  assert.deepEqual([...ledger(seedQuery.state).coins], [[color, { ...finalized, mt_index: 0n }]]);

  const incoming = { color, nonce: new Uint8Array(32).fill(0x43), value: 7n };
  const mergedCall = await contract.circuits.mergeEarlier(
    contextFor(seedQuery.state, 'mergeEarlier'), color, incoming,
  );
  const query = mergedCall.context.callContext.currentQueryContext;
  const zswap = mergedCall.context.callContext.currentZswapLocalState;
  const [finalizedInput, incomingInput] = zswap.inputs;
  const [bookedIncoming, mergedOutput] = zswap.outputs;

  assert.equal(zswap.currentIndex, 2n);
  assert.equal(zswap.inputs.length, 2);
  assert.equal(zswap.outputs.length, 2);
  assert.deepEqual(mergedCall.result.color, color);
  assert.equal(mergedCall.result.value, 12n);
  assert.equal(Buffer.from(mergedCall.result.nonce).toString('hex'),
    '008886c2deacb2bc58c16043752c6107ac13841d68ab515cf6d7ca9283255500');
  assert.deepEqual(mergedCall.result.nonce, mergedOutput.coinInfo.nonce);
  assert.deepEqual(finalizedInput, { ...finalized, mt_index: 0n });
  assert.deepEqual(incomingInput, { ...incoming, mt_index: 0n });
  assert.deepEqual(bookedIncoming.coinInfo, incoming);
  assert.deepEqual(mergedOutput.coinInfo, mergedCall.result);
  assert.equal(bookedIncoming.recipient.is_left, false);
  assert.equal(mergedOutput.recipient.is_left, false);
  assert.deepEqual(bookedIncoming.recipient.right.bytes, contractAddressBytes);
  assert.deepEqual(mergedOutput.recipient.right.bytes, contractAddressBytes);
  const sorted = (values) => [...values].sort();
  assert.deepEqual(sorted(query.effects.claimedShieldedReceives), [
    'dfb10c0f02bdda38262b6290bb6f612705f798c12143f36a73d17febdf2d1df2',
    '22c1d942576b35bea2e506169770fcc5932e05173d69470c57a70d4d4e125ef5',
  ].sort());
  assert.deepEqual(sorted(query.effects.claimedNullifiers), [
    '246570a69371f21f83a2da9aaf9f214198a29703c0721fb85de05888cc70b241',
    'ca83e7a3bd8c3a1d70258463efb2c83a44849adee2114324ccecdddc154d38ae',
  ].sort());
  assert.deepEqual(query.effects.claimedShieldedSpends, [
    '22c1d942576b35bea2e506169770fcc5932e05173d69470c57a70d4d4e125ef5',
  ]);
  assert.deepEqual([...ledger(query.state).coins], [[color, { ...mergedCall.result, mt_index: 1n }]]);

  console.log(JSON.stringify({
    fixture: 'merge-coin-immediate',
    returned: {
      color: Buffer.from(mergedCall.result.color).toString('hex'),
      value: mergedCall.result.value.toString(),
      nonce: Buffer.from(mergedCall.result.nonce).toString('hex'),
    },
    inputs: zswap.inputs.map(({ nonce, color: inputColor, value, mt_index }) => ({
      nonce: Buffer.from(nonce).toString('hex'),
      color: Buffer.from(inputColor).toString('hex'),
      value: value.toString(),
      mtIndex: mt_index.toString(),
    })),
    outputs: zswap.outputs.map(({ coinInfo, recipient }) => ({
      nonce: Buffer.from(coinInfo.nonce).toString('hex'),
      color: Buffer.from(coinInfo.color).toString('hex'),
      value: coinInfo.value.toString(),
      recipient: Buffer.from(recipient.right.bytes).toString('hex'),
    })),
    claimedReceives: sorted(query.effects.claimedShieldedReceives),
    claimedNullifiers: sorted(query.effects.claimedNullifiers),
    claimedSpends: query.effects.claimedShieldedSpends,
    finalizedInputAndIntraOperationBookedInput: true,
  }));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
