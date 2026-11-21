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
  const contextFor = (contractState) => createCircuitContext({
    circuitId: 'tip',
    contractAddress: dummyContractAddress(),
    coinPublicKeyOrZswapState: walletKey,
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
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
