import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/receive-unshielded.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/, `unexpected Compact compiler: ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(root, 'tests/compact/ReceiveUnshielded.compact');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'receive-unshielded-'));

try {
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  const { Contract } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const contract = new Contract({});
  const wallet = '00'.repeat(32);
  const color = Uint8Array.from({ length: 32 }, (_, index) => index + 1);
  const token = { tag: 'unshielded', raw: Buffer.from(color).toString('hex') };
  const { currentContractState } = await contract.initialState(
    runtime.createConstructorContext(null, wallet),
  );

  async function run(circuitId, enabled) {
    const context = runtime.createCircuitContext({
      circuitId, contractAddress: '09'.repeat(32), coinPublicKeyOrZswapState: wallet,
      contractState: currentContractState.data, privateState: null,
    });
    const vm = context.callContext.currentQueryContext;
    vm.block = { ...vm.block, balance: new Map([[token, 42n]]) };
    const { context: after } = await contract.circuits[circuitId](context, color, 7n, enabled);
    const effects = after.callContext.currentQueryContext.effects;
    assert.deepEqual([...effects.unshieldedOutputs], []);
    assert.deepEqual([...effects.claimedUnshieldedSpends], []);
    return [...effects.unshieldedInputs];
  }

  for (const enabled of [true, false]) {
    const expected = enabled ? [[token, 7n]] : [];
    const helper = await run('receiveHelper', enabled);
    const primitive = await run('primitive', enabled);
    assert.deepEqual(helper, expected);
    assert.deepEqual(helper, primitive);
  }
  console.log('Compact 0.36.1 receiveUnshielded matched the explicit unshielded-input primitive for active and inactive calls');
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
