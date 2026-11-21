import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/kernel-context.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/, `unexpected Compact compiler: ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(projectRoot, 'build/experiments/330');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'compact-kernel-context-'));

try {
  const generated = join(scratch, 'compact');
  execFileSync(compactc, [
    '--skip-zk', join(projectRoot, 'tests/compact/KernelContext.compact'), generated,
  ], { encoding: 'utf8' });
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  assert.equal(runtime.versionString, '0.21.0');
  const { Contract } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const contract = new Contract({});
  const wallet = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(
    runtime.createConstructorContext(null, wallet),
  );
  const self = Uint8Array.from({ length: 32 }, (_, index) => index + 1);
  const caller = new Uint8Array(32).fill(99);
  const color = Uint8Array.from({ length: 32 }, (_, index) => index + 1);
  const colorHex = Buffer.from(color).toString('hex');
  const selfHex = Buffer.from(self).toString('hex');
  const callerHex = Buffer.from(caller).toString('hex');
  const zero = new Uint8Array(32);

  function context(enabled, callerTag, unshielded, shielded) {
    const value = runtime.createCircuitContext({
      circuitId: 'inspect',
      contractAddress: selfHex,
      coinPublicKeyOrZswapState: wallet,
      contractState: currentContractState.data,
      privateState: null,
    });
    const vm = value.callContext.currentQueryContext;
    const balance = new Map();
    if (unshielded !== null) balance.set({ tag: 'unshielded', raw: colorHex }, unshielded);
    if (shielded !== null) balance.set({ tag: 'shielded', raw: colorHex }, shielded);
    vm.block = {
      ...vm.block,
      balance,
      ...(callerTag ? { caller: { tag: callerTag, address: callerHex } } : {}),
    };
    return value;
  }

  const check = async (enabled, callerTag, isUnshielded, balances, expected) => {
    const { result } = await contract.circuits.inspect(
      context(enabled, callerTag, balances[0], balances[1]),
      enabled, color, isUnshielded,
    );
    assert.deepEqual(result, expected);
  };

  await check(true, 'contract', true, [17n, 23n], [
    self, true, true, caller, zero, 17n,
  ]);
  await check(true, 'user', false, [17n, 23n], [
    self, true, false, zero, caller, 23n,
  ]);
  await check(true, undefined, true, [17n, 23n], [
    self, false, false, zero, zero, 17n,
  ]);
  await check(false, 'contract', true, [17n, 23n], [
    zero, false, false, zero, zero, 0n,
  ]);
  console.log('Compact kernel context matched self, caller variants, guard, and tagged starting balance');
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
