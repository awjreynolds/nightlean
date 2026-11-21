import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/list-head-maybe.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const version = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(version, /^0\.36\.1 \(7fa3a117c/, `expected pinned Compact 0.36.1 compiler, got ${version}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/ListHeadMaybe.compact');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'list-head-maybe-'));

try {
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtimeUrl = pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href;
  const contractUrl = pathToFileURL(join(generated, 'contract/index.js')).href;
  const {
    CompactTypeBoolean,
    CompactTypeUnsignedInteger,
    createCircuitContext,
    createConstructorContext,
    dummyContractAddress,
  } = await import(runtimeUrl);
  const { Contract } = await import(contractUrl);

  const contract = new Contract({});
  const uint8Descriptor = new CompactTypeUnsignedInteger(255n, 1);
  const maybeAlignment = CompactTypeBoolean.alignment().concat(uint8Descriptor.alignment());
  const encodeMaybe = (value) => CompactTypeBoolean.toValue(value.is_some)
    .concat(uint8Descriptor.toValue(value.value))
    .map((bytes) => Array.from(bytes));
  const walletKey = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(createConstructorContext(null, walletKey));
  const invoke = async (name, state, ...args) => {
    const context = createCircuitContext({
      circuitId: name,
      contractAddress: dummyContractAddress(),
      coinPublicKeyOrZswapState: walletKey,
      contractState: state,
      privateState: null,
    });
    const call = await contract.circuits[name](context, ...args);
    return [call.result, call.context.callContext.currentQueryContext.state];
  };

  const [empty, emptyState] = await invoke('head', currentContractState.data);
  assert.deepEqual(Object.keys(empty), ['is_some', 'value']);
  assert.equal(empty.is_some, false);
  assert.equal(empty.value, 0n);
  assert.deepEqual(encodeMaybe(empty), [[], []]);

  const [, populatedState] = await invoke('push', emptyState, 37n);
  const [oneElement] = await invoke('head', populatedState);
  assert.deepEqual(Object.keys(oneElement), ['is_some', 'value']);
  assert.equal(oneElement.is_some, true);
  assert.equal(oneElement.value, 37n);
  assert.deepEqual(encodeMaybe(oneElement), [[1], [37]]);

  console.log(JSON.stringify({
    alignment: maybeAlignment,
    empty: {is_some: empty.is_some, value: empty.value.toString(), encoding: encodeMaybe(empty)},
    oneElement: {is_some: oneElement.is_some, value: oneElement.value.toString(), encoding: encodeMaybe(oneElement)},
  }));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
