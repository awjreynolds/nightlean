import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/scalar-either-returns.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const version = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(version, /^0\.36\.1 \(7fa3a117c/, `expected pinned Compact 0.36.1 compiler, got ${version}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/ScalarEitherReturns.compact');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'scalar-either-returns-'));

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
  const { Contract } = await import(contractUrl);
  const contract = new Contract({});
  const walletKey = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(createConstructorContext(null, walletKey));

  const invoke = async (isLeft, leftValue, rightValue) => {
    const context = createCircuitContext({
      circuitId: 'canonicalize',
      contractAddress: dummyContractAddress(),
      coinPublicKeyOrZswapState: walletKey,
      contractState: currentContractState.data,
      privateState: null,
    });
    return contract.circuits.canonicalize(context, isLeft, leftValue, rightValue).then((call) => call.result);
  };

  for (const [isLeft, leftValue, rightValue, expected] of [
    [true, 37n, 513n, { is_left: true, left: 37n, right: 0n }],
    [false, 37n, 513n, { is_left: false, left: 0n, right: 513n }],
  ]) {
    const result = await invoke(isLeft, leftValue, rightValue);
    assert.deepEqual(Object.keys(result), ['is_left', 'left', 'right']);
    assert.deepEqual(result, expected);
  }

  console.log(JSON.stringify({
    left: { is_left: true, left: '37', right: '0' },
    right: { is_left: false, left: '0', right: '513' },
  }));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
