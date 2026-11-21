import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/jubjub-scalar-boundary.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const version = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(version, /^0\.36\.1 \(7fa3a117c/);
const packageJson = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(packageJson.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(root, 'tests/compact/JubjubScalarBoundary.compact');
const experiments = join(root, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'jubjub-scalar-boundary-'));
try {
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, compile.stderr || compile.stdout);
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  const { Contract } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const contract = new Contract({});
  const wallet = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(
    runtime.createConstructorContext(null, wallet),
  );
  const order = 6554484396890773809930967563523245729705921265872317281365359162392183254199n;
  const values = [7n, order + 7n];
  const expected = runtime.ecMulGenerator(7n);
  const results = [];
  for (const raw of values) {
    const context = runtime.createCircuitContext({
      circuitId: 'multiplyField', contractAddress: runtime.dummyContractAddress(),
      coinPublicKeyOrZswapState: wallet, contractState: currentContractState.data,
      privateState: null,
    });
    const { result } = await contract.circuits.multiplyField(context, raw);
    assert.deepEqual(result, expected, `Compact Field cast disagrees for ${raw}`);
    results.push({ raw: raw.toString(), x: result.x.toString(), y: result.y.toString() });
  }
  console.log(JSON.stringify({
    fixture: 'JubjubScalarBoundary.multiplyField', compact: version,
    cases: results, samePoint: true,
  }));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
