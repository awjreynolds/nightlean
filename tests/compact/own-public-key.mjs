import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdir, mkdtemp, rm, symlink } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/own-public-key.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const runtimeDirectory = resolve(runtimePath);
const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')));
assert.equal(runtime.versionString, '0.21.0');

const scratch = await mkdtemp(join(tmpdir(), 'noctium-own-public-key-'));
try {
  const generated = join(scratch, 'compact');
  const source = fileURLToPath(new URL('./OwnPublicKey.compact', import.meta.url));
  execFileSync(compactc, ['--skip-zk', source, generated]);
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  await mkdir(dirname(runtimeLink), { recursive: true });
  await symlink(runtimeDirectory, runtimeLink, 'dir');
  const { Contract } = await import(pathToFileURL(join(generated, 'contract/index.js')));
  const contract = new Contract({});
  const syntheticKey = Uint8Array.from({ length: 32 }, (_, index) => index + 1);
  const wallet = Buffer.from(syntheticKey).toString('hex');
  const { currentContractState } = await contract.initialState(runtime.createConstructorContext(null, wallet));
  const context = runtime.createCircuitContext({
    circuitId: 'exposeOwnPublicKey',
    contractAddress: runtime.dummyContractAddress(),
    coinPublicKeyOrZswapState: wallet,
    contractState: currentContractState.data,
    privateState: null,
  });
  const { result } = await contract.circuits.exposeOwnPublicKey(context);
  assert.deepEqual(result, syntheticKey);
  console.log(JSON.stringify({ fixture: 'own-public-key', output: Buffer.from(result).toString('hex') }));
} finally {
  await rm(scratch, { recursive: true, force: true });
}
