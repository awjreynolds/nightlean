import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/mixed-fab-persistent-hash.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/, `unexpected Compact compiler: ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, '271-mixed-fab-persistent-hash-'));

try {
  const generated = join(scratch, 'compact');
  const source = join(projectRoot, 'tests/compact/MerklePathRootNoLeafHash.compact');
  execFileSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href);
  assert.equal(runtime.versionString, '0.21.0');
  const { Contract } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);
  const contract = new Contract({});
  const walletKey = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(
    runtime.createConstructorContext(null, walletKey),
  );

  const octets = Uint8Array.from({ length: 32 }, (_, index) => index + 1);
  const payloads = [257n, 258n].map((counter) => ({
    octets,
    flag: true,
    counter,
    marker: 0,
    anchor: 42n,
  }));
  const opening = new Uint8Array(32).fill(9);
  const nonce = 77n;
  const persistentHashes = [];
  for (const payload of payloads) {
    const context = runtime.createCircuitContext({
      circuitId: 'fabHashes',
      contractAddress: runtime.dummyContractAddress(),
      coinPublicKeyOrZswapState: walletKey,
      contractState: currentContractState.data,
      privateState: null,
    });
    const call = await contract.circuits.fabHashes(context, payload, opening, nonce);
    assert.ok(Array.isArray(call.result) && call.result.length === 4, 'expected four FAB hash outputs');
    persistentHashes.push(Buffer.from(call.result[0]).toString('hex'));
  }

  assert.deepEqual(persistentHashes, [
    '05743c725c44c8d77bf1b9601385ef901ec4040ecb770014a535ddcb5e2840d9',
    '4376a00dd2129c85219a8aecd9a8209cad4fdc8d333ed7e127f71220697490c2',
  ]);
  assert.notEqual(persistentHashes[0], persistentHashes[1],
    'persistentHash must bind the changed UInt16 field');
  console.log(JSON.stringify({
    compiler: compilerVersion,
    runtime: runtime.versionString,
    circuit: 'fabHashes',
    layout: ['Bytes<32>', 'Boolean', 'Uint<16>', 'LeafMarker', 'Field'],
    inputs: payloads.map(({ counter }) => ({ counter: counter.toString() })),
    persistentHashes,
  }));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
