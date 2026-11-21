import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/opaque-cells.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const version = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(version, /^0\.36\.1 \(7fa3a117c/, `expected pinned Compact 0.36.1 compiler, got ${version}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/OpaqueCells.compact');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, '286-opaque-cells-'));

try {
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtimeUrl = pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href;
  const contractUrl = pathToFileURL(join(generated, 'contract/index.js')).href;
  const runtime = await import(runtimeUrl);
  const { Contract, ledger } = await import(contractUrl);
  const contract = new Contract({});
  const wallet = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(
    runtime.createConstructorContext(null, wallet),
  );
  const stateOf = (context) => context.callContext.currentQueryContext.state;
  const contextFor = (circuitId, contractState) => runtime.createCircuitContext({
    circuitId,
    contractAddress: runtime.dummyContractAddress(),
    coinPublicKeyOrZswapState: wallet,
    contractState,
    privateState: null,
  });

  const empty = ledger(currentContractState.data);
  assert.equal(empty.text, '');
  assert.deepEqual([...empty.bytes], []);

  const text = 'é\0λ';
  const bytes = Uint8Array.of(0x00, 0x01, 0xff);
  const write = await contract.circuits.write(
    contextFor('opaque-cell-write', currentContractState.data), text, bytes,
  );
  const updated = stateOf(write.context);
  assert.equal(ledger(updated).text, text);
  assert.deepEqual([...ledger(updated).bytes], [...bytes]);
  const compressAlignment = [{ tag: 'atom', value: { tag: 'compress' } }];
  const writeTrace = write.context.callProofDataTrace.at(-1);
  assert.deepEqual(writeTrace.input.value, [new TextEncoder().encode(text), bytes]);
  assert.deepEqual(writeTrace.input.alignment, [...compressAlignment, ...compressAlignment]);

  const stringRead = await contract.circuits.readText(contextFor('opaque-cell-read-text', updated));
  assert.equal(stringRead.result, text);
  const stringOutput = stringRead.context.callProofDataTrace.at(-1).output;
  assert.deepEqual(stringOutput.value, [new TextEncoder().encode(text)]);
  assert.deepEqual(stringOutput.alignment, compressAlignment);

  const bytesRead = await contract.circuits.readBytes(contextFor('opaque-cell-read-bytes', updated));
  assert.deepEqual([...bytesRead.result], [...bytes]);
  const bytesOutput = bytesRead.context.callProofDataTrace.at(-1).output;
  assert.deepEqual(bytesOutput.value, [bytes]);
  assert.deepEqual(bytesOutput.alignment, compressAlignment);

  const normalForm = /aligned value is not in normal form \(has trailing zero bytes\)/;
  await assert.rejects(
    () => contract.circuits.write(contextFor('opaque-cell-trailing-string', updated), 'é\0', bytes),
    normalForm,
  );
  await assert.rejects(
    () => contract.circuits.write(
      contextFor('opaque-cell-trailing-bytes', updated), text, Uint8Array.of(0x41, 0x00),
    ),
    normalForm,
  );
  assert.equal(ledger(updated).text, text);
  assert.deepEqual([...ledger(updated).bytes], [...bytes]);

  console.log('Compact 0.36.1 matched empty Opaque cells and Compress round trips for embedded-NUL UTF-8 and binary bytes');
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
