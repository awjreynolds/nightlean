import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/opaque-bytes.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const version = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(version, /^0\.36\.1 \(7fa3a117c/, `expected pinned Compact 0.36.1 compiler, got ${version}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/OpaqueBytes.compact');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, '235-opaque-bytes-'));

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
  const opaqueType = runtime.CompactTypeOpaqueUint8Array;
  const opaqueAlignment = [{ tag: 'atom', value: { tag: 'compress' } }];
  assert.deepEqual(opaqueType.alignment(), opaqueAlignment);
  const contract = new Contract({});
  const walletKey = '00'.repeat(32);
  const { currentContractState } = await contract.initialState(runtime.createConstructorContext(null, walletKey));
  const contextFor = (contractState, circuitId) => runtime.createCircuitContext({
    circuitId,
    contractAddress: runtime.dummyContractAddress(),
    coinPublicKeyOrZswapState: walletKey,
    contractState,
    privateState: null,
  });

  const examples = [
    { key: new Uint8Array(32).fill(1), payload: new Uint8Array(), name: 'empty' },
    { key: new Uint8Array(32).fill(2), payload: Uint8Array.of(0x00, 0x01, 0xff), name: 'binary' },
    { key: new Uint8Array(32).fill(3), payload: Uint8Array.of(0x4e, 0x6f, 0x63, 0x74, 0x69, 0x75, 0x6d), name: 'text bytes' },
  ];
  let state = currentContractState.data;
  const rows = [];
  for (const [index, example] of examples.entries()) {
    const stored = await contract.circuits.store(
      contextFor(state, `opaque-store-${index}`), example.key, example.payload,
    );
    state = stored.context.callContext.currentQueryContext.state;
    assert.deepEqual(ledger(state).payloads.lookup(example.key), example.payload);

    const trace = stored.context.callProofDataTrace.at(-1);
    assert.deepEqual(trace.input.value, [example.key, example.payload]);
    assert.deepEqual(trace.input.alignment, [
      { tag: 'atom', value: { tag: 'bytes', length: 32 } },
      ...opaqueAlignment,
    ]);
    assert.deepEqual(opaqueType.toValue(example.payload), [example.payload]);
    assert.throws(
      () => runtime.toBinaryRepr(opaqueType, example.payload),
      /cannot convert JS opaque values in toBinaryRepr/,
    );

    const read = await contract.circuits.read(contextFor(state, `opaque-read-${index}`), example.key);
    assert.deepEqual(read.result, example.payload);
    const readTrace = read.context.callProofDataTrace.at(-1);
    assert.deepEqual(readTrace.output.value, [example.payload]);
    assert.deepEqual(readTrace.output.alignment, opaqueAlignment);

    rows.push({
      name: example.name,
      hostBytesHex: Buffer.from(example.payload).toString('hex'),
      valueBytesHex: Buffer.from(trace.input.value[1]).toString('hex'),
      inputAlignment: trace.input.alignment[1],
      readBytesHex: Buffer.from(read.result).toString('hex'),
      outputAlignment: readTrace.output.alignment[0],
    });
  }

  const trailingZeroKey = new Uint8Array(32).fill(4);
  const trailingZeroPayload = Uint8Array.of(0x41, 0x00);
  assert.deepEqual(opaqueType.toValue(trailingZeroPayload), [trailingZeroPayload]);
  const rejectedContext = contextFor(state, 'opaque-trailing-zero');
  await assert.rejects(
    contract.circuits.store(rejectedContext, trailingZeroKey, trailingZeroPayload),
    /aligned value is not in normal form \(has trailing zero bytes\)/,
  );
  assert.equal(ledger(state).payloads.member(trailingZeroKey), false);
  assert.deepEqual(rejectedContext.callProofDataTrace, []);

  const info = JSON.parse(readFileSync(join(generated, 'compiler/contract-info.json'), 'utf8'));
  assert.deepEqual(info.ledger[0].value, { 'type-name': 'Opaque', tsType: 'Uint8Array' });
  const declarations = readFileSync(join(generated, 'contract/index.d.ts'), 'utf8');
  assert.match(declarations, /store\(context: [^,]+,\s*key_0: Uint8Array,\s*payload_0: Uint8Array\)/);
  assert.match(declarations, /read\(context: [^,]+,\s*key_0: Uint8Array\): Promise<[^>]*Uint8Array/);
  assert.match(declarations, /lookup\(key_0: Uint8Array\): Uint8Array/);
  const storeZkir = JSON.parse(readFileSync(join(generated, 'zkir/store.zkir'), 'utf8'));
  const readZkir = JSON.parse(readFileSync(join(generated, 'zkir/read.zkir'), 'utf8'));
  const storeImpact = storeZkir.instructions.filter(({ op }) => op === 'impact');
  const readImpact = readZkir.instructions.filter(({ op }) => op === 'impact');
  assert.deepEqual(storeZkir.inputs.at(-1), { name: '%payload.2', type: 'Scalar<BLS12-381>' });
  assert.deepEqual(readZkir.outputs, ['Scalar<BLS12-381>']);
  assert.deepEqual(storeImpact, [
    { op: 'impact', guard: '0x01', inputs: ['0x70', '0x01', '0x01', '0x00'] },
    { op: 'impact', guard: '0x01', inputs: ['0x10', '0x01', '0x01', '0x20', '%key.0', '%key.1'] },
    { op: 'impact', guard: '0x01', inputs: ['0x11', '0x01', '0x01', '-0x01', '%payload.2'] },
    { op: 'impact', guard: '0x01', inputs: ['0x91'] },
    { op: 'impact', guard: '0x01', inputs: ['0xa1'] },
  ]);
  assert.deepEqual(readImpact, [
    { op: 'impact', guard: '0x01', inputs: ['0x30'] },
    { op: 'impact', guard: '0x01', inputs: ['0x50', '0x01', '0x01', '0x00'] },
    { op: 'impact', guard: '0x01', inputs: ['0x50', '0x01', '0x20', '%key.0', '%key.1'] },
    { op: 'impact', guard: '0x01', inputs: ['0x0c', '0x01', '-0x01', '%t.2'] },
  ]);

  console.log(JSON.stringify({
    compiler: version,
    runtime: `${runtimePackage.name}@${runtimePackage.version}`,
    hostAbi: 'store(key: Uint8Array, payload: Uint8Array), read(key: Uint8Array): Uint8Array, Map.lookup(key: Uint8Array): Uint8Array',
    alignment: opaqueAlignment,
    rawValues: rows,
    nonCanonicalValue: {
      bytesHex: Buffer.from(trailingZeroPayload).toString('hex'),
      result: 'rejected before proof trace or ledger write because Compress values cannot end in zero',
    },
    storeInput: storeZkir.inputs.at(-1),
    storeImpact,
    readOutput: readZkir.outputs,
    readImpact,
    nativeProjection: {
      source: 'midnight-ledger a2b3012 transient-crypto/src/fab.rs:486-495',
      formula: 'empty bytes -> field 0; otherwise transient_commit(raw bytes, Fr(byte length))',
      circuitDecoder: 'midnight-zkir 7a51b33 zkir/src/ir_vm.rs:217 rejects compressed field-to-raw decoding',
    },
    fabBinaryEncoding: 'not emitted; toBinaryRepr rejects compress atoms',
  }, null, 2));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
