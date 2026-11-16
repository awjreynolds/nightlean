// Native checker/prover qualification for the typed helper and direct relation.
import assert from 'node:assert/strict';
import {readFile, writeFile} from 'node:fs/promises';
import {join, resolve, dirname} from 'node:path';
import {pathToFileURL} from 'node:url';
import {createHash} from 'node:crypto';
import {createProvingPayload} from '../../scripts/zkir/node_modules/@midnight-ntwrk/ledger-v9/midnight_ledger_wasm_v9_fs.js';

const [directory, checkerPath, mode = 'check'] = process.argv.slice(2);
if (!directory || !checkerPath || !['check', 'prove'].includes(mode))
  throw Error('Usage: node tests/helpers/qualify.mjs DIRECTORY PINNED_CHECKER_MODULE check|prove');
const digest = bytes => createHash('sha256').update(bytes).digest('hex');
const checkerDirectory = dirname(resolve(checkerPath));
const checkerPackage = JSON.parse(await readFile(join(checkerDirectory, 'package.json'), 'utf8'));
assert.equal(checkerPackage.name, '@midnightntwrk/zkir-v3');
assert.equal(checkerPackage.version, '3.2.1');
const checkerWasmSha256 = digest(await readFile(join(checkerDirectory, 'midnight_zkir_wasm_bg.wasm')));
assert.equal(checkerWasmSha256, '3568fafaf225469dbbd038b0236d1b6b76e0da19da565caba33efe2ceb682cfc');
const {Zkir, check} = await import(pathToFileURL(resolve(checkerPath)).href);

function scaleNatural(value) {
  const n = BigInt(value);
  assert.ok(n >= 0n && n < 1073741824n);
  const count = n < 64n ? 1 : n < 16384n ? 2 : 4;
  let encoded = (n << 2n) | BigInt(count === 1 ? 0 : count === 2 ? 1 : 2);
  return Buffer.from(Array.from({length: count}, () => {
    const byte = Number(encoded & 255n);
    encoded >>= 8n;
    return byte;
  }));
}
const vector = values => Buffer.concat([scaleNatural(values.length), ...values.map(scaleNatural)]);
function preimage({expected, secret, output}) {
  const location = Buffer.from('nightlean/helpers/qualification');
  return Buffer.concat([Buffer.from('midnight:proof-preimage:'), vector([]), vector([secret]),
    vector([expected, output]), vector([expected]), scaleNatural(42), Buffer.from([0]),
    scaleNatural(location.length), location]);
}

const cases = [
  {id: 'FN-NATIVE-VALID', expected: 49, secret: 7, output: 49, accepted: true},
  {id: 'FN-NATIVE-ZERO', expected: 0, secret: 0, output: 0, accepted: true},
  {id: 'FN-NATIVE-WRONG-SECRET', expected: 49, secret: 8, output: 49, accepted: false},
  {id: 'FN-NATIVE-WRONG-PUBLIC', expected: 50, secret: 7, output: 50, accepted: false},
  {id: 'FN-NATIVE-WRONG-OUTPUT', expected: 49, secret: 7, output: 50, accepted: false},
];
const evidence = {scope: 'scalar typed helpers and direct relation; no general compiler preservation or ledger claim',
  nativeVersion: checkerPackage.version, checkerWasmSha256, relations: []};
let directBytes;
for (const name of ['helperDirect', 'helperComposed']) {
  const source = await readFile(join(directory, `${name}.zkir`));
  const relation = Zkir.fromJson(source.toString());
  const ir = relation.serialize();
  if (directBytes) assert.deepEqual(ir, directBytes, 'helper and direct native relations differ');
  else directBytes = ir;
  const material = {ir, proverKey: new Uint8Array(), verifierKey: new Uint8Array()};
  if (mode === 'prove') {
    material.proverKey = await readFile(join(directory, `${name}.prover`));
    material.verifierKey = await readFile(join(directory, `${name}.verifier`));
  }
  const results = [];
  for (const test of cases) {
    let accepted = true;
    let activity;
    try {
      activity = await check(preimage(test), {lookupKey: async () => material});
    } catch { accepted = false; }
    assert.equal(accepted, test.accepted, `${name}/${test.id}`);
    if (accepted) assert.equal(activity.length, 2);
    results.push({id: test.id, accepted});
  }
  const record = {name, k: relation.getK(), sourceSha256: digest(source), binarySha256: digest(ir), cases: results};
  if (mode === 'prove') {
    const server = new URL(process.env.NIGHTLEAN_PROOF_SERVER ?? 'http://127.0.0.1:16300');
    assert.ok(['http:', 'https:'].includes(server.protocol) &&
      ['127.0.0.1', 'localhost', '[::1]'].includes(server.hostname) && !server.username && !server.password);
    const response = await fetch(new URL('/prove', server), {method: 'POST',
      body: createProvingPayload(preimage(cases[0]), 42n, material), redirect: 'error',
      signal: AbortSignal.timeout(120000)});
    // These vectors contain published synthetic values only.
    if (!response.ok) throw Error(`${name}: native prover HTTP ${response.status}: ${(await response.text()).slice(0, 2048)}`);
    const proof = Buffer.from(await response.arrayBuffer());
    assert.ok(proof.length > 0 && proof.length <= 1048576);
    await writeFile(join(directory, `${name}.proof`), proof, {mode: 0o600});
    record.proof = {bytes: proof.length, sha256: digest(proof), nativeServerSelfVerified: true};
  }
  evidence.relations.push(record);
}
evidence.identicalNativeRelations = true;
await writeFile(join(directory, `helper-${mode}-evidence.json`), JSON.stringify(evidence, null, 2) + '\n');
console.log(JSON.stringify(evidence, null, 2));
