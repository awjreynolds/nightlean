// Qualify the compiler-emitted component/helper relation with the pinned native checker and prover.
import assert from 'node:assert/strict';
import {readFile, writeFile} from 'node:fs/promises';
import {join, resolve, dirname} from 'node:path';
import {pathToFileURL} from 'node:url';
import {createHash} from 'node:crypto';
import {createProvingPayload} from '../../scripts/zkir/node_modules/@midnight-ntwrk/ledger-v9/midnight_ledger_wasm_v9_fs.js';

const [directory, checkerPath, proverPath, verifierPath, mode = 'check'] = process.argv.slice(2);
if (!directory || !checkerPath || !proverPath || !verifierPath || !['check', 'prove'].includes(mode))
  throw Error('Usage: node tests/component-disclosure/qualify.mjs ARTIFACTS PINNED_CHECKER PROVER_KEY VERIFIER_KEY check|prove');
const digest = bytes => createHash('sha256').update(bytes).digest('hex');
const checkerDirectory = dirname(resolve(checkerPath));
const checkerPackage = JSON.parse(await readFile(join(checkerDirectory, 'package.json'), 'utf8'));
assert.equal(checkerPackage.name, '@midnightntwrk/zkir-v3');
assert.equal(checkerPackage.version, '3.2.1');
assert.equal(digest(await readFile(checkerPath)), 'a4ec641776c45bd06fe033f25b8d74fccca7900d5e97cc360468ddeacfa2424c');
assert.equal(digest(await readFile(join(checkerDirectory, 'midnight_zkir_wasm_bg.wasm'))),
  '3568fafaf225469dbbd038b0236d1b6b76e0da19da565caba33efe2ceb682cfc');
const {Zkir, check} = await import(pathToFileURL(resolve(checkerPath)).href);

function compact(value) {
  let n = BigInt(value);
  assert.ok(n >= 0n && n < 52435875175126190479447740508185965837690552500527637822603658699938581184513n);
  const bytes = (number, count) => Buffer.from(Array.from({length: count}, () => {
    const byte = Number(number & 255n);
    number >>= 8n;
    return byte;
  }));
  if (n < 64n) return bytes(n << 2n, 1);
  if (n < 16384n) return bytes((n << 2n) | 1n, 2);
  if (n < 1073741824n) return bytes((n << 2n) | 2n, 4);
  const encoded = [];
  while (n) { encoded.push(Number(n & 255n)); n >>= 8n; }
  return Buffer.from([((encoded.length - 4) << 2) | 3, ...encoded]);
}
const vector = values => Buffer.concat([compact(values.length), ...values.map(compact)]);
function preimage(privateInputs, publicOutputs) {
  const location = Buffer.from('nightlean/component-disclosure/qualification');
  return Buffer.concat([Buffer.from('midnight:proof-preimage:'), vector([]), vector(privateInputs),
    vector(publicOutputs), vector([]), compact(42), Buffer.from([0]), compact(location.length), location]);
}

const source = await readFile(join(directory, 'componentRelease.zkir'));
const relation = Zkir.fromJson(source.toString());
const material = {ir: relation.serialize(), proverKey: new Uint8Array(), verifierKey: new Uint8Array()};
if (mode === 'prove') {
  material.proverKey = await readFile(proverPath);
  material.verifierKey = await readFile(verifierPath);
}
const privateInputs = ['9', '11', '13']; // payload.balance, payload.nonce, provider witness
const publicOutputs = ['9', '13']; // result.balance and result.nonce
const accepted = await check(preimage(privateInputs, publicOutputs), {lookupKey: async () => material});
assert.equal(accepted.length, 1);
await assert.rejects(() => check(preimage(privateInputs, ['10', '13']), {lookupKey: async () => material}));
await assert.rejects(() => check(preimage(privateInputs, ['9', '14']), {lookupKey: async () => material}));
await assert.rejects(() => check(preimage(['9', '11', '14'], publicOutputs), {lookupKey: async () => material}));

const evidence = {
  scope: 'compiler-generated disclosed composite result through a source helper and provider input; no ledger acceptance',
  nativeChecker: checkerPackage.version,
  checkerGlueSha256: digest(await readFile(checkerPath)),
  relationK: relation.getK(),
  relationSha256: digest(relation.serialize()),
  checkerAccepted: true,
  tamperedPublicOutputRejected: true,
  changedProviderWitnessRejected: true
};
if (mode === 'prove') {
  const server = new URL(process.env.NIGHTLEAN_PROOF_SERVER ?? 'http://127.0.0.1:16300');
  assert.ok(['http:', 'https:'].includes(server.protocol) &&
    ['127.0.0.1', 'localhost', '[::1]'].includes(server.hostname) && !server.username && !server.password);
  const response = await fetch(new URL('/prove', server), {method: 'POST',
    body: createProvingPayload(preimage(privateInputs, publicOutputs), 42n, material),
    redirect: 'error', signal: AbortSignal.timeout(120000)});
  const proof = Buffer.from(await response.arrayBuffer());
  assert.ok(response.ok, `native prover HTTP ${response.status}: ${proof.toString()}`);
  assert.ok(proof.length > 0 && proof.length <= 1048576);
  await writeFile(join(directory, 'componentRelease.proof'), proof, {mode: 0o600});
  evidence.proof = {bytes: proof.length, sha256: digest(proof), nativeServerSelfVerified: true};
  await writeFile(join(directory, 'component-disclosure-evidence.json'), JSON.stringify(evidence, null, 2) + '\n');
}
console.log(JSON.stringify(evidence, null, 2));
