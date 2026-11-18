// Native implementation qualification only. Compiler/model/proofs are Lean.
import assert from 'node:assert/strict';
import {readFile, writeFile, mkdtemp, rm} from 'node:fs/promises';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
import {pathToFileURL} from 'node:url';
import {resolve, join} from 'node:path';
import {tmpdir} from 'node:os';
import {execFileSync} from 'node:child_process';

const [checkerPath, artifactPath, nativeCli, ...extra] = process.argv.slice(2);
if (!checkerPath || !artifactPath || extra.length)
  throw Error('Usage: node tests/private-claim-lowering-checker.mjs OFFICIAL_321_CHECKER claimRelation.zkir [NATIVE_321_CLI]');
const {Zkir, check} = await import(pathToFileURL(resolve(checkerPath)).href);
const require = createRequire(new URL('../scripts/zkir/package.json', import.meta.url));
const {transientHash, bigIntToValue, valueToBigInt, createProvingPayload} =
  await import(pathToFileURL(require.resolve('@midnight-ntwrk/ledger-v9')).href);
const modulus = 52435875175126190479447740508185965837690552500527637822603658699938581184513n;
const field = {tag: 'atom', value: {tag: 'field'}};
const hash = values => valueToBigInt(transientHash(values.map(() => field), values.flatMap(bigIntToValue)));
const secret = 42n, campaign = 9n, sibling0 = 17n, sibling1 = 23n;
const leaf = hash([1n, secret, campaign]);
const node = hash([2n, leaf, sibling0]);
const root = hash([2n, sibling1, node]);
const nullifier = hash([3n, secret, campaign]);
const source = await readFile(artifactPath);
const artifact = JSON.parse(source);
assert.equal(artifact.instructions.length, 27);
assert.equal(artifact.do_communications_commitment, false);
const compact = value => {
  let n = BigInt(value);
  assert.ok(n >= 0n && n < modulus);
  const little = (v, count) => Buffer.from(Array.from({length: count}, () => {
    const byte = Number(v & 255n); v >>= 8n; return byte;
  }));
  if (n < 64n) return little(n << 2n, 1);
  if (n < 16384n) return little((n << 2n) | 1n, 2);
  if (n < 1073741824n) return little((n << 2n) | 2n, 4);
  const bytes = []; while (n) {bytes.push(Number(n & 255n)); n >>= 8n;}
  return Buffer.from([((bytes.length - 4) << 2) | 3, ...bytes]);
};
const vector = values => Buffer.concat([compact(values.length), ...values.map(compact)]);
const preimage = test => {
  const key = Buffer.from('noctium/claim-lowering/qualification');
  return Buffer.concat([Buffer.from('midnight:proof-preimage:'), vector([]), vector(test.private),
    vector(test.groups), vector(test.reads), compact(42), Buffer.from([0]), compact(key.length), key]);
};
const base = {private: [secret, sibling0, sibling1, 0n, 1n],
  reads: [root, campaign, nullifier], groups: [root, campaign, nullifier, nullifier]};
const fixture = (id, changes = {}, accepted = false, circuit = artifact) => ({id, ...structuredClone(base), ...changes, accepted, circuit});
const missing = structuredClone(artifact);
missing.instructions = missing.instructions.filter(op => !(op.op === 'assert' && op.cond === '%v7'));
const swapped = structuredClone(artifact);
const selector = swapped.instructions.find(op => op.output === '%v1');
[selector.a, selector.b] = [selector.b, selector.a];
const swappedRoot = hash([2n, sibling1, hash([2n, sibling0, sibling0])]);
const cases = [
  fixture('valid-source-claim', {}, true),
  fixture('wrong-direction', {private: [secret, sibling0, sibling1, 1n, 1n]}),
  fixture('non-boolean-direction', {private: [secret, sibling0, sibling1, 2n, 1n]}),
  fixture('wrong-root', {reads: [root + 1n, campaign, nullifier], groups: [root + 1n, campaign, nullifier, nullifier]}),
  fixture('wrong-nullifier', {reads: [root, campaign, nullifier + 1n], groups: [root, campaign, nullifier + 1n, nullifier + 1n]}),
  fixture('wrong-final-impact-return', {groups: [root, campaign, nullifier, nullifier + 1n]}),
  fixture('missing-root-assert-admits-wrong-root', {reads: [root + 1n, campaign, nullifier], groups: [root + 1n, campaign, nullifier, nullifier]}, true, missing),
  fixture('swapped-path-rejects-original-witness', {}, false, swapped),
  fixture('swapped-path-admits-different-relation', {reads: [swappedRoot, campaign, nullifier], groups: [swappedRoot, campaign, nullifier, nullifier]}, true, swapped),
];
const results = [];
let honestMaterial;
for (const test of cases) {
  const relation = Zkir.fromJson(JSON.stringify(test.circuit));
  const material = {ir: relation.serialize(), proverKey: new Uint8Array(), verifierKey: new Uint8Array()};
  let failure, groups;
  try {groups = await check(preimage(test), {lookupKey: async () => material});} catch (error) {failure = error;}
  assert.equal(!failure, test.accepted, `${test.id}: ${failure ?? 'unexpected acceptance'}`);
  results.push({id: test.id, checkerAccepted: !failure, impactGroups: groups?.length,
    error: failure ? String(failure.message ?? failure) : undefined});
  if (test.id === 'valid-source-claim') honestMaterial = material;
}
let proof;
if (nativeCli) {
  const directory = await mkdtemp(join(tmpdir(), 'noctium-lowering-prover-'));
  try {
    const input = join(directory, 'claim.zkir');
    await writeFile(input, source);
    execFileSync(resolve(nativeCli), ['compile', input, input + '.prover', input + '.verifier'], {stdio: 'pipe', timeout: 120000});
    const material = {...honestMaterial, proverKey: await readFile(input + '.prover'), verifierKey: await readFile(input + '.verifier')};
    const payload = createProvingPayload(preimage(cases[0]), 42n, material);
    const response = await fetch('http://127.0.0.1:16300/prove', {method: 'POST', body: payload,
      redirect: 'error', signal: AbortSignal.timeout(120000)});
    const bytes = Buffer.from(await response.arrayBuffer());
    assert.ok(response.ok, `native proof server ${response.status}: ${bytes.toString()}`);
    proof = {nativeKeygenSucceeded: true, serverSelfVerified: true, proofBytes: bytes.length,
      proofSha256: createHash('sha256').update(bytes).digest('hex')};
  } finally {await rm(directory, {recursive: true, force: true});}
}
console.log(JSON.stringify({scope: 'native implementation qualification; no arbitrary-internal-witness proof, ledger call or byte certificate',
  sourceRevision: '7a51b3385bbf4bce3604df87a7c70867c9ab43c0',
  artifactSha256: createHash('sha256').update(source).digest('hex'),
  checkerModuleSha256: createHash('sha256').update(await readFile(checkerPath)).digest('hex'),
  outputBinding: 'Final Impact authenticates the returned nullifier. Standalone Output alone is a host observation.',
  publicDevelopmentFixture: {secret: String(secret), campaign: String(campaign), siblings: [String(sibling0), String(sibling1)],
    directions: [0, 1], leaf: String(leaf), node: String(node), root: String(root), nullifier: String(nullifier)},
  cases: results, proof}, null, 2));
