// Prove one valid witness for an actual generic specialization with the local
// native proof service. Keep keys and proof bytes outside the repo.
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {readFile, writeFile} from 'node:fs/promises';
import {join, resolve, sep} from 'node:path';
import {createRequire} from 'node:module';
import {fileURLToPath, pathToFileURL} from 'node:url';

const [artifactDirectory, checkerPath, circuitName = 'genericAddSmall'] = process.argv.slice(2);
if (!artifactDirectory || !checkerPath) {
  throw Error('usage: node tests/generics/prove-native.mjs OUTPUT_DIRECTORY OFFICIAL_WASM_FS_MODULE [genericAddSmall|genericAddWide]');
}
assert.ok(['genericAddSmall', 'genericAddWide'].includes(circuitName), 'unsupported generic fixture circuit');

const directory = resolve(artifactDirectory);
const repository = resolve(fileURLToPath(new URL('../..', import.meta.url)));
assert.ok(directory !== repository && !directory.startsWith(repository + sep),
  'proof output directory must stay outside the repository');
const {Zkir, check} = await import(pathToFileURL(resolve(checkerPath)).href);
const require = createRequire(new URL('../../scripts/zkir/package.json', import.meta.url));
const ledger = await import(pathToFileURL(require.resolve('@midnight-ntwrk/ledger-v9')).href);
const proofServer = new URL(process.env.NOCTIUM_PROOF_SERVER ?? 'http://127.0.0.1:16300');
assert.ok(['http:', 'https:'].includes(proofServer.protocol));
assert.ok(['127.0.0.1', 'localhost', '[::1]'].includes(proofServer.hostname));
assert.ok(!proofServer.username && !proofServer.password);
const relation = Zkir.fromJson(await readFile(join(directory, `${circuitName}.zkir`), 'utf8'));
const material = {
  ir: relation.serialize(),
  proverKey: new Uint8Array(await readFile(join(directory, 'keys', `${circuitName}.prover`))),
  verifierKey: new Uint8Array(await readFile(join(directory, 'keys', `${circuitName}.verifier`))),
};
const keyLocation = `noctium/generics/${circuitName}`;
const witness = circuitName === 'genericAddSmall'
  ? {privateValues: ['7', '8'], publicValues: ['15', '15'], publicReads: ['15']}
  : {privateValues: ['100', '155'], publicValues: ['255', '255'], publicReads: ['255']};
const provider = {
  lookupKey: async (location) => location === keyLocation ? material : undefined,
};

function compact(value) {
  let n = BigInt(value);
  assert.ok(n >= 0n, 'proof transcript values must be nonnegative');
  const bytes = (v, count) => Buffer.from(Array.from({length: count}, () => {
    const byte = Number(v & 255n);
    v >>= 8n;
    return byte;
  }));
  if (n < 64n) return bytes(n << 2n, 1);
  if (n < 16384n) return bytes((n << 2n) | 1n, 2);
  if (n < 1073741824n) return bytes((n << 2n) | 2n, 4);
  const encoded = [];
  while (n) {
    encoded.push(Number(n & 255n));
    n >>= 8n;
  }
  return Buffer.from([((encoded.length - 4) << 2) | 3, ...encoded]);
}

const vector = (values) => Buffer.concat([compact(values.length), ...values.map(compact)]);
const key = Buffer.from(keyLocation);
const serializedPreimage = Buffer.concat([
  Buffer.from('midnight:proof-preimage:'),
  vector([]),
  vector(witness.privateValues),
  vector(witness.publicValues),
  vector(witness.publicReads),
  compact(42),
  Buffer.from([0]),
  compact(key.length),
  key,
]);

const activity = await check(serializedPreimage, provider);
assert.equal(activity.length, 2, 'both public input and result impacts must match');
const payload = ledger.createProvingPayload(serializedPreimage, 42n, material);
const response = await fetch(new URL('/prove', proofServer), {
  method: 'POST',
  body: payload,
  redirect: 'error',
  signal: AbortSignal.timeout(120_000),
});
const proof = Buffer.from(await response.arrayBuffer());
if (!response.ok) throw Error(`native proof service ${response.status}: ${proof.toString()}`);
assert.ok(proof.length > 0, 'the official prover must return a proof');
await writeFile(join(directory, `${circuitName}.proof`), proof, {mode: 0o600});
console.log(JSON.stringify({
  circuit: circuitName,
  k: relation.getK(),
  proofBytes: proof.length,
  proofSha256: createHash('sha256').update(proof).digest('hex'),
  nativeProofServiceSelfVerified: true,
}));
