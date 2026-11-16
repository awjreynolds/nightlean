// Experimental standalone relation harness, not a contract-call transcript adapter.
import { readFile, writeFile } from 'node:fs/promises';
import { Zkir, check } from '@midnightntwrk/zkir-v3';
import { maxField, createProvingPayload } from '@midnight-ntwrk/ledger-v9';
import { createHash } from 'node:crypto';

const proofServer = new URL(process.env.NIGHTLEAN_PROOF_SERVER ?? 'http://127.0.0.1:16300');
if (!['http:', 'https:'].includes(proofServer.protocol) ||
    !['127.0.0.1', 'localhost', '[::1]'].includes(proofServer.hostname) ||
    proofServer.username || proofServer.password) {
  throw new Error('Relation proving requires a loopback proof server');
}

function encodeScaleInt(value) {
  let n = BigInt(value);
  if (n < 0n) throw new Error('negative SCALE value');
  const littleEndian = (v, count) => Buffer.from(Array.from({ length: count }, () => {
    const b = Number(v & 255n); v >>= 8n; return b;
  }));
  if (n < 64n) return littleEndian(n << 2n, 1);
  if (n < 16384n) return littleEndian((n << 2n) | 1n, 2);
  if (n < 1073741824n) return littleEndian((n << 2n) | 2n, 4);
  const bytes = [];
  while (n) { bytes.push(Number(n & 255n)); n >>= 8n; }
  if (bytes.length > 32) throw new Error('SCALE value exceeds field width');
  return Buffer.from([((bytes.length - 4) << 2) | 3, ...bytes]);
}
const field = value => {
  if (typeof value !== 'string' || !/^(0|[1-9][0-9]*)$/.test(value))
    throw new Error('field elements must be canonical decimal strings');
  const n = BigInt(value);
  if (n > maxField()) throw new Error('field element exceeds Native modulus');
  return n;
};
const vector = values => {
  if (!Array.isArray(values)) throw new Error('missing transcript vector');
  return Buffer.concat([encodeScaleInt(values.length), ...values.map(value => encodeScaleInt(field(value)))]);
};
const args = process.argv.slice(2);
if (args.length !== 5) {
  console.error('usage: node prove-relation.mjs CIRCUIT.zkir KEY.prover KEY.verifier WITNESS.json OUTPUT.proof');
  process.exitCode = 2;
} else {
  try {
    const spec = JSON.parse(await readFile(args[3], 'utf8'));
    const key = Buffer.from('nightlean/standalone-relation');
    // Mirrors pinned ledger9 ProofPreimage struct and SCALE serialization.
    // Public vectors here are synthetic relation statements, not encoded ledger operations.
    const serialized = Buffer.concat([
      Buffer.from('midnight:proof-preimage:'), vector(spec.inputs),
      vector(spec.privateTranscript), vector(spec.publicTranscriptInputs),
      vector(spec.publicTranscriptOutputs), encodeScaleInt(field(spec.bindingInput)),
      Buffer.from([0]), encodeScaleInt(key.length), key
    ]);
    const ir = Zkir.fromJson(await readFile(args[0], 'utf8'));
    const material = {
      ir: ir.serialize(), proverKey: await readFile(args[1]), verifierKey: await readFile(args[2])
    };
    await check(serialized, { lookupKey: async () => material });
    const payload = createProvingPayload(serialized, field(spec.bindingInput), material);
    const response = await fetch(new URL('/prove', proofServer), {
      method: 'POST', body: payload, redirect: 'error', signal: AbortSignal.timeout(120_000)
    });
    const proof = Buffer.from(await response.arrayBuffer());
    if (!response.ok) throw new Error(`proof server ${response.status}: ${proof.toString()}`);
    await writeFile(args[4], proof, { mode: 0o600 });
    console.log(JSON.stringify({
      proofBytes: proof.length, proofSha256: createHash('sha256').update(proof).digest('hex'),
      qualification: 'standalone relation checked and native proof server self-verified; no ledger acceptance'
    }));
  } catch (error) {
    console.error(`Relation proving failed: ${error.message ?? error}`);
    process.exitCode = 1;
  }
}
