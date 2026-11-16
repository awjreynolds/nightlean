// Bounded native artifact/proof experiment. This script never submits a transaction.
import assert from 'node:assert/strict';
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { resolve, join } from 'node:path';
import { createHash } from 'node:crypto';
import * as l from '@midnight-ntwrk/ledger-v9';
import * as z from '@midnightntwrk/zkir-v3';

const [operationsPath, circuitPath, proverPath, verifierPath, outputPath, ...options] = process.argv.slice(2);
if (!outputPath || options.some(option => option !== '--prove') || options.length > 1) {
  throw Error('Usage: node native-contract.mjs OPERATIONS.json ENTRYPOINT.zkir KEY.prover KEY.verifier OUTPUT_DIRECTORY [--prove]');
}
const out = resolve(outputPath);
await mkdir(join(out, 'keys'), { recursive: true });
await mkdir(join(out, 'zkir'), { recursive: true });
const atom = { tag: 'atom', value: { tag: 'field' } };
const field = n => ({ value: l.bigIntToValue(n), alignment: [atom] });
const empty = { value: [], alignment: [] };
const hash = xs => l.valueToBigInt(l.transientHash(xs.map(() => atom), xs.flatMap(l.bigIntToValue)));
const secret = 42n, campaign = 7n;
const leaf = hash([1n, secret, campaign]), node = hash([2n, leaf, 17n]);
const root = hash([2n, 23n, node]), nullifier = hash([3n, secret, campaign]);
function hydrate(x) {
  if (Array.isArray(x)) return x.map(hydrate);
  if (!x || typeof x !== 'object') return x;
  const o = Object.fromEntries(Object.entries(x).map(([k, v]) => [k, hydrate(v)]));
  if (o.value && o.alignment) {
    o.value = o.value.map(bytes => Uint8Array.from(bytes));
    if (o.alignment[0]?.value?.tag === 'field') {
      const value = l.valueToBigInt(o.value);
      if (value === 99n) o.value = field(root).value;
      if (value === 123n) o.value = field(nullifier).value;
    }
  }
  return o;
}
const operations = hydrate(JSON.parse(await readFile(operationsPath, 'utf8')));
const json = await readFile(circuitPath, 'utf8');
assert.equal(JSON.parse(json).do_communications_commitment, true,
  'native contract entrypoints must bind their communication commitment');
const ir = z.Zkir.fromJson(json);
const material = { ir: ir.serialize(), proverKey: await readFile(proverPath), verifierKey: await readFile(verifierPath) };
const operation = new l.ContractOperation();
operation.verifierKey = material.verifierKey;
assert.deepEqual(Buffer.from(l.ContractOperation.deserialize(operation.serialize()).verifierKey), material.verifierKey);
let data = l.StateValue.newArray();
data = data.arrayPush(l.StateValue.newCell(field(root)));
data = data.arrayPush(l.StateValue.newCell(field(campaign)));
data = data.arrayPush(l.StateValue.newMap(new l.StateMap()));
const state = new l.ContractState();
state.data = new l.ChargedState(data);
state.setOperation('claim', operation);
state.maintenanceAuthority = new l.ContractMaintenanceAuthority([], 1);
const deployment = new l.ContractDeploy(state);
const ttl = new Date(Date.now() + 60 * 60 * 1000);
const deploymentIntent = l.Intent.new(ttl).addDeploy(deployment);

const context = new l.QueryContext(state.data, deployment.address);
const cost = l.CostModel.initialCostModel();
const gather = context.query(operations.map(op => op.popeq ? { popeq: { ...op.popeq, result: null } } : op), cost);
const transcript = { gas: gather.gasCost, effects: gather.context.effects, program: operations };
const after = context.runTranscript(transcript, cost);
assert.equal(l.valueToBigInt(after.state.state.asArray()[2].asMap().get(field(nullifier)).asCell().value), 1n);
const privateOutputs = [secret, 17n, 23n, 0n, 1n].map(field);
const prototype = new l.ContractCallPrototype(deployment.address, 'claim', operation,
  transcript, undefined, privateOutputs, empty, empty, l.communicationCommitmentRandomness(), 'claim');
const callIntent = l.Intent.new(ttl).addCall(prototype);
const preimage = l.proofDataIntoSerializedPreimage(empty, empty, operations, privateOutputs, 'claim');
const activity = await z.check(preimage, { lookupKey: async () => material });
assert.equal(activity.length, operations.length, 'native activity groups must match VM operation count');

await writeFile(join(out, 'keys/claim.prover'), material.proverKey);
await writeFile(join(out, 'keys/claim.verifier'), material.verifierKey);
await writeFile(join(out, 'zkir/claim.zkir'), json);
await writeFile(join(out, 'zkir/claim.bzkir'), material.ir);
await writeFile(join(out, 'initial-state.bin'), state.serialize());
await writeFile(join(out, 'deploy-intent.bin'), deploymentIntent.serialize());
await writeFile(join(out, 'call-intent.bin'), callIntent.serialize(), { mode: 0o600 });
const predicted = new l.ContractState();
predicted.data = after.state;
predicted.setOperation('claim', operation);
predicted.maintenanceAuthority = state.maintenanceAuthority;
await writeFile(join(out, 'predicted-state.bin'), predicted.serialize());
const summary = {
  qualification: 'native artifact and call assembly; no ledger acceptance',
  address: deployment.address, entrypoint: 'claim', root: root.toString(), campaign: campaign.toString(),
  nullifier: nullifier.toString(), k: ir.getK(), operationBytes: operation.serialize().length,
  deploymentIntentBytes: deploymentIntent.serialize().length, callIntentBytes: callIntent.serialize().length,
  nativeVmStateUpdate: true, officialPreprocessing: true,
  cryptographicProofGenerated: false, transactionSubmitted: false,
};
if (options.includes('--prove')) {
  const url = new URL(process.env.NIGHTLEAN_PROOF_SERVER ?? 'http://127.0.0.1:16300');
  if (!['http:', 'https:'].includes(url.protocol) ||
      !['127.0.0.1', 'localhost', '[::1]'].includes(url.hostname) || url.username || url.password)
    throw Error('Native witness proving requires a loopback proof server');
  const payload = l.createProvingPayload(preimage, 42n, material);
  const response = await fetch(new URL('/prove', url), { method: 'POST', body: payload,
    redirect: 'error', signal: AbortSignal.timeout(120_000) });
  const proof = Buffer.from(await response.arrayBuffer());
  if (!response.ok) throw Error(`Native proof server ${response.status}: ${proof.toString()}`);
  await writeFile(join(out, 'native-claim.proof'), proof, { mode: 0o600 });
  summary.cryptographicProofGenerated = true;
  summary.proofBytes = proof.length;
  summary.proofSha256 = createHash('sha256').update(proof).digest('hex');
}
await writeFile(join(out, 'native-contract.json'), JSON.stringify(summary, null, 2));
console.log(JSON.stringify(summary, null, 2));
