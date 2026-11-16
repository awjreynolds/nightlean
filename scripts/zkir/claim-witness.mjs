// Public development fixture values only. Produces local files for the example claim.
import { writeFile } from 'node:fs/promises';
import { transientHash, bigIntToValue, valueToBigInt } from '@midnight-ntwrk/ledger-v9';
const [destination] = process.argv.slice(2);
if (!destination) throw new Error('usage: node claim-witness.mjs OUTPUT.json');
const field = { tag: 'atom', value: { tag: 'field' } };
const hash = xs => valueToBigInt(transientHash(xs.map(() => field), xs.flatMap(bigIntToValue)));
const secret = 42n, campaign = 9n, siblings = [17n, 23n], directions = [0n, 1n];
const leaf = hash([1n, secret, campaign]);
const node = hash([2n, leaf, siblings[0]]);
const root = hash([2n, siblings[1], node]);
const nullifier = hash([3n, secret, campaign]);
const spec = {
  inputs: [], privateTranscript: [secret, ...siblings, ...directions].map(String),
  publicTranscriptInputs: [root, campaign, nullifier, nullifier].map(String),
  publicTranscriptOutputs: [root, campaign, nullifier].map(String), bindingInput: '42'
};
await writeFile(destination, JSON.stringify(spec, null, 2) + '\n', { mode: 0o600 });
console.log(JSON.stringify({ root: String(root), campaign: String(campaign), nullifier: String(nullifier),
  leaf: String(leaf), node: String(node), qualification: 'development fixture and synthetic relation transcript' }));
