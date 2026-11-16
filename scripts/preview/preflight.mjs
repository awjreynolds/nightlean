import { readFile, lstat, stat, realpath } from 'node:fs/promises';
import { resolve, join } from 'node:path';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { WalletSeeds } from '@midnightntwrk/wallet-sdk/hd';
import { createKeystore } from '@midnightntwrk/wallet-sdk/unshielded';
import { Token } from '@midnightntwrk/wallet-sdk-abstractions';
import { buildPreviewWallet, localProofServerUrl } from './wallet-full.mjs';

const exec = promisify(execFile);
const nativeImage = 'midnightntwrk/midnight-node-toolkit@sha256:904f824f3350530bc2fb03448906cc5f9f200b98e98bd9fbb274a1cc25b9f89c';
const options = process.argv.slice(2);
let artifacts;
let checkToolkit = false;
for (let i = 0; i < options.length; i++) {
  if (options[i] === '--toolkit-identity') checkToolkit = true;
  else if (options[i] === '--artifacts' && options[i + 1]) artifacts = resolve(options[++i]);
  else throw new Error('usage: node preflight.mjs [--toolkit-identity] [--artifacts COMPILED_DIRECTORY]');
}

const report = { network: 'preview', readOnly: true, submissionReady: false, blockers: [] };
const print = () => console.log(JSON.stringify(report, (_key, value) => typeof value === 'bigint' ? value.toString() : value));
const deadline = setTimeout(() => {
  report.blockers.push('Read-only preflight exceeded its 120 second deadline');
  print();
  process.exit(2);
}, 120_000);
deadline.unref();
async function check(name, operation) {
  try { report[name] = await operation(); }
  catch { report[name] = { ok: false }; report.blockers.push(`${name} check failed`); }
}

await check('rpc', async () => {
  const response = await fetch('https://rpc.preview.midnight.network', {
    method: 'POST', headers: { 'content-type': 'application/json' },
    body: JSON.stringify({ jsonrpc: '2.0', id: 1, method: 'state_getRuntimeVersion', params: [] }),
    signal: AbortSignal.timeout(15_000),
  });
  const body = await response.json();
  if (!response.ok || body.error || !body.result?.specVersion) throw Error('RPC unavailable');
  return { ok: true, specName: body.result.specName, specVersion: body.result.specVersion };
});
await check('indexer', async () => {
  const response = await fetch('https://indexer.preview.midnight.network/api/v4/graphql', {
    method: 'POST', headers: { 'content-type': 'application/json' },
    body: JSON.stringify({ query: '{__typename}' }), signal: AbortSignal.timeout(15_000),
  });
  const body = await response.json();
  if (!response.ok || body.errors || body.data?.__typename !== 'Query') throw Error('Indexer unavailable');
  return { ok: true };
});
await check('proofServer', async () => {
  const url = localProofServerUrl();
  const response = await fetch(new URL('/health', url), { signal: AbortSignal.timeout(5000) });
  if (!response.ok) throw Error('Proof service unhealthy');
  return { ok: true, url: url.toString(), scope: 'health only, no proving request' };
});

if (artifacts) await check('artifacts', async () => {
  const metadata = JSON.parse(await readFile(join(artifacts, 'compiler/contract-info.json'), 'utf8'));
  const contract = await stat(join(artifacts, 'contract/index.js'));
  const prover = await stat(join(artifacts, 'keys/claim.prover'));
  const verifier = await stat(join(artifacts, 'keys/claim.verifier'));
  if (!contract.isFile() || !prover.isFile() || !verifier.isFile() || !prover.size || !verifier.size) throw Error('Missing artifacts');
  return { ok: true, contractName: metadata.name ?? null, proverBytes: prover.size, verifierBytes: verifier.size,
    scope: 'presence only, Preview deployment unqualified' };
});

let identity;
await check('identity', async () => {
  const directory = await realpath(process.env.NIGHTLEAN_WALLET_DIR ?? '/private/tmp/nightlean-preview-wallet');
  const seedPath = join(directory, 'wallet.seed');
  const directoryInfo = await stat(directory), seedInfo = await lstat(seedPath);
  if (!seedInfo.isFile() || seedInfo.isSymbolicLink() || (directoryInfo.mode & 0o077) || (seedInfo.mode & 0o077)) throw Error('Unsafe identity path');
  const text = (await readFile(seedPath, 'utf8')).trim();
  if (!/^[0-9a-f]{64}$/.test(text)) throw Error('Invalid identity');
  const master = Buffer.from(text, 'hex');
  const seeds = WalletSeeds.fromMasterSeed(master);
  master.fill(0);
  const keystore = createKeystore({ kind: 'schnorr', secret: seeds.unshielded }, 'preview');
  identity = { seeds, keystore, directory, seedPath, address: keystore.getBech32Address().asString() };
  return { ok: true, address: identity.address };
});

if (identity && checkToolkit) await check('toolkitIdentity', async () => {
  // Only a path and fixed shell source appear in the host command arguments. The secret stays in
  // its readonly mounted file and the child's memory. Capture output and expose public addresses only.
  const result = await exec('docker', ['run', '--rm', '--pull', 'never', '--network', 'none',
    '--read-only', '--cap-drop', 'ALL', '--security-opt', 'no-new-privileges',
    '--mount', `type=bind,source=${identity.seedPath},target=/wallet.seed,readonly`,
    '--entrypoint', '/bin/sh', nativeImage, '-c',
    'exec /midnight-node-toolkit show-address --network preview --unshielded --seed "$(cat /wallet.seed)"'],
  { timeout: 30_000, maxBuffer: 2 ** 16 });
  const address = result.stdout.trim();
  if (!/^mn_addr_preview1[0-9a-z]+$/.test(address) || address !== identity.address) throw Error('Identity mismatch');
  return { ok: true, addressMatchesSdk: true, image: nativeImage };
});

if (identity) await check('wallet', async () => {
  const wallet = await buildPreviewWallet(identity);
  let timeout;
  try {
    const operation = (async () => { await wallet.start(identity.seeds); return await wallet.waitForSyncedState(); })();
    const state = await Promise.race([operation, new Promise((_resolve, reject) => {
      timeout = setTimeout(() => reject(Error('Wallet sync timeout')), 120_000);
    })]);
    const night = BigInt(state.unshielded.balances[Token.night] ?? 0n);
    const dust = state.dust.balance(new Date());
    if (night === 0n) report.blockers.push('Preview wallet has no confirmed NIGHT funding');
    if (BigInt(dust) === 0n) report.blockers.push('Preview wallet has no available DUST for fees');
    return { ok: true, synced: state.isSynced, protocolVersion: state.activeProtocolVersion,
      balances: state.unshielded.balances, nightAssetId: Token.night, night, dust,
      unregisteredNightUtxos: state.unshielded.availableCoins.filter((coin) => coin.meta?.registeredForDustGeneration !== true).length };
  } finally { clearTimeout(timeout); await wallet.stop(); }
});

// Funding checks do not qualify the remaining Preview integration or estimate a deployment fee.
report.blockers.push('Preview transaction build, fee estimate, submission, and receipt checks still required');
print();
clearTimeout(deadline);
process.exitCode = report.blockers.length ? 2 : 0;
