import { randomBytes } from 'node:crypto';
import { mkdir, open, readFile, chmod, stat } from 'node:fs/promises';
import { join, resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import { WalletSeeds } from '@midnightntwrk/wallet-sdk/hd';
import { createKeystore, PublicKey, UnshieldedWallet } from '@midnightntwrk/wallet-sdk/unshielded';
import { NoOpTransactionHistoryStorage, ProtocolVersion } from '@midnightntwrk/wallet-sdk-abstractions';
import { WebSocket } from 'ws';

export async function loadPreviewIdentity(directory = process.env.NOCTIUM_WALLET_DIR ?? '/private/tmp/noctium-preview-wallet') {
  directory = resolve(directory);
  await mkdir(directory, { recursive: true, mode: 0o700 });
  await chmod(directory, 0o700);
  const seedPath = join(directory, 'wallet.seed');
  try {
    const file = await open(seedPath, 'wx', 0o600);
    try { await file.writeFile(randomBytes(32).toString('hex') + '\n'); }
    finally { await file.close(); }
  } catch (error) {
    if (error.code !== 'EEXIST') throw error;
  }
  await chmod(seedPath, 0o600);
  const seed = (await readFile(seedPath, 'utf8')).trim();
  if (!/^[0-9a-f]{64}$/.test(seed)) throw new Error('Invalid stored seed format');
  const seeds = WalletSeeds.fromMasterSeed(Buffer.from(seed, 'hex'));
  const keystore = createKeystore({ kind: 'schnorr', secret: seeds.unshielded }, 'preview');
  return { seeds, keystore, seedPath, address: keystore.getBech32Address().asString() };
}

async function main() {
  globalThis.WebSocket = WebSocket;
  const { keystore, seedPath, address } = await loadPreviewIdentity();
  console.log(JSON.stringify({ network: 'preview', address, faucet: 'https://midnight-tmnight-preview.nethermind.dev/', seedFile: seedPath, seedMode: (await stat(seedPath)).mode & 0o777 }));
  if (!process.argv.includes('--balance')) return;
  const timeout = setTimeout(() => { console.error('Wallet sync timed out after 90 seconds'); process.exit(2); }, 90_000);
  let wallet;
  try {
    wallet = await UnshieldedWallet({
      networkId: 'preview',
      indexerClientConnection: {
        indexerHttpUrl: 'https://indexer.preview.midnight.network/api/v4/graphql',
        indexerWsUrl: 'wss://indexer.preview.midnight.network/api/v4/graphql/ws',
      },
      txHistoryStorage: new NoOpTransactionHistoryStorage(),
      forks: ProtocolVersion.V9NativeForkSchedule,
    }).startWithPublicKey(PublicKey.fromKeyStore(keystore));
    await wallet.start();
    const state = await wallet.waitForSyncedState();
    console.log(JSON.stringify({ synced: true, balances: state.balances }, (_key, value) => typeof value === 'bigint' ? value.toString() : value));
  } finally { clearTimeout(timeout); await wallet?.stop(); }
}

if (process.argv[1] && pathToFileURL(resolve(process.argv[1])).href === import.meta.url) await main();
