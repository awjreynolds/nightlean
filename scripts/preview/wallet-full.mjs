import { WalletFacade } from '@midnightntwrk/wallet-sdk/facade';
import { ShieldedWallet } from '@midnightntwrk/wallet-sdk/shielded';
import { DustWallet } from '@midnightntwrk/wallet-sdk/dust';
import { PublicKey, UnshieldedWallet } from '@midnightntwrk/wallet-sdk/unshielded';
import { NoOpTransactionHistoryStorage, ProtocolVersion } from '@midnightntwrk/wallet-sdk-abstractions';
import { distinctUntilChanged, map, throttleTime } from 'rxjs';
import { pathToFileURL } from 'node:url';
import { resolve } from 'node:path';
import { loadPreviewIdentity } from './wallet.mjs';
import { WebSocket } from 'ws';

export function localProofServerUrl(value = process.env.NOCTIUM_PROOF_SERVER ?? 'http://127.0.0.1:16300') {
  const url = new URL(value);
  if (!['http:', 'https:'].includes(url.protocol) || !['localhost', '127.0.0.1', '[::1]'].includes(url.hostname) || url.username || url.password) {
    throw new Error('Proof server must use loopback HTTP(S). Remote proving needs explicit authorization.');
  }
  return url;
}

export async function buildPreviewWallet(identity) {
  const proofServer = localProofServerUrl();
  globalThis.WebSocket = WebSocket;
  identity ??= await loadPreviewIdentity();
  const { seeds: walletSeeds, keystore } = identity;
  return await WalletFacade.init({
    configuration: {
      networkId: 'preview',
      forks: ProtocolVersion.V9NativeForkSchedule,
      indexerClientConnection: {
        indexerHttpUrl: 'https://indexer.preview.midnight.network/api/v4/graphql',
        indexerWsUrl: 'wss://indexer.preview.midnight.network/api/v4/graphql/ws',
      },
      relayURL: new URL('wss://rpc.preview.midnight.network'),
      provers: { v9: { kind: 'server', url: proofServer } },
      txHistoryStorage: new NoOpTransactionHistoryStorage(),
      costParameters: { additionalFeeOverhead: 0n, feeBlocksMargin: 5 },
    },
    shielded: (cfg) => ShieldedWallet(cfg).startWithSeed(walletSeeds.shielded),
    unshielded: (cfg) => UnshieldedWallet(cfg).startWithPublicKey(PublicKey.fromKeyStore(keystore)),
    dust: (cfg) => DustWallet(cfg).startWithSeed(walletSeeds.dust),
  });
}

async function main() {
const timeout = setTimeout(() => { console.error('Full wallet operation timed out after 120 seconds'); process.exit(2); }, 120_000);
console.log(JSON.stringify({ stage: 'initializing-full-wallet' }));
const identity = await loadPreviewIdentity();
const { seeds: walletSeeds, keystore } = identity;
const wallet = await buildPreviewWallet(identity);
console.log(JSON.stringify({ stage: 'starting-full-wallet' }));
const progress = wallet.state().pipe(throttleTime(10_000), map((state) => JSON.stringify({
  stage: 'wallet-progress', synced: state.isSynced,
  shielded: state.shielded.progress, unshielded: state.unshielded.progress, dust: state.dust.progress,
}, (_key, value) => typeof value === 'bigint' ? value.toString() : value)), distinctUntilChanged()).subscribe((value) => console.log(value));
try {
  await wallet.start(walletSeeds);
  console.log(JSON.stringify({ stage: 'waiting-for-full-sync' }));
  const state = await wallet.waitForSyncedState();
  const balances = state.unshielded.balances;
  console.log(JSON.stringify({ synced: state.isSynced, protocolVersion: state.activeProtocolVersion, balances, dust: state.dust.balance(new Date()) }, (_key, value) => typeof value === 'bigint' ? value.toString() : value));
  if (process.argv.includes('--register-dust')) {
    const unregistered = state.unshielded.availableCoins.filter((coin) => coin.meta?.registeredForDustGeneration !== true);
    if (unregistered.length === 0) {
      console.log(JSON.stringify({ registered: false, reason: 'No unregistered funded NIGHT UTXOs available' }));
    } else {
      const { fee } = await wallet.estimateRegistration(unregistered);
      await wallet.waitForGeneratedDust(unregistered, fee, { timeoutMs: 60_000 });
      const recipe = await wallet.registerNightUtxosForDustGeneration(unregistered, keystore.getPublicKey(), keystore.signDataAsync);
      const finalized = await wallet.finalizeRecipe(recipe);
      const transactionId = await wallet.submitTransaction(finalized);
      console.log(JSON.stringify({ registered: true, transactionId }));
    }
  }
} finally { clearTimeout(timeout); progress.unsubscribe(); await wallet.stop(); }
}

if (process.argv[1] && pathToFileURL(resolve(process.argv[1])).href === import.meta.url) await main();
