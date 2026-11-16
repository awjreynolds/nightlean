import { WalletFacade, WalletSeeds, ShieldedWallet, UnshieldedWallet, DustWallet, createKeystore, PublicKey, InMemoryTransactionHistoryStorage, WalletEntrySchema, mergeWalletEntries } from '@midnightntwrk/wallet-sdk';
import { WebSocket } from 'ws';
globalThis.WebSocket = WebSocket;

const expectedGenesis = '0x823383ec0302be8417cfcbcc62f21df08f4047bca37aaea89e3f54b550ebae1d';
const node = 'http://127.0.0.1:19944';
async function rpc(method, params = []) {
  const response = await fetch(node, { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({ jsonrpc: '2.0', id: 1, method, params }), signal: AbortSignal.timeout(5000) });
  const body = await response.json();
  if (!response.ok || body.error) throw new Error(`Local RPC failed: ${method}`);
  return body.result;
}
export async function buildLocalWallet() {
  if (await rpc('chain_getBlockHash', [0]) !== expectedGenesis) throw new Error('Refusing non-development genesis');
  const runtime = await rpc('state_getRuntimeVersion');
  if (runtime.specVersion !== 2001100 || runtime.transactionVersion !== 4) throw new Error('Unexpected local ledger profile');
  // The development chain publishes this synthetic genesis identity. Never use on a public network.
  const master = Buffer.alloc(32); master[31] = 1;
  const seeds = WalletSeeds.fromMasterSeed(master); master.fill(0);
  const keystore = createKeystore({ kind: 'schnorr', secret: seeds.unshielded }, 'undeployed');
  const wallet = await WalletFacade.init({
    configuration: {
      networkId: 'undeployed', relayURL: new URL('ws://127.0.0.1:19944'),
      indexerClientConnection: { indexerHttpUrl: 'http://127.0.0.1:18088/api/v4/graphql', indexerWsUrl: 'ws://127.0.0.1:18088/api/v4/graphql/ws' },
      costParameters: { feeBlocksMargin: 5 },
      provers: { v9: { kind: 'server', url: new URL('http://127.0.0.1:16300') } },
      txHistoryStorage: new InMemoryTransactionHistoryStorage(WalletEntrySchema, mergeWalletEntries),
    },
    shielded: (cfg) => ShieldedWallet(cfg).startWithSeed(seeds.shielded),
    unshielded: (cfg) => UnshieldedWallet(cfg).startWithPublicKey(PublicKey.fromKeyStore(keystore)),
    dust: (cfg) => DustWallet({ ...cfg, chainVersionProbe: async () => BigInt(runtime.specVersion) }).startWithSeed(seeds.dust),
  });
  return { wallet, seeds, keystore };
}

if (process.argv[1]?.endsWith('/wallet-local.mjs')) {
  const timeout = setTimeout(() => { console.error('Local wallet synchronization timed out'); process.exit(2); }, 90_000);
  const { wallet, seeds, keystore } = await buildLocalWallet();
  try {
    await wallet.start(seeds);
    const state = await wallet.waitForSyncedState();
    console.log(JSON.stringify({ network: 'undeployed', genesis: expectedGenesis, synced: state.isSynced, protocolVersion: state.activeProtocolVersion, address: keystore.getBech32Address().asString(), balances: state.unshielded.balances, dust: state.dust.balance(new Date()), availableDustCoins: state.dust.availableCoins.length }, (_key, value) => typeof value === 'bigint' ? value.toString() : value));
  } finally { clearTimeout(timeout); await wallet.stop(); }
}
