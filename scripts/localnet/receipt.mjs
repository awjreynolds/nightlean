import { createRequire } from 'node:module';
import { resolve, join } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const genesis = '0x823383ec0302be8417cfcbcc62f21df08f4047bca37aaea89e3f54b550ebae1d';
const addressTag = '0x' + Buffer.from('midnight:contract-address[v2]:').toString('hex');
const hashPattern = /^0x[0-9a-f]{64}$/;
const field = (record) => record.event.data.toJSON()[0] ?? {};
const transactionHash = (record) => field(record).txHash ?? field(record).tx_hash;
const contractAddress = (record) => field(record).contractAddress ?? field(record).contract_address;

export async function observeLocalReceipt({ txHash, address, event, fromBlock }) {
  txHash = txHash.toLowerCase();
  address = address.toLowerCase().replace(/^0x/, '');
  if (!hashPattern.test(txHash) || !/^[0-9a-f]{64}$/.test(address) || !['ContractDeploy', 'ContractCall'].includes(event)) throw new Error('Invalid expected transaction, address, or event');
  const dependencies = resolve(process.env.NIGHTLEAN_WALLET_DEPENDENCIES ?? fileURLToPath(new URL('../preview/', import.meta.url)));
  const require = createRequire(join(dependencies, 'package.json'));
  const { ApiPromise, WsProvider } = require('@polkadot/api');
  const provider = new WsProvider('ws://127.0.0.1:19944', false, {}, 5000);
  const deadline = setTimeout(() => { console.error('Local receipt observation timed out after 60 seconds'); process.exit(2); }, 60_000);
  try {
    await provider.connect();
    const api = await ApiPromise.create({ provider, noInitWarn: true, throwOnConnect: true });
    if ((await api.rpc.chain.getBlockHash(0)).toHex() !== genesis) throw new Error('Refusing unexpected development genesis');
    const finalHash = await api.rpc.chain.getFinalizedHead();
    const finalHeader = await api.rpc.chain.getHeader(finalHash);
    const finalHeight = finalHeader.number.toBigInt();
    const runtime = await api.rpc.state.getRuntimeVersion(finalHash);
    if (runtime.specVersion.toString() !== '2001100' || runtime.transactionVersion.toString() !== '4') throw new Error('Unexpected local runtime');
    const start = fromBlock === undefined ? (finalHeight > 511n ? finalHeight - 511n : 1n) : BigInt(fromBlock);
    if (start < 1n || start > finalHeight || finalHeight - start > 4095n) throw new Error('Receipt scan must cover one through 4096 finalized blocks');
    for (let height = start; height <= finalHeight; height++) {
      const blockHash = await api.rpc.chain.getBlockHash(height.toString());
      const at = await api.at(blockHash);
      const events = [...await at.query.system.events()].filter((record) => record.phase.isApplyExtrinsic && record.event.section === 'midnight');
      const outcomes = events.filter((record) => ['TxApplied', 'TxPartialSuccess'].includes(record.event.method) && transactionHash(record) === txHash);
      if (!outcomes.length) continue;
      if (outcomes.length !== 1 || outcomes[0].event.method !== 'TxApplied') throw new Error('Ledger transaction did not have exactly one TxApplied outcome');
      const extrinsicIndex = outcomes[0].phase.asApplyExtrinsic.toNumber();
      const matching = events.filter((record) => contractAddress(record) === addressTag + address);
      if (matching.length !== 1 || matching[0].event.method !== event || matching[0].phase.asApplyExtrinsic.toNumber() !== extrinsicIndex || transactionHash(matching[0]) !== txHash) throw new Error('Contract event did not uniquely match the accepted ledger transaction and address');
      const { block } = await api.rpc.chain.getBlock(blockHash);
      const extrinsic = block.extrinsics[extrinsicIndex];
      if (extrinsic.method.section !== 'midnight' || extrinsic.method.method !== 'sendMnTransaction') throw new Error('Accepted ledger event did not belong to midnight.sendMnTransaction');
      return { outcome: 'applied', network: 'undeployed', genesis, finalizedAt: finalHash.toHex(), blockHash: blockHash.toHex(), height: height.toString(), extrinsicIndex, extrinsicHash: extrinsic.hash.toHex(), txHash, contractAddress: '0x' + address, contractEvent: event, ledgerEvent: 'TxApplied' };
    }
    throw new Error('Expected transaction was not found in the finalized scan window');
  } finally { clearTimeout(deadline); await provider.disconnect(); }
}

if (process.argv[1] && pathToFileURL(resolve(process.argv[1])).href === import.meta.url) {
  const [txHash, address, event, fromBlock] = process.argv.slice(2);
  if (!txHash || !address || !event) {
    console.error('Usage: node scripts/localnet/receipt.mjs TX_HASH CONTRACT_ADDRESS ContractDeploy|ContractCall [FROM_BLOCK]');
    process.exitCode = 1;
  } else console.log(JSON.stringify(await observeLocalReceipt({ txHash, address, event, fromBlock }), null, 2));
}
