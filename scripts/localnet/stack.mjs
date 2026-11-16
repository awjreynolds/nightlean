import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { access, cp, mkdir, readFile } from 'node:fs/promises';
import { createHash } from 'node:crypto';
import { join, resolve } from 'node:path';
import { setTimeout as sleep } from 'node:timers/promises';

const exec = promisify(execFile);
const name = 'nightlean-dev';
const label = 'org.nightlean.localnet';
const params = resolve(process.env.NIGHTLEAN_PROOF_CACHE ?? '/private/tmp/nightlean-proof-params');
const images = {
  node: 'midnightntwrk/midnight-node@sha256:0c1ad548d523c1109aa1f16daab1bf72dcb78c7e17b8a8c6d97424ad0eba7b8a',
  relay: 'node@sha256:e67514e5d0f6c46656005e1b693b2ec9d52e80b641307de684d4a015ba7a4eaf',
  toolkit: 'midnightntwrk/midnight-node-toolkit@sha256:904f824f3350530bc2fb03448906cc5f9f200b98e98bd9fbb274a1cc25b9f89c',
  proof: 'midnightntwrk/proof-server@sha256:5617e26aa76d06c44f4bee667c37eb71ccf02fefe0e5848100fa84001282d515',
  indexer: 'midnightntwrk/indexer-standalone@sha256:119f35db548ba1c390845f215bb1e928e73038bef7c315825aee0461bd54499d',
};
const endpoints = { networkId: 'undeployed', node: 'http://127.0.0.1:19944', nodeWs: 'ws://127.0.0.1:19944', proof: 'http://127.0.0.1:16300', indexer: 'http://127.0.0.1:18088/api/v4/graphql', indexerWs: 'ws://127.0.0.1:18088/api/v4/graphql/ws', genesis: '0x823383ec0302be8417cfcbcc62f21df08f4047bca37aaea89e3f54b550ebae1d' };
async function docker(args) { return (await exec('docker', args, { timeout: 120_000, maxBuffer: 2 ** 20 })).stdout.trim(); }
async function exists(container) { try { return JSON.parse(await docker(['inspect', container]))[0]; } catch { return undefined; } }
async function start(role, args) {
  const container = `${name}-${role}`;
  const prior = await exists(container);
  if (prior) {
    if (prior.Config.Labels?.[label] !== name) throw new Error(`Container name belongs to another owner: ${container}`);
    if (!prior.State.Running) await docker(['start', container]);
    return;
  }
  await docker(['run', '-d', '--pull', 'never', '--name', container, '--label', `${label}=${name}`, '--cap-drop', 'ALL', '--security-opt', 'no-new-privileges', '--cpus=2', '--memory=3g', '--pids-limit=512', ...args]);
}
async function rpc(method, params = []) {
  const response = await fetch(endpoints.node, { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({ jsonrpc: '2.0', id: 1, method, params }), signal: AbortSignal.timeout(3000) });
  const body = await response.json();
  if (!response.ok || body.error) throw new Error(`RPC failed: ${method}`);
  return body.result;
}
async function waitFor(check, title) {
  for (let attempt = 0; attempt < 60; attempt++) {
    try { if (await check()) return; } catch { /* Service starts asynchronously. */ }
    await sleep(1000);
  }
  throw new Error(`Timed out waiting for ${title}`);
}
async function prepareProofCache() {
  await mkdir(params, { recursive: true });
  for (const source of [process.env.NIGHTLEAN_PROOF_CACHE_SOURCE, process.env.NIGHTLEAN_PROOF_CACHE_EXTRA_SOURCE].filter(Boolean)) {
    if (resolve(source) === params) throw new Error('Proof cache source and destination must differ');
    await cp(resolve(source), params, { recursive: true, force: false, dereference: true });
  }
  const k9 = await readFile(join(params, 'bls_midnight_2p9'));
  if (createHash('sha256').update(k9).digest('hex') !== 'b9009f1098bcefffec3c461ab3a5e3a17f7e5599f0f08c70fcdc55a89227bcbd') {
    throw new Error('k9 SRS digest does not match the qualified official parameter');
  }
}
async function startProof() {
  await start('proof', ['--network', name, '--mount', `type=bind,source=${params},target=/params`, '--env', 'MIDNIGHT_PP=/params', '--env', 'MIDNIGHT_PROOF_SERVER_JOB_CAPACITY=2', images.proof]);
  await waitFor(async () => (await fetch(`${endpoints.proof}/health`, { signal: AbortSignal.timeout(2000) })).ok, 'proof server');
}
async function startRelay() {
  const relay = "const net=require('net'); for(const [port,host,target] of [[9944,'nightlean-dev-node',9944],[6300,'nightlean-dev-proof',6300],[8088,'nightlean-dev-indexer',8088]]) net.createServer(s=>{const t=net.connect(target,host);s.pipe(t);t.pipe(s);s.on('error',()=>t.destroy());t.on('error',()=>s.destroy());}).listen(port,'0.0.0.0');";
  await start('relay', ['--read-only', '-p', '127.0.0.1:19944:9944', '-p', '127.0.0.1:16300:6300', '-p', '127.0.0.1:18088:8088', '--entrypoint', 'node', images.relay, '-e', relay]);
  const relayInfo = await exists(`${name}-relay`);
  if (!relayInfo.NetworkSettings.Networks[name]) await docker(['network', 'connect', name, `${name}-relay`]);
  await waitFor(async () => Boolean(await rpc('system_health')), 'node relay');
}
if (process.argv[2] === 'down') {
  for (const role of ['relay', 'indexer', 'proof', 'node']) {
    const prior = await exists(`${name}-${role}`);
    if (prior?.Config.Labels?.[label] === name) await docker(['rm', '-f', `${name}-${role}`]);
  }
  const networks = await docker(['network', 'ls', '--filter', `label=${label}=${name}`, '--format', '{{.Name}}']);
  if (networks.split('\n').includes(name)) await docker(['network', 'rm', name]);
  console.log(JSON.stringify({ stopped: name }));
} else if (process.argv[2] === 'restart-proof') {
  await prepareProofCache();
  const prior = await exists(`${name}-proof`);
  if (prior && prior.Config.Labels?.[label] !== name) throw new Error('Proof container belongs to another owner');
  if (prior) await docker(['rm', '-f', `${name}-proof`]);
  await startProof();
  console.log(JSON.stringify({ proof: endpoints.proof, cache: params, healthy: true }));
} else if (process.argv[2] === 'restart-relay') {
  const beforeHash = await rpc('chain_getFinalizedHead');
  const before = await rpc('chain_getHeader', [beforeHash]);
  if (await rpc('chain_getBlockHash', [0]) !== endpoints.genesis) throw new Error('Development genesis mismatch');
  const prior = await exists(`${name}-relay`);
  if (prior && prior.Config.Labels?.[label] !== name) throw new Error('Relay container belongs to another owner');
  await docker(['image', 'inspect', images.relay]);
  if (prior) await docker(['rm', '-f', `${name}-relay`]);
  await startRelay();
  const afterHash = await rpc('chain_getFinalizedHead');
  const after = await rpc('chain_getHeader', [afterHash]);
  if (await rpc('chain_getBlockHash', [0]) !== endpoints.genesis || BigInt(after.number) < BigInt(before.number)) throw new Error('Chain state changed unexpectedly during relay replacement');
  await waitFor(async () => (await fetch(`${endpoints.proof}/health`, { signal: AbortSignal.timeout(2000) })).ok, 'proof relay');
  await waitFor(async () => {
    const response = await fetch(endpoints.indexer, { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({ query: '{__typename}' }), signal: AbortSignal.timeout(2000) });
    return (await response.json()).data?.__typename === 'Query';
  }, 'indexer relay');
  console.log(JSON.stringify({ relay: images.relay, healthy: true, genesis: endpoints.genesis, finalizedHeightBefore: BigInt(before.number).toString(), finalizedHeightAfter: BigInt(after.number).toString(), finalizedHashAfter: afterHash }));
} else if (process.argv[2] === 'up') {
  await prepareProofCache();
  await access(params);
  for (const image of Object.values(images)) await docker(['image', 'inspect', image]);
  const networks = await docker(['network', 'ls', '--format', '{{.Name}}']);
  if (!networks.split('\n').includes(name)) await docker(['network', 'create', '--internal', '--label', `${label}=${name}`, name]);
  await start('node', ['--network', name, '--env', 'CFG_PRESET=dev', images.node, '--dev', '--force-authoring', '--base-path', '/tmp/nightlean-dev', '--no-telemetry', '--reserved-only', '--state-pruning', 'archive', '--blocks-pruning', 'archive', '--rpc-external', '--rpc-cors', 'all']);
  await startRelay();
  await waitFor(async () => Number.parseInt(await rpc('chain_getHeader').then((h) => h.number), 16) >= 1, 'development block one');
  if (await rpc('chain_getBlockHash', [0]) !== endpoints.genesis) throw new Error('Development genesis mismatch');
  await startProof();
  await start('indexer', ['--network', name, '--env', 'APP__INFRA__NODE__URL=ws://nightlean-dev-node:9944', '--env', 'APP__APPLICATION__NETWORK_ID=undeployed', '--env', `APP__INFRA__SECRET=${'1'.repeat(64)}`, '--env', 'APP__INFRA__SPO_NODE__URL=ws://nightlean-dev-node:9944', '--env', 'APP__INFRA__SPO_NODE__BLOCKFROST_ID=synthetic', images.indexer]);
  await waitFor(async () => (await fetch(`${endpoints.proof}/health`, { signal: AbortSignal.timeout(2000) })).ok, 'proof server');
  await waitFor(async () => {
    const response = await fetch(endpoints.indexer, { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({ query: '{__typename}' }), signal: AbortSignal.timeout(2000) });
    return (await response.json()).data?.__typename === 'Query';
  }, 'indexer');
  console.log(JSON.stringify({ ...endpoints, containers: name, runtime: await rpc('state_getRuntimeVersion'), images }, null, 2));
} else {
  console.error('Usage: node scripts/localnet/stack.mjs up|down|restart-proof|restart-relay');
  process.exitCode = 1;
}
