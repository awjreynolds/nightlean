import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { mkdir, readFile, writeFile, symlink, realpath } from 'node:fs/promises';
import { resolve } from 'node:path';
import { createHash } from 'node:crypto';
import { setTimeout as sleep } from 'node:timers/promises';
const exec = promisify(execFile);
const [artifactArg, workArg] = process.argv.slice(2);
if (!artifactArg || !workArg) throw new Error('usage: node deploy-claim.mjs COMPILED_DIRECTORY WORK_DIRECTORY');
const artifacts = await realpath(artifactArg), work = resolve(workArg);
await mkdir(work, { recursive: true });
const params = await realpath(process.env.NIGHTLEAN_PROOF_CACHE ?? '/private/tmp/authzk-compact036-params');
const jsImage = 'midnightntwrk/midnight-node-toolkit@sha256:edcfc892eafc850c60db58045e6f2575d600cd84dc30a73e35bf9f5086dcc24f';
const nativeImage = 'midnightntwrk/midnight-node-toolkit@sha256:904f824f3350530bc2fb03448906cc5f9f200b98e98bd9fbb274a1cc25b9f89c';
const coin = '1bd4f827be97ff013c4a702e4b08f30ec378728a54670cf7cc92cb9b1a14eff6';
const root = '28399696706114328615841781920356350076672934126225635254148383513591039775413';
const campaign = '9', nullifier = '16533581147424469099777953019315187868248076859940057971562926865714239641352';
const rpc = async (method, params=[]) => {
  const res = await fetch('http://127.0.0.1:19944', { method:'POST', headers:{'content-type':'application/json'},body:JSON.stringify({jsonrpc:'2.0',id:1,method,params}) });
  const body=await res.json();if(body.error)throw Error('local RPC failed');return body.result;
};
if (await rpc('chain_getBlockHash',[0]) !== '0x823383ec0302be8417cfcbcc62f21df08f4047bca37aaea89e3f54b550ebae1d') throw Error('Refusing non-development genesis');
const run = async (javascript,args,offline=false) => {
  const cmd=['run','--rm','--pull','never','--network',offline?'none':'nightlean-dev','--cpus=4','--memory=4g','--pids-limit=256','--cap-drop','ALL','--security-opt','no-new-privileges','--user',`${process.getuid()}:${process.getgid()}`,'--workdir','/work','--mount',`type=bind,source=${work},target=/work`,'--mount',`type=bind,source=${artifacts},target=/work/out,readonly`,'--mount',`type=bind,source=${params},target=/params,readonly`,'--env','MIDNIGHT_PP=/params','--env','MN_FETCH_CACHE=inmemory','--env','MN_LEDGER_CACHE_DB=','--env','NODE_OPTIONS=--max-old-space-size=768','--env','COMPACTC_VERSION=0.36.0','--entrypoint',javascript?'node':'/midnight-node-toolkit',javascript?jsImage:nativeImage,...javascript?['/toolkit-js/dist/bin.js']:[],...args];
  return await exec('docker',cmd,{timeout:120000,maxBuffer:2**22});
};
await symlink('/toolkit-js/node_modules',`${work}/node_modules`).catch(e=>{if(e.code!=='EEXIST')throw e;});
// All values below are public development fixtures. The seeded chain identity never leaves localnet.
const config = `import { CompiledContract, ContractExecutable } from '@midnight-ntwrk/compact-js/effect';
import { Contract } from './out/contract/index.js';
const witnesses = Object.fromEntries(['secret','sibling0','sibling1','direction0','direction1'].map(name => ['w_claim_' + name, ({privateState}: {privateState: Record<string, any>}) => [privateState, name.startsWith('direction') ? privateState[name] : BigInt(privateState[name])]]));
export default { contractExecutable: CompiledContract.make('PrivateClaim',Contract).pipe(CompiledContract.withWitnesses(witnesses),CompiledContract.withCompiledFileAssets('./out'),ContractExecutable.make), createInitialPrivateState:()=>({secret:'42',sibling0:'17',sibling1:'23',direction0:false,direction1:true}),config:{keys:{coinPublic:'${coin}'},network:'undeployed'}};`;
await writeFile(`${work}/contract.config.ts`,config);
const context=['-c','/work/contract.config.ts','--coin-public',coin,'--ledger-era','9'];
const commonOutputs=['--output','/work/intent.bin','--output-ps','/work/candidate.json','--output-zswap','/work/zswap.json'];
async function buildAndSubmit(filename) {
  await run(false,['send-intent','--src-url','ws://nightlean-dev-node:9944','--compiled-contract-dir','/work/out','--intent-file','/work/intent.bin','--zswap-state-file','/work/zswap.json','--funding-seed','00..01','--proof-server','http://nightlean-dev-proof:6300','--dest-file',`/work/${filename}`]);
  const shown=await run(false,['show-transaction','--src-file',`/work/${filename}`]);
  const hash=[...`${shown.stdout}\n${shown.stderr}`.matchAll(/Midnight \(\d+ bytes\) hash: (0x[0-9a-f]{64})/g)][0]?.[1];
  if(!hash)throw Error('No ledger transaction hash');
  await run(false,['generate-txs',`--src-file=/work/${filename}`,'send','-d','ws://nightlean-dev-node:9944']);
  return hash;
}
console.error('Generating deployment intent');
await run(true,['deploy',...context,...commonOutputs,root,campaign],true);
console.error('Proving and submitting deployment');
const deployHash=await buildAndSubmit('deploy.mn');
const address=(await run(false,['contract-address','--src-file','/work/deploy.mn'])).stdout.trim();
if(!/^[0-9a-f]{64}$/.test(address))throw Error('Unexpected contract address');
const state=async destination => run(false,['contract-state','--src-url','ws://nightlean-dev-node:9944','--contract-address',address,'--dest-file',`/work/${destination}`]);
for(let i=0;;i++){try{await state('before.mn');break;}catch(e){if(i===29)throw e;await sleep(1000);}}
const parameters=(await run(false,['show-ledger-parameters','--read-from-rpc-url','ws://nightlean-dev-node:9944','--serialize'])).stdout.trim();
await writeFile(`${work}/ledger.params`,Buffer.from(parameters,'hex'));
await writeFile(`${work}/private.json`,JSON.stringify({secret:'42',sibling0:'17',sibling1:'23',direction0:false,direction1:true}));
const digest=async file=>createHash('sha256').update(await readFile(`${work}/${file}`)).digest('hex');
const invoke=(callRoot=root,callNullifier=nullifier)=>run(true,['circuit',...context,'--input','/work/before.mn','--input-ps','/work/private.json','--input-ledger-params','/work/ledger.params',...commonOutputs,'--output-oc','/work/predicted.mn','--output-result','/work/result.json',address,'claim',callRoot,campaign,callNullifier],true);
const validPrivate={secret:'42',sibling0:'17',sibling1:'23',direction0:false,direction1:true};
const negatives=[];
for(const [name,privateChange,callRoot,callNullifier] of [
 ['secret',{secret:'43'},root,nullifier],['path',{sibling0:'18'},root,nullifier],
 ['direction',{direction0:true},root,nullifier],['root',{},String(BigInt(root)+1n),nullifier],
 ['nullifier',{},root,String(BigInt(nullifier)+1n)]
]){
 console.error(`Checking invalid ${name}`);
 await writeFile(`${work}/private.json`,JSON.stringify({...validPrivate,...privateChange}));
 let rejected=false;
 try{await invoke(callRoot,callNullifier);}catch(e){if(!/assert|constraint|mismatch|failed/i.test(`${e.stdout}\n${e.stderr}`))throw e;rejected=true;}
 if(!rejected)throw Error(`Invalid ${name} accepted`);
 await state(`after-invalid-${name}.mn`);
 if(await digest(`after-invalid-${name}.mn`)!==await digest('before.mn'))throw Error(`Invalid ${name} changed state`);
 negatives.push(name);
}
await writeFile(`${work}/private.json`,JSON.stringify(validPrivate));
await invoke();
console.error('Proving and submitting valid claim');
const claimHash=await buildAndSubmit('claim.mn');
for(let i=0;;i++){await state('observed.mn');if(await digest('observed.mn')===await digest('predicted.mn'))break;if(i===29)throw Error('Observed ledger state differs from predicted state');await sleep(1000);}
await writeFile(`${work}/before.mn`,await readFile(`${work}/observed.mn`));
console.error('Checking replay rejection');
let replayRejected=false;
try{await invoke();}catch(e){if(!`${e.stdout}\n${e.stderr}`.includes('spent'))throw e;replayRejected=true;}
if(!replayRejected)throw Error('Repeated nullifier accepted');
await state('after-replay.mn');
if(await digest('after-replay.mn')!==await digest('observed.mn'))throw Error('Replay changed state');
console.log(JSON.stringify({network:'undeployed',address,deployHash,claimHash,replayRejected,negatives,publicStateSha256:await digest('observed.mn')}));
