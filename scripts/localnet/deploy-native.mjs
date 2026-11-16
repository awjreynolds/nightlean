// Funds and submits ledger-native Nightlean intents on the isolated development chain.
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { readFile, writeFile, mkdir, realpath } from 'node:fs/promises';
import { resolve } from 'node:path';
import { createHash } from 'node:crypto';
import { setTimeout as sleep } from 'node:timers/promises';
import { observeLocalReceipt } from './receipt.mjs';
import {nativeToolkitConfig,nativeToolkitTimeout} from './native-toolkit-config.mjs';
const exec=promisify(execFile);
const [artifactArg,workArg,mode]=process.argv.slice(2);
if(mode && mode!=='--resume-call')throw Error('Unknown mode');
if(!artifactArg||!workArg)throw Error('usage: node deploy-native.mjs NATIVE_ARTIFACT_DIRECTORY WORK_DIRECTORY [--resume-call]');
const artifacts=await realpath(artifactArg),work=resolve(workArg);
await mkdir(work,{recursive:true});
const summary=JSON.parse(await readFile(`${artifacts}/native-contract.json`,'utf8'));
if(!/^[a-f0-9]{64}$/.test(summary.address))throw Error('Invalid native contract address');
const rustAssembly=summary.runtime==='native Rust';
const nativeRuntime=process.env.NIGHTLEAN_NATIVE_RUNTIME;
if(rustAssembly&&!nativeRuntime)throw Error('Rust-assembled artifacts require NIGHTLEAN_NATIVE_RUNTIME pointing to the native runtime executable');
const params=await realpath(process.env.NIGHTLEAN_PROOF_CACHE??'/private/tmp/nightlean-proof-params');
const image='midnightntwrk/midnight-node-toolkit@sha256:904f824f3350530bc2fb03448906cc5f9f200b98e98bd9fbb274a1cc25b9f89c';
const rpc=async(method,params=[])=>{const response=await fetch('http://127.0.0.1:19944',{method:'POST',headers:{'content-type':'application/json'},body:JSON.stringify({jsonrpc:'2.0',id:1,method,params})});const body=await response.json();if(body.error)throw Error('local RPC failed');return body.result;};
if(await rpc('chain_getBlockHash',[0])!=='0x823383ec0302be8417cfcbcc62f21df08f4047bca37aaea89e3f54b550ebae1d')throw Error('Refusing non-development genesis');
const runtime=await rpc('state_getRuntimeVersion');
if(runtime.specVersion!==2001100||runtime.transactionVersion!==4)throw Error('Refusing unsupported development runtime');
const fromBlock=BigInt((await rpc('chain_getHeader')).number).toString();
const toolkit=await nativeToolkitConfig(work);
const run=async args=>await exec('docker',['run','--rm','--pull','never','--network','nightlean-dev','--cpus=4','--memory=4g','--pids-limit=256','--cap-drop','ALL','--security-opt','no-new-privileges','--user',`${process.getuid()}:${process.getgid()}`,'--workdir','/work','--mount',`type=bind,source=${work},target=/work`,'--mount',`type=bind,source=${artifacts},target=/work/artifacts,readonly`,'--mount',`type=bind,source=${params},target=/params,readonly`,'--env','MIDNIGHT_PP=/params','--entrypoint','/midnight-node-toolkit',image,...toolkit.args(args)],{timeout:nativeToolkitTimeout,maxBuffer:2**22});
await writeFile(`${work}/zswap.json`,JSON.stringify({coinPublicKey:{bytes:Array.from(Buffer.from('1bd4f827be97ff013c4a702e4b08f30ec378728a54670cf7cc92cb9b1a14eff6','hex'))},currentIndex:'0',inputs:[],outputs:[]}));
async function submit(intent,filename,event){
 console.error(`Funding and submitting native ${event}`);
 await run(['send-intent','--src-url','ws://nightlean-dev-node:9944','--compiled-contract-dir','/work/artifacts','--intent-file',`/work/artifacts/${intent}`,'--zswap-state-file','/work/zswap.json','--funding-seed','00..01','--proof-server','http://nightlean-dev-proof:6300','--dest-file',`/work/${filename}`]);
 const shown=await run(['show-transaction','--src-file',`/work/${filename}`]);
 const txHash=[...`${shown.stdout}\n${shown.stderr}`.matchAll(/Midnight \(\d+ bytes\) hash: (0x[0-9a-f]{64})/g)][0]?.[1];
 if(!txHash)throw Error('Missing native ledger transaction hash');
 await run(['generate-txs',`--src-file=/work/${filename}`,'send','-d','ws://nightlean-dev-node:9944']);
 for(let i=0;;i++)try{return await observeLocalReceipt({txHash,address:summary.address,event,fromBlock});}catch(error){if(i===20||!error.message.includes('not found'))throw error;await sleep(1000);}
}
let negativeChecks;
if(rustAssembly){
 const checked=await exec(nativeRuntime,[artifacts],{timeout:30000,maxBuffer:2**20});
 const result=JSON.parse(checked.stdout);
 if(!result.validCheck||!result.stateUnchangedOnRejection||!result.negativeChecks?.length||result.negativeChecks.some(value=>!value.rejected))throw Error('Native runtime preflight checks failed');
 negativeChecks=result.negativeChecks;
}else{
 await exec(process.execPath,[new URL('../zkir/check-native-cases.mjs',import.meta.url).pathname,artifacts,`${artifacts}/initial-state.bin`,'negative'],{timeout:30000,maxBuffer:2**20});
 negativeChecks=JSON.parse(await readFile(`${artifacts}/negative-checks.json`));
}
const deployment=mode==='--resume-call' ? JSON.parse(await readFile(`${work}/deployment-receipt.json`,'utf8')) : await submit('deploy-intent.bin','native-deploy.mn','ContractDeploy');
if(deployment.contractAddress!=='0x'+summary.address)throw Error('Resume contract address mismatch');
await writeFile(`${work}/deployment-receipt.json`,JSON.stringify(deployment,null,2));
const call=await submit('call-intent.bin','native-call.mn','ContractCall');
await run(['contract-state','--src-url','ws://nightlean-dev-node:9944','--contract-address',summary.address,'--dest-file','/work/observed-state.bin']);
const observed=await readFile(`${work}/observed-state.bin`),predicted=await readFile(`${artifacts}/predicted-state.bin`);
if(!observed.equals(predicted))throw Error('Native accepted state differs from predicted state');
if(rustAssembly){
 const checked=await exec(nativeRuntime,[artifacts,'--check-state',`${work}/observed-state.bin`,'--expect-rejection'],{timeout:30000,maxBuffer:2**20});
 if(JSON.parse(checked.stdout).rejected!==true)throw Error('Native runtime accepted replay against fetched state');
}else await exec(process.execPath,[new URL('../zkir/check-native-cases.mjs',import.meta.url).pathname,artifacts,`${work}/observed-state.bin`,'replay'],{timeout:30000,maxBuffer:2**20});
await run(['contract-state','--src-url','ws://nightlean-dev-node:9944','--contract-address',summary.address,'--dest-file','/work/after-replay-state.bin']);
if(!(await readFile(`${work}/after-replay-state.bin`)).equals(observed))throw Error('Rejected replay changed ledger state');
const evidence={negativeChecks,replayRejected:true,replayTransactionSubmitted:false,artifactAssembly:rustAssembly?'native Rust':'JavaScript conformance reference',executionChecks:rustAssembly?'native Rust':'JavaScript conformance reference',orchestration:'Node localnet harness and native funding/proof toolkit',route:'Lean ZKIR and native ledger artifacts, without Compact',network:'undeployed',address:summary.address,deployment,call,stateMatches:true,stateSha256:createHash('sha256').update(observed).digest('hex')};
await writeFile(`${work}/native-localnet.json`,JSON.stringify(evidence,null,2));
console.log(JSON.stringify(evidence,null,2));
