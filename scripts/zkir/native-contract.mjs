// Assemble ledger-native artifacts from the actual Lean compiler's symbolic plan.
import assert from 'node:assert/strict';
import {readFile,writeFile,mkdir} from 'node:fs/promises';
import {resolve,join} from 'node:path';
import {createHash} from 'node:crypto';
import * as l from '@midnight-ntwrk/ledger-v9';
import * as z from '@midnightntwrk/zkir-v3';
import {empty,createState,callPrototype} from './native-runtime.mjs';
const [planPath,circuitPath,proverPath,verifierPath,outputPath,...options]=process.argv.slice(2);
let paramsPath,configPath,prove=false;
for(let index=0;index<options.length;index++){
 const option=options[index];
 if(option==='--prove'){if(prove)throw Error('Duplicate --prove');prove=true;continue;}
 if(!['--ledger-params','--config'].includes(option))throw Error(`Unknown option ${option}`);
 const value=options[++index];if(!value||value.startsWith('--'))throw Error(`Missing value for ${option}`);
 if(option==='--ledger-params'){if(paramsPath)throw Error('Duplicate --ledger-params');paramsPath=value;}
 else{if(configPath)throw Error('Duplicate --config');configPath=value;}
}
if(!outputPath||!paramsPath||!configPath)throw Error('Usage: node native-contract.mjs SOURCE_PLAN.json ENTRYPOINT.zkir KEY.prover KEY.verifier OUTPUT_DIRECTORY --ledger-params LEDGER.params --config INPUTS.json [--prove]');
const plan=JSON.parse(await readFile(planPath,'utf8')),config=JSON.parse(await readFile(configPath,'utf8'));
assert.equal(plan.schemaVersion,1);
if(typeof plan.entrypoint!=='string'||!/^[_A-Za-z][_A-Za-z0-9]*$/.test(plan.entrypoint))throw Error('Unsafe native entrypoint artifact name');
const out=resolve(outputPath);await mkdir(join(out,'keys'),{recursive:true});await mkdir(join(out,'zkir'),{recursive:true});
const json=await readFile(circuitPath,'utf8');assert.equal(JSON.parse(json).do_communications_commitment,true);
const ir=z.Zkir.fromJson(json),material={ir:ir.serialize(),proverKey:await readFile(proverPath),verifierKey:await readFile(verifierPath)};
const parameters=l.LedgerParameters.deserialize(await readFile(paramsPath));
const operation=new l.ContractOperation();operation.verifierKey=material.verifierKey;
const state=new l.ContractState();state.data=createState(plan,config.state);state.setOperation(plan.entrypoint,operation);state.maintenanceAuthority=new l.ContractMaintenanceAuthority([],1);
const deployment=new l.ContractDeploy(state),ttl=new Date(Date.now()+3600000);
const deploymentIntent=l.Intent.new(ttl).addDeploy(deployment);
const built=callPrototype(plan,config.inputs,state,deployment.address,operation,parameters);
const callIntent=l.Intent.new(ttl).addCall(built.prototype);
const preimage=l.proofDataIntoSerializedPreimage(empty,empty,built.program,built.privateOutputs,plan.entrypoint);
const activity=await z.check(preimage,{lookupKey:async()=>material});assert.equal(activity.length,built.program.length);
const predicted=new l.ContractState();predicted.data=built.after.state;predicted.setOperation(plan.entrypoint,operation);predicted.maintenanceAuthority=state.maintenanceAuthority;
for(const [name,bytes]of [['keys/'+plan.entrypoint+'.prover',material.proverKey],['keys/'+plan.entrypoint+'.verifier',material.verifierKey],['zkir/'+plan.entrypoint+'.zkir',json],['zkir/'+plan.entrypoint+'.bzkir',material.ir],['initial-state.bin',state.serialize()],['deploy-intent.bin',deploymentIntent.serialize()],['call-intent.bin',callIntent.serialize()],['predicted-state.bin',predicted.serialize()],['source-plan.json',JSON.stringify(plan)],['runtime-config.json',JSON.stringify(config)],['ledger.params',await readFile(paramsPath)]])await writeFile(join(out,name),bytes,{mode:0o600});
const summary={qualification:'source-driven native artifact assembly; no ledger acceptance',address:deployment.address,entrypoint:plan.entrypoint,k:ir.getK(),operationBytes:operation.serialize().length,guaranteedOps:built.guaranteed?.program.length??0,fallibleOps:built.fallible?.program.length??0,sourcePlanSha256:createHash('sha256').update(await readFile(planPath)).digest('hex'),nativeCircuitSha256:createHash('sha256').update(json).digest('hex'),ledgerParametersSha256:createHash('sha256').update(await readFile(paramsPath)).digest('hex'),officialPreprocessing:true,cryptographicProofGenerated:false,transactionSubmitted:false};
if(prove){
 const url=new URL(process.env.NIGHTLEAN_PROOF_SERVER??'http://127.0.0.1:16300');if(!['http:','https:'].includes(url.protocol)||!['127.0.0.1','localhost','[::1]'].includes(url.hostname)||url.username||url.password)throw Error('Witness proving requires a loopback service');
 const response=await fetch(new URL('/prove',url),{method:'POST',body:l.createProvingPayload(preimage,42n,material),redirect:'error',signal:AbortSignal.timeout(120000)});const proof=Buffer.from(await response.arrayBuffer());if(!response.ok)throw Error(proof.toString());await writeFile(join(out,'native-claim.proof'),proof,{mode:0o600});summary.cryptographicProofGenerated=true;summary.proofBytes=proof.length;
}
await writeFile(join(out,'native-contract.json'),JSON.stringify(summary,null,2));console.log(JSON.stringify(summary,null,2));
