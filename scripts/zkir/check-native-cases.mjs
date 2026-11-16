import assert from 'node:assert/strict';
import {readFile,writeFile} from 'node:fs/promises';
import * as l from '@midnight-ntwrk/ledger-v9';
import * as z from '@midnightntwrk/zkir-v3';
import {callPrototype,empty,environment,evaluate} from './native-runtime.mjs';
const [directory,statePath,mode='negative']=process.argv.slice(2);
if(!directory||!statePath||!['negative','replay'].includes(mode))throw Error('Usage: node check-native-cases.mjs ARTIFACT_DIRECTORY STATE.bin negative|replay');
const plan=JSON.parse(await readFile(`${directory}/source-plan.json`)),config=JSON.parse(await readFile(`${directory}/runtime-config.json`));
const summary=JSON.parse(await readFile(`${directory}/native-contract.json`));
const state=l.ContractState.deserialize(await readFile(statePath));
const operation=new l.ContractOperation();operation.verifierKey=await readFile(`${directory}/keys/${plan.entrypoint}.verifier`);
const parameters=l.LedgerParameters.deserialize(await readFile(`${directory}/ledger.params`));
const ir=z.Zkir.fromJson(await readFile(`${directory}/zkir/${plan.entrypoint}.zkir`,'utf8'));
const provider={lookupKey:async()=>({ir:ir.serialize(),proverKey:new Uint8Array(),verifierKey:new Uint8Array()})};
const before=state.serialize();
async function check(inputs){const call=callPrototype(plan,inputs,state,summary.address,operation,parameters);await z.check(l.proofDataIntoSerializedPreimage(empty,empty,call.program,call.privateOutputs,plan.entrypoint),provider);}
const results=[];
if(mode==='negative'){
 await check(config.inputs);
 const firstNative=plan.circuit.inputs.find(input=>input.type==='Native');
 if(firstNative)assert.throws(()=>environment(plan,{...config.inputs,[firstNative.name]:'042'}),/canonical/);
 const firstBool=plan.circuit.inputs.find(input=>input.type==='Bool');
 if(firstBool)assert.throws(()=>environment(plan,{...config.inputs,[firstBool.name]:'true'}),/Expected boolean/);
 assert.throws(()=>environment(plan,{...config.inputs,__unexpected:'0'}),/Unknown native input/);
 assert.throws(()=>evaluate({tag:'select',condition:{tag:'bool',value:true},yes:{tag:'constant',value:'0'},no:{tag:'reference',name:'unbound'}},new Map()),/Unbound/);
 if(!Array.isArray(config.negativeCases)||config.negativeCases.length===0)throw Error('Runtime config must explicitly define negativeCases');
 for(const test of config.negativeCases){
  let rejection;
  try{await check({...config.inputs,...test.inputs});}catch(error){rejection=error.message;}
  if(!rejection)throw Error(`Invalid ${test.name} was accepted`);
  if(!/Failed direct assertion|Native VM expected read mismatch/.test(rejection))throw Error(`Unexpected negative failure: ${rejection}`);
  assert.deepEqual(state.serialize(),before,'Rejected case changed native state');
  results.push({name:test.name,rejected:true,reason:rejection});
 }
}else{
 await assert.rejects(()=>check(config.inputs),/Native VM expected read mismatch/,'Spent nullifier must fail against accepted native state');
 assert.deepEqual(state.serialize(),before,'Replay changed native state');
 results.push({name:'replay',rejected:true,reason:'Native VM spent-nullifier read mismatch'});
}
await writeFile(`${directory}/${mode}-checks.json`,JSON.stringify(results,null,2));
console.log(JSON.stringify({mode,results,stateUnchanged:true}));
