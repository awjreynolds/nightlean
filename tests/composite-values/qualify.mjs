// Raw witnesses bypass the evaluator. This qualifies a standalone relation, not ledger acceptance.
import assert from 'node:assert/strict';
import {readFile,writeFile} from 'node:fs/promises';
import {resolve,join,dirname} from 'node:path';
import {pathToFileURL} from 'node:url';
import {createHash} from 'node:crypto';
import {createProvingPayload} from '../../scripts/zkir/node_modules/@midnight-ntwrk/ledger-v9/midnight_ledger_wasm_v9_fs.js';

const [directory,checkerPath,mode='check']=process.argv.slice(2);
if(!directory||!checkerPath||!['check','prove'].includes(mode))
  throw Error('Usage: node tests/composite-values/qualify.mjs DIRECTORY PINNED_CHECKER_MODULE check|prove');
const checkerDirectory=dirname(resolve(checkerPath));
const checkerPackage=JSON.parse(await readFile(join(checkerDirectory,'package.json'),'utf8'));
assert.equal(checkerPackage.name,'@midnightntwrk/zkir-v3');
assert.equal(checkerPackage.version,'3.2.1');
const checkerWasmSha256=createHash('sha256').update(await readFile(join(checkerDirectory,'midnight_zkir_wasm_bg.wasm'))).digest('hex');
assert.equal(checkerWasmSha256,'3568fafaf225469dbbd038b0236d1b6b76e0da19da565caba33efe2ceb682cfc');
const {Zkir,check}=await import(pathToFileURL(resolve(checkerPath)).href);
const modulus=52435875175126190479447740508185965837690552500527637822603658699938581184513n;
function compact(value){
  let n=BigInt(value);
  assert.ok(n>=0n&&n<modulus);
  const bytes=(v,count)=>Buffer.from(Array.from({length:count},()=>{const b=Number(v&255n);v>>=8n;return b;}));
  if(n<64n)return bytes(n<<2n,1);
  if(n<16384n)return bytes((n<<2n)|1n,2);
  if(n<1073741824n)return bytes((n<<2n)|2n,4);
  const output=[];while(n){output.push(Number(n&255n));n>>=8n;}
  return Buffer.from([((output.length-4)<<2)|3,...output]);
}
const vector=values=>Buffer.concat([compact(values.length),...values.map(compact)]);
function preimage(test){
  const key=Buffer.from('nightlean/aggregate/qualification');
  return Buffer.concat([Buffer.from('midnight:proof-preimage:'),vector([]),vector(test.private),
    vector(test.publicInputs),vector(test.publicReads),compact(42),Buffer.from([0]),compact(key.length),key]);
}
const source=await readFile(join(directory,'aggregate.zkir'),'utf8');
const relation=Zkir.fromJson(source),ir=relation.serialize();
const material={ir,proverKey:new Uint8Array(),verifierKey:new Uint8Array()};
if(mode==='prove'){
  material.proverKey=await readFile(join(directory,'aggregate.prover'));
  material.verifierKey=await readFile(join(directory,'aggregate.verifier'));
}
const cases=JSON.parse(await readFile(join(directory,'cases.json'),'utf8'));
const nativeSchema=JSON.parse(await readFile(join(directory,'native-schema.json'),'utf8'));
const codecSchema=JSON.parse(await readFile(new URL('../../runtime/tests/fixtures/aggregates/schema.json',import.meta.url),'utf8'));
assert.deepEqual(nativeSchema,codecSchema,'native and host schema traversal differ');
const canonicalLeaves=JSON.parse(await readFile(new URL('../../runtime/tests/fixtures/aggregates/leaves.json',import.meta.url),'utf8'));
assert.deepEqual(cases[0].private.slice(0,-1),canonicalLeaves,'native and host leaf order differs');

const results=[];
for(const test of cases){
  let failure,activity;
  try{activity=await check(preimage(test),{lookupKey:async()=>material});}catch(error){failure=error;}
  assert.equal(!failure,test.accepted,`${test.id}: ${failure?.message??'invalid witness accepted'}`);
  if(!failure)assert.equal(activity.length,test.activityGroups,test.id);
  results.push({id:test.id,accepted:!failure});
}
// Separately change the Impact-bound output sequence, leaving public inputs valid.
const changed={...cases[0],publicInputs:[...cases[0].publicInputs]};
changed.publicInputs[changed.publicReads.length]='201';
await assert.rejects(()=>check(preimage(changed),{lookupKey:async()=>material}));
results.push({id:'TYV-CHANGED-BOUND-OUTPUT',accepted:false});
const evidence={scope:'typed backend standalone aggregate relation; source aggregate effects gated on DF-01; no ledger acceptance',
  nativeVersion:checkerPackage.version,checkerWasmSha256,k:relation.getK(),sourceSha256:createHash('sha256').update(source).digest('hex'),
  binarySha256:createHash('sha256').update(ir).digest('hex'),
  schemaSha256:createHash('sha256').update(JSON.stringify(nativeSchema)).digest('hex'),hostSchemaAndLeafOrderMatch:true,cases:results};
if(mode==='prove'){
  const server=new URL(process.env.NIGHTLEAN_PROOF_SERVER??'http://127.0.0.1:16300');
  assert.ok(['http:','https:'].includes(server.protocol)&&['127.0.0.1','localhost','[::1]'].includes(server.hostname)&&!server.username&&!server.password);
  const payload=createProvingPayload(preimage(cases[0]),42n,material);
  const response=await fetch(new URL('/prove',server),{method:'POST',body:payload,redirect:'error',signal:AbortSignal.timeout(120000)});
  const proof=Buffer.from(await response.arrayBuffer());
  assert.ok(response.ok,`native prover ${response.status}: ${proof.toString()}`);
  assert.ok(proof.length>0);
  await writeFile(join(directory,'aggregate.proof'),proof,{mode:0o600});
  evidence.proof={bytes:proof.length,sha256:createHash('sha256').update(proof).digest('hex'),nativeServerSelfVerified:true};
}
if(mode==='prove')await writeFile(join(directory,'qualification.json'),JSON.stringify(evidence,null,2)+'\n');
console.log(JSON.stringify(evidence,null,2));
