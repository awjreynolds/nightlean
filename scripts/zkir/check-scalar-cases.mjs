// Source-generated circuits checked with raw witnesses, bypassing the Noctium evaluator.
import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {resolve,join} from 'node:path';
import {pathToFileURL} from 'node:url';

const [directory,checkerPath,casesPath,...extra]=process.argv.slice(2);
if(!directory||extra.length)throw Error('Usage: node scripts/zkir/check-scalar-cases.mjs EMITTED_DIRECTORY [OFFICIAL_CHECKER_MODULE [CASES_JSON]]');
const {Zkir,check}=checkerPath?await import(pathToFileURL(resolve(checkerPath)).href):await import('@midnightntwrk/zkir-v3');
const cases=JSON.parse(await readFile(casesPath?resolve(casesPath):new URL('../../tests/scalars/constraint-cases.json',import.meta.url),'utf8'));
const modulus=52435875175126190479447740508185965837690552500527637822603658699938581184513n;
function scaleCompact(value){
 let n=BigInt(value);
 assert.ok(n>=0n&&n<modulus,'fixture value must be a canonical field integer');
 const bytes=(v,count)=>Buffer.from(Array.from({length:count},()=>{const b=Number(v&255n);v>>=8n;return b;}));
 if(n<64n)return bytes(n<<2n,1);
 if(n<16384n)return bytes((n<<2n)|1n,2);
 if(n<1073741824n)return bytes((n<<2n)|2n,4);
 const output=[];while(n){output.push(Number(n&255n));n>>=8n;}
 return Buffer.from([((output.length-4)<<2)|3,...output]);
}
const vector=values=>Buffer.concat([scaleCompact(values.length),...values.map(scaleCompact)]);
function preimage(test){
 const key=Buffer.from('noctium/scalars/conformance');
 return Buffer.concat([Buffer.from('midnight:proof-preimage:'),vector([]),
  vector(test.private),vector(test.publicInputs),vector(test.publicReads),scaleCompact(42),
  Buffer.from([0]),scaleCompact(key.length),key]);
}
const circuits=new Map(),results=[];
for(const test of cases){
 assert.match(test.circuit,/^[A-Za-z][A-Za-z0-9]*$/);
 if(!circuits.has(test.circuit)){
  const relation=Zkir.fromJson(await readFile(join(directory,test.circuit+'.zkir'),'utf8'));
  circuits.set(test.circuit,{ir:relation.serialize(),proverKey:new Uint8Array(),verifierKey:new Uint8Array()});
 }
 let failure,activity;
 try{activity=await check(preimage(test),{lookupKey:async()=>circuits.get(test.circuit)});}catch(error){failure=error;}
 assert.equal(!failure,test.accepted,`${test.id}: ${failure??'invalid raw witness accepted'}`);
 if(!failure)assert.equal(activity.length,test.activityGroups,`${test.id}: activity groups`);
 results.push({id:test.id,accepted:!failure});
}
console.log(JSON.stringify({scope:'raw-witness checks of actual Lean-generated scalar circuits; no proof or ledger submission',cases:results},null,2));
