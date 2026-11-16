// Independent raw-ZKIR semantic fixtures. No Compact compiler or runtime is loaded.
import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {resolve} from 'node:path';
import {pathToFileURL} from 'node:url';
const [checkerPath]=process.argv.slice(2);
if(!checkerPath)throw Error('usage: node tests/zkir321/check-fixtures.mjs OFFICIAL_WASM_FS_MODULE');
const {Zkir,check}=await import(pathToFileURL(resolve(checkerPath)).href);
function compact(value){
 let n=BigInt(value);
 if(n<0n)throw Error('Negative SCALE input');
 const bytes=(v,count)=>Buffer.from(Array.from({length:count},()=>{const b=Number(v&255n);v>>=8n;return b;}));
 if(n<64n)return bytes(n<<2n,1);
 if(n<16384n)return bytes((n<<2n)|1n,2);
 if(n<1073741824n)return bytes((n<<2n)|2n,4);
 const output=[];while(n){output.push(Number(n&255n));n>>=8n;}
 return Buffer.from([((output.length-4)<<2)|3,...output]);
}
const vector=values=>Buffer.concat([compact(values.length),...values.map(compact)]);
const preimage=inputs=>{
 const key=Buffer.from('nightlean/zkir321/qualification');
 return Buffer.concat([Buffer.from('midnight:proof-preimage:'),vector(inputs),vector([]),vector([]),vector([]),compact(42),Buffer.from([0]),compact(key.length),key]);
};
const circuit=Zkir.fromJson(await readFile(new URL('./boolean-deserialization-contract.zkir',import.meta.url),'utf8'));
const material={ir:circuit.serialize(),proverKey:new Uint8Array(),verifierKey:new Uint8Array()};
const cases=JSON.parse(await readFile(new URL('./boolean-cases.json',import.meta.url),'utf8'));
const results=[];
for(const test of cases){
 let activity,error;
 try{activity=await check(preimage([test.byte,test.flag,test.result??'0']),{lookupKey:async()=>material});}catch(cause){error=cause;}
 if(test.accepted){
  assert.equal(error,undefined,`${test.name}: ${error}`);
  assert.deepEqual(activity,[],`${test.name}: unexpected transcript activity`);
 }else assert.ok(error,`${test.name}: invalid value was accepted`);
 results.push({name:test.name,accepted:!error,...(error?{}:{result:test.result})});
}
const jubjub=Zkir.fromJson(await readFile(new URL('./jubjub-intermediate.zkir',import.meta.url),'utf8'));
const jubjubActivity=await check(preimage(['7']),{lookupKey:async()=>({ir:jubjub.serialize(),proverKey:new Uint8Array(),verifierKey:new Uint8Array()})});
assert.deepEqual(jubjubActivity,[]);
console.log(JSON.stringify({qualification:'raw ZKIR contracts only; source deserialization and Jubjub types unimplemented',cases:results,jubjubIntermediate:{accepted:true,k:jubjub.getK()}},null,2));
