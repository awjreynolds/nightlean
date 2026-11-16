// Qualification only. The producer, descriptor registry and validator are Lean.
import assert from 'node:assert/strict';
import {readFile,writeFile,mkdtemp,rm} from 'node:fs/promises';
import {join,resolve} from 'node:path';
import {tmpdir} from 'node:os';
import {pathToFileURL} from 'node:url';
import {execFileSync} from 'node:child_process';

const [checkerPath,sourceDirectory,nativeCli,...extra]=process.argv.slice(2);
if(!checkerPath||!sourceDirectory||extra.length)throw Error('Usage: node tests/native-producer-checker.mjs OFFICIAL_CHECKER_MODULE BOOL_SOURCE_DIRECTORY [NATIVE_ZKIR_CLI]');
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
 const key=Buffer.from('nightlean/native-producer/safety');
 return Buffer.concat([Buffer.from('midnight:proof-preimage:'),vector([]),vector(test.private??[]),
  vector(test.publicInputs??[]),vector(test.publicReads??[]),compact(42),Buffer.from([0]),compact(key.length),key]);
}
const op=(name,fields={})=>({op:name,...fields});
const output=op('output',{vals:[]});
const input=guard=>op('private_input',{guard,type:'Scalar<BLS12-381>',output:'%x'});
const raw=instructions=>({version:{major:3,minor:2},inputs:[],outputs:[],do_communications_commitment:false,instructions});
const fixtures=[
 {id:'NATIVE-ASSERT-ONE',circuit:raw([op('assert',{cond:'0x01'}),output]),accepted:true},
 {id:'NATIVE-ASSERT-TWO-CHECKER',circuit:raw([op('assert',{cond:'0x02'}),output]),accepted:false,keygen:true},
 {id:'NATIVE-DUPLICATE-OUTPUT-UPSTREAM',circuit:raw([output,output]),accepted:true,keygen:true},
 {id:'NATIVE-OUTPUT-DOES-NOT-TERMINATE',circuit:raw([output,op('assert',{cond:'0x00'})]),accepted:false},
 {id:'NATIVE-INACTIVE-INPUT-DOES-NOT-SKIP-INVERSION',circuit:raw([input('0x00'),op('inv',{a:'%x',output:'%inverse'}),output]),accepted:false},
 {id:'NATIVE-LESS-THAN-UNBOUNDED-OUTSIDE-CONTRACT',circuit:raw([input(null),op('less_than',{a:'%x',b:'0xff',bits:8,output:'%bit'}),output]),private:['256'],accepted:null},
 {id:'NATIVE-LESS-THAN-RANGED-REJECTS-BAD-WITNESS',circuit:raw([input(null),op('constrain_bits',{val:'%x',bits:8}),op('less_than',{a:'%x',b:'0xff',bits:8,output:'%bit'}),output]),private:['256'],accepted:false},
];
const boolCircuit=JSON.parse(await readFile(join(sourceDirectory,'publicBoolRoundTrip.zkir'),'utf8'));
fixtures.push(
 {id:'SOURCE-PUBLIC-BOOL-FALSE',circuit:boolCircuit,publicInputs:['0','0'],publicReads:['0'],accepted:true},
 {id:'SOURCE-PUBLIC-BOOL-TRUE',circuit:boolCircuit,publicInputs:['1','1'],publicReads:['1'],accepted:true},
 {id:'SOURCE-PUBLIC-BOOL-TWO-REJECT',circuit:boolCircuit,publicInputs:['2','2'],publicReads:['2'],accepted:false},
 {id:'SOURCE-PUBLIC-BOOL-WRONG-RETURN-REJECT',circuit:boolCircuit,publicInputs:['1','0'],publicReads:['1'],accepted:false},
);
const directory=await mkdtemp(join(tmpdir(),'nightlean-native-producer-'));
const results=[];
try{
 for(const test of fixtures){
  const relation=Zkir.fromJson(JSON.stringify(test.circuit));
  const key={ir:relation.serialize(),proverKey:new Uint8Array(),verifierKey:new Uint8Array()};
  let failure,activity;
  try{activity=await check(preimage(test),{lookupKey:async()=>key});}catch(error){failure=error;}
  if(test.accepted!==null)assert.equal(!failure,test.accepted,`${test.id}: ${failure??'invalid witness accepted'}`);
  const result={id:test.id,checkerAccepted:!failure,activityGroups:activity?.length};
  if(test.accepted===null)result.scope='undefined out-of-range LessThan input, observation only, rejected by Lean producer';
  if(test.keygen&&nativeCli){
   const source=join(directory,test.id+'.zkir');
   await writeFile(source,JSON.stringify(test.circuit)+'\n');
   execFileSync(resolve(nativeCli),['compile',source,source+'.prover',source+'.verifier'],{stdio:'pipe',timeout:120000});
   result.nativeKeygenSucceeded=true;
  }
  results.push(result);
 }
 console.log(JSON.stringify({scope:'official preprocessing checker and optional native synthesis/keygen observations; no malicious internal-witness proof or ledger submission',cases:results},null,2));
}finally{await rm(directory,{recursive:true,force:true});}
