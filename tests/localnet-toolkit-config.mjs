import assert from 'node:assert/strict';
import {mkdtemp,rm,stat} from 'node:fs/promises';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {test} from 'node:test';
import {nativeToolkitConfig,nativeToolkitTimeout} from '../scripts/localnet/native-toolkit-config.mjs';

test('funding and state queries bound RPC, compute and wallet replay workers',async()=>{
 const work=await mkdtemp(join(tmpdir(),'noctium-toolkit-test-'));
 try{
  const config=await nativeToolkitConfig(work);
  for(const command of ['send-intent','contract-state']){
   const args=config.args([command,'--src-url','ws://noctium-dev-node:9944']);
   for(const option of ['--fetch-concurrency','--fetch-compute-concurrency','--replay-concurrency']){
    assert.equal(args.filter(arg=>arg===option).length,1);
    assert.equal(args[args.indexOf(option)+1],'2');
   }
   assert.deepEqual(args.slice(-2),['--src-url','ws://noctium-dev-node:9944']);
  }
  assert.equal(nativeToolkitTimeout,600000);
 }finally{await rm(work,{recursive:true,force:true});}
});

test('sequential commands share disk caches, separate runs receive private fresh caches',async()=>{
 const work=await mkdtemp(join(tmpdir(),'noctium-toolkit-test-'));
 try{
  const config=await nativeToolkitConfig(work),other=await nativeToolkitConfig(work);
  assert.notEqual(config.directory,other.directory);
  assert.equal((await stat(config.directory)).mode&0o777,0o700);
  const first=config.args(['send-intent']),next=config.args(['contract-state']);
  for(const option of ['--fetch-cache','--ledger-state-db']){
   const path=first[first.indexOf(option)+1];
   assert.equal(path,next[next.indexOf(option)+1]);
   assert.match(path,option==='--fetch-cache'?/^redb:\/work\/\.native-toolkit-[A-Za-z0-9]+\/fetch\.db$/:/^\/work\/\.native-toolkit-[A-Za-z0-9]+\/ledger$/);
   const separate=other.args(['send-intent']);
   assert.notEqual(path,separate[separate.indexOf(option)+1]);
  }
  for(const command of [['show-transaction','--src-file','/work/native-deploy.mn'],['generate-txs','--src-file=/work/native-deploy.mn','send','-d','ws://noctium-dev-node:9944']])assert.deepEqual(config.args(command),command);
 }finally{await rm(work,{recursive:true,force:true});}
});
