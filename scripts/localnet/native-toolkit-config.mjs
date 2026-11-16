import {mkdtemp} from 'node:fs/promises';
import {basename,join} from 'node:path';

export const nativeToolkitTimeout=600000;

export async function nativeToolkitConfig(work){
 // Reuse snapshots within this run without trusting stale data from a reset dev chain.
 const directory=await mkdtemp(join(work,'.native-toolkit-'));
 const containerDirectory='/work/'+basename(directory);
 return {
  directory,
  args(args){
   if(!['send-intent','contract-state'].includes(args[0]))return args;
   return [args[0],
    '--fetch-concurrency','2','--fetch-compute-concurrency','2','--replay-concurrency','2',
    '--fetch-cache','redb:'+containerDirectory+'/fetch.db',
    '--ledger-state-db',containerDirectory+'/ledger',...args.slice(1)];
  }
 };
}
