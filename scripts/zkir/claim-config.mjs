// Public development fixture for examples/PrivateClaim.lean. Never use these secrets for real claims.
import {writeFile} from 'node:fs/promises';
import * as l from '@midnight-ntwrk/ledger-v9';
const [destination]=process.argv.slice(2);if(!destination)throw Error('Usage: node claim-config.mjs OUTPUT.json');
const field={tag:'atom',value:{tag:'field'}};
const hash=xs=>l.valueToBigInt(l.transientHash(xs.map(()=>field),xs.flatMap(l.bigIntToValue)));
const secret=42n,campaign=9n,leaf=hash([1n,secret,campaign]),node=hash([2n,leaf,17n]);
const root=hash([2n,23n,node]),nullifier=hash([3n,secret,campaign]);
const inputs={root:String(root),campaign:String(campaign),suppliedNullifier:String(nullifier),secret:String(secret),sibling0:'17',sibling1:'23',direction0:false,direction1:true};
const config={inputs,state:{acceptedRoot:String(root),campaignId:String(campaign),spent:[]},negativeCases:[{name:'secret',inputs:{secret:'43'}},{name:'path',inputs:{sibling0:'18'}},{name:'direction',inputs:{direction0:true}},{name:'root',inputs:{root:String(root+1n)}},{name:'nullifier',inputs:{suppliedNullifier:String(nullifier+1n)}}]};
await writeFile(destination,JSON.stringify(config,null,2)+'\n',{mode:0o600});console.log(JSON.stringify({root:String(root),campaign:String(campaign),nullifier:String(nullifier),qualification:'public development fixture values'}));
