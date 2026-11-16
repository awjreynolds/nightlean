import {execFile} from 'node:child_process';
import {promisify} from 'node:util';
import {writeFile} from 'node:fs/promises';
const [destination]=process.argv.slice(2);if(!destination)throw Error('Usage: node ledger-parameters.mjs OUTPUT.params');
const response=await fetch('http://127.0.0.1:19944',{method:'POST',headers:{'content-type':'application/json'},body:JSON.stringify({jsonrpc:'2.0',id:1,method:'chain_getBlockHash',params:[0]})});
if((await response.json()).result!=='0x823383ec0302be8417cfcbcc62f21df08f4047bca37aaea89e3f54b550ebae1d')throw Error('Refusing non-development genesis');
const {stdout}=await promisify(execFile)('docker',['run','--rm','--pull','never','--network','nightlean-dev','--cap-drop','ALL','--security-opt','no-new-privileges','--entrypoint','/midnight-node-toolkit','midnightntwrk/midnight-node-toolkit@sha256:904f824f3350530bc2fb03448906cc5f9f200b98e98bd9fbb274a1cc25b9f89c','show-ledger-parameters','--read-from-rpc-url','ws://nightlean-dev-node:9944','--serialize'],{timeout:30000,maxBuffer:2**20});
const hex=stdout.trim();if(!/^(?:[a-f0-9]{2})+$/.test(hex))throw Error('Invalid serialized ledger parameters');await writeFile(destination,Buffer.from(hex,'hex'));
