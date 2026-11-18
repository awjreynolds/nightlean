import * as l from '@midnight-ntwrk/ledger-v9';
const prime=l.maxField()+1n;
const atom={tag:'atom',value:{tag:'field'}};
export const empty={value:[],alignment:[]};
export function native(value){
 if(typeof value==='bigint'){if(value<0n||value>=prime)throw Error('Native value out of range');return value;}
 if(typeof value!=='string'||!/^(0|[1-9][0-9]*)$/.test(value))throw Error('Native inputs require canonical decimal strings');
 return native(BigInt(value));
}
export const field=n=>({value:l.bigIntToValue(typeof n==='boolean'?(n?1n:0n):native(n)),alignment:[atom]});
export const bit=b=>({value:[b?Uint8Array.of(1):new Uint8Array()],alignment:[{tag:'atom',value:{tag:'bytes',length:1}}]});
export function evaluate(expr,env){
 switch(expr.tag){
  case 'constant':return native(expr.value);
  case 'bool':if(typeof expr.value!=='boolean')throw Error('Invalid boolean constant');return expr.value;
  case 'let':{const value=evaluate(expr.value,env),local=new Map(env);local.set(expr.name,value);return evaluate(expr.body,local);}
  case 'assertThen':if(evaluate(expr.condition,env)!==true)throw Error('helper assertion failed');return evaluate(expr.body,env);
  case 'reference':if(!env.has(expr.name))throw Error(`Unbound native reference ${expr.name}`);return env.get(expr.name);
  case 'add':return (evaluate(expr.left,env)+evaluate(expr.right,env))%prime;
  case 'mul':return (evaluate(expr.left,env)*evaluate(expr.right,env))%prime;
  case 'eq':return evaluate(expr.left,env)===evaluate(expr.right,env);
  case 'select':{const condition=evaluate(expr.condition,env);if(typeof condition!=='boolean')throw Error('Expected boolean selector');const yes=evaluate(expr.yes,env),no=evaluate(expr.no,env);return condition?yes:no;}
  case 'poseidon2':{const values=[native(expr.domain),evaluate(expr.left,env),evaluate(expr.right,env)];return l.valueToBigInt(l.transientHash(values.map(()=>atom),values.flatMap(l.bigIntToValue)));}
  default:throw Error(`Unsupported emitted expression ${expr.tag}`);
 }
}
export function environment(plan,inputs){
 if(plan.schemaVersion!==1)throw Error('Unsupported emitted native plan schema');
 const names=new Set(plan.circuit.inputs.map(input=>input.name));
 if(Object.keys(inputs).some(name=>!names.has(name)))throw Error('Unknown native input');
 const env=new Map();
 for(const input of plan.circuit.inputs){const value=inputs[input.name];if(input.type==='Bool'){if(typeof value!=='boolean')throw Error(`Expected boolean ${input.name}`);env.set(input.name,value);}else env.set(input.name,native(value));}
 for(const output of plan.circuit.outputs)env.set(output.name,evaluate(output.expression,env));
 return env;
}
export function createState(plan,config){
 let data=l.StateValue.newArray();
 for(const declaration of plan.state){
  if(declaration.kind.cell){const value=config[declaration.name];if(declaration.kind.cell==='Bool'&&typeof value!=='boolean')throw Error('Expected boolean initial cell');data=data.arrayPush(l.StateValue.newCell(field(declaration.kind.cell==='Bool'?value:native(value))));}
  else{if(!Array.isArray(config[declaration.name])||config[declaration.name].length)throw Error('Initial map must be explicitly empty in this profile');data=data.arrayPush(l.StateValue.newMap(new l.StateMap()));}
 }
 return new l.ChargedState(data);
}
export function materialize(plan,inputs,context,cost){
 if(plan.returns?.length)throw Error('Committed call returns require the native Rust runtime');
 const env=environment(plan,inputs),program=[];let readIndex=0,previous;
 for(const instruction of plan.operations){
  let op;
  switch(instruction.op){
   case 'dup':op={dup:{n:0}};break;
   case 'index':{const path=[{tag:'value',value:field(BigInt(instruction.slot))}];if(instruction.key)path.push({tag:'value',value:field(evaluate(instruction.key,env))});op={idx:{cached:false,pushPath:instruction.pushPath,path}};break;}
   case 'push':{const value=evaluate(instruction.expression,env);op={push:{storage:instruction.storage,value:{tag:'cell',content:instruction.alignment==='bit'?bit(value):field(value)}}};break;}
   case 'popeq':{
    const read=plan.reads[readIndex++];
    if(instruction.expression.tag==='reference'&&!env.has(instruction.expression.name)){
     if(previous?.op!=='index')throw Error('Unsupported state-read shape');
     const witness=context.query([...program.map(item=>typeof item==='object'&&item.popeq?{popeq:{...item.popeq,result:null}}:item),{popeq:{cached:false,result:null}}],cost).events.filter(event=>event.tag==='read').at(-1);
     if(!witness)throw Error('Native VM did not produce the indexed state read');
     const number=l.valueToBigInt(witness.content.value);
     env.set(instruction.expression.name,read.type==='Bool'?number===1n:number);
    }
    const expected=evaluate(instruction.expression,env);
    if(!env.has(read.name))env.set(read.name,expected);
    op={popeq:{cached:false,result:instruction.alignment==='bit'?bit(expected):field(expected)}};
    break;
   }
   case 'member':op='member';break;
   case 'insert':op={ins:{cached:false,n:instruction.n}};break;
   default:throw Error(`Unsupported emitted operation ${instruction.op}`);
  }
  program.push(op);previous=instruction;
 }
 const observed=context.query(program.map(op=>typeof op==='object'&&op.popeq?{popeq:{...op.popeq,result:null}}:op),cost).events.filter(event=>event.tag==='read');
 const expected=program.filter(op=>typeof op==='object'&&op.popeq).map(op=>op.popeq.result);
 if(observed.length!==expected.length||observed.some((event,index)=>l.valueToBigInt(event.content.value)!==l.valueToBigInt(expected[index].value)))throw Error('Native VM expected read mismatch (spent nullifier or inconsistent state)');
 if(readIndex!==plan.reads.length)throw Error('Native read plan mismatch');
 const privateOutputs=plan.circuit.inputs.filter(input=>input.visibility==='private').map(input=>field(env.get(input.name)));
 return {program,privateOutputs,env};
}
export function callPrototype(plan,inputs,state,address,operation,parameters){
 const context=new l.QueryContext(state.data,address),cost=parameters.transactionCostModel.runtimeCostModel;
 const {program,privateOutputs}=materialize(plan,inputs,context,cost);
 const randomness=l.communicationCommitmentRandomness();
 const commitment=l.communicationCommitment(empty,empty,randomness);
 const [guaranteed,fallible]=l.partitionTranscripts([new l.PreTranscript(context,program,commitment)],parameters)[0];
 const prototype=new l.ContractCallPrototype(address,plan.entrypoint,operation,guaranteed,fallible,privateOutputs,empty,empty,randomness,plan.entrypoint);
 let after=context;
 if(guaranteed)after=after.runTranscript(guaranteed,cost);
 if(fallible)after=after.runTranscript(fallible,cost);
 return {prototype,program,privateOutputs,after,guaranteed,fallible};
}
