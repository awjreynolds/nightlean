import init, { WitnessSession } from './noctium_witness.js';

const assert = (condition, label) => { if (!condition) throw new Error(label); };
const encoder = new TextEncoder();
const decoder = new TextDecoder();
const encode = (value) => encoder.encode(JSON.stringify(value));
const decode = (bytes) => JSON.parse(decoder.decode(bytes));
const read = 'private_state.read.v1';
const stage = 'private_state.stage.v1';
const cas = 'private_state.compare_exchange.v1';
const same = (left, right) => JSON.stringify(left) === JSON.stringify(right);

async function run() {
  await init();
  const plan = await (await fetch('./plan.json')).json();
  for (const invalid of [false, true]) {
    const attemptId = (invalid ? 'b' : 'a').repeat(64);
    const capabilities = plan.witnesses.map(({ operation, capability, privateKey }) => ({
      id: capability, namespace: 'noctium',
      keyPrefix: privateKey ? 'noctium/ContainerWallet/' : 'lookup/',
      operations: operation === read ? [read, stage] : [operation],
    }));
    capabilities.push({ id: 'commit', namespace: 'noctium', keyPrefix: 'noctium/ContainerWallet/', operations: [cas] });
    const operations = plan.witnesses.map(({ operation, parameters, resultType }) => ({
      operation, argumentSchema: operation === read ? { key: 'Key' } :
        Object.fromEntries(parameters.map(({ name, type }) => [name, type])),
      resultSchema: resultType,
    }));
    const providers = plan.witnesses.map(({ name, operation, capability, privateKey }) => ({
      input: name, operation, capability, arguments: privateKey ? { key: privateKey } : {},
    }));
    const session = new WitnessSession(encode({
      abiVersion: 1, plan, inputs: { expected: '9' },
      hostContext: { protocolVersion: 1, namespace: 'noctium', baseRevision: 'r0', attemptId,
        capabilities, operations, providers, commitCapability: 'commit',
        limits: { requests: 64, writes: 64, privateBytes: 65536 } },
    }));
    const trace = [];
    const beforeEmpty = ['bytes', 'read:0', 'step:4:0', 'read:4', 'step:5:4'];
    try {
      while (true) {
        const status = decode(session.advance());
        if (status.status === 'failed' || status.status === 'completed') {
          assert(status.status === (invalid ? 'failed' : 'completed'), 'wrong outcome');
          if (!invalid) assert(status.result === '9', 'wrong result');
          assert(same(trace, invalid ? beforeEmpty : [...beforeEmpty, 'empty', 'read:9']), JSON.stringify(trace));
          break;
        }
        assert(status.status === 'need_host', JSON.stringify(status));
        const { requestId, operation, capability, schema, name } = status.request;
        const args = decode(session.privateRequest());
        let value;
        if (operation === read) {
          assert(args.arguments.key === 'noctium/ContainerWallet/last', 'wrong state key');
          value = args.invocationWrites?.['noctium/ContainerWallet/last']?.value ?? '0';
          trace.push('read:' + value);
        } else if (name === 'containerBytes' || name === 'emptyContainer') {
          const full = name === 'containerBytes';
          trace.push(full ? 'bytes' : 'empty');
          value = { kind: 'bytes', values: full ? [4, 5] : [] };
        } else {
          assert(name === 'containerStep', name);
          const { item, previous } = args.arguments;
          trace.push(`step:${item}:${previous}`);
          value = invalid && item === '5' ? '8' : String(BigInt(item) + BigInt(previous));
        }
        session.resume(encode({ protocolVersion: 2, requestId, operation, capability, schema,
          attemptId, outcome: 'value', value }), true);
      }
    } finally { session.free(); }
  }
  return 'PASS 9 and rejected invalid step before empty';
}

try { document.body.textContent = await run(); }
catch (error) { document.body.textContent = 'FAIL ' + String(error); }
