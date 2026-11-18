#!/usr/bin/env node
// Optional raw-ZKIR protocol research. This script is not part of the app build.
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFile, writeFile } from 'node:fs/promises';
import { createRequire } from 'node:module';
import { dirname, join, resolve } from 'node:path';
import { pathToFileURL } from 'node:url';

const pins = {
  nativeSourceRevision: '7a51b3385bbf4bce3604df87a7c70867c9ab43c0',
  nativeCliSha256: '7396c9a368e70fb66cb91f39d1508c9f983cacc8d3bc27f7a94e12d9fe327c40',
  checkerPackage: '@midnightntwrk/zkir-v3',
  checkerVersion: '3.2.1',
  checkerPackageJsonSha256: '8fdbb3861ee27d2691d9c50ae50837061657fd5430506f6d7eec19b0910d4a84',
  checkerModuleSha256: 'a4ec641776c45bd06fe033f25b8d74fccca7900d5e97cc360468ddeacfa2424c',
  checkerWasmSha256: '3568fafaf225469dbbd038b0236d1b6b76e0da19da565caba33efe2ceb682cfc',
  k4SrsSha256: '232f401fad10c7ddf8828d2aa4c85c6506c5da09795998cecaeb9f75fc8f6ada',
  k5SrsSha256: '0a1c9229f315fc1868ff25f668fb83aec4d09f4f23a706b5197c692c619d72c6'
};

const fixturePins = {
  'guarded-impact': {
    json: 'e9497768dd02f324212860b3abe8312b2c013615ebc0c719dff15d26b8f7a7ff',
    binary: '4391aa308022aaa601d2d813d222a12a009ed2deeaac5b51615bfc580429cabb'
  },
  'input-guards': {
    json: '7b96d32e617c4d87f026906c4c6125011885b8027b351092f5cfc81c546698c8',
    binary: '240a23e1344fa9cbb7a2e805e998d423dc00fd33c8f087411fbb11d072dea499'
  },
  'private-input-guard': {
    json: '07a43fd0b339c57ecf28a61c49e81035997261e6829a007aa43dae1ab8bc21cd',
    binary: '4f6c26f1121559ed5a351709a9ace111c2a32d2fbaf1407fd93b998c95a863a3'
  }
};

const usage = `Usage:
  node tests/guarded-native-prerequisites/probe.mjs \\
    --checker MODULE --wasm WASM --cli ZKIR --params DIR --artifacts DIR [--mode check|prove]

Checker-only mode is the default and makes no network request. Prove mode also requires:
  --proof-url http://127.0.0.1:16300
`;

function parseArgs(argv) {
  const result = {};
  for (let i = 0; i < argv.length; i += 1) {
    const name = argv[i];
    if (name === '--help' || name === '-h') {
      result.help = true;
      continue;
    }
    if (!['--checker', '--wasm', '--cli', '--params', '--artifacts', '--mode', '--proof-url'].includes(name)) {
      throw new Error(`Unknown option: ${name}`);
    }
    if (result[name] !== undefined || argv[i + 1] === undefined || argv[i + 1].startsWith('--')) {
      throw new Error(`Expected one value after ${name}`);
    }
    result[name] = argv[++i];
  }
  return result;
}

const sha256 = bytes => createHash('sha256').update(bytes).digest('hex');
async function fileHash(path, label, expected) {
  const bytes = await readFile(path);
  const actual = sha256(bytes);
  assert.equal(actual, expected, `${label} SHA-256 mismatch at ${path}`);
  return { bytes, sha256: actual };
}

function compact(value) {
  let n = BigInt(value);
  if (n < 0n) throw new Error('Negative SCALE input');
  const littleEndian = (number, count) => Buffer.from(Array.from({ length: count }, () => {
    const byte = Number(number & 255n);
    number >>= 8n;
    return byte;
  }));
  if (n < 64n) return littleEndian(n << 2n, 1);
  if (n < 16384n) return littleEndian((n << 2n) | 1n, 2);
  if (n < 1073741824n) return littleEndian((n << 2n) | 2n, 4);
  const bytes = [];
  while (n > 0n) {
    bytes.push(Number(n & 255n));
    n >>= 8n;
  }
  return Buffer.from([((bytes.length - 4) << 2) | 3, ...bytes]);
}

const vector = values => Buffer.concat([compact(values.length), ...values.map(compact)]);
function serializedPreimage(circuit, witness) {
  const key = Buffer.from(`noctium/issue43/${circuit}`);
  return Buffer.concat([
    Buffer.from('midnight:proof-preimage:'),
    vector(witness.inputs),
    vector(witness.privateTranscript ?? []),
    vector(witness.publicTranscriptInputs ?? []),
    vector(witness.publicTranscriptOutputs ?? []),
    compact(witness.bindingInput ?? 42),
    Buffer.from([0]),
    compact(key.length),
    key
  ]);
}

function assertLoopbackUrl(value) {
  if (!value) throw new Error('Prove mode requires an explicit --proof-url');
  const url = new URL(value);
  if (!['http:', 'https:'].includes(url.protocol) ||
      !['127.0.0.1', 'localhost', '[::1]'].includes(url.hostname) ||
      url.username || url.password || url.search || url.hash || !['', '/'].includes(url.pathname)) {
    throw new Error('--proof-url must be an HTTP(S) loopback origin without credentials, path, query, or fragment');
  }
  return url;
}

async function readBounded(response, limit) {
  const declared = Number(response.headers.get('content-length'));
  if (Number.isFinite(declared) && declared > limit) {
    await response.body?.cancel();
    throw new Error(`Proof service response exceeds ${limit} bytes`);
  }
  if (!response.body) return Buffer.alloc(0);
  const reader = response.body.getReader();
  const chunks = [];
  let length = 0;
  while (true) {
    const { done, value } = await reader.read();
    if (done) break;
    length += value.byteLength;
    if (length > limit) {
      await reader.cancel();
      throw new Error(`Proof service response exceeds ${limit} bytes`);
    }
    chunks.push(Buffer.from(value));
  }
  return Buffer.concat(chunks, length);
}

async function main() {
  const args = parseArgs(process.argv.slice(2));
  if (args.help) {
    process.stdout.write(usage);
    return;
  }
  const required = ['--checker', '--wasm', '--cli', '--params', '--artifacts'];
  for (const name of required) if (!args[name]) throw new Error(`Missing required option ${name}`);
  const mode = args['--mode'] ?? 'check';
  if (!['check', 'prove'].includes(mode)) throw new Error('--mode must be check or prove');
  if (mode === 'check' && args['--proof-url']) throw new Error('--proof-url is only accepted with --mode prove');
  const proofOrigin = mode === 'prove' ? assertLoopbackUrl(args['--proof-url']) : undefined;

  const checkerPath = resolve(args['--checker']);
  const wasmPath = resolve(args['--wasm']);
  const cliPath = resolve(args['--cli']);
  const paramsPath = resolve(args['--params']);
  const artifactsPath = resolve(args['--artifacts']);
  assert.equal(dirname(checkerPath), dirname(wasmPath), 'Checker JS and WASM must be siblings from the same package');
  const packageManifest = await fileHash(join(dirname(checkerPath), 'package.json'), 'Official checker package manifest', pins.checkerPackageJsonSha256);
  const checkerPackage = JSON.parse(packageManifest.bytes.toString('utf8'));
  assert.equal(checkerPackage.name, pins.checkerPackage, 'Unexpected checker package name');
  assert.equal(checkerPackage.version, pins.checkerVersion, 'Unexpected checker package version');
  const checker = await fileHash(checkerPath, 'Official checker module', pins.checkerModuleSha256);
  const wasm = await fileHash(wasmPath, 'Official checker WASM', pins.checkerWasmSha256);
  const cli = await fileHash(cliPath, 'Native ZKIR CLI', pins.nativeCliSha256);
  const srs4 = await fileHash(join(paramsPath, 'bls_midnight_2p4'), 'K4 SRS', pins.k4SrsSha256);
  const srs5 = await fileHash(join(paramsPath, 'bls_midnight_2p5'), 'K5 SRS', pins.k5SrsSha256);

  const materials = {};
  const artifactHashes = {};
  for (const [name, pin] of Object.entries(fixturePins)) {
    const jsonPath = join(artifactsPath, `${name}.zkir`);
    const binaryPath = join(artifactsPath, `${name}.bzkir`);
    const source = await fileHash(jsonPath, `${name} JSON fixture`, pin.json);
    const binary = await fileHash(binaryPath, `${name} tagged binary IR`, pin.binary);
    const proverKey = await readFile(join(artifactsPath, `${name}.prover`));
    const verifierKey = await readFile(join(artifactsPath, `${name}.verifier`));
    assert.ok(proverKey.length > 0, `${name} prover key is empty`);
    assert.ok(verifierKey.length > 0, `${name} verifier key is empty`);
    artifactHashes[name] = {
      jsonSha256: source.sha256,
      taggedBinaryIrSha256: binary.sha256,
      proverKeySha256: sha256(proverKey),
      verifierKeySha256: sha256(verifierKey)
    };
    materials[name] = {
      irJson: source.bytes.toString('utf8'),
      key: { ir: undefined, proverKey, verifierKey }
    };
  }

  // Check the official package files before importing its WASM module.
  const { Zkir, check } = await import(pathToFileURL(checkerPath).href);
  for (const [name, material] of Object.entries(materials)) {
    const ir = Zkir.fromJson(material.irJson);
    material.key.ir = ir.serialize();
    material.k = ir.getK();
  }

  async function checkCase(circuit, witness, expectedActivity, accept, label) {
    const provider = { lookupKey: async () => materials[circuit].key };
    let activity;
    try {
      activity = await check(serializedPreimage(circuit, witness), provider);
    } catch (error) {
      if (accept) throw new Error(`${label}: unexpected checker rejection: ${error.message ?? error}`);
      return { label, accepted: false, error: String(error.message ?? error).slice(0, 240) };
    }
    if (!accept) throw new Error(`${label}: checker unexpectedly accepted the case`);
    assert.deepEqual(activity, expectedActivity, `${label}: activity vector differs`);
    return { label, accepted: true, activity: activity.map(value => value === undefined ? null : String(value)) };
  }

  const positiveCases = [
    ['guarded-impact', { inputs: [0, 0, 300, 1, 1, 255], publicTranscriptInputs: [255] }, [2n, undefined], 'group0-off-group1-on'],
    ['guarded-impact', { inputs: [1, 1, 127, 0, 0, 600], publicTranscriptInputs: [127, 1] }, [undefined, 1n], 'group0-on-group1-off'],
    ['input-guards', { inputs: [1], publicTranscriptOutputs: [1], privateTranscript: [1] }, [], 'guarded-transcript-read-true'],
    ['private-input-guard', { inputs: [1], privateTranscript: [1] }, [], 'private-guard-true']
  ];
  const negativeCases = [
    ['guarded-impact', { inputs: [2, 0, 300, 1, 1, 255], publicTranscriptInputs: [255] }, 'nonboolean-guard'],
    ['guarded-impact', { inputs: [1, 0, 255, 0, 0, 300], publicTranscriptInputs: [255] }, 'inactive-assertion-is-still-gated'],
    ['guarded-impact', { inputs: [1, 1, 256, 0, 0, 300], publicTranscriptInputs: [256, 1] }, 'active-range-overflow'],
    ['guarded-impact', { inputs: [0, 0, 300, 1, 1, 255], publicTranscriptInputs: [254] }, 'public-field-mismatch'],
    ['guarded-impact', { inputs: [0, 0, 300, 1, 1, 255], publicTranscriptInputs: [300, 0, 255] }, 'inactive-group-fields-are-omitted'],
    ['guarded-impact', { inputs: [0, 0, 300, 0, 0, 600], publicTranscriptInputs: [300] }, 'off-groups-consume-no-public-fields'],
    ['guarded-impact', { inputs: [0, 2, 300, 1, 1, 255], publicTranscriptInputs: [255] }, 'inactive-predicate-still-must-be-boolean'],
    ['input-guards', { inputs: [0] }, 'guarded-transcript-read-false-does-not-skip-assert'],
    ['input-guards', { inputs: [2], publicTranscriptOutputs: [1], privateTranscript: [1] }, 'nonboolean-input-guard'],
    ['private-input-guard', { inputs: [0] }, 'private-guard-false-still-reaches-assert']
  ];

  const report = {
    status: 'raw-native-prerequisite-only',
    mode,
    sourceRevision: pins.nativeSourceRevision,
    pins: {
      nativeCliSha256: cli.sha256,
      checkerPackage: `${checkerPackage.name}@${checkerPackage.version}`,
      checkerPackageJsonSha256: packageManifest.sha256,
      checkerModuleSha256: checker.sha256,
      checkerWasmSha256: wasm.sha256,
      k4SrsSha256: srs4.sha256,
      k5SrsSha256: srs5.sha256
    },
    artifacts: artifactHashes,
    checker: { positive: [], negative: [] },
    nativeProofService: { status: 'not-run' }
  };
  for (const [circuit, witness, activity, label] of positiveCases) {
    report.checker.positive.push(await checkCase(circuit, witness, activity, true, label));
  }
  for (const [circuit, witness, label] of negativeCases) {
    report.checker.negative.push(await checkCase(circuit, witness, [], false, label));
  }

  if (mode === 'prove') {
    const require = createRequire(new URL('../../scripts/zkir/package.json', import.meta.url));
    const ledger = await import(pathToFileURL(require.resolve('@midnight-ntwrk/ledger-v9')).href);
    const endpoint = new URL('/prove', proofOrigin);
    const positiveProofCases = [
      ['guarded-impact', positiveCases[0][1], 'group0-off-group1-on'],
      ['guarded-impact', positiveCases[1][1], 'group0-on-group1-off'],
      ['private-input-guard', positiveCases[3][1], 'private-input-guard-true']
    ];
    const negativeProofCases = [
      ['guarded-impact', negativeCases[0][1], 'prover-nonboolean-impact-guard'],
      ['guarded-impact', negativeCases[1][1], 'prover-active-implication-failure'],
      ['input-guards', negativeCases[7][1], 'prover-input-guard-false-downstream-assert'],
      ['private-input-guard', negativeCases[9][1], 'prover-private-input-guard-false-downstream-assert']
    ];
    const results = [];
    async function requestProof(circuit, witness, expectProof, label) {
      const bytes = serializedPreimage(circuit, witness);
      const payload = Buffer.from(ledger.createProvingPayload(bytes, BigInt(witness.bindingInput ?? 42), materials[circuit].key));
      assert.ok(payload.length <= 1024 * 1024, `${label}: proving request exceeds 1 MiB`);
      const response = await fetch(endpoint, {
        method: 'POST', body: payload, credentials: 'omit', redirect: 'error',
        signal: AbortSignal.timeout(120000)
      });
      const body = await readBounded(response, expectProof ? 1024 * 1024 : 4096);
      if (expectProof) {
        assert.ok(response.ok, `${label}: HTTP ${response.status}: ${body.toString()}`);
        assert.ok(body.length > 0, `${label}: empty proof response`);
        const proofPath = join(artifactsPath, `${label}.proof`);
        await writeFile(proofPath, body, { flag: 'wx', mode: 0o600 });
        results.push({ label, httpStatus: response.status, proofReturned: true, proofBytes: body.length, proofSha256: sha256(body), k: materials[circuit].k });
      } else {
        assert.ok(!response.ok, `${label}: prover unexpectedly returned HTTP ${response.status}`);
        results.push({ label, httpStatus: response.status, rejected: true, error: body.toString() });
      }
    }
    for (const item of positiveProofCases) await requestProof(...item.slice(0, 2), true, item[2]);
    for (const item of negativeProofCases) await requestProof(...item.slice(0, 2), false, item[2]);
    report.nativeProofService = { endpoint, positive: results.filter(result => !result.rejected), negative: results.filter(result => result.rejected) };
  }

  process.stdout.write(`${JSON.stringify(report, null, 2)}\n`);
}

main().catch(error => {
  process.stderr.write(`Guard prerequisite probe failed: ${error.message ?? error}\n`);
  process.exitCode = 1;
});
