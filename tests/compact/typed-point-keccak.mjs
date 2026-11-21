import assert from 'node:assert/strict';
import {spawnSync} from 'node:child_process';
import {mkdir, mkdtemp, readFile, readdir, rm, rmdir} from 'node:fs/promises';
import {tmpdir} from 'node:os';
import {join, resolve} from 'node:path';
import {pathToFileURL} from 'node:url';

const [compactc = 'compactc', runtimePath] = process.argv.slice(2);
if (!runtimePath) {
  throw new Error('usage: node typed-point-keccak.mjs <compactc> <compact-runtime-dir-or-index.js>');
}
const version = spawnSync(compactc, ['--version'], {encoding: 'utf8'});
assert.equal(version.status, 0, version.stderr);
assert.match(version.stdout, /^0\.36\.1\b/);

const runtimeEntry = resolve(runtimePath);
const runtime = await import(pathToFileURL(
  runtimeEntry.endsWith('.js') ? runtimeEntry : join(runtimeEntry, 'dist/index.js'),
).href);
assert.equal(runtime.versionString, '0.21.0');

const fixture = new URL('./TypedPointKeccak.compact', import.meta.url);
const experiments = resolve(new URL('../../build/experiments', import.meta.url).pathname);
await mkdir(experiments, {recursive: true});
const scratch = await mkdtemp(join(experiments, 'typed-point-keccak-'));
try {
  const output = join(scratch, 'compact-output');
  const compiled = spawnSync(compactc, ['--skip-zk', fixture.pathname, output], {encoding: 'utf8'});
  assert.equal(compiled.status, 0, compiled.stderr || compiled.stdout);

  const collect = async (directory) => {
    const paths = [];
    for (const entry of await readdir(directory, {withFileTypes: true})) {
      const path = join(directory, entry.name);
      if (entry.isDirectory()) paths.push(...await collect(path));
      else if (entry.name.endsWith('.zkir')) paths.push(path);
    }
    return paths;
  };
  const zkirFiles = await collect(output);
  assert.equal(zkirFiles.length, 1, `expected one relation, got ${zkirFiles.length}`);
  const zkir = JSON.parse(await readFile(zkirFiles[0], 'utf8'));
  const hashes = [];
  const visit = (value) => {
    if (!value || typeof value !== 'object') return;
    if (value.op === 'keccak256') hashes.push(value);
    for (const child of Object.values(value)) {
      if (Array.isArray(child)) child.forEach(visit);
      else visit(child);
    }
  };
  visit(zkir);
  assert.equal(hashes.length, 1, `expected one typed Keccak, got ${hashes.length}`);
  assert.deepEqual(hashes[0].alignment, [
    {tag: 'atom', value: {tag: 'bytes', length: 24}},
    {tag: 'atom', value: {tag: 'bytes', length: 8}},
    {tag: 'atom', value: {tag: 'bytes', length: 24}},
    {tag: 'atom', value: {tag: 'bytes', length: 8}},
    {tag: 'atom', value: {tag: 'field'}},
  ]);

  const point = {
    x: 55066263022277343669578718895168534326250603453777594175500187360389116729240n,
    y: 32670510020758816978083085130507043184471273380659243275938904335757337482424n,
    identity: false,
  };
  const preimage = runtime.toBinaryRepr(runtime.CompactTypeSecp256k1Point, point);
  assert.equal(preimage.length, 96);
  assert.equal(Buffer.from(preimage).toString('hex'),
    '9717f8165b81f259d928ce2ddbfc9b02070b87ce9562a055acbbdcf97e66be79' +
    'b7d410fb8fd0479c195485a648b417fda808110efcfba45d65c4a32677da3a48' +
    '00'.repeat(32));
  const digest = Buffer.from(runtime.keccak256(runtime.CompactTypeSecp256k1Point, point)).toString('hex');
  assert.equal(digest, '571cf838e63c171196cd7a301bb8fab87d13d946769a41e1004d9da49f6bfca8');
  console.log(`Compact ${version.stdout.trim()} / runtime ${runtime.versionString}: typed Keccak alignment and digest match`);
} finally {
  await rm(scratch, {recursive: true, force: true});
  try {
    await rmdir(experiments);
  } catch {
    // Keep the shared experiments directory when another task uses it.
  }
}
