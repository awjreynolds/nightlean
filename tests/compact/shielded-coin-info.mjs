import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/shielded-coin-info.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.version, '0.21.0');

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(root, 'tests/compact/ShieldedCoinInfo.compact');
const experiments = join(root, 'build/experiments/315');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'shielded-coin-info-compact-'));
try {
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, compile.stderr || compile.stdout);
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');
  const { pureCircuits } = await import(pathToFileURL(join(generated, 'contract/index.js')).href);

  const nonce = Uint8Array.from({ length: 32 }, (_, index) => index + 1);
  const color = Uint8Array.from({ length: 32 }, (_, index) => 255 - index);
  const maximum = (1n << 128n) - 1n;
  const cases = [0n, maximum].map((value) => ({
    value,
    coin: pureCircuits.shieldedCoinInfoShape(nonce, color, value),
  }));
  for (const { value, coin } of cases) {
    assert.deepEqual(Object.keys(coin), ['nonce', 'color', 'value']);
    assert.deepEqual(coin.nonce, nonce);
    assert.deepEqual(coin.color, color);
    assert.equal(coin.value, value);
  }
  assert.throws(() => pureCircuits.shieldedCoinInfoShape(nonce, color, maximum + 1n));
  console.log(JSON.stringify({
    fixture: 'ShieldedCoinInfo',
    compact: compilerVersion,
    fields: ['nonce:Bytes<32>', 'color:Bytes<32>', 'value:Uint<128>'],
    values: cases.map(({ value }) => value.toString()),
  }));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
