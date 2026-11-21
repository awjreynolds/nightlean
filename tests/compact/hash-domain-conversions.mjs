import assert from 'node:assert/strict';
import { resolve, join } from 'node:path';
import { pathToFileURL } from 'node:url';

const [runtimePath] = process.argv.slice(2);
assert.ok(runtimePath, 'usage: node tests/compact/hash-domain-conversions.mjs <compact-runtime-0.21.0>');
const runtime = await import(pathToFileURL(join(resolve(runtimePath), 'dist/index.js')));
assert.equal(runtime.versionString, '0.21.0');

const modulus = 52435875175126190479447740508185965837690552500527637822603658699938581184513n;
for (const [highByte, field] of [[0, 0n], [255, modulus - 1n]]) {
  const digest = new Uint8Array(32).fill(255);
  digest[31] = highByte;
  assert.equal(runtime.degradeToTransient(digest), (1n << 248n) - 1n);
  const upgraded = Uint8Array.from({ length: 32 }, (_, index) =>
    index === 31 ? 0 : Number((field >> BigInt(8 * index)) & 255n));
  assert.deepEqual(runtime.upgradeFromTransient(field), upgraded);
}
assert.throws(() => runtime.upgradeFromTransient(modulus));
assert.throws(() => runtime.degradeToTransient(new Uint8Array(31)));
console.log('Pinned Compact hash conversions match the canonical boundary values');
