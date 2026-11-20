import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import * as rt from '@midnight-ntwrk/compact-runtime';
import {Contract, ledger, pureCircuits} from './compact/contract/index.js';

const contract = new Contract({});
const wallet = '00'.repeat(32);
const cases = [
  ['JubjubScalar', 'scalars', 'appendScalar', 'scalarPathRoot', 7n, {kind: 'jubjubScalar', value: '7'}],
];
for (const point of [{x: 0n, y: 1n}, {
  x: 47805549206756120863994733988949966563868680443409072344285414365387721651928n,
  y: 10883866336127360287053583923937114185802477515052223349661086820822299756070n,
}]) {
  cases.push(['JubjubPoint', 'points', 'appendPoint', 'pointPathRoot', point,
    {kind: 'jubjubPoint', x: point.x.toString(), y: point.y.toString()}]);
}
const curveFamilies = [
  ['Secp256k1', 'k1', rt.secp256k1MulGenerator(1n), '0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798'],
  ['Secp256r1', 'r1', rt.secp256r1MulGenerator(1n), '036b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296'],
  ['Curve25519', 'c255', rt.curve25519MulGenerator(1n), '58' + '66'.repeat(31)],
];
for (const [family, prefix, generator, generatorBytes] of curveFamilies) {
  const collect = (role, value, bytes) => {
    const type = family + role;
    cases.push([type, prefix + role + 'Tree',
      'append' + prefix[0].toUpperCase() + prefix.slice(1) + role, prefix + role + 'Root',
      value, {kind: 'foreign', type, bytes: Array.from(bytes)}]);
  };
  for (const role of ['Base', 'Scalar']) {
    for (const value of [0, 1]) collect(role, BigInt(value), [value, ...Array(31).fill(0)]);
  }
  collect('Point', generator, Buffer.from(generatorBytes, 'hex'));
  if (family === 'Curve25519') {
    collect('Point', {x: 0n, y: 1n}, [1, ...Array(31).fill(0)]);
  } else {
    collect('Point', {x: 0n, y: 0n, identity: true}, Array(33).fill(0));
  }
}

const vectors = [];
for (const [type, name, entry, digest, value, leaf] of cases) {
  const initial = await contract.initialState(rt.createConstructorContext(null, wallet));
  const result = await contract.circuits[entry](rt.createCircuitContext({
    circuitId: entry, contractAddress: rt.dummyContractAddress(), coinPublicKeyOrZswapState: wallet,
    contractState: initial.currentContractState.data, privateState: null,
  }), value);
  const tree = ledger(result.context.callContext.currentQueryContext.state)[name];
  const path = tree.pathForLeaf(0n, value);
  assert.deepEqual(tree.findPathForLeaf(value), path);
  const root = tree.root().field;
  assert.equal(pureCircuits[digest](path), root);
  const descriptor = rt['CompactType' + type];
  const leafHash = createHash('sha256').update('mdn:lh')
    .update(rt.toBinaryRepr(descriptor, value)).digest('hex');
  const nativeHash = rt.leafHash({value: descriptor.toValue(value), alignment: descriptor.alignment()});
  assert.equal(leafHash, Buffer.from(nativeHash.value[0]).toString('hex'));
  vectors.push({leaf, leafHash, root: root.toString()});
}
console.log(JSON.stringify(vectors));
