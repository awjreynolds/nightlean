import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';

const [compactc, runtimeDirectory] = process.argv.slice(2);
assert.ok(compactc && runtimeDirectory,
  'usage: node tests/compact/shielded-role-gate.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');

const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/, `expected pinned Compact 0.36.1 compiler, got ${compilerVersion}`);
const runtimePackage = JSON.parse(readFileSync(join(runtimeDirectory, 'package.json'), 'utf8'));
assert.equal(runtimePackage.name, '@midnight-ntwrk/compact-runtime');
assert.equal(runtimePackage.version, '0.21.0', 'expected pinned Compact runtime 0.21.0');

const projectRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const source = join(projectRoot, 'tests/compact/ShieldedRoleGate.compact');
const experiments = join(projectRoot, 'build/experiments');
mkdirSync(experiments, { recursive: true });
const scratch = mkdtempSync(join(experiments, 'shielded-role-gate-'));

const bytes32 = (start) => Uint8Array.from({ length: 32 }, (_, index) => start + index);
const toHex = (bytes) => Buffer.from(bytes).toString('hex');
const pathJson = (path) => ({
  leaf: toHex(path.leaf),
  path: path.path.map(({ sibling, goes_left: goesLeft }) => ({
    sibling: { field: sibling.field.toString() },
    goes_left: goesLeft,
  })),
});

try {
  const generated = join(scratch, 'compact');
  const compile = spawnSync(compactc, ['--skip-zk', source, generated], { encoding: 'utf8' });
  assert.equal(compile.status, 0, `Compact compilation failed:\n${compile.stderr || compile.stdout}`);

  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  mkdirSync(dirname(runtimeLink), { recursive: true });
  symlinkSync(runtimeDirectory, runtimeLink, 'dir');

  const runtimeUrl = pathToFileURL(join(runtimeDirectory, 'dist/index.js')).href;
  const contractUrl = pathToFileURL(join(generated, 'contract/index.js')).href;
  const runtime = await import(runtimeUrl);
  const { Contract, ledger } = await import(contractUrl);

  const salt = bytes32(0xa0);
  const secretKey = bytes32(0x20);
  const role = bytes32(0x60);
  const anchor = bytes32(0x40);
  const forgedLeaf = bytes32(0xd0);
  const walletKey = '00'.repeat(32);
  let witnessPath;
  let observedCommitment;
  const contract = new Contract({
    wit_secretKey: () => [null, secretKey],
    wit_getRoleCommitmentPath: (_context, commitment) => {
      assert.deepEqual(commitment, observedCommitment);
      return [null, witnessPath];
    },
  });
  const { currentContractState } = await contract.initialState(
    runtime.createConstructorContext(null, walletKey), salt,
  );

  const computeContext = runtime.createCircuitContext({
    circuitId: 'vector',
    contractAddress: runtime.dummyContractAddress(),
    coinPublicKeyOrZswapState: walletKey,
    contractState: currentContractState.data,
    privateState: null,
  });
  const partialProofData = {
    input: { value: [], alignment: [] },
    output: undefined,
    publicTranscript: [],
    privateTranscriptOutputs: [],
  };
  const accountId = await contract._computeAccountId_0(computeContext, partialProofData, secretKey);
  const roleCommitment = await contract._computeRoleCommitment_0(
    computeContext, partialProofData, role, accountId,
  );
  const nullifier = contract._computeNullifier_0(roleCommitment);
  observedCommitment = roleCommitment;

  const bytesType = new runtime.CompactTypeBytes(32);
  const aligned = (value) => ({ value: bytesType.toValue(value), alignment: bytesType.alignment() });
  // This pinned OZ slice omits role grant. Seed only the in-memory ledger tree,
  // preserving the Compact state layout and avoiding a test-only circuit.
  const stateWithLeaves = (leaves) => {
    const fields = currentContractState.data.state.asArray();
    const operatorFields = fields[0].asArray();
    let tree = operatorFields[0].asBoundedMerkleTree();
    for (const [index, leaf] of leaves.entries()) {
      tree = tree.update(BigInt(index), aligned(leaf));
    }
    tree = tree.rehash();
    const cursor = runtime.StateValue.newCell({
      value: runtime.CompactTypeField.toValue(BigInt(leaves.length)),
      alignment: runtime.CompactTypeField.alignment(),
    });
    const operatorState = runtime.StateValue.newArray()
      .arrayPush(runtime.StateValue.newBoundedMerkleTree(tree))
      .arrayPush(cursor);
    let state = runtime.StateValue.newArray().arrayPush(operatorState);
    for (const field of fields.slice(1)) state = state.arrayPush(field);
    return state;
  };
  const revoke = (state, digest) => {
    const fields = state.asArray();
    const revoked = fields[1].asMap().insert(aligned(digest), runtime.StateValue.newNull());
    let updated = runtime.StateValue.newArray().arrayPush(fields[0])
      .arrayPush(runtime.StateValue.newMap(revoked));
    for (const field of fields.slice(2)) updated = updated.arrayPush(field);
    return updated;
  };
  const validState = stateWithLeaves([anchor, roleCommitment]);
  const validLedger = ledger(validState);
  const validPath = validLedger.operatorRoles.pathForLeaf(1n, roleCommitment);
  const validRoot = validLedger.operatorRoles.root();
  assert.equal(validLedger.operatorRoles.firstFree(), 2n);
  assert.deepEqual(validPath.leaf, roleCommitment);
  assert.equal(contract._merkleTreePathRoot_0(validPath).field, validRoot.field);
  assert.equal(validPath.path.length, 20);
  assert.deepEqual(validPath.path[0].goes_left, false);
  const anchorDigest = contract._degradeToTransient_0(contract._persistentHash_2({
    domain_sep: Uint8Array.from([109, 100, 110, 58, 108, 104]),
    data: anchor,
  }));
  assert.equal(validPath.path[0].sibling.field, anchorDigest);

  const contextFor = (state) => runtime.createCircuitContext({
    circuitId: 'protectedAction',
    contractAddress: runtime.dummyContractAddress(),
    coinPublicKeyOrZswapState: walletKey,
    contractState: state,
    privateState: null,
  });
  const invokeRejected = async (state, path, diagnostic) => {
    witnessPath = path;
    const context = contextFor(state);
    await assert.rejects(contract.circuits.protectedAction(context, role), diagnostic);
    assert.equal(ledger(state).protectedActions, 0n);
    assert.equal(ledger(context.callContext.currentQueryContext.state).protectedActions, 0n);
  };

  witnessPath = validPath;
  const accepted = await contract.circuits.protectedAction(contextFor(validState), role);
  assert.deepEqual(accepted.result, []);
  assert.equal(ledger(accepted.context.callContext.currentQueryContext.state).protectedActions, 1n);

  const wrongLeafState = stateWithLeaves([anchor, forgedLeaf]);
  const wrongLeafPath = ledger(wrongLeafState).operatorRoles.pathForLeaf(1n, forgedLeaf);
  assert.equal(contract._merkleTreePathRoot_0(wrongLeafPath).field,
    ledger(wrongLeafState).operatorRoles.root().field);
  assert.notDeepEqual(wrongLeafPath.leaf, roleCommitment);
  await invokeRejected(wrongLeafState, wrongLeafPath, /path leaf does not match role commitment/);

  const wrongRootPath = {
    ...validPath,
    path: validPath.path.map((step, index) => index === 0
      ? { ...step, sibling: { field: step.sibling.field + 1n } }
      : step),
  };
  const wrongRoot = contract._merkleTreePathRoot_0(wrongRootPath);
  assert.notEqual(wrongRoot.field, validRoot.field);
  await invokeRejected(validState, wrongRootPath, /unauthorized role/);

  const revokedState = revoke(validState, nullifier);
  assert.equal(ledger(revokedState).revokedRoleNullifiers.member(nullifier), true);
  await invokeRejected(revokedState, validPath, /unauthorized role/);

  const vector = {
    profile: {
      compiler: compilerVersion,
      runtime: runtimePackage.version,
      ledger: '9.1.0.1',
    },
    inputs: {
      instanceSalt: toHex(salt),
      secretKey: toHex(secretKey),
      roleIdentifier: toHex(role),
      anchorLeaf: toHex(anchor),
    },
    derived: {
      accountId: toHex(accountId),
      roleCommitment: toHex(roleCommitment),
      nullifier: toHex(nullifier),
    },
    cases: {
      accepted: {
        root: validRoot.field.toString(),
        leafIndex: '1',
        path: pathJson(validPath),
        publicOutput: { result: [], protectedActions: '1' },
      },
      wrongLeaf: {
        root: ledger(wrongLeafState).operatorRoles.root().field.toString(),
        path: pathJson(wrongLeafPath),
        publicOutput: { rejected: 'path leaf does not match role commitment', protectedActions: '0' },
      },
      wrongRoot: {
        contractRoot: validRoot.field.toString(),
        witnessPathRoot: wrongRoot.field.toString(),
        path: pathJson(wrongRootPath),
        publicOutput: { rejected: 'unauthorized role', protectedActions: '0' },
      },
      revoked: {
        root: validRoot.field.toString(),
        nullifier: toHex(nullifier),
        path: pathJson(validPath),
        publicOutput: { rejected: 'unauthorized role', protectedActions: '0' },
      },
    },
    traceScope: 'Compact 0.36.1 in-memory protectedAction circuit; the tree and revocation set are seeded through Compact runtime StateValue. No proving, transaction assembly, or ledger submission.',
  };
  const vectorPath = process.env.NOCTIUM_SHIELDED_ROLE_GATE_VECTOR_OUT;
  if (vectorPath) {
    const outputPath = resolve(vectorPath);
    mkdirSync(dirname(outputPath), { recursive: true });
    writeFileSync(outputPath, `${JSON.stringify(vector, null, 2)}\n`);
  }
  console.log('Shielded role gate: seeded membership accepted; wrong leaf, wrong root, and revoked role rejected');
  console.log(JSON.stringify({ roleCommitment: toHex(roleCommitment), root: validRoot.field.toString(), protectedActions: '1' }));
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
