import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdir, mkdtemp, rm, symlink } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const [compactc, runtimePath] = process.argv.slice(2);
assert.ok(compactc && runtimePath,
  'usage: node tests/compact/explicit-booked-coin-recipients.mjs <compactc-0.36.1> <compact-runtime-0.21.0>');
const compilerVersion = execFileSync(compactc, ['--version'], { encoding: 'utf8' }).trim();
assert.match(compilerVersion, /^0\.36\.1 \(7fa3a117c/);
const runtimeDirectory = resolve(runtimePath);
const runtime = await import(pathToFileURL(join(runtimeDirectory, 'dist/index.js')));
assert.equal(runtime.versionString, '0.21.0');

const scratch = await mkdtemp(join(tmpdir(), 'noctium-booked-recipients-'));
try {
  const generated = join(scratch, 'compact');
  const source = fileURLToPath(new URL('./ExplicitBookedCoinRecipients.compact', import.meta.url));
  execFileSync(compactc, ['--skip-zk', source, generated]);
  const runtimeLink = join(generated, 'node_modules/@midnight-ntwrk/compact-runtime');
  await mkdir(dirname(runtimeLink), { recursive: true });
  await symlink(runtimeDirectory, runtimeLink, 'dir');
  const { Contract, ledger } = await import(pathToFileURL(join(generated, 'contract/index.js')));
  const contract = new Contract({});
  const wallet = '00'.repeat(32);
  const own = '09'.repeat(32);
  const { currentContractState } = await contract.initialState(runtime.createConstructorContext(null, wallet));
  const contextFor = () => runtime.createCircuitContext({
    circuitId: 'store', contractAddress: own, coinPublicKeyOrZswapState: wallet,
    contractState: currentContractState.data, privateState: null,
  });
  const domain = new Uint8Array(32).fill(1);
  const nonce = new Uint8Array(32).fill(2);
  const address = new Uint8Array(32).fill(4);
  const other = new Uint8Array(32).fill(5);
  const view = (state) => {
    const { coinSlot, coinSet, coinList } = ledger(state);
    return { coinSlot, coinSet: [...coinSet], coinList: [...coinList] };
  };
  const initial = view(currentContractState.data);

  for (const isContract of [false, true]) {
    const { context, result } = await contract.circuits.store(
      contextFor(), domain, nonce, 5n, true, isContract, address, isContract, address,
    );
    const query = context.callContext.currentQueryContext;
    assert.equal(context.callContext.currentZswapLocalState.outputs.length, 1);
    const qualified = { ...result, mt_index: 0n };
    assert.deepEqual(view(query.state), { coinSlot: qualified, coinSet: [qualified], coinList: [qualified] });

    for (const [book, writeIsContract, writeAddress] of [
      [false, isContract, address], [true, isContract, other], [true, !isContract, address],
    ]) {
      const wrong = contextFor();
      await assert.rejects(contract.circuits.store(
        wrong, domain, nonce, 5n, book, isContract, address, writeIsContract, writeAddress,
      ), /Coin commitment not found/);
      assert.deepEqual(view(wrong.callContext.currentQueryContext.state), initial);
    }
  }
  console.log('Pinned Compact checked wallet and other-contract bookings for Cell, Set and List');
} finally {
  await rm(scratch, { recursive: true, force: true });
}
