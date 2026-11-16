// Build the independent upstream ZKIR CLI. Requires Rust 1.100.0, Git, and a native C toolchain.
import { spawn } from 'node:child_process';
import { access, copyFile, mkdir, readFile, writeFile } from 'node:fs/promises';
import { resolve, join } from 'node:path';
import { createHash } from 'node:crypto';

const revision = '446c7fecc6bd41dab99ebe89ab404e9d077d11a9';
const repository = 'https://github.com/midnightntwrk/midnight-zkir';
const rust = '1.100.0';
const directory = resolve(process.argv[2] ?? '/private/tmp/nightlean-native-zkir');
const source = resolve(process.env.NIGHTLEAN_ZKIR_SOURCE ?? join(directory, 'source'));
const cargo = process.env.NIGHTLEAN_CARGO ?? 'cargo';
const env = { ...process.env, CARGO_BUILD_JOBS: process.env.CARGO_BUILD_JOBS ?? '4' };
function run(command, args, cwd, capture = false) {
  return new Promise((resolvePromise, reject) => {
    const child = spawn(command, args, { cwd, env, stdio: ['ignore', capture ? 'pipe' : 'inherit', 'inherit'] });
    let result = '';
    if (capture) child.stdout.on('data', (chunk) => { result += chunk; });
    child.on('error', reject);
    child.on('exit', (code, signal) => code === 0 ? resolvePromise(result.trim()) : reject(new Error(`${command} failed (${signal ?? code})`)));
  });
}
const digest = async (path) => createHash('sha256').update(await readFile(path)).digest('hex');
await mkdir(directory, { recursive: true });
try { await access(join(source, '.git')); }
catch {
  await run('git', ['clone', '--filter=blob:none', '--no-checkout', repository, source], directory);
  await run('git', ['checkout', '--detach', revision], source);
}
if (await run('git', ['rev-parse', 'HEAD'], source, true) !== revision) throw new Error('ZKIR source is not the pinned official revision');
if (await run('git', ['status', '--porcelain', '--untracked-files=no'], source, true)) throw new Error('Refusing modified ZKIR source');
await run(cargo, [`+${rust}`, 'build', '--release', '--locked', '--package', 'midnight-zkir', '--features', 'binary'], source);
await mkdir(join(directory, 'bin'), { recursive: true });
const binary = join(directory, 'bin', process.platform === 'win32' ? 'zkir.exe' : 'zkir');
await copyFile(join(source, 'target/release', process.platform === 'win32' ? 'zkir.exe' : 'zkir'), binary);
const version = await run(binary, ['--version'], directory, true);
if (version !== 'midnight-zkir 3.2.0') throw new Error(`Unexpected native compiler version: ${version}`);
const manifest = { repository, revision, rust, host: `${process.platform}-${process.arch}`, version, binary,
  binarySha256: await digest(binary), cargoLockSha256: await digest(join(source, 'Cargo.lock')),
  command: 'cargo +1.100.0 build --release --locked --package midnight-zkir --features binary' };
await writeFile(join(directory, 'build-manifest.json'), JSON.stringify(manifest, null, 2) + '\n');
console.log(JSON.stringify(manifest, null, 2));
