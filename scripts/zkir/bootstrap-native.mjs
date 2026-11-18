// Build the independent upstream ZKIR CLI. Requires Rust 1.100.0, Git, and a native C toolchain.
import { spawn } from 'node:child_process';
import { access, copyFile, mkdir, readFile, writeFile } from 'node:fs/promises';
import { resolve, join } from 'node:path';
import { createHash } from 'node:crypto';

const releases = {
  '3.2.0': { revision: '446c7fecc6bd41dab99ebe89ab404e9d077d11a9', cliVersion: '3.2.0', directory: '/private/tmp/noctium-native-zkir' },
  // The official 3.2.1 tag retains 3.2.0 in zkir/Cargo.toml. Preserve that upstream
  // provenance rather than rewriting source or treating the CLI banner as the release identity.
  '3.2.1': { revision: '7a51b3385bbf4bce3604df87a7c70867c9ab43c0', cliVersion: '3.2.0', directory: '/private/tmp/noctium-native-zkir-321' },
};
let requestedVersion = '3.2.0';
let requestedDirectory;
let versionSeen = false;
const args = process.argv.slice(2);
for (let index = 0; index < args.length; index++) {
  const argument = args[index];
  if (argument === '--version') {
    if (versionSeen) throw new Error('Duplicate --version option');
    requestedVersion = args[++index];
    if (!requestedVersion || !Object.hasOwn(releases, requestedVersion))
      throw new Error('Supported native ZKIR versions: 3.2.0, 3.2.1');
    versionSeen = true;
  } else if (argument.startsWith('-')) throw new Error(`Unknown option: ${argument}`);
  else if (requestedDirectory) throw new Error('Expected one output directory');
  else requestedDirectory = argument;
}
const { revision, cliVersion } = releases[requestedVersion];
const repository = 'https://github.com/midnightntwrk/midnight-zkir';
const rust = '1.100.0';
const directory = resolve(requestedDirectory ?? releases[requestedVersion].directory);
const source = resolve(process.env.NOCTIUM_ZKIR_SOURCE ?? join(directory, 'source'));
const cargo = process.env.NOCTIUM_CARGO ?? 'cargo';
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
const target = resolve(source, process.env.CARGO_TARGET_DIR ?? 'target');
await copyFile(join(target, 'release', process.platform === 'win32' ? 'zkir.exe' : 'zkir'), binary);
const version = await run(binary, ['--version'], directory, true);
if (version !== `midnight-zkir ${cliVersion}`) throw new Error(`Unexpected native compiler version: ${version}`);
const manifest = { repository, revision, rust, host: `${process.platform}-${process.arch}`, requestedVersion,
  releaseLabel: requestedVersion, expectedCliVersion: cliVersion, version, binary,
  binarySha256: await digest(binary), cargoLockSha256: await digest(join(source, 'Cargo.lock')),
  command: 'cargo +1.100.0 build --release --locked --package midnight-zkir --features binary' };
await writeFile(join(directory, 'build-manifest.json'), JSON.stringify(manifest, null, 2) + '\n');
console.log(JSON.stringify(manifest, null, 2));
