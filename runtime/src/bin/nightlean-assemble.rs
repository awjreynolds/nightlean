use anyhow::{Context, Result, anyhow, ensure};
use nightlean_runtime::{
    artifacts,
    assembly::{Inputs, assemble, assemble_verified},
};
use std::{
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
};

const USAGE: &str = "usage: nightlean-assemble --bundle DIRECTORY --manifest-sha256 TRUSTED_DIGEST --config PRIVATE_CONFIG.json --ttl-unix UNIX_SECONDS NEW_OUTPUT_DIRECTORY | PLAN.json CIRCUIT.zkir KEY.prover KEY.verifier NEW_OUTPUT_DIRECTORY --ledger-params LEDGER.params --config PRIVATE_CONFIG.json --ttl-unix UNIX_SECONDS";
fn ttl(value: &OsString) -> Result<u64> {
    let text = value
        .to_str()
        .ok_or_else(|| anyhow!("TTL requires canonical Unix seconds"))?;
    ensure!(
        !text.is_empty() && text.bytes().all(|b| b.is_ascii_digit()) && !text.starts_with('0'),
        "TTL requires canonical positive Unix seconds"
    );
    text.parse::<u64>()
        .context("TTL outside Unix seconds range")
}
fn read(path: &Path, limit: u64) -> Result<Vec<u8>> {
    let metadata = fs::metadata(path).context("cannot inspect selected input")?;
    ensure!(
        metadata.is_file() && metadata.len() <= limit,
        "selected input exceeds file limit"
    );
    let bytes = fs::read(path).context("cannot read selected input")?;
    ensure!(
        bytes.len() as u64 <= limit,
        "selected input exceeds file limit"
    );
    Ok(bytes)
}
fn run() -> Result<()> {
    let args: Vec<OsString> = std::env::args_os().skip(1).collect();
    if args.first().is_some_and(|value| value == "--bundle") {
        ensure!(args.len() == 9, USAGE);
        let mut digest = None;
        let mut config = None;
        let mut expiry = None;
        for pair in args[2..8].chunks_exact(2) {
            match pair[0].to_str() {
                Some("--manifest-sha256") if digest.is_none() => {
                    digest = Some(
                        pair[1]
                            .to_str()
                            .ok_or_else(|| anyhow!("manifest digest must be UTF-8 hex"))?,
                    )
                }
                Some("--config") if config.is_none() => config = Some(PathBuf::from(&pair[1])),
                Some("--ttl-unix") if expiry.is_none() => expiry = Some(ttl(&pair[1])?),
                _ => return Err(anyhow!(USAGE)),
            }
        }
        // Authenticate public bytes before opening or decoding private configuration.
        let bundle = artifacts::verify(
            Path::new(&args[1]),
            Some(digest.ok_or_else(|| anyhow!(USAGE))?),
        )?;
        let config = read(&config.ok_or_else(|| anyhow!(USAGE))?, 1_048_576)?;
        let summary = assemble_verified(
            &bundle,
            &config,
            expiry.ok_or_else(|| anyhow!(USAGE))?,
            Path::new(&args[8]),
        )?;
        println!("{}", serde_json::to_string_pretty(&summary)?);
        return Ok(());
    }
    ensure!(args.len() == 11, USAGE);
    let mut parameters = None;
    let mut config = None;
    let mut ttl = None;
    for pair in args[5..].chunks_exact(2) {
        match pair[0].to_str() {
            Some("--ledger-params") if parameters.is_none() => {
                parameters = Some(PathBuf::from(&pair[1]))
            }
            Some("--config") if config.is_none() => config = Some(PathBuf::from(&pair[1])),
            Some("--ttl-unix") if ttl.is_none() => {
                ttl = Some(crate::ttl(&pair[1])?);
            }
            _ => return Err(anyhow!(USAGE)),
        }
    }
    let plan = read(Path::new(&args[0]), 1_048_576)?;
    let circuit = read(Path::new(&args[1]), 4_194_304)?;
    let prover = read(Path::new(&args[2]), 134_217_728)?;
    let verifier = read(Path::new(&args[3]), 1_048_576)?;
    let parameters = read(&parameters.ok_or_else(|| anyhow!(USAGE))?, 1_048_576)?;
    let config = read(&config.ok_or_else(|| anyhow!(USAGE))?, 1_048_576)?;
    let summary = assemble(
        Inputs {
            plan: &plan,
            circuit: &circuit,
            prover_key: &prover,
            verifier_key: &verifier,
            ledger_parameters: &parameters,
            config: &config,
            ttl_unix: ttl.ok_or_else(|| anyhow!(USAGE))?,
        },
        Path::new(&args[4]),
    )?;
    println!("{}", serde_json::to_string_pretty(&summary)?);
    Ok(())
}
fn main() {
    if let Err(error) = run() {
        eprintln!("nightlean-assemble: {error}");
        std::process::exit(1)
    }
}
