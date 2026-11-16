use midnight_proofs::{poly::kzg::params::ParamsKZG, utils::SerdeFormat};
use sha2::{Digest, Sha256};
use std::{fs, sync::Arc};
use transient_crypto::proofs::ParamsProver;
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    if args.len() != 2 {
        return Err("usage: qualify_helper_parameters PARENT_K5_FILE OUTPUT_K4_FILE".into());
    }
    let input = fs::read(&args[0])?;
    assert_eq!(input.len(), 6532);
    assert_eq!(&input[..4], &5u32.to_le_bytes());
    let original_sha = hex::encode(Sha256::digest(&input));
    assert_eq!(
        original_sha,
        "0a1c9229f315fc1868ff25f668fb83aec4d09f4f23a706b5197c692c619d72c6"
    );
    let params = ParamsProver(Arc::new(ParamsKZG::read_custom(
        &mut input.as_slice(),
        SerdeFormat::RawBytes,
    )?));
    let mut smaller = (*params.0).clone();
    smaller.downsize(4);
    let mut output = Vec::new();
    smaller.write_custom(&mut output, SerdeFormat::RawBytes)?;
    let output_sha = hex::encode(Sha256::digest(&output));
    let path = &args[1];
    if let Ok(prior) = fs::read(path) {
        assert_eq!(prior, output);
    } else {
        use std::io::Write;
        fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(path)?
            .write_all(&output)?;
    }
    println!("{{\"operation\":\"pinned ParamsKZG::downsize(4)\",\"parentK\":5,\"parentSha256\":\"{}\",\"k\":4,\"sha256\":\"{}\",\"bytes\":{}}}", original_sha, output_sha, output.len());
    Ok(())
}
