use noctium_runtime::artifacts::{self, BundleError};
use serde_json::json;
use std::path::Path;

fn run() -> artifacts::Result<serde_json::Value> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some(command @ ("assemble" | "assemble-without-prover-key")) if args.len() == 3 => {
            let recipe = artifacts::read_recipe(Path::new(&args[1]))?;
            let destination = Path::new(&args[2]);
            let manifest = if command == "assemble" {
                artifacts::assemble(recipe, destination)?
            } else {
                artifacts::assemble_without_prover_key(recipe, destination)?
            };
            let digest = artifacts::digest(&artifacts::manifest_bytes(&manifest)?);
            Ok(json!({"status":"assembled","manifestSha256":digest,"entries":manifest.entries.len(),"authenticated":false}))
        }
        Some("verify") if args.len() == 2 || args.len() == 3 => {
            let bundle = artifacts::verify(Path::new(&args[1]), args.get(2).map(String::as_str))?;
            Ok(json!({"status":"verified","entries":bundle.manifest().entries.len(),"externalManifestDigestChecked":args.len()==3,"semanticCorrespondenceProved":false}))
        }
        _ => Err(BundleError { code: "usage", message: "usage: noctium-bundle (assemble | assemble-without-prover-key) RECIPE.json NEW_DIRECTORY | verify DIRECTORY [TRUSTED_MANIFEST_SHA256]".into() }),
    }
}
fn main() {
    match run() {
        Ok(result) => println!("{result}"),
        Err(error) => {
            eprintln!("{}", json!({"status":"error","error":error}));
            std::process::exit(1);
        }
    }
}
