//! Public, selected-entrypoint bundles. Hashes establish integrity, not authenticity.
use serde::{Deserialize, Serialize};
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt, fs,
    io::{self, Read, Write},
    path::{Component, Path, PathBuf},
};

pub const SCHEMA_VERSION: u32 = 1;
pub const MAX_ENTRIES: usize = 64;
pub const MAX_FILE_BYTES: u64 = 256 * 1024 * 1024;
pub const MAX_TOTAL_BYTES: u64 = 1024 * 1024 * 1024;
pub const MAX_JSON_BYTES: u64 = 2 * 1024 * 1024;
const LEDGER_REVISION: &str = "a2b30128ca4b660b73a068e29b56b48ede8c9a74";
const ZKIR_REVISION: &str = crate::profile::REVISION;
const TOOL_REPOSITORY: &str = "https://github.com/midnightntwrk/midnight-zkir";

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct BundleError {
    pub code: &'static str,
    pub message: String,
}
impl fmt::Display for BundleError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.code, self.message)
    }
}
impl std::error::Error for BundleError {}
pub type Result<T> = std::result::Result<T, BundleError>;
fn error(code: &'static str, message: impl Into<String>) -> BundleError {
    BundleError {
        code,
        message: message.into(),
    }
}
fn require(condition: bool, code: &'static str, message: &str) -> Result<()> {
    if condition {
        Ok(())
    } else {
        Err(error(code, message))
    }
}
fn io_error(_: io::Error) -> BundleError {
    error("io_error", "cannot access selected bundle file")
}

#[derive(Clone, Copy, Debug, Deserialize, Serialize, Eq, PartialEq, Ord, PartialOrd)]
#[serde(rename_all = "camelCase")]
pub enum Role {
    Source,
    Circuit,
    Plan,
    Metadata,
    Abi,
    Profile,
    LedgerParameters,
    ProverKey,
    VerifierKey,
    Toolchain,
}
impl Role {
    fn path(self, name: &str) -> String {
        match self {
            Self::Source => format!("source/{name}"),
            Self::Circuit => "circuit/entrypoint.zkir".into(),
            Self::Plan => "plan/entrypoint.impact.json".into(),
            Self::Metadata => "schema/nightlean.json".into(),
            Self::Abi => format!("schema/{name}"),
            Self::Profile => "profile/target.json".into(),
            Self::LedgerParameters => "parameters/ledger.params".into(),
            Self::ProverKey => "keys/entrypoint.prover".into(),
            Self::VerifierKey => "keys/entrypoint.verifier".into(),
            Self::Toolchain => "provenance/native-zkir.json".into(),
        }
    }
}

/// This recipe is local build input. Its paths never enter the public manifest.
#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct Recipe {
    pub schema_version: u32,
    pub compiler_revision: String,
    pub files: Vec<Selection>,
}
#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct Selection {
    pub role: Role,
    pub name: String,
    pub input: PathBuf,
}
#[derive(Clone, Debug, Deserialize, Serialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct Entry {
    pub role: Role,
    pub name: String,
    pub path: String,
    pub size: u64,
    pub sha256: String,
}
#[derive(Clone, Debug, Deserialize, Serialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct Manifest {
    pub schema_version: u32,
    pub kind: String,
    pub profile: String,
    pub ledger_revision: String,
    pub zkir_revision: String,
    pub compiler: Compiler,
    pub stages: Vec<String>,
    pub entries: Vec<Entry>,
}
#[derive(Clone, Debug, Deserialize, Serialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct Compiler {
    pub implementation: String,
    pub toolchain: String,
    pub source_revision: String,
}

/// Retains verified payload bytes so callers need not reopen mutable paths.
pub struct VerifiedBundle {
    manifest: Manifest,
    files: BTreeMap<String, Vec<u8>>,
    authenticated_manifest_sha256: Option<String>,
}
impl VerifiedBundle {
    /// External authority supplied to `verify`. Integrity-only verification returns `None`.
    pub fn authenticated_manifest_sha256(&self) -> Option<&str> {
        self.authenticated_manifest_sha256.as_deref()
    }
    pub fn manifest(&self) -> &Manifest {
        &self.manifest
    }
    pub fn file(&self, role: Role) -> Result<&[u8]> {
        require(
            role != Role::Source,
            "invalid_role",
            "select source files by name",
        )?;
        let entry = self
            .manifest
            .entries
            .iter()
            .find(|entry| entry.role == role)
            .ok_or_else(|| error("missing_role", "bundle role is absent"))?;
        self.files
            .get(&entry.path)
            .map(Vec::as_slice)
            .ok_or_else(|| error("missing_role", "verified payload is absent"))
    }
    pub fn source(&self, name: &str) -> Result<&[u8]> {
        let entry = self
            .manifest
            .entries
            .iter()
            .find(|entry| entry.role == Role::Source && entry.name == name)
            .ok_or_else(|| error("missing_role", "selected source is absent"))?;
        self.files
            .get(&entry.path)
            .map(Vec::as_slice)
            .ok_or_else(|| error("missing_role", "verified source is absent"))
    }
}

fn hex_length(value: &str, length: usize) -> bool {
    value.len() == length
        && value
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}
fn safe_relative(name: &str) -> Result<()> {
    require(
        name.is_ascii(),
        "unsupported_name",
        "schema 1 logical artifact names must use ASCII",
    )?;
    require(
        !name.is_empty()
            && name.len() <= 240
            && !name.contains('\\')
            && !name.contains(':')
            && !name.contains('\0')
            && !name
                .split('/')
                .any(|p| p.is_empty() || p == "." || p == "..")
            && Path::new(name)
                .components()
                .all(|p| matches!(p, Component::Normal(_))),
        "unsafe_path",
        "bundle paths must be canonical relative paths",
    )
}
fn private_name(name: &str) -> bool {
    let name = name.rsplit('/').next().unwrap_or(name).to_ascii_lowercase();
    [
        "runtime-config",
        "runtime_config",
        "preimage",
        "private-state",
        "private_state",
    ]
    .iter()
    .any(|part| name.contains(part))
        || name == "witness.json"
        || name.ends_with("-witness.json")
        || name.ends_with("_witness.json")
}
fn validate_name(role: Role, name: &str) -> Result<()> {
    safe_relative(name)?;
    require(
        !private_name(name),
        "private_artifact",
        "private execution material is forbidden in a public bundle",
    )?;
    let expected = match role {
        Role::Source => name.ends_with(".lean"),
        Role::Circuit => !name.contains('/') && name.ends_with(".zkir"),
        Role::Plan => !name.contains('/') && name.ends_with(".impact.json"),
        Role::Metadata => name == "nightlean.json",
        Role::Abi => name == "nightlean_runtime.h" || name == "abi.schema.json",
        Role::Profile => name == "target.json",
        Role::LedgerParameters => name == "ledger.params",
        Role::ProverKey => name == "entrypoint.prover",
        Role::VerifierKey => name == "entrypoint.verifier",
        Role::Toolchain => name == "native-zkir.json",
    };
    require(
        expected,
        "invalid_role",
        "file name does not match its public artifact role",
    )
}
fn no_symlinks(path: &Path) -> Result<()> {
    let mut current = PathBuf::new();
    for component in path.components() {
        require(
            !matches!(component, Component::ParentDir),
            "unsafe_path",
            "parent traversal is forbidden",
        )?;
        current.push(component.as_os_str());
        let metadata = fs::symlink_metadata(&current).map_err(io_error)?;
        require(
            !metadata.file_type().is_symlink(),
            "unsafe_path",
            "symbolic links are forbidden",
        )?;
    }
    Ok(())
}
fn read(path: &Path, limit: u64) -> Result<Vec<u8>> {
    no_symlinks(path)?;
    let metadata = fs::metadata(path).map_err(io_error)?;
    require(
        metadata.is_file(),
        "invalid_file",
        "artifact must be a regular file",
    )?;
    require(
        metadata.len() <= limit,
        "limit_exceeded",
        "artifact exceeds its size limit",
    )?;
    let mut bytes = Vec::new();
    fs::File::open(path)
        .map_err(io_error)?
        .take(limit + 1)
        .read_to_end(&mut bytes)
        .map_err(io_error)?;
    require(
        bytes.len() as u64 <= limit,
        "limit_exceeded",
        "artifact exceeds its size limit",
    )?;
    Ok(bytes)
}
pub fn read_recipe(path: &Path) -> Result<Recipe> {
    let bytes = read(path, MAX_JSON_BYTES)?;
    serde_json::from_slice(&bytes).map_err(|_| error("invalid_recipe", "invalid bundle recipe"))
}
fn json(bytes: &[u8]) -> Result<Value> {
    require(
        bytes.len() as u64 <= MAX_JSON_BYTES,
        "limit_exceeded",
        "JSON artifact exceeds its size limit",
    )?;
    serde_json::from_slice(bytes).map_err(|_| error("invalid_json", "invalid public JSON artifact"))
}
fn only_fields(value: &Value, allowed: &[&str]) -> Result<()> {
    let object = value
        .as_object()
        .ok_or_else(|| error("invalid_json", "public artifact must be an object"))?;
    require(
        object.keys().all(|key| allowed.contains(&key.as_str())),
        "unsupported_schema",
        "public artifact contains an unknown top-level field",
    )
}
fn canonical(value: &impl Serialize) -> Result<Vec<u8>> {
    let value = serde_json::to_value(value)
        .map_err(|_| error("invalid_json", "cannot serialize public artifact"))?;
    // serde_json maps are ordered without preserve_order. Pin canonical byte format.
    let mut bytes = serde_json::to_vec(&value)
        .map_err(|_| error("invalid_json", "cannot serialize public artifact"))?;
    bytes.push(b'\n');
    Ok(bytes)
}
pub fn manifest_bytes(manifest: &Manifest) -> Result<Vec<u8>> {
    canonical(manifest)
}
pub fn digest(bytes: &[u8]) -> String {
    hex::encode(Sha256::digest(bytes))
}

fn normalize_toolchain(bytes: &[u8]) -> Result<Vec<u8>> {
    let input = json(bytes)?;
    let object = input
        .as_object()
        .ok_or_else(|| error("invalid_provenance", "native provenance must be an object"))?;
    let allowed = [
        "repository",
        "revision",
        "rust",
        "host",
        "version",
        "binary",
        "binarySha256",
        "cargoLockSha256",
        "command",
        "requestedVersion",
        "releaseLabel",
        "expectedCliVersion",
    ];
    require(
        object.keys().all(|key| allowed.contains(&key.as_str())),
        "invalid_provenance",
        "unknown native provenance field",
    )?;
    require(
        input["repository"] == TOOL_REPOSITORY
            && input["revision"] == ZKIR_REVISION
            && input["rust"] == "1.100.0"
            && input["version"] == crate::profile::CLI_BANNER,
        "profile_mismatch",
        "native tool identity does not match the supported profile",
    )?;
    for field in ["requestedVersion", "releaseLabel", "expectedCliVersion"] {
        let expected = if field == "expectedCliVersion" {
            crate::profile::CRATE_VERSION
        } else {
            crate::profile::RELEASE
        };
        require(
            if cfg!(feature = "zkir-321") {
                input.get(field).is_some_and(|v| v == expected)
            } else {
                input.get(field).is_none_or(|v| v == expected)
            },
            "profile_mismatch",
            "native tool release identity differs from profile",
        )?;
    }
    let mut normalized = BTreeMap::new();
    for field in [
        "repository",
        "revision",
        "rust",
        "host",
        "version",
        "binarySha256",
        "cargoLockSha256",
        "command",
    ] {
        let text = input[field].as_str().ok_or_else(|| {
            error(
                "invalid_provenance",
                "native provenance field must be a string",
            )
        })?;
        if field.ends_with("Sha256") {
            require(
                hex_length(text, 64),
                "invalid_provenance",
                "native provenance digest must be lowercase SHA-256",
            )?;
        } else if field == "host" {
            require(
                !text.is_empty()
                    && text.len() <= 80
                    && text
                        .bytes()
                        .all(|b| b.is_ascii_alphanumeric() || b == b'-' || b == b'_'),
                "invalid_provenance",
                "invalid native host identity",
            )?;
        } else if field == "command" {
            require(
                text == "cargo +1.100.0 build --release --locked --package midnight-zkir --features binary",
                "invalid_provenance",
                "unsupported native build command",
            )?;
        }
        normalized.insert(field.to_owned(), text.to_owned());
    }
    if cfg!(feature = "zkir-321") {
        normalized.insert("requestedVersion".into(), crate::profile::RELEASE.into());
        normalized.insert("releaseLabel".into(), crate::profile::RELEASE.into());
        normalized.insert(
            "expectedCliVersion".into(),
            crate::profile::CRATE_VERSION.into(),
        );
    }
    canonical(&normalized)
}
fn validate_profile(value: &Value) -> Result<()> {
    let expected = crate::profile::target_json();
    require(
        value == &expected,
        "profile_mismatch",
        "target profile does not match the linked native consumer",
    )
}

type Payloads = BTreeMap<Role, Vec<(String, Vec<u8>)>>;
fn one(payloads: &Payloads, role: Role) -> Result<(&str, &[u8])> {
    let values = payloads.get(&role).ok_or_else(|| {
        error(
            "missing_role",
            "bundle is missing a required public artifact role",
        )
    })?;
    require(
        values.len() == 1,
        "duplicate_role",
        "public artifact role must occur exactly once",
    )?;
    Ok((&values[0].0, &values[0].1))
}
fn validate_payloads(payloads: &Payloads) -> Result<()> {
    require(
        payloads
            .get(&Role::Source)
            .is_some_and(|sources| !sources.is_empty()),
        "missing_role",
        "bundle needs explicit source selections",
    )?;
    for role in [
        Role::Circuit,
        Role::Plan,
        Role::Metadata,
        Role::Abi,
        Role::Profile,
        Role::LedgerParameters,
        Role::ProverKey,
        Role::VerifierKey,
        Role::Toolchain,
    ] {
        one(payloads, role)?;
    }
    let (circuit_name, circuit_bytes) = one(payloads, Role::Circuit)?;
    let circuit = json(circuit_bytes)?;
    only_fields(
        &circuit,
        &[
            "version",
            "inputs",
            "outputs",
            "do_communications_commitment",
            "instructions",
        ],
    )?;
    require(
        circuit["version"] == serde_json::json!({"major":3,"minor":2})
            && circuit["do_communications_commitment"] == true
            && circuit["instructions"].is_array(),
        "profile_mismatch",
        "bundle requires a native ZKIR 3.2 contract relation",
    )?;
    let (plan_name, plan_bytes) = one(payloads, Role::Plan)?;
    let plan = json(plan_bytes)?;
    only_fields(
        &plan,
        &[
            "schemaVersion",
            "nativeCircuitFile",
            "contractName",
            "entrypoint",
            "operations",
            "reads",
            "state",
            "circuit",
            "guards",
            "target",
            "targetProfile",
        ],
    )?;
    if let Some(target) = plan.get("target") {
        require(
            target.is_string(),
            "profile_mismatch",
            "plan target must be a string when present",
        )?;
    }
    require(
        crate::profile::validate_plan(
            plan.get("target").and_then(Value::as_str),
            plan.get("targetProfile"),
        ),
        "profile_mismatch",
        "plan target differs from linked native consumer",
    )?;
    require(
        plan["schemaVersion"] == 1
            && plan["nativeCircuitFile"] == circuit_name
            && plan["operations"].is_array()
            && plan["reads"].is_array()
            && plan["state"].is_array()
            && plan["circuit"].is_object(),
        "plan_mismatch",
        "execution plan does not name the selected native circuit",
    )?;
    let contract = plan["contractName"]
        .as_str()
        .ok_or_else(|| error("plan_mismatch", "plan lacks a contract name"))?;
    let entrypoint = plan["entrypoint"]
        .as_str()
        .ok_or_else(|| error("plan_mismatch", "plan lacks an entrypoint name"))?;
    require(
        !contract.is_empty() && !entrypoint.is_empty(),
        "plan_mismatch",
        "contract and entrypoint names must be nonempty",
    )?;
    let profile = json(one(payloads, Role::Profile)?.1)?;
    validate_profile(&profile)?;
    let metadata = json(one(payloads, Role::Metadata)?.1)?;
    only_fields(
        &metadata,
        &[
            "schemaVersion",
            "target",
            "targetProfile",
            "qualification",
            "deployable",
            "contracts",
            "circuits",
        ],
    )?;
    require(
        metadata["schemaVersion"] == 1
            && metadata["target"] == crate::profile::NAME
            && metadata["targetProfile"] == profile,
        "profile_mismatch",
        "compiler metadata does not match the target profile",
    )?;
    let contracts = metadata["contracts"]
        .as_array()
        .ok_or_else(|| error("plan_mismatch", "compiler metadata lacks contracts"))?;
    let matched: Vec<_> = contracts
        .iter()
        .filter(|item| item["name"] == contract)
        .collect();
    require(
        matched.len() == 1,
        "plan_mismatch",
        "selected plan contract is missing or ambiguous",
    )?;
    require(
        matched[0]["state"] == plan["state"],
        "plan_mismatch",
        "plan state schema differs from compiler metadata",
    )?;
    let entries = matched[0]["entrypoints"]
        .as_array()
        .ok_or_else(|| error("plan_mismatch", "metadata lacks entrypoints"))?;
    let matched: Vec<_> = entries
        .iter()
        .filter(|item| item["name"] == entrypoint)
        .collect();
    require(
        matched.len() == 1
            && matched[0]["nativeCircuitFile"] == circuit_name
            && matched[0]["nativePlanFile"] == plan_name
            && matched[0]["circuit"] == plan["circuit"]["name"],
        "plan_mismatch",
        "metadata entrypoint does not match selected plan and circuit",
    )?;
    let circuits = metadata["circuits"]
        .as_array()
        .ok_or_else(|| error("plan_mismatch", "metadata lacks circuit schemas"))?;
    require(
        circuits
            .iter()
            .filter(|value| **value == plan["circuit"])
            .count()
            == 1,
        "plan_mismatch",
        "plan circuit schema differs from compiler metadata",
    )?;
    let (abi_name, abi_bytes) = one(payloads, Role::Abi)?;
    if abi_name.ends_with(".h") {
        let header = std::str::from_utf8(abi_bytes)
            .map_err(|_| error("invalid_abi", "ABI header is not UTF-8"))?;
        require(
            header.contains("#define NIGHTLEAN_ABI_VERSION 1u")
                && header.contains("nightlean_session_begin("),
            "invalid_abi",
            "unsupported native ABI header",
        )?;
    } else {
        let abi = json(abi_bytes)?;
        require(
            abi["abiVersion"] == 1 && abi["profile"] == crate::profile::ABI,
            "invalid_abi",
            "unsupported ABI schema",
        )?;
    }
    let toolchain = one(payloads, Role::Toolchain)?.1;
    require(
        normalize_toolchain(toolchain)? == toolchain,
        "invalid_provenance",
        "native provenance must use normalized canonical encoding",
    )?;
    for role in [Role::LedgerParameters, Role::ProverKey, Role::VerifierKey] {
        require(
            !one(payloads, role)?.1.is_empty(),
            "invalid_file",
            "public parameter/key file must be nonempty",
        )?;
    }
    Ok(())
}

fn validate_manifest(manifest: &Manifest) -> Result<()> {
    require(
        manifest.schema_version == SCHEMA_VERSION
            && manifest.kind == "nightlean-public-entrypoint-bundle",
        "unsupported_version",
        "unsupported bundle schema or kind",
    )?;
    require(
        manifest.profile == crate::profile::NAME
            && manifest.ledger_revision == LEDGER_REVISION
            && manifest.zkir_revision == ZKIR_REVISION,
        "profile_mismatch",
        "bundle profile or source pins differ",
    )?;
    require(
        manifest.compiler.implementation == "Lean4"
            && manifest.compiler.toolchain == "leanprover/lean4:v4.35.0"
            && hex_length(&manifest.compiler.source_revision, 40),
        "invalid_provenance",
        "unsupported compiler provenance",
    )?;
    require(
        manifest.stages
            == [
                "lean-compilation",
                "native-key-generation",
                "public-bundle-assembly",
            ],
        "unsupported_version",
        "unsupported artifact stage sequence",
    )?;
    require(
        !manifest.entries.is_empty() && manifest.entries.len() <= MAX_ENTRIES,
        "limit_exceeded",
        "invalid bundle entry count",
    )?;
    let mut paths: BTreeSet<String> = BTreeSet::new();
    let mut directory_spellings: BTreeMap<String, String> = BTreeMap::new();
    let mut keys = BTreeSet::new();
    let mut previous: Option<(&Role, &str)> = None;
    let mut total = 0u64;
    for entry in &manifest.entries {
        validate_name(entry.role, &entry.name)?;
        require(
            entry.path == entry.role.path(&entry.name),
            "unsafe_path",
            "artifact path does not match its fixed public role",
        )?;
        let mut prefix = String::new();
        let components: Vec<_> = entry.path.split('/').collect();
        for component in &components[..components.len() - 1] {
            if !prefix.is_empty() {
                prefix.push('/');
            }
            prefix.push_str(component);
            let folded = prefix.to_lowercase();
            if let Some(existing) = directory_spellings.get(&folded) {
                require(
                    existing == &prefix,
                    "duplicate_path",
                    "shared directory prefixes must use identical casing",
                )?;
            } else {
                directory_spellings.insert(folded, prefix.clone());
            }
        }
        let folded_path = entry.path.to_lowercase();
        require(
            paths.iter().all(|old| {
                !folded_path.starts_with(&format!("{old}/"))
                    && !old.starts_with(&format!("{folded_path}/"))
            }),
            "duplicate_path",
            "public file paths conflict with directories",
        )?;
        require(
            paths.insert(folded_path) && keys.insert((entry.role, &entry.name)),
            "duplicate_path",
            "duplicate public artifact path or name",
        )?;
        if let Some(old) = previous {
            require(
                old < (&entry.role, &entry.name),
                "noncanonical_manifest",
                "manifest entries must be ordered by role then name",
            )?;
        }
        previous = Some((&entry.role, &entry.name));
        require(
            entry.size <= MAX_FILE_BYTES && hex_length(&entry.sha256, 64),
            "invalid_manifest",
            "invalid artifact digest or size",
        )?;
        total = total
            .checked_add(entry.size)
            .ok_or_else(|| error("limit_exceeded", "bundle total size overflow"))?;
    }
    require(
        total <= MAX_TOTAL_BYTES,
        "limit_exceeded",
        "bundle exceeds total size limit",
    )
}

/// Assemble only explicitly selected files. An existing destination is never overwritten.
pub fn assemble(recipe: Recipe, destination: &Path) -> Result<Manifest> {
    require(
        recipe.schema_version == SCHEMA_VERSION,
        "unsupported_version",
        "unsupported recipe version",
    )?;
    require(
        !recipe.files.is_empty() && recipe.files.len() <= MAX_ENTRIES,
        "limit_exceeded",
        "invalid selection count",
    )?;
    require(
        hex_length(&recipe.compiler_revision, 40),
        "invalid_provenance",
        "compiler source revision must be a lowercase Git SHA",
    )?;
    let mut payloads = Payloads::new();
    let mut names = BTreeSet::new();
    let mut total = 0u64;
    for selection in recipe.files {
        validate_name(selection.role, &selection.name)?;
        require(
            !selection
                .input
                .file_name()
                .is_some_and(|name| private_name(&name.to_string_lossy())),
            "private_artifact",
            "private execution files cannot be selected under a public name",
        )?;
        let extension = selection.input.extension().and_then(|value| value.to_str());
        let expected_extension = match selection.role {
            Role::Source => "lean",
            Role::Circuit => "zkir",
            Role::LedgerParameters => "params",
            Role::ProverKey => "prover",
            Role::VerifierKey => "verifier",
            Role::Abi if selection.name.ends_with(".h") => "h",
            _ => "json",
        };
        require(
            extension == Some(expected_extension),
            "invalid_role",
            "selected input extension differs from its public artifact role",
        )?;
        require(
            names.insert((selection.role, selection.name.clone())),
            "duplicate_path",
            "duplicate public selection",
        )?;
        let mut bytes = read(&selection.input, MAX_FILE_BYTES)?;
        if selection.role == Role::Toolchain {
            bytes = normalize_toolchain(&bytes)?;
        }
        total = total
            .checked_add(bytes.len() as u64)
            .ok_or_else(|| error("limit_exceeded", "bundle total size overflow"))?;
        require(
            total <= MAX_TOTAL_BYTES,
            "limit_exceeded",
            "bundle exceeds total size limit",
        )?;
        payloads
            .entry(selection.role)
            .or_default()
            .push((selection.name, bytes));
    }
    for values in payloads.values_mut() {
        values.sort_by(|a, b| a.0.cmp(&b.0));
    }
    validate_payloads(&payloads)?;
    let entries = payloads
        .iter()
        .flat_map(|(role, values)| {
            values.iter().map(|(name, bytes)| Entry {
                role: *role,
                name: name.clone(),
                path: role.path(name),
                size: bytes.len() as u64,
                sha256: digest(bytes),
            })
        })
        .collect();
    let manifest = Manifest {
        schema_version: SCHEMA_VERSION,
        kind: "nightlean-public-entrypoint-bundle".into(),
        profile: crate::profile::NAME.into(),
        ledger_revision: LEDGER_REVISION.into(),
        zkir_revision: ZKIR_REVISION.into(),
        compiler: Compiler {
            implementation: "Lean4".into(),
            toolchain: "leanprover/lean4:v4.35.0".into(),
            source_revision: recipe.compiler_revision,
        },
        stages: vec![
            "lean-compilation".into(),
            "native-key-generation".into(),
            "public-bundle-assembly".into(),
        ],
        entries,
    };
    validate_manifest(&manifest)?;
    no_symlinks(
        destination
            .parent()
            .ok_or_else(|| error("unsafe_path", "destination requires an existing parent"))?,
    )?;
    fs::create_dir(destination).map_err(|_| {
        error(
            "destination_exists",
            "destination must be a new directory under an existing parent",
        )
    })?;
    let write_result = (|| {
        for (role, values) in &payloads {
            for (name, bytes) in values {
                let path = destination.join(role.path(name));
                fs::create_dir_all(path.parent().unwrap()).map_err(io_error)?;
                // Exclusive creation also rejects aliases normalized by the host filesystem.
                fs::OpenOptions::new()
                    .write(true)
                    .create_new(true)
                    .open(path)
                    .map_err(io_error)?
                    .write_all(bytes)
                    .map_err(io_error)?;
            }
        }
        // Manifest is the completion marker. Failed assembly removes only its own new directory.
        fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(destination.join("manifest.json"))
            .map_err(io_error)?
            .write_all(&manifest_bytes(&manifest)?)
            .map_err(io_error)
    })();
    if write_result.is_err() {
        let _ = fs::remove_dir_all(destination);
    }
    write_result?;
    Ok(manifest)
}

fn reject_extra_files(root: &Path, manifest: &Manifest) -> Result<()> {
    let expected: BTreeSet<PathBuf> = manifest
        .entries
        .iter()
        .map(|entry| root.join(&entry.path))
        .chain(std::iter::once(root.join("manifest.json")))
        .collect();
    let mut allowed_dirs = BTreeSet::new();
    for path in &expected {
        let mut parent = path.parent();
        while let Some(path) = parent {
            if path == root {
                break;
            }
            allowed_dirs.insert(path.to_path_buf());
            parent = path.parent();
        }
    }
    let mut directories = vec![root.to_path_buf()];
    while let Some(directory) = directories.pop() {
        for entry in fs::read_dir(directory).map_err(io_error)? {
            let entry = entry.map_err(io_error)?;
            let kind = entry.file_type().map_err(io_error)?;
            let path = entry.path();
            require(
                !kind.is_symlink(),
                "unsafe_path",
                "bundle contains a symbolic link",
            )?;
            if kind.is_dir() {
                require(
                    allowed_dirs.contains(&path),
                    "unexpected_file",
                    "bundle contains an unlisted directory",
                )?;
                directories.push(path);
            } else {
                require(
                    kind.is_file() && expected.contains(&path),
                    "unexpected_file",
                    "bundle contains an unlisted file",
                )?;
            }
        }
    }
    Ok(())
}
/// Verify before use, then execute retained bytes. A trusted digest authenticates the manifest.
/// Without a trusted digest or signature, an attacker could replace the entire unsigned bundle.
pub fn verify(root: &Path, trusted_manifest_sha256: Option<&str>) -> Result<VerifiedBundle> {
    verify_with_limit(root, trusted_manifest_sha256, MAX_TOTAL_BYTES)
}
/// Apply a host payload budget after manifest authentication, before reading any payload.
/// This narrows resource policy without changing the compiler or other bundle consumers.
pub fn verify_with_limit(
    root: &Path,
    trusted_manifest_sha256: Option<&str>,
    max_total_bytes: u64,
) -> Result<VerifiedBundle> {
    require(
        max_total_bytes > 0 && max_total_bytes <= MAX_TOTAL_BYTES,
        "limit_exceeded",
        "unsupported host payload budget",
    )?;
    no_symlinks(root)?;
    let manifest_data = read(&root.join("manifest.json"), MAX_JSON_BYTES)?;
    if let Some(expected) = trusted_manifest_sha256 {
        require(
            hex_length(expected, 64),
            "invalid_digest",
            "trusted manifest digest must be lowercase SHA-256",
        )?;
        require(
            digest(&manifest_data) == expected,
            "manifest_digest_mismatch",
            "manifest differs from trusted external digest",
        )?;
    }
    let manifest: Manifest = serde_json::from_slice(&manifest_data)
        .map_err(|_| error("invalid_manifest", "invalid bundle manifest"))?;
    validate_manifest(&manifest)?;
    require(
        manifest_bytes(&manifest)? == manifest_data,
        "noncanonical_manifest",
        "manifest must use canonical JSON bytes",
    )?;
    require(
        manifest.entries.iter().map(|entry| entry.size).sum::<u64>() <= max_total_bytes,
        "limit_exceeded",
        "bundle exceeds host payload budget",
    )?;
    let mut payloads = Payloads::new();
    for entry in &manifest.entries {
        let bytes = read(&root.join(&entry.path), entry.size)?;
        require(
            bytes.len() as u64 == entry.size && digest(&bytes) == entry.sha256,
            "digest_mismatch",
            "public artifact content or size differs from manifest",
        )?;
        payloads
            .entry(entry.role)
            .or_default()
            .push((entry.name.clone(), bytes));
    }
    validate_payloads(&payloads)?;
    reject_extra_files(root, &manifest)?;
    let files = payloads
        .into_iter()
        .flat_map(|(role, values)| {
            values
                .into_iter()
                .map(move |(name, bytes)| (role.path(&name), bytes))
        })
        .collect();
    Ok(VerifiedBundle {
        manifest,
        files,
        authenticated_manifest_sha256: trusted_manifest_sha256.map(str::to_owned),
    })
}
