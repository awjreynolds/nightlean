//! Development-host filesystem journal and private-state CAS. The directory is a trusted
//! host capability. Hashes detect corruption and correlate records, not malicious disk edits.
use crate::{
    client::{
        CasReceipt, HostFailure, JournalIdentity, JournalStore, RecoveryRecord,
        StoreAcknowledgement, StoredRecord,
    },
    lifecycle::Phase,
};
use serde::{Deserialize, Serialize};
use serde_json::Value as Json;
use sha2::{Digest, Sha256};
use std::{
    collections::BTreeMap,
    fs::{self, File, OpenOptions},
    io::{Read, Write},
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
    time::{Duration, Instant},
};
use zeroize::Zeroizing;

const MAX_FILE: usize = 128 * 1024 * 1024;
static NEXT: AtomicU64 = AtomicU64::new(1);
fn hash(bytes: &[u8]) -> String {
    hex::encode(Sha256::digest(bytes))
}
#[derive(Serialize, Deserialize)]
struct StoredAttempt {
    revision: u64,
    body: String,
    digest: String,
    bytes: Vec<u8>,
    phase: String,
}
#[derive(Default, Serialize, Deserialize)]
struct Namespace {
    revision: u64,
    values: BTreeMap<String, Json>,
}
#[derive(Serialize, Deserialize)]
struct State {
    version: u32,
    attempts: BTreeMap<String, StoredAttempt>,
    namespaces: BTreeMap<String, Namespace>,
    receipts: BTreeMap<String, CasReceipt>,
}
impl Default for State {
    fn default() -> Self {
        Self {
            version: 1,
            attempts: BTreeMap::new(),
            namespaces: BTreeMap::new(),
            receipts: BTreeMap::new(),
        }
    }
}
impl Drop for StoredAttempt {
    fn drop(&mut self) {
        use zeroize::Zeroize;
        self.bytes.zeroize();
    }
}

#[cfg(unix)]
fn sync_directory(path: &Path) -> Result<(), HostFailure> {
    use std::os::unix::fs::OpenOptionsExt;
    let directory = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_DIRECTORY)
        .open(path)
        .map_err(|_| HostFailure)?;
    if !directory.metadata().map_err(|_| HostFailure)?.is_dir() {
        return Err(HostFailure);
    }
    directory.sync_all().map_err(|_| HostFailure)
}
#[cfg(not(unix))]
fn sync_directory(_: &Path) -> Result<(), HostFailure> {
    Err(HostFailure)
}

#[cfg(unix)]
fn provision_directory(path: &Path) -> Result<(), HostFailure> {
    use std::os::unix::fs::DirBuilderExt;
    match fs::symlink_metadata(path) {
        Ok(metadata) => {
            if !metadata.is_dir() {
                return Err(HostFailure);
            }
            return Ok(());
        }
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(_) => return Err(HostFailure),
    }
    let parent = path.parent().ok_or(HostFailure)?;
    provision_directory(parent)?;
    match fs::DirBuilder::new().mode(0o700).create(path) {
        Ok(()) => {}
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {
            if !fs::symlink_metadata(path)
                .map_err(|_| HostFailure)?
                .is_dir()
            {
                return Err(HostFailure);
            }
        }
        Err(_) => return Err(HostFailure),
    }
    // Persist the new directory and its link before any record acknowledgement.
    sync_directory(path)?;
    sync_directory(parent)
}

pub struct DirectoryJournal {
    root: PathBuf,
    timeout: Duration,
}
impl DirectoryJournal {
    pub fn new(root: &Path, timeout: Duration) -> Result<Self, HostFailure> {
        if timeout.is_zero() || timeout > Duration::from_secs(10) {
            return Err(HostFailure);
        }
        #[cfg(unix)]
        {
            if !root.is_absolute() {
                return Err(HostFailure);
            }
            provision_directory(root)?;
            use std::os::unix::fs::PermissionsExt;
            let metadata = fs::symlink_metadata(root).map_err(|_| HostFailure)?;
            if !metadata.is_dir() || metadata.permissions().mode() & 0o077 != 0 {
                return Err(HostFailure);
            }
            sync_directory(root)?;
            sync_directory(root.parent().ok_or(HostFailure)?)?;
        }
        #[cfg(not(unix))]
        {
            return Err(HostFailure);
        }
        Ok(Self {
            root: fs::canonicalize(root).map_err(|_| HostFailure)?,
            timeout,
        })
    }
    fn open_private(&self, path: &Path, exclusive: bool) -> Result<File, HostFailure> {
        let mut options = OpenOptions::new();
        options.read(true).write(true);
        if exclusive {
            options.create_new(true);
        } else {
            options.create(true).truncate(false);
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::OpenOptionsExt;
            // Reject links atomically, and never block opening a FIFO or device.
            options
                .mode(0o600)
                .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK);
        }
        let file = options.open(path).map_err(|_| HostFailure)?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let metadata = file.metadata().map_err(|_| HostFailure)?;
            if !metadata.is_file() || metadata.permissions().mode() & 0o077 != 0 {
                return Err(HostFailure);
            }
        }
        Ok(file)
    }
    fn with_state<T>(
        &self,
        write: bool,
        action: impl FnOnce(&mut State) -> Result<T, HostFailure>,
    ) -> Result<T, HostFailure> {
        let lock = self.open_private(&self.root.join("lock"), false)?;
        let deadline = Instant::now() + self.timeout;
        while lock.try_lock().is_err() {
            if Instant::now() >= deadline {
                return Err(HostFailure);
            }
            std::thread::sleep(Duration::from_millis(5));
        }
        let path = self.root.join("state.json");
        let exists = match fs::symlink_metadata(&path) {
            Ok(_) => true,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => false,
            Err(_) => return Err(HostFailure),
        };
        let mut state = if exists {
            let mut bytes = Zeroizing::new(Vec::new());
            self.open_private(&path, false)?
                .take(MAX_FILE as u64 + 1)
                .read_to_end(&mut bytes)
                .map_err(|_| HostFailure)?;
            if bytes.len() > MAX_FILE {
                return Err(HostFailure);
            }
            serde_json::from_slice::<State>(&bytes).map_err(|_| HostFailure)?
        } else {
            State::default()
        };
        if state.version != 1 {
            return Err(HostFailure);
        }
        let result = action(&mut state)?;
        if write {
            let bytes = Zeroizing::new(serde_json::to_vec(&state).map_err(|_| HostFailure)?);
            if bytes.len() > MAX_FILE {
                return Err(HostFailure);
            }
            let temporary = self.root.join(format!(
                "write-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            let mut file = self.open_private(&temporary, true)?;
            let written = (|| {
                file.write_all(&bytes).map_err(|_| HostFailure)?;
                file.sync_all().map_err(|_| HostFailure)?;
                fs::rename(&temporary, &path).map_err(|_| HostFailure)?;
                sync_directory(&self.root)
            })();
            if written.is_err() {
                let _ = fs::remove_file(&temporary);
            }
            written?;
        }
        drop(lock);
        Ok(result)
    }
    pub fn revision(&self, namespace: &str) -> Result<String, HostFailure> {
        self.with_state(false, |state| {
            Ok(format!(
                "r{}",
                state.namespaces.get(namespace).map_or(0, |ns| ns.revision)
            ))
        })
    }
    pub fn private_value(&self, namespace: &str, key: &str) -> Result<Option<Json>, HostFailure> {
        self.with_state(false, |state| {
            Ok(state
                .namespaces
                .get(namespace)
                .and_then(|ns| ns.values.get(key))
                .cloned())
        })
    }
}
fn phase_name(phase: Phase) -> String {
    format!("{phase:?}")
}
fn valid_step(old: &str, new: Phase) -> bool {
    match old {
        "Prepared" => matches!(new, Phase::Prepared | Phase::Submitted | Phase::Cancelled),
        "Submitted" | "Uncertain" => matches!(
            new,
            Phase::Submitted
                | Phase::Uncertain
                | Phase::AwaitingCas
                | Phase::PartiallyAccepted
                | Phase::Rejected
        ),
        "AwaitingCas" => matches!(
            new,
            Phase::AwaitingCas | Phase::Committed | Phase::Conflicted
        ),
        "Committed" => new == Phase::Committed,
        "Conflicted" => new == Phase::Conflicted,
        "PartiallyAccepted" => new == Phase::PartiallyAccepted,
        "Cancelled" => new == Phase::Cancelled,
        "Rejected" => new == Phase::Rejected,
        _ => false,
    }
}
impl JournalStore for DirectoryJournal {
    async fn load(&self, attempt_id: &str) -> Result<StoredRecord, HostFailure> {
        self.with_state(false, |state| {
            let record = state.attempts.get(attempt_id).ok_or(HostFailure)?;
            if hash(&record.bytes) != record.digest {
                return Err(HostFailure);
            }
            Ok(StoredRecord {
                private_bytes: Zeroizing::new(record.bytes.clone()),
                revision: record.revision,
            })
        })
    }
    async fn persist(
        &self,
        record: &RecoveryRecord,
        expected_revision: Option<u64>,
    ) -> Result<StoreAcknowledgement, HostFailure> {
        let bytes = record.private_bytes().map_err(|_| HostFailure)?;
        let digest = hash(&bytes);
        let body = record.immutable_digest().map_err(|_| HostFailure)?;
        let id = record.identity();
        self.with_state(true, |state| {
            let previous = state.attempts.get(&id.attempt_id);
            let revision = if let Some(old) = previous {
                if old.body != body
                    || !valid_step(&old.phase, record.phase())
                    || (old.phase == "PartiallyAccepted" && old.digest != digest)
                {
                    return Err(HostFailure);
                }
                if old.digest == digest
                    && (expected_revision == Some(old.revision)
                        || expected_revision.and_then(|r| r.checked_add(1)) == Some(old.revision))
                {
                    old.revision
                } else {
                    if expected_revision != Some(old.revision) {
                        return Err(HostFailure);
                    }
                    old.revision.checked_add(1).ok_or(HostFailure)?
                }
            } else {
                if expected_revision.is_some()
                    || state.attempts.len() >= 256
                    || !matches!(record.phase(), Phase::Prepared | Phase::Cancelled)
                {
                    return Err(HostFailure);
                }
                1
            };
            if matches!(record.phase(), Phase::Committed | Phase::Conflicted) {
                let known = state.receipts.get(&id.attempt_id).ok_or(HostFailure)?;
                let claimed = record.cas_receipt().ok_or(HostFailure)?;
                if known.identity != claimed.identity
                    || known.revision != claimed.revision
                    || known.committed != claimed.committed
                {
                    return Err(HostFailure);
                }
            }
            state.attempts.insert(
                id.attempt_id.clone(),
                StoredAttempt {
                    revision,
                    body,
                    digest: digest.clone(),
                    bytes: bytes.to_vec(),
                    phase: phase_name(record.phase()),
                },
            );
            Ok(StoreAcknowledgement {
                identity: id.clone(),
                record_sha256: digest,
                revision,
            })
        })
    }
    async fn compare_exchange(&self, record: &RecoveryRecord) -> Result<CasReceipt, HostFailure> {
        let id = record.identity();
        let digest = hash(&record.private_bytes().map_err(|_| HostFailure)?);
        self.with_state(true, |state| {
            if let Some(receipt) = state.receipts.get(&id.attempt_id) {
                if receipt.identity != *id {
                    return Err(HostFailure);
                }
                return Ok(receipt.clone());
            }
            let stored = state.attempts.get(&id.attempt_id).ok_or(HostFailure)?;
            if stored.digest != digest || record.phase() != Phase::AwaitingCas {
                return Err(HostFailure);
            }
            let journal: Json =
                serde_json::from_slice(record.journal_bytes()).map_err(|_| HostFailure)?;
            let namespace = journal["namespace"].as_str().ok_or(HostFailure)?;
            let private = state.namespaces.entry(namespace.into()).or_default();
            let committed = id.base_revision == format!("r{}", private.revision);
            if committed {
                for (key, value) in journal["writes"].as_object().ok_or(HostFailure)? {
                    private.values.insert(key.clone(), value.clone());
                }
                private.revision = private.revision.checked_add(1).ok_or(HostFailure)?;
            }
            let receipt = CasReceipt {
                identity: JournalIdentity {
                    attempt_id: id.attempt_id.clone(),
                    transaction_id: id.transaction_id.clone(),
                    base_revision: id.base_revision.clone(),
                    journal_digest: id.journal_digest.clone(),
                },
                revision: format!("r{}", private.revision),
                committed,
            };
            state
                .receipts
                .insert(id.attempt_id.clone(), receipt.clone());
            Ok(receipt)
        })
    }
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use std::{
        ffi::CString,
        os::unix::{
            ffi::OsStrExt,
            fs::{PermissionsExt, symlink},
        },
    };
    fn temporary() -> PathBuf {
        std::env::temp_dir().join(format!(
            "noctium-journal-files-{}-{}",
            std::process::id(),
            rand::random::<u64>()
        ))
    }
    fn fifo(path: &Path) {
        let path = CString::new(path.as_os_str().as_bytes()).unwrap();
        assert_eq!(unsafe { libc::mkfifo(path.as_ptr(), 0o600) }, 0);
    }
    #[test]
    fn links_fifos_and_nonregular_files_reject_without_blocking_or_external_creation() {
        let base = temporary();
        let store = DirectoryJournal::new(&base, Duration::from_millis(50)).unwrap();
        let external = base.with_extension("outside");
        for name in ["lock", "state.json"] {
            let path = base.join(name);
            symlink(&external, &path).unwrap();
            let start = Instant::now();
            assert!(store.revision("test").is_err());
            assert!(start.elapsed() < Duration::from_secs(1));
            assert!(!external.exists());
            fs::remove_file(&path).unwrap();
            fifo(&path);
            let start = Instant::now();
            assert!(store.revision("test").is_err());
            assert!(start.elapsed() < Duration::from_secs(1));
            fs::remove_file(&path).unwrap();
            fs::create_dir(&path).unwrap();
            assert!(store.revision("test").is_err());
            fs::remove_dir(&path).unwrap();
        }
        let root_link = base.with_extension("link");
        symlink(&external, &root_link).unwrap();
        assert!(DirectoryJournal::new(&root_link, Duration::from_millis(50)).is_err());
        fs::remove_file(&root_link).unwrap();
        symlink(&base, &root_link).unwrap();
        assert!(DirectoryJournal::new(&root_link, Duration::from_millis(50)).is_err());
        fs::remove_file(&root_link).unwrap();
        let root_fifo = base.with_extension("fifo");
        fifo(&root_fifo);
        assert!(DirectoryJournal::new(&root_fifo, Duration::from_millis(50)).is_err());
        fs::remove_file(root_fifo).unwrap();
        fs::remove_dir_all(base).unwrap();
    }
    #[test]
    fn fresh_nested_directories_are_private_and_synced_before_use() {
        let base = temporary();
        let root = base.join("first").join("journal");
        let store = DirectoryJournal::new(&root, Duration::from_millis(50)).unwrap();
        for path in [&base, &base.join("first"), &root] {
            assert_eq!(
                fs::metadata(path).unwrap().permissions().mode() & 0o777,
                0o700
            );
            sync_directory(path).unwrap();
        }
        assert_eq!(store.revision("test").unwrap(), "r0");
        // Provisioning never treats an existing link as a newly created directory.
        let link = base.join("linked-parent");
        symlink(base.join("first"), &link).unwrap();
        assert!(DirectoryJournal::new(&link.join("absent"), Duration::from_millis(50)).is_err());
        fs::remove_dir_all(base).unwrap();
    }
}
