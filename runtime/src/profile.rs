//! A build selects exactly one official native source pin. Release and banner are distinct.
use serde_json::{Value as Json, json};
#[cfg(feature = "zkir-321")]
pub const NAME: &str = "midnight-ledger-9-zkir-3.2.1";
#[cfg(not(feature = "zkir-321"))]
pub const NAME: &str = "midnight-ledger-9";
#[cfg(feature = "zkir-321")]
pub const ABI: &str = "midnight-ledger-9-zkir-3.2.1";
#[cfg(not(feature = "zkir-321"))]
pub const ABI: &str = "midnight-ledger-9-zkir-3.2.0";
#[cfg(feature = "zkir-321")]
pub const RELEASE: &str = "3.2.1";
#[cfg(not(feature = "zkir-321"))]
pub const RELEASE: &str = "3.2.0";
#[cfg(feature = "zkir-321")]
pub const REVISION: &str = "7a51b3385bbf4bce3604df87a7c70867c9ab43c0";
#[cfg(not(feature = "zkir-321"))]
pub const REVISION: &str = "446c7fecc6bd41dab99ebe89ab404e9d077d11a9";
pub const CLI_BANNER: &str = "midnight-zkir 3.2.0";
pub const CRATE_VERSION: &str = "3.2.0";
pub fn target_json() -> Json {
    let mut profile = json!({"schemaVersion":1,"name":NAME,"ledger":"9.1.0.1","zkir":RELEASE,"circuits":"7.3.0","zkStdlib":"2.4.0","proofServer":"9.0.0","onchainRuntime":"4.0.1","qualification":"source-baseline-unqualified"});
    if cfg!(feature = "zkir-321") {
        profile["qualification"] = json!("selected-native-subset-qualified");
        profile["nativeSource"] = json!({"repository":"https://github.com/midnightntwrk/midnight-zkir","tag":"zkir-3.2.1","revision":REVISION,"declaredCrateVersion":CRATE_VERSION,"reportedCliVersion":CLI_BANNER});
    }
    profile
}
/// Legacy unlabeled plans are 3.2.0 inputs only. A 3.2.1 consumer requires explicit provenance.
pub fn validate_plan(target: Option<&str>, profile: Option<&Json>) -> bool {
    match (target, profile) {
        (None, None) => !cfg!(feature = "zkir-321"),
        (Some(target), Some(profile)) => target == NAME && *profile == target_json(),
        _ => false,
    }
}
