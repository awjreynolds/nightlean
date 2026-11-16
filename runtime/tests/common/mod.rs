#![allow(dead_code)]
//! Adapt version-independent semantic vectors to the explicitly linked test profile.
//! Fresh source-emission and real provenance qualification are separate integration gates.
use nightlean_runtime::Plan;
use serde_json::Value as Json;
pub fn plan_json(mut value: Json) -> Json {
    if cfg!(feature = "zkir-321") {
        value["target"] = nightlean_runtime::profile::NAME.into();
        value["targetProfile"] = nightlean_runtime::profile::target_json();
    }
    value
}
pub fn selected(mut plan: Plan) -> Plan {
    if cfg!(feature = "zkir-321") {
        plan.target = Some(nightlean_runtime::profile::NAME.into());
        plan.target_profile = Some(nightlean_runtime::profile::target_json());
    }
    plan
}
pub fn unsigned_json() -> Json {
    plan_json(serde_json::from_str(include_str!("../fixtures/unsigned/plan.json")).unwrap())
}
