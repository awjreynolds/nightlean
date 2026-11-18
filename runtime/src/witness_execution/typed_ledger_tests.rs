use super::ledger_tests::{advance_native, complete_native_inputs, source_execution};
use super::*;
use crate::{
    Environment, Expr, Plan, Value, evaluate,
    foreign::{ForeignFamily, ForeignRole, ForeignType, ForeignValue},
};
use base_crypto::fab::{AlignedValue, Alignment, AlignmentAtom, Value as FabValue, ValueAtom};
use host::{Capability, Context, Limits, Operation, Provider};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use storage::arena::Sp;

const IMPACT: &str = include_str!(
    "../../tests/fixtures/structured-typed-cells/321/StructuredTypedCells.update.impact.json"
);
const CIRCUIT: &[u8] = include_bytes!(
    "../../tests/fixtures/structured-typed-cells/321/StructuredTypedCells.update.zkir"
);
const WITNESS: &[u8] = include_bytes!(
    "../../tests/fixtures/structured-typed-cells/321/StructuredTypedCells.update.witness.json"
);
const CONTROL: &[u8] = include_bytes!(
    "../../tests/fixtures/structured-typed-cells/321/StructuredTypedCells.update.witness.control.json"
);

const PROVIDERS: [(&str, &str, &str, &str); 5] = [
    (
        "echoBytes33",
        "noctium.echo.bytes33.v1",
        "echo.bytes33",
        "Bytes<33>",
    ),
    (
        "echoBytes0",
        "noctium.echo.bytes0.v1",
        "echo.bytes0",
        "Bytes<0>",
    ),
    (
        "echoJubjubScalar",
        "noctium.echo.jubjub-scalar.v1",
        "echo.jubjub-scalar",
        "JubjubScalar",
    ),
    (
        "echoJubjubPoint",
        "noctium.echo.jubjub-point.v1",
        "echo.jubjub-point",
        "JubjubPoint",
    ),
    (
        "echoSecp256k1Base",
        "noctium.echo.secp256k1-base.v1",
        "echo.secp256k1-base",
        "Secp256k1Base",
    ),
];

#[derive(Clone)]
struct TypedValues {
    bytes33: Value,
    empty: Value,
    jubjub_scalar: Value,
    jubjub_point: Value,
    secp256k1_base: Value,
    registry: Value,
}

fn constant(value: u64) -> Expr {
    Expr::Constant {
        value: value.to_string(),
    }
}

fn jubjub_scalar(value: u64) -> Value {
    evaluate(
        &Expr::JubjubScalarFromNative {
            value: Box::new(constant(value)),
        },
        &Environment::new(),
    )
    .unwrap()
}

fn jubjub_point(multiplier: u64) -> Value {
    evaluate(
        &Expr::JubjubMulGenerator {
            scalar: Box::new(Expr::JubjubScalarFromNative {
                value: Box::new(constant(multiplier)),
            }),
        },
        &Environment::new(),
    )
    .unwrap()
}

fn secp256k1_base(value: u8) -> Value {
    let ty = ForeignType::new(ForeignFamily::Secp256k1, ForeignRole::Base);
    let mut bytes = vec![0; ty.byte_len()];
    bytes[0] = value;
    Value::Foreign(ForeignValue::from_bytes(ty, &bytes).unwrap())
}

fn values(bytes33: Vec<u8>, scalar: u64, point: u64, base: u8) -> TypedValues {
    TypedValues {
        bytes33: Value::Bytes(bytes33.clone()),
        empty: Value::Bytes(Vec::new()),
        jubjub_scalar: jubjub_scalar(scalar),
        jubjub_point: jubjub_point(point),
        secp256k1_base: secp256k1_base(base),
        registry: Value::Bytes(bytes33),
    }
}

fn aligned_bytes(bytes: &[u8]) -> AlignedValue {
    AlignedValue::new(
        FabValue(vec![ValueAtom::from(bytes)]),
        Alignment::singleton(AlignmentAtom::Bytes {
            length: bytes.len() as u32,
        }),
    )
    .unwrap()
}

fn slot(plan: &Plan, name: &str) -> usize {
    plan.state
        .iter()
        .position(|decl| decl.name == name)
        .unwrap()
}

fn state(plan: &Plan, registry_key: &[u8; 32], values: &TypedValues) -> ChargedState<crate::Db> {
    let initial = crate::create_state(
        plan,
        &BTreeMap::from([
            ("bytes33".into(), values.bytes33.public_json()),
            ("empty".into(), values.empty.public_json()),
            ("jubjubScalar".into(), values.jubjub_scalar.public_json()),
            ("jubjubPoint".into(), values.jubjub_point.public_json()),
            ("secp256k1Base".into(), values.secp256k1_base.public_json()),
            ("registry".into(), json!([])),
        ]),
    )
    .unwrap();
    let StateValue::Array(array) = initial.get_ref() else {
        panic!("expected state array")
    };
    let StateValue::Map(map) = &*array.get(slot(plan, "registry")).unwrap() else {
        panic!("expected registry map")
    };
    let Value::Bytes(registry_value) = &values.registry else {
        panic!("expected bytes33")
    };
    let seeded = StateValue::Map(map.insert(
        aligned_bytes(registry_key),
        StateValue::Cell(Sp::new(aligned_bytes(registry_value))),
    ));
    ChargedState::new(StateValue::Array(
        array.insert(slot(plan, "registry"), seeded).unwrap(),
    ))
}

fn host_context(attempt_id: &str) -> Context {
    let mut capabilities = vec![
        Capability {
            id: "private".into(),
            namespace: "noctium".into(),
            key_prefix: "ledger/".into(),
            operations: vec![host::STAGE.into()],
        },
        Capability {
            id: "commit".into(),
            namespace: "noctium".into(),
            key_prefix: "ledger/".into(),
            operations: vec![host::CAS.into()],
        },
    ];
    let mut operations = Vec::new();
    let mut providers = Vec::new();
    for (name, operation, capability, schema) in PROVIDERS {
        capabilities.push(Capability {
            id: capability.into(),
            namespace: "noctium".into(),
            key_prefix: "echo/".into(),
            operations: vec![operation.into()],
        });
        operations.push(Operation {
            operation: operation.into(),
            argument_schema: BTreeMap::from([("value".into(), schema.into())]),
            result_schema: schema.into(),
        });
        providers.push(Provider {
            input: name.into(),
            operation: operation.into(),
            capability: capability.into(),
            arguments: BTreeMap::new(),
        });
    }
    Context {
        protocol_version: 1,
        namespace: "noctium".into(),
        base_revision: "typed-ledger-r0".into(),
        attempt_id: attempt_id.into(),
        capabilities,
        operations,
        providers,
        commit_capability: "commit".into(),
        limits: Limits::default(),
    }
}

fn source_inputs(enabled: bool, registry_key: &[u8; 32]) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("enabled".into(), json!(enabled)),
        (
            "registryKey".into(),
            Value::Bytes(registry_key.to_vec()).public_json(),
        ),
    ])
}

fn typed_response(request: &Json, attempt_id: &str, value: Json) -> TypedResponse {
    serde_json::from_value(json!({
        "protocolVersion": 2,
        "requestId": request["request"]["requestId"],
        "attemptId": attempt_id,
        "outcome": "value",
        "operation": request["request"]["operation"],
        "capability": request["request"]["capability"],
        "schema": request["request"]["schema"],
        "value": value,
    }))
    .unwrap()
}

fn begin(
    enabled: bool,
    attempt_id: &str,
    initial: &ChargedState<crate::Db>,
) -> (WitnessExecution, Plan, crate::zkir::IrSource) {
    source_execution(
        IMPACT,
        CIRCUIT,
        CONTROL,
        WITNESS,
        source_inputs(enabled, &[0x42; 32]),
        initial,
        host_context(attempt_id),
    )
}

#[test]
fn typed_external_witnesses_update_native_cells_and_a_seeded_map() {
    let attempt_id = "d".repeat(64);
    let registry_key = [0x42; 32];
    let mut bytes = (1..=32).collect::<Vec<_>>();
    bytes.push(0);
    let initial_values = values(bytes, 7, 7, 9);
    let mut updated_bytes = match &initial_values.bytes33 {
        Value::Bytes(bytes) => bytes.clone(),
        _ => unreachable!(),
    };
    updated_bytes.reverse();
    let updated_values = values(updated_bytes, 8, 8, 10);
    let plan: Plan = serde_json::from_str(IMPACT).unwrap();
    let initial = state(&plan, &registry_key, &initial_values);
    let (mut execution, plan, circuit) = begin(true, &attempt_id, &initial);
    let calls = [
        (
            "echoBytes33",
            initial_values.bytes33.public_json(),
            updated_values.bytes33.public_json(),
        ),
        (
            "echoBytes0",
            initial_values.empty.public_json(),
            updated_values.empty.public_json(),
        ),
        (
            "echoJubjubScalar",
            initial_values.jubjub_scalar.public_json(),
            updated_values.jubjub_scalar.public_json(),
        ),
        (
            "echoJubjubPoint",
            initial_values.jubjub_point.public_json(),
            updated_values.jubjub_point.public_json(),
        ),
        (
            "echoSecp256k1Base",
            initial_values.secp256k1_base.public_json(),
            updated_values.secp256k1_base.public_json(),
        ),
        (
            "echoBytes33",
            initial_values.registry.public_json(),
            updated_values.registry.public_json(),
        ),
    ];
    for (index, (name, before, after)) in calls.into_iter().enumerate() {
        let request = execution.advance().unwrap();
        assert_eq!(request["status"], "need_host");
        assert_eq!(request["request"]["name"], name);
        let provider = PROVIDERS[if index == 5 { 0 } else { index }];
        assert_eq!(request["request"]["operation"], provider.1);
        assert_eq!(request["request"]["capability"], provider.2);
        assert_eq!(request["request"]["schema"], provider.3);
        assert_eq!(
            execution.private_request().unwrap()["arguments"]["value"],
            before
        );
        execution
            .resume_typed(typed_response(&request, &attempt_id, after))
            .unwrap();
    }
    assert_eq!(execution.advance().unwrap()["status"], "completed");

    let session = execution.session.as_mut().unwrap();
    let relation: Json = serde_json::from_slice(CIRCUIT).unwrap();
    let inputs = complete_native_inputs(session, &relation);
    let native = advance_native(&plan, &circuit, &initial, &inputs);
    assert_eq!(
        native.after.state,
        state(&plan, &registry_key, &updated_values)
    );
}

#[test]
fn inactive_typed_ledger_branch_keeps_native_state_unchanged() {
    let attempt_id = "e".repeat(64);
    let registry_key = [0x42; 32];
    let initial_values = values((1..=33).collect(), 7, 7, 9);
    let plan: Plan = serde_json::from_str(IMPACT).unwrap();
    let initial = state(&plan, &registry_key, &initial_values);
    let (mut execution, plan, circuit) = begin(false, &attempt_id, &initial);
    assert_eq!(execution.advance().unwrap()["status"], "completed");

    let session = execution.session.as_mut().unwrap();
    let relation: Json = serde_json::from_slice(CIRCUIT).unwrap();
    let inputs = complete_native_inputs(session, &relation);
    let native = advance_native(&plan, &circuit, &initial, &inputs);
    assert_eq!(native.after.state, initial);
}

#[test]
fn typed_bytes_callback_rejects_a_value_with_the_wrong_length() {
    let attempt_id = "f".repeat(64);
    let registry_key = [0x42; 32];
    let initial_values = values((1..=33).collect(), 7, 7, 9);
    let plan: Plan = serde_json::from_str(IMPACT).unwrap();
    let initial = state(&plan, &registry_key, &initial_values);
    let (mut execution, _, _) = begin(true, &attempt_id, &initial);
    let request = execution.advance().unwrap();
    assert_eq!(request["status"], "need_host");
    assert_eq!(request["request"]["name"], "echoBytes33");
    let rejected = execution.resume_typed(typed_response(
        &request,
        &attempt_id,
        json!({"kind":"bytes", "values":vec![0; 32]}),
    ));
    assert!(rejected.is_err());
    execution
        .resume_typed(typed_response(
            &request,
            &attempt_id,
            initial_values.bytes33.public_json(),
        ))
        .expect("a corrected typed response resumes the same pending provider");
}

#[test]
fn typed_ledger_metadata_binds_point_projections_and_foreign_input_types() {
    let impact: Json = serde_json::from_str(IMPACT).unwrap();
    let mut control_plan: Json = serde_json::from_slice(CONTROL).unwrap();
    let mut binding: Json = serde_json::from_slice(WITNESS).unwrap();
    let mut relation: Json = serde_json::from_slice(CIRCUIT).unwrap();
    let mut altered_plan = impact.clone();
    let point_read = altered_plan["reads"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|read| read["type"] == "JubjubPoint")
        .unwrap();
    point_read["projections"].as_array_mut().unwrap().swap(0, 1);
    let check = |control: &Json, binding: &[u8], relation: &Json, plan: &Json| {
        control::validate_witness_artifacts(
            control,
            binding,
            relation,
            plan,
            "StructuredTypedCells",
            "update",
            "StructuredTypedCells.update.zkir",
            crate::profile::NAME,
        )
    };
    assert!(check(&control_plan, WITNESS, &relation, &altered_plan).is_err());

    let foreign_input = relation["instructions"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|instruction| {
            instruction["op"] == "private_input" && instruction["type"] != "Scalar<BLS12-381>"
        })
        .unwrap();
    foreign_input["type"] = json!("Scalar<BLS12-381>");
    binding["nativeRelation"] = relation.clone();
    let binding_text = serde_json::to_string(&binding).unwrap() + "\n";
    control_plan["binding"] = json!(binding_text);
    assert!(check(&control_plan, binding_text.as_bytes(), &relation, &impact).is_err());
}
