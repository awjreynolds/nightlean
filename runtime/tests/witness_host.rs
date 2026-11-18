use noctium_runtime::{
    ScalarType,
    host::{self, Capability, Context, Limits, Operation, Provider},
    witness::{Parameter, Projection, Registry, Type, WitnessSignature},
};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;

fn native_struct_schema(id: &str) -> Vec<u8> {
    let fingerprint = format!(
        "NoctiumCompositeTypeV1;r{}:{}NoctiumCompositeLayoutV1;1;R{}:{}1;f1:xsN0;",
        id.len(),
        id,
        id.len(),
        id
    );
    serde_json::to_vec(&json!({
        "schemaVersion":1,
        "typeFingerprint":fingerprint,
        "layout":{"kind":"struct","id":id,"fields":[
            {"name":"x","layout":{"kind":"scalar","leaf":{"kind":"native"}}}
        ]},
        "counts":{"leaves":1,"expandedNodes":2,"layoutNodes":2}
    }))
    .unwrap()
}

fn value(id: &str, number: &str) -> Json {
    json!({"kind":"struct","id":id,"fields":[
        {"name":"x","value":{"kind":"native","value":number}}
    ]})
}

fn registry() -> Registry {
    let mut result = Registry::default();
    result
        .register_json("Aggregate:t0", &native_struct_schema("Test.A"))
        .unwrap();
    result
        .register_json("Aggregate:t1", &native_struct_schema("Test.B"))
        .unwrap();
    result
}

fn fixed_vector_schema() -> Vec<u8> {
    serde_json::to_vec(&json!({
        "schemaVersion":1,
        "typeFingerprint":"NoctiumCompositeTypeV1;v2;sU255;NoctiumCompositeLayoutV1;0;0;",
        "layout":{"kind":"vector","length":2,"element":{"kind":"scalar","leaf":{"kind":"uint","maximum":"255"}}},
        "counts":{"leaves":2,"expandedNodes":3,"layoutNodes":2}
    })).unwrap()
}

fn fixed_bytes_schema() -> Vec<u8> {
    serde_json::to_vec(&json!({
        "schemaVersion":1,
        "typeFingerprint":"NoctiumCompositeTypeV1;b2;NoctiumCompositeLayoutV1;0;0;",
        "layout":{"kind":"bytes","length":2},
        "counts":{"leaves":2,"expandedNodes":3,"layoutNodes":1}
    }))
    .unwrap()
}

fn context() -> Context {
    Context {
        protocol_version: 1,
        namespace: "app".into(),
        base_revision: "r0".into(),
        attempt_id: "a".repeat(64),
        capabilities: vec![
            Capability {
                id: "witness".into(),
                namespace: "app".into(),
                key_prefix: "claims/".into(),
                operations: vec!["witness.lookup.v1".into()],
            },
            Capability {
                id: "store".into(),
                namespace: "app".into(),
                key_prefix: "claims/".into(),
                operations: vec![host::STAGE.into()],
            },
            Capability {
                id: "commit".into(),
                namespace: "app".into(),
                key_prefix: "claims/".into(),
                operations: vec![host::CAS.into()],
            },
        ],
        operations: vec![Operation {
            operation: "witness.lookup.v1".into(),
            argument_schema: BTreeMap::from([("subject".into(), "Native".into())]),
            result_schema: "Bool".into(),
        }],
        providers: vec![Provider {
            input: "lookup".into(),
            operation: "witness.lookup.v1".into(),
            capability: "witness".into(),
            arguments: BTreeMap::new(),
        }],
        commit_capability: "commit".into(),
        limits: Limits::default(),
    }
}

fn signature() -> WitnessSignature {
    WitnessSignature {
        name: "lookup".into(),
        operation: "witness.lookup.v1".into(),
        capability: "witness".into(),
        parameters: vec![Parameter {
            name: "subject".into(),
            type_token: "Native".into(),
        }],
        result_type: "Bool".into(),
        private_key: None,
    }
}

fn read_context(key: &str) -> Context {
    let mut result = context();
    result.capabilities[0].operations = vec![host::READ.into()];
    result.operations = vec![Operation {
        operation: host::READ.into(),
        argument_schema: BTreeMap::from([("key".into(), "Key".into())]),
        result_schema: "Bool".into(),
    }];
    result.providers = vec![Provider {
        input: "cache".into(),
        operation: host::READ.into(),
        capability: "witness".into(),
        arguments: BTreeMap::from([("key".into(), json!(key))]),
    }];
    result
}

fn source_signatures(plan: &Json) -> Vec<WitnessSignature> {
    plan["witnesses"]
        .as_array()
        .unwrap()
        .iter()
        .map(|value| WitnessSignature {
            name: value["name"].as_str().unwrap().to_owned(),
            operation: value["operation"].as_str().unwrap().to_owned(),
            capability: value["capability"].as_str().unwrap().to_owned(),
            parameters: value["parameters"]
                .as_array()
                .unwrap()
                .iter()
                .map(|parameter| Parameter {
                    name: parameter["name"].as_str().unwrap().to_owned(),
                    type_token: parameter["type"].as_str().unwrap().to_owned(),
                })
                .collect(),
            result_type: value["resultType"].as_str().unwrap().to_owned(),
            private_key: value["privateKey"].as_str().map(str::to_owned),
        })
        .collect()
}

fn source_registry(plan: &Json) -> Registry {
    let mut registry = Registry::default();
    for declaration in plan["types"].as_array().unwrap() {
        let token = format!("Aggregate:{}", declaration["id"].as_str().unwrap());
        registry
            .register_json(&token, &serde_json::to_vec(&declaration["schema"]).unwrap())
            .unwrap();
    }
    registry
}

fn source_context(signatures: &[WitnessSignature]) -> Context {
    let mut operations = BTreeMap::new();
    let mut providers = Vec::new();
    let mut capabilities: BTreeMap<String, (String, std::collections::BTreeSet<String>)> =
        BTreeMap::new();
    for signature in signatures {
        let mut arguments: BTreeMap<_, _> = signature
            .parameters
            .iter()
            .map(|parameter| (parameter.name.clone(), parameter.type_token.clone()))
            .collect();
        if signature.operation == host::READ {
            arguments.insert("key".into(), "Key".into());
        }
        let descriptor = Operation {
            operation: signature.operation.clone(),
            argument_schema: arguments,
            result_schema: signature.result_type.clone(),
        };
        assert!(
            operations
                .insert(signature.operation.clone(), descriptor)
                .is_none()
        );

        let prefix = signature
            .private_key
            .as_deref()
            .map(|key| match key.rsplit_once('/') {
                Some((root, _)) => format!("{root}/"),
                None => key.to_owned(),
            })
            .unwrap_or_else(|| "claims/".into());
        let entry = capabilities
            .entry(signature.capability.clone())
            .or_insert_with(|| (prefix.clone(), std::collections::BTreeSet::new()));
        assert_eq!(entry.0, prefix);
        entry.1.insert(signature.operation.clone());
        if signature.private_key.is_some() {
            entry.1.insert(host::STAGE.into());
        }
        providers.push(Provider {
            input: signature.name.clone(),
            operation: signature.operation.clone(),
            capability: signature.capability.clone(),
            arguments: signature
                .private_key
                .as_ref()
                .map(|key| BTreeMap::from([("key".into(), json!(key))]))
                .unwrap_or_default(),
        });
    }
    let mut capability_values: Vec<_> = capabilities
        .into_iter()
        .map(|(id, (key_prefix, operations))| Capability {
            id,
            namespace: "app".into(),
            key_prefix,
            operations: operations.into_iter().collect(),
        })
        .collect();
    capability_values.push(Capability {
        id: "commit".into(),
        namespace: "app".into(),
        key_prefix: "claims/".into(),
        operations: vec![host::CAS.into()],
    });
    Context {
        protocol_version: 1,
        namespace: "app".into(),
        base_revision: "r0".into(),
        attempt_id: "a".repeat(64),
        capabilities: capability_values,
        operations: operations.into_values().collect(),
        providers,
        commit_capability: "commit".into(),
        limits: Limits::default(),
    }
}

#[test]
fn aggregate_registry_keeps_nominal_identity_and_roundtrips_typed_leaves() {
    let registry = registry();
    let input = value("Test.A", "123");
    registry.validate("Aggregate:t0", &input).unwrap();
    assert!(registry.validate("Aggregate:t1", &input).is_err());
    assert_eq!(registry.leaf_types("Aggregate:t0").unwrap(), ["Native"]);
    assert_eq!(
        registry.flatten_leaves("Aggregate:t0", &input).unwrap(),
        [json!("123")]
    );
    assert_eq!(
        registry
            .from_leaves("Aggregate:t0", &[json!("456")])
            .unwrap(),
        value("Test.A", "456")
    );

    let projection = Projection {
        kind: "field".into(),
        index: None,
        name: Some("x".into()),
        variant: None,
        type_token: "Native".into(),
    };
    let (token, projected, range) = registry
        .project_with_range("Aggregate:t0", &input, &projection)
        .unwrap();
    assert_eq!(token, "Native");
    assert_eq!(projected, json!("123"));
    assert_eq!(range, 0..1);
    let wrong = Projection {
        type_token: "Aggregate:t1".into(),
        ..projection
    };
    assert!(registry.projection_type("Aggregate:t0", &wrong).is_err());
}

#[test]
fn aggregate_leaf_codec_preserves_variant_shapes_and_checked_index_types() {
    let mut fixture = Registry::default();
    fixture
        .register_json(
            "Aggregate:t0",
            include_bytes!("fixtures/aggregates/schema.json"),
        )
        .unwrap();
    let value: Json =
        serde_json::from_slice(include_bytes!("fixtures/aggregates/value.json")).unwrap();
    let leaves = fixture.flatten_leaves("Aggregate:t0", &value).unwrap();
    assert_eq!(
        leaves,
        [
            json!("200"),
            json!(true),
            json!("3"),
            json!("4"),
            json!("0"),
            json!("1"),
            json!("7"),
            json!("255"),
            json!("0"),
        ]
    );
    assert_eq!(fixture.from_leaves("Aggregate:t0", &leaves).unwrap(), value);

    let mut vectors = Registry::default();
    vectors
        .register_json("Aggregate:t0", &fixed_vector_schema())
        .unwrap();
    let vector_value = json!({"kind":"vector","items":[
        {"kind":"uint","maximum":"255","value":"3"},
        {"kind":"uint","maximum":"255","value":"9"}
    ]});
    assert_eq!(
        vectors.index_type("Aggregate:t0").unwrap(),
        "UIntRange<256>"
    );
    let (token, projected, range) = vectors
        .index_with_range("Aggregate:t0", &vector_value, 1)
        .unwrap();
    assert_eq!(token, "UIntRange<256>");
    assert_eq!(projected, json!("9"));
    assert_eq!(range, 1..2);
    assert!(
        vectors
            .index_with_range("Aggregate:t0", &vector_value, 2)
            .is_err()
    );

    let mut bytes = Registry::default();
    bytes
        .register_json("Aggregate:t0", &fixed_bytes_schema())
        .unwrap();
    let byte_value = json!({"kind":"bytes","values":[0,255]});
    let projection = Projection {
        kind: "byteIndex".into(),
        index: Some(1),
        name: None,
        variant: None,
        type_token: "UIntRange<256>".into(),
    };
    assert_eq!(
        bytes.projection_type("Aggregate:t0", &projection).unwrap(),
        ("UIntRange<256>".into(), 1..2)
    );
    let (_, projected, range) = bytes
        .project_with_range("Aggregate:t0", &byte_value, &projection)
        .unwrap();
    assert_eq!(projected, json!("255"));
    assert_eq!(range, 1..2);
}

#[test]
fn typed_provider_correlates_and_validates_without_exposing_arguments_in_metadata() {
    let registry = registry();
    assert!(matches!(
        Type::parse("Aggregate:t0", &registry).unwrap(),
        Type::Aggregate(_)
    ));
    assert!(Type::parse("Aggregate:t9", &registry).is_err());
    assert_eq!(ScalarType::parse("Bool").unwrap(), ScalarType::Bool);
    let mut runtime = host::Runtime::new_typed(
        context(),
        &["lookup".into()],
        "contract".into(),
        "claim".into(),
        &registry,
    )
    .unwrap();
    let arguments = json!({"subject":"987654321"});
    let request = runtime
        .begin_typed_input("lookup", 1, &signature(), &arguments, &registry)
        .unwrap()
        .unwrap();
    assert_eq!(request["protocolVersion"], 2);
    assert_eq!(request["requestId"], "1");
    assert_eq!(request["arguments"][0]["name"], "subject");
    assert!(request.to_string().find("987654321").is_none());
    assert_eq!(runtime.private_arguments().unwrap()["arguments"], arguments);

    assert!(
        runtime
            .finish_typed_input(
                "lookup",
                2,
                Some(&"a".repeat(64)),
                Some("witness.lookup.v1"),
                Some("witness"),
                Some("Bool"),
                &json!(true),
                &registry
            )
            .is_err()
    );
    assert!(
        runtime
            .finish_typed_input(
                "lookup",
                1,
                Some(&"a".repeat(64)),
                Some("wrong.v1"),
                Some("witness"),
                Some("Bool"),
                &json!(true),
                &registry
            )
            .is_err()
    );
    assert!(
        runtime
            .finish_typed_input(
                "lookup",
                1,
                Some(&"a".repeat(64)),
                Some("witness.lookup.v1"),
                Some("witness"),
                Some("Bool"),
                &json!("true"),
                &registry
            )
            .is_err()
    );
    assert_eq!(runtime.private_arguments().unwrap()["arguments"], arguments);
    assert_eq!(
        runtime
            .finish_typed_input(
                "lookup",
                1,
                Some(&"a".repeat(64)),
                Some("witness.lookup.v1"),
                Some("witness"),
                Some("Bool"),
                &json!(true),
                &registry
            )
            .unwrap(),
        json!(true)
    );
    assert!(
        runtime
            .finish_typed_input(
                "lookup",
                1,
                Some(&"a".repeat(64)),
                Some("witness.lookup.v1"),
                Some("witness"),
                Some("Bool"),
                &json!(true),
                &registry
            )
            .is_err()
    );
    assert!(runtime.private_arguments().is_err());
}

#[test]
fn typed_provider_rejects_extra_arguments_and_stages_checked_composites() {
    let registry = registry();
    let mut runtime = host::Runtime::new_typed(
        context(),
        &["lookup".into()],
        "contract".into(),
        "claim".into(),
        &registry,
    )
    .unwrap();
    assert!(
        runtime
            .begin_typed_input(
                "lookup",
                1,
                &signature(),
                &json!({"subject":"1","extra":"2"}),
                &registry
            )
            .is_err()
    );
    runtime
        .stage_typed(
            host::Stage {
                abi_version: 2,
                operation: host::STAGE.into(),
                capability: "store".into(),
                key: "claims/value".into(),
                ty: "Aggregate:t0".into(),
                value: value("Test.A", "123"),
            },
            &registry,
        )
        .unwrap();
    assert!(
        runtime
            .stage_typed(
                host::Stage {
                    abi_version: 2,
                    operation: host::STAGE.into(),
                    capability: "store".into(),
                    key: "claims/other".into(),
                    ty: "Aggregate:t1".into(),
                    value: value("Test.A", "123"),
                },
                &registry
            )
            .is_err()
    );
    runtime.execution_finished(true).unwrap();
    runtime
        .notify(host::Notice {
            abi_version: 1,
            event: "bind".into(),
            attempt_id: "a".repeat(64),
            transaction_id: "b".repeat(64),
        })
        .unwrap();
    let journal = runtime.private_journal().unwrap();
    assert_eq!(journal["writes"]["claims/value"]["type"], "Aggregate:t0");
    assert_eq!(
        journal["writes"]["claims/value"]["value"],
        value("Test.A", "123")
    );
}

#[test]
fn typed_private_read_binds_the_source_key_and_keeps_it_out_of_metadata() {
    let registry = registry();
    let context_key = "claims/last";
    let mut runtime = host::Runtime::new_typed(
        read_context(context_key),
        &["cache".into()],
        "contract".into(),
        "claim".into(),
        &registry,
    )
    .unwrap();
    let signature = WitnessSignature {
        name: "cache".into(),
        operation: host::READ.into(),
        capability: "witness".into(),
        parameters: vec![],
        result_type: "Bool".into(),
        private_key: Some(context_key.into()),
    };
    let request = runtime
        .begin_typed_input("cache", 9, &signature, &json!({}), &registry)
        .unwrap()
        .unwrap();
    assert_eq!(request["protocolVersion"], 2);
    assert!(request.to_string().find(context_key).is_none());
    let private = runtime.private_arguments().unwrap();
    assert_eq!(private["arguments"]["key"], context_key);
    assert_eq!(
        runtime
            .finish_typed_input(
                "cache",
                9,
                Some(&"a".repeat(64)),
                Some(host::READ),
                Some("witness"),
                Some("Bool"),
                &json!(true),
                &registry
            )
            .unwrap(),
        json!(true)
    );

    let mut mismatched = host::Runtime::new_typed(
        read_context(context_key),
        &["cache".into()],
        "contract".into(),
        "claim".into(),
        &registry,
    )
    .unwrap();
    let wrong_signature = WitnessSignature {
        private_key: Some("claims/other".into()),
        ..signature
    };
    assert!(
        mismatched
            .begin_typed_input("cache", 10, &wrong_signature, &json!({}), &registry)
            .is_err()
    );
}

fn staged_read_signature(result_type: &str) -> WitnessSignature {
    WitnessSignature {
        name: "cache".into(),
        operation: host::READ.into(),
        capability: "witness".into(),
        parameters: vec![],
        result_type: result_type.into(),
        private_key: Some("claims/last".into()),
    }
}

fn stage_read_value(runtime: &mut host::Runtime, registry: &Registry, ty: &str, value: Json) {
    runtime
        .stage_typed(
            host::Stage {
                abi_version: 2,
                operation: host::STAGE.into(),
                capability: "store".into(),
                key: "claims/last".into(),
                ty: ty.into(),
                value,
            },
            registry,
        )
        .unwrap();
}

fn finish_read(
    runtime: &mut host::Runtime,
    registry: &Registry,
    id: u64,
    schema: &str,
    value: &Json,
) -> host::Result<Json> {
    runtime.finish_typed_input(
        "cache",
        id,
        Some(&"a".repeat(64)),
        Some(host::READ),
        Some("witness"),
        Some(schema),
        value,
        registry,
    )
}

#[test]
fn scalar_read_rejects_lies_about_owned_stages_and_retains_retry() {
    let registry = registry();
    let mut runtime = host::Runtime::new_typed(
        read_context("claims/last"),
        &["cache".into()],
        "contract".into(),
        "claim".into(),
        &registry,
    )
    .unwrap();
    let signature = staged_read_signature("Bool");
    stage_read_value(&mut runtime, &registry, "Bool", json!(true));
    runtime
        .begin_typed_input("cache", 21, &signature, &json!({}), &registry)
        .unwrap();
    let pending = runtime.private_arguments().unwrap();
    assert!(finish_read(&mut runtime, &registry, 21, "Bool", &json!(false)).is_err());
    assert!(finish_read(&mut runtime, &registry, 21, "Native", &json!("1")).is_err());
    assert_eq!(runtime.private_arguments().unwrap(), pending);
    assert_eq!(
        finish_read(&mut runtime, &registry, 21, "Bool", &json!(true)).unwrap(),
        json!(true)
    );
    stage_read_value(&mut runtime, &registry, "Bool", json!(false));
    runtime
        .begin_typed_input("cache", 22, &signature, &json!({}), &registry)
        .unwrap();
    assert!(finish_read(&mut runtime, &registry, 22, "Bool", &json!(true)).is_err());
    assert_eq!(
        finish_read(&mut runtime, &registry, 22, "Bool", &json!(false)).unwrap(),
        json!(false)
    );
    runtime.execution_finished(true).unwrap();
    runtime
        .notify(host::Notice {
            abi_version: 1,
            event: "bind".into(),
            attempt_id: "a".repeat(64),
            transaction_id: "b".repeat(64),
        })
        .unwrap();
    let journal = runtime.private_journal().unwrap();
    assert_eq!(
        journal["writes"]["claims/last"],
        json!({"type":"Bool","value":false})
    );
}

#[test]
fn nominal_read_requires_exact_owned_stage_type_and_latest_value() {
    let registry = registry();
    let mut context = read_context("claims/last");
    context.operations[0].result_schema = "Aggregate:t0".into();
    let mut runtime = host::Runtime::new_typed(
        context,
        &["cache".into()],
        "contract".into(),
        "claim".into(),
        &registry,
    )
    .unwrap();
    let signature = staged_read_signature("Aggregate:t0");
    stage_read_value(
        &mut runtime,
        &registry,
        "Aggregate:t0",
        value("Test.A", "123"),
    );
    runtime
        .begin_typed_input("cache", 31, &signature, &json!({}), &registry)
        .unwrap();
    let pending = runtime.private_arguments().unwrap();
    assert!(
        finish_read(
            &mut runtime,
            &registry,
            31,
            "Aggregate:t0",
            &value("Test.A", "999")
        )
        .is_err()
    );
    assert!(
        finish_read(
            &mut runtime,
            &registry,
            31,
            "Aggregate:t1",
            &value("Test.B", "123")
        )
        .is_err()
    );
    assert!(
        finish_read(
            &mut runtime,
            &registry,
            31,
            "Aggregate:t0",
            &value("Test.B", "123")
        )
        .is_err()
    );
    assert_eq!(runtime.private_arguments().unwrap(), pending);
    assert_eq!(
        finish_read(
            &mut runtime,
            &registry,
            31,
            "Aggregate:t0",
            &value("Test.A", "123")
        )
        .unwrap(),
        value("Test.A", "123")
    );
    stage_read_value(
        &mut runtime,
        &registry,
        "Aggregate:t0",
        value("Test.A", "456"),
    );
    runtime
        .begin_typed_input("cache", 32, &signature, &json!({}), &registry)
        .unwrap();
    assert!(
        finish_read(
            &mut runtime,
            &registry,
            32,
            "Aggregate:t0",
            &value("Test.A", "123")
        )
        .is_err()
    );
    finish_read(
        &mut runtime,
        &registry,
        32,
        "Aggregate:t0",
        &value("Test.A", "456"),
    )
    .unwrap();
    stage_read_value(
        &mut runtime,
        &registry,
        "Aggregate:t1",
        value("Test.B", "456"),
    );
    runtime
        .begin_typed_input("cache", 33, &signature, &json!({}), &registry)
        .unwrap();
    assert!(
        finish_read(
            &mut runtime,
            &registry,
            33,
            "Aggregate:t0",
            &value("Test.A", "456")
        )
        .is_err()
    );
    assert_eq!(
        runtime.private_arguments().unwrap()["arguments"]["key"],
        "claims/last"
    );
    runtime.cancel().unwrap();
}

#[test]
fn generated_scalar_plan_separates_public_requests_from_private_read_arguments() {
    let plan: Json = serde_json::from_slice(include_bytes!(
        "fixtures/witness/320/TypedWitness.ScalarWitness.claim.witness.control.json"
    ))
    .unwrap();
    let signatures = source_signatures(&plan);
    let registry = source_registry(&plan);
    let context = source_context(&signatures);
    let typed_inputs = signatures
        .iter()
        .map(|signature| signature.name.clone())
        .collect::<Vec<_>>();
    let mut runtime = host::Runtime::new_typed(
        context,
        &typed_inputs,
        "scalar".into(),
        "claim".into(),
        &registry,
    )
    .unwrap();
    let lookup = signatures
        .iter()
        .find(|signature| signature.name == "lookup")
        .unwrap();
    let cache = signatures
        .iter()
        .find(|signature| signature.name == "cache")
        .unwrap();

    let metadata = runtime
        .begin_typed_input("cache", 1, cache, &json!({}), &registry)
        .unwrap()
        .unwrap();
    assert_eq!(metadata["protocolVersion"], 2);
    assert_eq!(metadata["requestId"], "1");
    assert_eq!(metadata["attemptId"], "a".repeat(64));
    assert!(metadata.to_string().find("cache/last").is_none());
    let private = runtime.private_arguments().unwrap();
    assert_eq!(private["attemptId"], metadata["attemptId"]);
    assert_eq!(private["arguments"]["key"], "cache/last");
    assert_eq!(
        runtime
            .finish_typed_input(
                "cache",
                1,
                Some(&"a".repeat(64)),
                Some(host::READ),
                Some("private"),
                Some("UIntRange<256>"),
                &json!("0"),
                &registry
            )
            .unwrap(),
        json!("0")
    );

    let metadata = runtime
        .begin_typed_input("lookup", 2, lookup, &json!({"seed":"7"}), &registry)
        .unwrap()
        .unwrap();
    assert_eq!(metadata["requestId"], "2");
    assert_eq!(metadata["attemptId"], "a".repeat(64));
    assert!(metadata.to_string().find('7').is_none());
    assert_eq!(
        runtime.private_arguments().unwrap()["arguments"]["seed"],
        "7"
    );
    assert!(
        runtime
            .finish_typed_input(
                "lookup",
                2,
                Some("b"),
                Some("noctium.lookup.v1"),
                Some("lookup"),
                Some("UIntRange<256>"),
                &json!("14"),
                &registry
            )
            .is_err()
    );
    assert!(
        runtime
            .finish_typed_input(
                "lookup",
                3,
                Some(&"a".repeat(64)),
                Some("noctium.lookup.v1"),
                Some("lookup"),
                Some("UIntRange<256>"),
                &json!("14"),
                &registry
            )
            .is_err()
    );
    assert!(
        runtime
            .finish_typed_input(
                "lookup",
                2,
                Some(&"a".repeat(64)),
                Some("noctium.lookup.v1"),
                Some("lookup"),
                Some("Native"),
                &json!("14"),
                &registry
            )
            .is_err()
    );
    assert!(
        runtime
            .finish_typed_input(
                "lookup",
                2,
                Some(&"a".repeat(64)),
                Some("noctium.lookup.v1"),
                Some("lookup"),
                Some("UIntRange<256>"),
                &json!("999"),
                &registry
            )
            .is_err()
    );
    assert_eq!(
        runtime.private_arguments().unwrap()["arguments"]["seed"],
        "7"
    );
    assert_eq!(
        runtime
            .finish_typed_input(
                "lookup",
                2,
                Some(&"a".repeat(64)),
                Some("noctium.lookup.v1"),
                Some("lookup"),
                Some("UIntRange<256>"),
                &json!("14"),
                &registry
            )
            .unwrap(),
        json!("14")
    );
    assert!(
        runtime
            .finish_typed_input(
                "lookup",
                2,
                Some(&"a".repeat(64)),
                Some("noctium.lookup.v1"),
                Some("lookup"),
                Some("UIntRange<256>"),
                &json!("14"),
                &registry
            )
            .is_err()
    );

    runtime
        .begin_typed_input("cache", 4, cache, &json!({}), &registry)
        .unwrap();
    runtime.cancel().unwrap();
    assert!(runtime.private_arguments().is_err());

    let mut limited_context = source_context(&signatures);
    limited_context.limits.private_bytes = 1024;
    let mut limited = host::Runtime::new_typed(
        limited_context,
        &typed_inputs,
        "scalar".into(),
        "claim".into(),
        &registry,
    )
    .unwrap();
    let oversized = json!({"seed":"1".repeat(2048)});
    assert_eq!(
        limited
            .begin_typed_input("lookup", 5, lookup, &oversized, &registry)
            .unwrap_err(),
        host::Error::Limit
    );
}

#[test]
fn generated_composite_and_zero_leaf_plans_roundtrip_and_recover_registry() {
    let pair_plan: Json = serde_json::from_slice(include_bytes!(
        "fixtures/witness/320/TypedWitness.PairWitness.claim.witness.control.json"
    ))
    .unwrap();
    let pair_signatures = source_signatures(&pair_plan);
    let pair_registry = source_registry(&pair_plan);
    let pair_context = source_context(&pair_signatures);
    let pair_signature = &pair_signatures[0];
    let pair = json!({
        "kind":"struct",
        "id":"TypedWitness.Pair",
        "fields":[
            {"name":"amount","value":{"kind":"uint","maximum":"255","value":"9"}},
            {"name":"okay","value":{"kind":"bool","value":true}}
        ]
    });
    assert_eq!(
        pair_registry.flatten_leaves("Aggregate:t0", &pair).unwrap(),
        [json!("9"), json!(true)]
    );
    assert!(
        pair_registry
            .validate(
                "Aggregate:t0",
                &json!({
                    "kind":"struct", "id":"TypedWitness.Other", "fields":pair["fields"]
                })
            )
            .is_err()
    );
    let mut runtime = host::Runtime::new_typed(
        pair_context,
        &[pair_signature.name.clone()],
        "pair".into(),
        "claim".into(),
        &pair_registry,
    )
    .unwrap();
    assert!(
        runtime
            .begin_typed_input(
                "pair",
                10,
                pair_signature,
                &json!({"request":{
                    "kind":"struct", "id":"TypedWitness.Other", "fields":pair["fields"]
                }}),
                &pair_registry
            )
            .is_err()
    );
    let metadata = runtime
        .begin_typed_input(
            "pair",
            11,
            pair_signature,
            &json!({"request":pair}),
            &pair_registry,
        )
        .unwrap()
        .unwrap();
    assert_eq!(metadata["schema"], "Aggregate:t0");
    assert!(metadata.to_string().find("\"9\"").is_none());
    assert_eq!(
        runtime.private_arguments().unwrap()["arguments"]["request"],
        pair
    );
    assert!(
        runtime
            .finish_typed_input(
                "pair",
                11,
                Some(&"a".repeat(64)),
                Some("noctium.pair.v1"),
                Some("pair"),
                Some("Aggregate:t0"),
                &json!({
                    "kind":"struct", "id":"TypedWitness.Other", "fields":pair["fields"]
                }),
                &pair_registry
            )
            .is_err()
    );
    assert_eq!(
        runtime
            .finish_typed_input(
                "pair",
                11,
                Some(&"a".repeat(64)),
                Some("noctium.pair.v1"),
                Some("pair"),
                Some("Aggregate:t0"),
                &pair,
                &pair_registry
            )
            .unwrap(),
        pair
    );
    runtime.execution_finished(true).unwrap();
    let recovery = runtime.recovery_context().unwrap();
    assert_eq!(recovery["typedSchemas"][0]["id"], "Aggregate:t0");
    let mut tampered_recovery = recovery.clone();
    tampered_recovery["typedSchemas"][0]["schema"]["typeFingerprint"] = "forged".into();
    assert!(host::Runtime::from_recovery_context(tampered_recovery).is_err());
    let mut unknown_field = recovery.clone();
    unknown_field["extra"] = json!(true);
    assert!(host::Runtime::from_recovery_context(unknown_field).is_err());
    let mut restored = host::Runtime::from_recovery_context(recovery).unwrap();
    assert!(restored.typed_registry().unwrap().contains("Aggregate:t0"));
    let restored_registry = restored.typed_registry().unwrap().clone();
    let metadata = restored
        .begin_typed_input(
            "pair",
            12,
            pair_signature,
            &json!({"request":pair}),
            &restored_registry,
        )
        .unwrap()
        .unwrap();
    assert_eq!(metadata["schema"], "Aggregate:t0");
    assert_eq!(
        restored
            .finish_typed_input(
                "pair",
                12,
                Some(&"a".repeat(64)),
                Some("noctium.pair.v1"),
                Some("pair"),
                Some("Aggregate:t0"),
                &pair,
                &restored_registry
            )
            .unwrap(),
        pair
    );

    let empty_plan: Json = serde_json::from_slice(include_bytes!(
        "fixtures/witness/320/TypedWitness.emptyRelation.witness.control.json"
    ))
    .unwrap();
    let empty_signatures = source_signatures(&empty_plan);
    let empty_registry = source_registry(&empty_plan);
    let mut empty_runtime = host::Runtime::new_typed(
        source_context(&empty_signatures),
        &["empty".into()],
        "empty".into(),
        "prove".into(),
        &empty_registry,
    )
    .unwrap();
    let empty = json!({"kind":"struct","id":"TypedWitness.Empty","fields":[]});
    assert!(
        empty_registry
            .flatten_leaves("Aggregate:t0", &empty)
            .unwrap()
            .is_empty()
    );
    let signature = &empty_signatures[0];
    empty_runtime
        .begin_typed_input("empty", 13, signature, &json!({}), &empty_registry)
        .unwrap();
    assert_eq!(
        empty_runtime
            .finish_typed_input(
                "empty",
                13,
                Some(&"a".repeat(64)),
                Some("noctium.empty.v1"),
                Some("empty"),
                Some("Aggregate:t0"),
                &empty,
                &empty_registry
            )
            .unwrap(),
        empty
    );
}
