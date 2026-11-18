use noctium_runtime::aggregates::{MAGIC, Schema};
use serde_json::{Value as Json, json};

fn schema(layout: Json, fingerprint: &str, counts: (usize, usize, usize)) -> Vec<u8> {
    serde_json::to_vec(
        &json!({"schemaVersion":1,"typeFingerprint":fingerprint,"layout":layout,
        "counts":{"leaves":counts.0,"expandedNodes":counts.1,"layoutNodes":counts.2}}),
    )
    .unwrap()
}
fn native() -> Json {
    json!({"kind":"scalar","leaf":{"kind":"native"}})
}
fn boolean() -> Json {
    json!({"kind":"scalar","leaf":{"kind":"bool"}})
}
fn uint(maximum: &str) -> Json {
    json!({"kind":"scalar","leaf":{"kind":"uint","maximum":maximum}})
}
fn field(name: &str, layout: Json) -> Json {
    json!({"name":name,"layout":layout})
}
fn unit_schema() -> Vec<u8> {
    schema(
        json!({"kind":"unit"}),
        "NoctiumCompositeTypeV1;uNoctiumCompositeLayoutV1;0;0;",
        (0, 1, 1),
    )
}
fn nested_schema() -> Vec<u8> {
    schema(
        json!({"kind":"tuple","items":[{"kind":"struct","id":"Test.Packet","fields":[
        field("amount",uint("255")),field("flags",json!({"kind":"vector","length":2,"element":boolean()})),
        field("choice",json!({"kind":"enum","id":"Test.Choice","variants":[
            {"name":"None","fields":[]},{"name":"Some","fields":[field("pair",json!({"kind":"tuple","items":[native(),uint("15")]}))]}
        ]})),field("bytes",json!({"kind":"bytes","length":2}))
    ]},{"kind":"unit"}]}),
        "NoctiumCompositeTypeV1;t2;[r11:Test.Packetu]NoctiumCompositeLayoutV1;1;R11:Test.Packet4;f6:amountsU255;f5:flagsv2;sBf6:choicee11:Test.Choicef5:bytesb2;1;E11:Test.Choice2;V4:None0;V4:Some1;f4:pairt2;[sNsU15;]",
        (8, 16, 13),
    )
}
fn value_field(name: &str, value: Json) -> Json {
    json!({"name":name,"value":value})
}
fn nested_value(some: bool) -> Json {
    json!({"kind":"tuple","items":[{"kind":"struct","id":"Test.Packet","fields":[
        value_field("amount",json!({"kind":"uint","maximum":"255","value":"9"})),
        value_field("flags",json!({"kind":"vector","items":[{"kind":"bool","value":true},{"kind":"bool","value":false}]})),
        value_field("choice",if some { json!({"kind":"enum","id":"Test.Choice","variant":"Some","fields":[
            value_field("pair",json!({"kind":"tuple","items":[{"kind":"native","value":"42"},{"kind":"uint","maximum":"15","value":"7"}]}))
        ]}) } else { json!({"kind":"enum","id":"Test.Choice","variant":"None","fields":[]}) }),
        value_field("bytes",json!({"kind":"bytes","values":[0,255]}))
    ]},{"kind":"unit"}]})
}
fn leaves_offset(wire: &[u8]) -> usize {
    let p = MAGIC.len();
    p + 4 + u32::from_le_bytes(wire[p..p + 4].try_into().unwrap()) as usize + 4
}
#[test]
fn nested_nominal_roundtrip_has_fixed_order_and_enum_padding() {
    let checked = Schema::from_json(&nested_schema()).unwrap();
    assert_eq!(checked.counts().leaves, 8);
    for some in [false, true] {
        let value = nested_value(some);
        let wire = checked
            .encode_json_value(&serde_json::to_vec(&value).unwrap())
            .unwrap();
        let decoded = checked.decode_wire(&wire).unwrap();
        assert_eq!(serde_json::from_slice::<Json>(&decoded).unwrap(), value);
        assert_eq!(checked.encode_json_value(&decoded).unwrap(), wire);
        let start = leaves_offset(&wire);
        let low: Vec<_> = wire[start..].chunks_exact(32).map(|leaf| leaf[0]).collect();
        assert_eq!(
            low,
            if some {
                vec![9, 1, 0, 1, 42, 7, 0, 255]
            } else {
                vec![9, 1, 0, 0, 0, 0, 0, 255]
            }
        );
    }
}
#[test]
fn malformed_tags_padding_and_canonical_fields_reject() {
    let checked = Schema::from_json(&nested_schema()).unwrap();
    let original = checked
        .encode_json_value(&serde_json::to_vec(&nested_value(false)).unwrap())
        .unwrap();
    let start = leaves_offset(&original);
    let mut bad = original.clone();
    bad[start + 3 * 32] = 2;
    assert!(checked.decode_wire(&bad).is_err());
    let mut bad = original.clone();
    bad[start + 4 * 32] = 1;
    assert!(checked.decode_wire(&bad).is_err());
    let mut bad = original.clone();
    bad[start + 1 * 32] = 2;
    assert!(checked.decode_wire(&bad).is_err());
    let mut bad = original.clone();
    bad[start + 7 * 32 + 1] = 1;
    assert!(checked.decode_wire(&bad).is_err());
    let mut bad = original.clone();
    bad.push(0);
    assert!(checked.decode_wire(&bad).is_err());
    assert!(
        checked
            .decode_wire(&original[..original.len() - 1])
            .is_err()
    );
    assert!(checked.decode_wire(&original[..MAGIC.len() + 3]).is_err());
    let mut bad = original.clone();
    bad[start..start + 32].fill(255);
    assert!(checked.decode_wire(&bad).is_err());
    let mut bad = original.clone();
    bad[MAGIC.len() + 4] ^= 1;
    assert!(checked.decode_wire(&bad).is_err());
}
#[test]
fn malformed_logical_values_preserve_scalar_and_nominal_identity() {
    let checked = Schema::from_json(&nested_schema()).unwrap();
    let mut bad = nested_value(true);
    bad["items"][0]["id"] = "Test.Other".into();
    assert!(
        checked
            .encode_json_value(&serde_json::to_vec(&bad).unwrap())
            .is_err()
    );
    let mut bad = nested_value(true);
    bad["items"][0]["fields"][0]["value"]["value"] = "256".into();
    assert!(
        checked
            .encode_json_value(&serde_json::to_vec(&bad).unwrap())
            .is_err()
    );
    let mut bad = nested_value(true);
    bad["items"][0]["fields"][0]["value"]["value"] = "09".into();
    assert!(
        checked
            .encode_json_value(&serde_json::to_vec(&bad).unwrap())
            .is_err()
    );
    let mut bad = nested_value(true);
    bad["items"][0]["fields"][0]["value"]["maximum"] = "511".into();
    assert!(
        checked
            .encode_json_value(&serde_json::to_vec(&bad).unwrap())
            .is_err()
    );
    let mut bad = nested_value(true);
    bad["items"][0]["fields"].as_array_mut().unwrap().swap(0, 1);
    assert!(
        checked
            .encode_json_value(&serde_json::to_vec(&bad).unwrap())
            .is_err()
    );
    let mut bad = nested_value(true);
    bad["items"][0]["fields"][1]["value"]["items"][0]["value"] = 1.into();
    assert!(
        checked
            .encode_json_value(&serde_json::to_vec(&bad).unwrap())
            .is_err()
    );
    let mut bad = nested_value(true);
    bad["items"][0]["fields"][2]["value"]["variant"] = "Unknown".into();
    assert!(
        checked
            .encode_json_value(&serde_json::to_vec(&bad).unwrap())
            .is_err()
    );
}
#[test]
fn scalar_extrema_and_full_width_wire_are_checked() {
    let modulus =
        num_bigint::BigUint::parse_bytes(noctium_runtime::MODULUS.as_bytes(), 10).unwrap();
    let maximum = &modulus - 1u8;
    let checked = Schema::from_json(&schema(
        native(),
        "NoctiumCompositeTypeV1;sNNoctiumCompositeLayoutV1;0;0;",
        (1, 1, 1),
    ))
    .unwrap();
    let value = json!({"kind":"native","value":maximum.to_str_radix(10)});
    let wire = checked
        .encode_json_value(&serde_json::to_vec(&value).unwrap())
        .unwrap();
    assert_eq!(wire.len() - leaves_offset(&wire), 32);
    assert_eq!(
        serde_json::from_slice::<Json>(&checked.decode_wire(&wire).unwrap()).unwrap(),
        value
    );
    assert!(
        checked
            .encode_json_value(
                &serde_json::to_vec(&json!({"kind":"native","value":noctium_runtime::MODULUS}))
                    .unwrap()
            )
            .is_err()
    );
    let zero = Schema::from_json(&schema(
        uint("0"),
        "NoctiumCompositeTypeV1;sU0;NoctiumCompositeLayoutV1;0;0;",
        (1, 1, 1),
    ))
    .unwrap();
    assert!(
        zero.encode_json_value(br#"{"kind":"uint","maximum":"0","value":"0"}"#)
            .is_ok()
    );
    assert!(
        zero.encode_json_value(br#"{"kind":"uint","maximum":"0","value":"1"}"#)
            .is_err()
    );
}
#[test]
fn unit_and_empty_sequences_roundtrip_without_invented_leaves() {
    for (layout, fingerprint, counts, value) in [
        (
            json!({"kind":"unit"}),
            "NoctiumCompositeTypeV1;uNoctiumCompositeLayoutV1;0;0;",
            (0, 1, 1),
            json!({"kind":"unit"}),
        ),
        (
            json!({"kind":"tuple","items":[]}),
            "NoctiumCompositeTypeV1;t0;[]NoctiumCompositeLayoutV1;0;0;",
            (0, 1, 1),
            json!({"kind":"tuple","items":[]}),
        ),
        (
            json!({"kind":"vector","length":0,"element":native()}),
            "NoctiumCompositeTypeV1;v0;sNNoctiumCompositeLayoutV1;0;0;",
            (0, 1, 2),
            json!({"kind":"vector","items":[]}),
        ),
        (
            json!({"kind":"bytes","length":0}),
            "NoctiumCompositeTypeV1;b0;NoctiumCompositeLayoutV1;0;0;",
            (0, 1, 1),
            json!({"kind":"bytes","values":[]}),
        ),
    ] {
        let checked = Schema::from_json(&schema(layout, fingerprint, counts)).unwrap();
        let wire = checked
            .encode_json_value(&serde_json::to_vec(&value).unwrap())
            .unwrap();
        assert_eq!(wire.len(), leaves_offset(&wire));
        assert_eq!(
            serde_json::from_slice::<Json>(&checked.decode_wire(&wire).unwrap()).unwrap(),
            value
        );
    }
}
#[test]
fn deep_zero_vectors_validate_retained_children_without_a_new_depth_limit() {
    let depth = noctium_runtime::aggregates::MAX_NODES - 1;
    let mut layout = String::new();
    for _ in 0..depth {
        layout.push_str("{\"kind\":\"vector\",\"length\":0,\"element\":");
    }
    layout.push_str("{\"kind\":\"scalar\",\"leaf\":{\"kind\":\"native\"}}");
    for _ in 0..depth {
        layout.push('}');
    }
    let fingerprint = format!(
        "NoctiumCompositeTypeV1;{}sNNoctiumCompositeLayoutV1;0;0;",
        "v0;".repeat(depth)
    );
    let text = format!(
        "{{\"schemaVersion\":1,\"typeFingerprint\":{},\"layout\":{},\"counts\":{{\"leaves\":0,\"expandedNodes\":1,\"layoutNodes\":{}}}}}",
        serde_json::to_string(&fingerprint).unwrap(),
        layout,
        depth + 1
    );
    let checked = Schema::from_json(text.as_bytes()).unwrap();
    assert_eq!(checked.counts().layout_nodes, noctium_runtime::aggregates::MAX_NODES);
    let wire = checked
        .encode_json_value(b"{\"kind\":\"vector\",\"items\":[]}")
        .unwrap();
    assert_eq!(
        checked.decode_wire(&wire).unwrap(),
        b"{\"kind\":\"vector\",\"items\":[]}"
    );

    let over_limit_depth = depth + 1;
    let mut over_limit_layout = String::new();
    for _ in 0..over_limit_depth {
        over_limit_layout.push_str("{\"kind\":\"vector\",\"length\":0,\"element\":");
    }
    over_limit_layout.push_str("{\"kind\":\"scalar\",\"leaf\":{\"kind\":\"native\"}}");
    for _ in 0..over_limit_depth {
        over_limit_layout.push('}');
    }
    let over_limit = format!(
        "{{\"schemaVersion\":1,\"typeFingerprint\":{},\"layout\":{},\"counts\":{{\"leaves\":0,\"expandedNodes\":1,\"layoutNodes\":{}}}}}",
        serde_json::to_string(&format!(
            "NoctiumCompositeTypeV1;{}sNNoctiumCompositeLayoutV1;0;0;",
            "v0;".repeat(over_limit_depth)
        ))
        .unwrap(),
        over_limit_layout,
        over_limit_depth + 1
    );
    assert!(Schema::from_json(over_limit.as_bytes()).is_err());
}

#[test]
fn transport_limit_accepts_exact_boundary_and_rejects_one_byte_over() {
    let mut schema = unit_schema();
    schema.resize(noctium_runtime::aggregates::MAX_TRANSPORT_BYTES, b' ');
    let checked = Schema::from_json(&schema).unwrap();
    schema.push(b' ');
    assert!(Schema::from_json(&schema).is_err());

    let mut value = b"{\"kind\":\"unit\"}".to_vec();
    value.resize(noctium_runtime::aggregates::MAX_TRANSPORT_BYTES, b' ');
    assert!(checked.encode_json_value(&value).is_ok());
    value.push(b' ');
    assert!(checked.encode_json_value(&value).is_err());
}
#[test]
fn schema_fingerprint_conflicts_counts_unknown_fields_and_duplicates_reject() {
    let mut bad: Json = serde_json::from_slice(&nested_schema()).unwrap();
    bad["counts"]["leaves"] = 9.into();
    assert!(Schema::from_json(&serde_json::to_vec(&bad).unwrap()).is_err());
    let mut bad: Json = serde_json::from_slice(&nested_schema()).unwrap();
    bad["typeFingerprint"] = "forged".into();
    assert!(Schema::from_json(&serde_json::to_vec(&bad).unwrap()).is_err());
    let mut bad: Json = serde_json::from_slice(&nested_schema()).unwrap();
    bad["ignored"] = Json::Null;
    assert!(Schema::from_json(&serde_json::to_vec(&bad).unwrap()).is_err());
    let duplicate = String::from_utf8(unit_schema()).unwrap().replacen(
        "\"schemaVersion\":1",
        "\"schemaVersion\":1,\"schemaVersion\":1",
        1,
    );
    assert!(Schema::from_json(duplicate.as_bytes()).is_err());
    let conflicting = schema(
        json!({"kind":"tuple","items":[
            {"kind":"struct","id":"A","fields":[field("x",native())]},
            {"kind":"struct","id":"A","fields":[field("x",boolean())]}
        ]}),
        "forged",
        (2, 5, 5),
    );
    assert!(Schema::from_json(&conflicting).is_err());
    let invalid_zero = schema(
        json!({"kind":"vector","length":0,"element":{"kind":"scalar","leaf":{"kind":"uint","maximum":"999999999999999999999999999999999999999999999999999999999999999999999999999999"}}}),
        "forged",
        (0, 1, 2),
    );
    assert!(Schema::from_json(&invalid_zero).is_err());
}
#[test]
fn lean_generated_cross_language_fixture_matches_exact_wire() {
    let checked = Schema::from_json(include_bytes!("fixtures/aggregates/schema.json")).unwrap();
    let value = include_bytes!("fixtures/aggregates/value.json");
    let expected = hex::decode(include_str!("fixtures/aggregates/wire.hex").trim()).unwrap();
    assert_eq!(checked.encode_json_value(value).unwrap(), expected);
    assert_eq!(
        serde_json::from_slice::<Json>(&checked.decode_wire(&expected).unwrap()).unwrap(),
        serde_json::from_slice::<Json>(value).unwrap()
    );
}
#[test]
fn repeated_nominal_definitions_agree_and_physical_aliases_do_not() {
    let repeated = schema(
        json!({"kind":"tuple","items":[
            {"kind":"struct","id":"A","fields":[field("x",native())]},
            {"kind":"struct","id":"A","fields":[field("x",native())]}
        ]}),
        "NoctiumCompositeTypeV1;t2;[r1:Ar1:A]NoctiumCompositeLayoutV1;1;R1:A1;f1:xsN0;",
        (2, 5, 5),
    );
    let checked = Schema::from_json(&repeated).unwrap();
    let value = json!({"kind":"tuple","items":[
        {"kind":"struct","id":"A","fields":[value_field("x",json!({"kind":"native","value":"1"}))]},
        {"kind":"struct","id":"A","fields":[value_field("x",json!({"kind":"native","value":"2"}))]}
    ]});
    let wire = checked
        .encode_json_value(&serde_json::to_vec(&value).unwrap())
        .unwrap();
    assert_eq!(
        serde_json::from_slice::<Json>(&checked.decode_wire(&wire).unwrap()).unwrap(),
        value
    );
    let a = Schema::from_json(&schema(
        json!({"kind":"struct","id":"A","fields":[field("x",native())]}),
        "NoctiumCompositeTypeV1;r1:ANoctiumCompositeLayoutV1;1;R1:A1;f1:xsN0;",
        (1, 2, 2),
    ))
    .unwrap();
    let b = Schema::from_json(&schema(
        json!({"kind":"struct","id":"B","fields":[field("x",native())]}),
        "NoctiumCompositeTypeV1;r1:BNoctiumCompositeLayoutV1;1;R1:B1;f1:xsN0;",
        (1, 2, 2),
    ))
    .unwrap();
    let value = json!({"kind":"struct","id":"A","fields":[value_field("x",json!({"kind":"native","value":"7"}))]});
    let wire = a
        .encode_json_value(&serde_json::to_vec(&value).unwrap())
        .unwrap();
    assert!(b.decode_wire(&wire).is_err());
}
#[test]
fn enum_active_native_branch_does_not_inherit_inactive_uint_bounds() {
    let checked = Schema::from_json(include_bytes!("fixtures/aggregates/schema.json")).unwrap();
    let mut value: Json =
        serde_json::from_slice(include_bytes!("fixtures/aggregates/value.json")).unwrap();
    let wide = (num_bigint::BigUint::from(1u8) << 248usize).to_str_radix(10);
    value["items"][2] = json!({"kind":"enum","id":"Demo.Choice","variant":"Native","fields":[
        value_field("value",json!({"kind":"native","value":wide}))
    ]});
    let wire = checked
        .encode_json_value(&serde_json::to_vec(&value).unwrap())
        .unwrap();
    assert_eq!(
        serde_json::from_slice::<Json>(&checked.decode_wire(&wire).unwrap()).unwrap(),
        value
    );
    let mut bad = wire.clone();
    let start = leaves_offset(&bad);
    bad[start + 6 * 32] = 1;
    assert!(checked.decode_wire(&bad).is_err());
}
#[test]
fn c_abi_has_owned_copy_free_null_and_stale_token_behavior() {
    use noctium_runtime::aggregates::*;
    let schema = unit_schema();
    let value = b"{\"kind\":\"unit\"}";
    unsafe {
        let mut token = 99;
        assert_eq!(
            noctium_aggregate_encode(
                std::ptr::null(),
                0,
                value.as_ptr(),
                value.len(),
                &mut token
            ),
            1
        );
        assert_eq!(token, 0);
        assert_eq!(
            noctium_aggregate_encode(
                schema.as_ptr(),
                schema.len(),
                value.as_ptr(),
                value.len(),
                &mut token
            ),
            0
        );
        let mut length = 0;
        assert_eq!(noctium_aggregate_buffer_length(token, &mut length), 0);
        let mut wire = vec![0u8; length];
        let mut written = 99;
        assert_eq!(
            noctium_aggregate_buffer_copy(token, wire.as_mut_ptr(), length - 1, &mut written),
            7
        );
        assert_eq!(written, 0);
        assert_eq!(
            noctium_aggregate_buffer_copy(token, wire.as_mut_ptr(), length, &mut written),
            0
        );
        assert_eq!(written, length);
        assert_eq!(noctium_aggregate_buffer_free(token), 0);
        assert_eq!(noctium_aggregate_buffer_free(token), 2);
        assert_eq!(noctium_aggregate_buffer_length(token, &mut length), 2);
        assert_eq!(length, 0);
        let mut decoded = 0;
        assert_eq!(
            noctium_aggregate_decode(
                schema.as_ptr(),
                schema.len(),
                wire.as_ptr(),
                wire.len(),
                &mut decoded
            ),
            0
        );
        assert_eq!(noctium_aggregate_buffer_free(decoded), 0);
        let mut tokens = vec![];
        for _ in 0..64 {
            let mut current = 0;
            assert_eq!(
                noctium_aggregate_encode(
                    schema.as_ptr(),
                    schema.len(),
                    value.as_ptr(),
                    value.len(),
                    &mut current
                ),
                0
            );
            tokens.push(current);
        }
        let mut exhausted = 99;
        assert_eq!(
            noctium_aggregate_encode(
                schema.as_ptr(),
                schema.len(),
                value.as_ptr(),
                value.len(),
                &mut exhausted
            ),
            5
        );
        assert_eq!(exhausted, 0);
        assert_eq!(noctium_aggregate_buffer_free(tokens.pop().unwrap()), 0);
        assert_eq!(
            noctium_aggregate_encode(
                schema.as_ptr(),
                schema.len(),
                value.as_ptr(),
                value.len(),
                &mut exhausted
            ),
            0
        );
        tokens.push(exhausted);
        for current in tokens {
            assert_eq!(noctium_aggregate_buffer_free(current), 0);
        }
    }
}
