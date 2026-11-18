use anyhow::{Context, Result, anyhow, bail, ensure};
use base_crypto::fab::AlignedValue;
use noctium_runtime::{
    Db, Plan, canonical_field,
    control::TypedResponse,
    field_decimal,
    host::{self, Capability, Context as HostContext, Limits, Operation, Provider},
    witness_execution::WitnessExecution,
};
use onchain_runtime::state::{ChargedState, StateValue};
use rand::{RngCore, rngs::OsRng};
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use transient_crypto::{
    curve::{EmbeddedFr, EmbeddedGroupAffine, Fr},
    fab::AlignedValueExt,
};

// shortcut: decode only small fixture amounts, use wallet balance tracking for real workloads.
const MAX_FIXTURE_BALANCE: u64 = 64;

#[derive(Clone, Copy)]
pub(super) struct Wallet {
    account_secret: [u8; 32],
    encryption_secret: [u8; 32],
}

const ALICE: Wallet = Wallet {
    account_secret: [17; 32],
    encryption_secret: [7; 32],
};
const BOB: Wallet = Wallet {
    account_secret: [18; 32],
    encryption_secret: [8; 32],
};

#[derive(Clone, Copy)]
struct Ciphertext {
    c1: EmbeddedGroupAffine,
    c2: EmbeddedGroupAffine,
}

pub(super) async fn run(host: &mut crate::Host) -> Result<()> {
    let alice_id = account_id(&ALICE.account_secret);
    let bob_id = account_id(&BOB.account_secret);
    let alice_key = EmbeddedGroupAffine::generator() * encryption_scalar(&ALICE.encryption_secret);
    let bob_key = EmbeddedGroupAffine::generator() * encryption_scalar(&BOB.encryption_secret);

    host.invoke("totalSupply", BTreeMap::new(), None).await?;
    host.invoke(
        "computeAccountId",
        BTreeMap::from([("secret".into(), bytes(&ALICE.account_secret))]),
        None,
    )
    .await?;

    for (wallet, account, key) in [(&ALICE, alice_id, alice_key), (&BOB, bob_id, bob_key)] {
        host.invoke(
            "registerWithKey",
            BTreeMap::from([
                ("accountId".into(), bytes(&account)),
                ("pk".into(), point_json(key)),
            ]),
            Some(wallet),
        )
        .await?;
    }

    host.invoke(
        "isRegistered",
        BTreeMap::from([("account".into(), bytes(&alice_id))]),
        None,
    )
    .await?;
    host.invoke(
        "balanceOf",
        BTreeMap::from([("account".into(), bytes(&alice_id))]),
        None,
    )
    .await?;
    host.invoke(
        "pendingOf",
        BTreeMap::from([("account".into(), bytes(&bob_id))]),
        None,
    )
    .await?;

    host.invoke(
        "mint",
        mint_inputs(&host.plan, &host.state, &alice_id, alice_key)?,
        Some(&ALICE),
    )
    .await?;
    host.invoke(
        "sweep",
        sweep_inputs(&host.plan, &host.state, &alice_id)?,
        Some(&ALICE),
    )
    .await?;
    host.invoke(
        "transfer",
        transfer_inputs(&host.plan, &host.state, &alice_id, &bob_id, bob_key, 5, 1)?,
        Some(&ALICE),
    )
    .await?;
    host.invoke(
        "burn",
        burn_inputs(&host.plan, &host.state, &alice_id, 2)?,
        Some(&ALICE),
    )
    .await?;
    host.invoke(
        "_move",
        transfer_inputs(
            &host.plan,
            &host.state,
            &alice_id,
            &alice_id,
            alice_key,
            1,
            2,
        )?,
        Some(&ALICE),
    )
    .await?;
    host.invoke(
        "clearMemos",
        BTreeMap::from([
            ("accountId".into(), bytes(&alice_id)),
            (
                "expectedEpoch".into(),
                json!(counter(&host.plan, &host.state, "creditEpochs", &alice_id)?.to_string()),
            ),
        ]),
        Some(&ALICE),
    )
    .await?;
    host.invoke(
        "approve",
        approve_inputs(&host.plan, &host.state, &alice_id, &bob_id, bob_key)?,
        Some(&ALICE),
    )
    .await?;
    host.invoke(
        "allowance",
        BTreeMap::from([
            ("owner".into(), bytes(&alice_id)),
            ("spender".into(), bytes(&bob_id)),
        ]),
        None,
    )
    .await?;
    host.invoke(
        "transferFrom",
        transfer_from_inputs(
            &host.plan,
            &host.state,
            &alice_id,
            &bob_id,
            &bob_id,
            alice_key,
            bob_key,
            2,
        )?,
        Some(&BOB),
    )
    .await?;
    host.invoke(
        "burnFrom",
        escrow_spend_inputs(&host.plan, &host.state, &alice_id, &bob_id, alice_key, 1)?,
        Some(&BOB),
    )
    .await?;

    assert_final_state(
        &host.plan,
        &host.state,
        &alice_id,
        &bob_id,
        alice_key,
        bob_key,
    )?;
    Ok(())
}

pub(super) fn complete_source(
    execution: &mut WitnessExecution,
    attempt: &str,
    wallet: &Wallet,
) -> Result<()> {
    let mut seeds = BTreeSet::<[u8; 32]>::new();
    loop {
        let status = execution.advance()?;
        let status = status.as_json();
        if status["status"] != "need_host" {
            ensure!(
                status["status"] == "completed",
                "source operation failed: {status}"
            );
            break;
        }
        let request = &status["request"];
        let private = execution.private_request()?;
        let value = if request["operation"] == host::READ {
            let key = private["arguments"]["key"]
                .as_str()
                .context("private wallet read omitted key")?;
            if key.ends_with("/accountSecret") {
                bytes(&wallet.account_secret)
            } else if key.ends_with("/encryptionSecret") {
                bytes(&wallet.encryption_secret)
            } else {
                bail!("unexpected fixture wallet key {key}")
            }
        } else {
            match request["name"]
                .as_str()
                .context("witness request omitted name")?
            {
                "OpenZeppelinPort.freshSeed" => {
                    let mut seed = [0; 32];
                    loop {
                        OsRng.fill_bytes(&mut seed);
                        if seeds.insert(seed) {
                            break;
                        }
                    }
                    bytes(&seed)
                }
                "OpenZeppelinPort.plaintextBalance" => {
                    let arguments = &private["arguments"];
                    let ciphertext = Ciphertext {
                        c1: point_from_json(&arguments["c1"])?,
                        c2: point_from_json(&arguments["c2"])?,
                    };
                    let plaintext = decrypt_small(
                        ciphertext,
                        encryption_scalar(&wallet.encryption_secret),
                        MAX_FIXTURE_BALANCE,
                    )?;
                    json!(plaintext.to_string())
                }
                name => bail!("unexpected token witness callback {name}"),
            }
        };
        let response: TypedResponse = serde_json::from_value(json!({
            "protocolVersion": 2,
            "requestId": request["requestId"],
            "attemptId": attempt,
            "outcome": "value",
            "operation": request["operation"],
            "capability": request["capability"],
            "schema": request["schema"],
            "value": value
        }))?;
        execution.resume_typed(response)?;
    }
    Ok(())
}

pub(super) fn context(
    plan: &Json,
    attempt: &str,
    namespace: &str,
    base_revision: &str,
) -> Result<HostContext> {
    let mut operations = BTreeMap::<String, Operation>::new();
    let mut providers = Vec::new();
    let mut capabilities = BTreeMap::<String, (String, BTreeSet<String>)>::new();
    for signature in plan["witnesses"]
        .as_array()
        .context("witness sidecar omitted signatures")?
    {
        let operation = signature["operation"]
            .as_str()
            .context("witness signature omitted operation")?
            .to_owned();
        let name = signature["name"]
            .as_str()
            .context("witness signature omitted name")?
            .to_owned();
        let capability = signature["capability"]
            .as_str()
            .context("witness signature omitted capability")?
            .to_owned();
        let mut argument_schema = BTreeMap::new();
        for parameter in signature["parameters"]
            .as_array()
            .context("witness signature omitted parameters")?
        {
            argument_schema.insert(
                parameter["name"]
                    .as_str()
                    .context("witness parameter omitted name")?
                    .to_owned(),
                parameter["type"]
                    .as_str()
                    .context("witness parameter omitted type")?
                    .to_owned(),
            );
        }
        if operation == host::READ {
            argument_schema.insert("key".into(), "Key".into());
        }
        let result_schema = signature["resultType"]
            .as_str()
            .context("witness signature omitted result type")?
            .to_owned();
        let spec = Operation {
            operation: operation.clone(),
            argument_schema: argument_schema.clone(),
            result_schema: result_schema.clone(),
        };
        if let Some(previous) = operations.insert(operation.clone(), spec) {
            ensure!(
                previous.argument_schema == argument_schema
                    && previous.result_schema == result_schema,
                "conflicting witness operation schema"
            );
        }
        let private_key = signature["privateKey"].as_str();
        let prefix = private_key
            .and_then(|key| key.rsplit_once('/').map(|(root, _)| format!("{root}/")))
            .unwrap_or_else(|| "lookup/".into());
        let capability_entry = capabilities
            .entry(capability.clone())
            .or_insert_with(|| (prefix.clone(), BTreeSet::new()));
        ensure!(
            capability_entry.0 == prefix,
            "conflicting witness capability prefix"
        );
        capability_entry.1.insert(operation.clone());
        providers.push(Provider {
            input: name,
            operation,
            capability,
            arguments: private_key
                .map(|key| BTreeMap::from([("key".into(), json!(key))]))
                .unwrap_or_default(),
        });
    }
    let mut capability_list = capabilities
        .into_iter()
        .map(|(id, (key_prefix, operations))| Capability {
            id,
            namespace: namespace.into(),
            key_prefix,
            operations: operations.into_iter().collect(),
        })
        .collect::<Vec<_>>();
    capability_list.push(Capability {
        id: "commit".into(),
        namespace: namespace.into(),
        key_prefix: "noctium/OpenZeppelinPort.Wallet/".into(),
        operations: vec![host::CAS.into()],
    });
    Ok(HostContext {
        protocol_version: 1,
        namespace: namespace.into(),
        base_revision: base_revision.into(),
        attempt_id: attempt.into(),
        capabilities: capability_list,
        operations: operations.into_values().collect(),
        providers,
        commit_capability: "commit".into(),
        limits: Limits::default(),
    })
}

fn mint_inputs(
    plan: &Plan,
    state: &ChargedState<Db>,
    alice: &[u8; 32],
    alice_key: EmbeddedGroupAffine,
) -> Result<BTreeMap<String, Json>> {
    let previous = map_record(plan, state, "pending", alice)?;
    let mut values = BTreeMap::from([
        ("recipient".into(), bytes(alice)),
        ("value".into(), json!("12")),
        ("recipientPk".into(), point_json(alice_key)),
        ("epoch".into(), json!("1")),
    ]);
    insert_native_fields(
        &mut values,
        &["previousC1X", "previousC1Y", "previousC2X", "previousC2Y"],
        &previous,
    );
    Ok(values)
}

fn sweep_inputs(
    plan: &Plan,
    state: &ChargedState<Db>,
    account: &[u8; 32],
) -> Result<BTreeMap<String, Json>> {
    let balance = map_record(plan, state, "balances", account)?;
    let pending = map_record(plan, state, "pending", account)?;
    let mut values = BTreeMap::from([("accountId".into(), bytes(account))]);
    insert_native_fields(
        &mut values,
        &["balanceC1X", "balanceC1Y", "balanceC2X", "balanceC2Y"],
        &balance,
    );
    insert_native_fields(
        &mut values,
        &["pendingC1X", "pendingC1Y", "pendingC2X", "pendingC2Y"],
        &pending,
    );
    Ok(values)
}

fn transfer_inputs(
    plan: &Plan,
    state: &ChargedState<Db>,
    sender: &[u8; 32],
    recipient: &[u8; 32],
    recipient_key: EmbeddedGroupAffine,
    amount: u64,
    epoch: u64,
) -> Result<BTreeMap<String, Json>> {
    let balance = map_record(plan, state, "balances", sender)?;
    let pending = map_record(plan, state, "pending", recipient)?;
    let mut values = BTreeMap::from([
        ("accountId".into(), bytes(sender)),
        ("recipient".into(), bytes(recipient)),
        ("value".into(), json!(amount.to_string())),
        ("recipientPk".into(), point_json(recipient_key)),
        ("epoch".into(), json!(epoch.to_string())),
    ]);
    insert_native_fields(
        &mut values,
        &["balanceC1X", "balanceC1Y", "balanceC2X", "balanceC2Y"],
        &balance,
    );
    insert_native_fields(
        &mut values,
        &["pendingC1X", "pendingC1Y", "pendingC2X", "pendingC2Y"],
        &pending,
    );
    Ok(values)
}

fn burn_inputs(
    plan: &Plan,
    state: &ChargedState<Db>,
    account: &[u8; 32],
    amount: u64,
) -> Result<BTreeMap<String, Json>> {
    let balance = map_record(plan, state, "balances", account)?;
    let mut values = BTreeMap::from([
        ("accountId".into(), bytes(account)),
        ("value".into(), json!(amount.to_string())),
    ]);
    insert_native_fields(
        &mut values,
        &["balanceC1X", "balanceC1Y", "balanceC2X", "balanceC2Y"],
        &balance,
    );
    Ok(values)
}

fn approve_inputs(
    plan: &Plan,
    state: &ChargedState<Db>,
    owner: &[u8; 32],
    spender: &[u8; 32],
    spender_key: EmbeddedGroupAffine,
) -> Result<BTreeMap<String, Json>> {
    let balance = map_record(plan, state, "balances", owner)?;
    let previous_owner = escrow_record(plan, state, owner, spender)?
        .map(|entry| [[entry[4], entry[5]], [entry[6], entry[7]]])
        .unwrap_or_else(|| {
            let identity = coordinates(EmbeddedGroupAffine::identity());
            [identity, identity]
        });
    Ok(BTreeMap::from([
        ("accountId".into(), bytes(owner)),
        ("spender".into(), bytes(spender)),
        ("value".into(), json!("3")),
        ("spenderPk".into(), point_json(spender_key)),
        (
            "balanceC1".into(),
            point_json_from_fields([balance[0], balance[1]]),
        ),
        (
            "balanceC2".into(),
            point_json_from_fields([balance[2], balance[3]]),
        ),
        (
            "previousOwnerC1".into(),
            point_json_from_fields(previous_owner[0]),
        ),
        (
            "previousOwnerC2".into(),
            point_json_from_fields(previous_owner[1]),
        ),
    ]))
}

fn transfer_from_inputs(
    plan: &Plan,
    state: &ChargedState<Db>,
    owner: &[u8; 32],
    spender: &[u8; 32],
    recipient: &[u8; 32],
    owner_key: EmbeddedGroupAffine,
    recipient_key: EmbeddedGroupAffine,
    amount: u64,
) -> Result<BTreeMap<String, Json>> {
    let escrow = escrow_record(plan, state, owner, spender)?
        .context("escrow record missing before transferFrom")?;
    let pending = map_record(plan, state, "pending", recipient)?;
    let spend_epoch = spend_epoch(plan, state, owner, spender)? + 1;
    let credit_epoch = counter(plan, state, "creditEpochs", recipient)? + 1;
    let mut values = BTreeMap::from([
        ("fromAddress".into(), bytes(owner)),
        ("spenderId".into(), bytes(spender)),
        ("to".into(), bytes(recipient)),
        ("value".into(), json!(amount.to_string())),
        ("ownerPk".into(), point_json(owner_key)),
        (
            "spenderC1".into(),
            point_json_from_fields([escrow[0], escrow[1]]),
        ),
        (
            "spenderC2".into(),
            point_json_from_fields([escrow[2], escrow[3]]),
        ),
        (
            "ownerC1".into(),
            point_json_from_fields([escrow[4], escrow[5]]),
        ),
        (
            "ownerC2".into(),
            point_json_from_fields([escrow[6], escrow[7]]),
        ),
        ("spendEpoch".into(), json!(spend_epoch.to_string())),
        ("recipientPk".into(), point_json(recipient_key)),
        (
            "pendingC1".into(),
            point_json_from_fields([pending[0], pending[1]]),
        ),
        (
            "pendingC2".into(),
            point_json_from_fields([pending[2], pending[3]]),
        ),
        ("creditEpoch".into(), json!(credit_epoch.to_string())),
    ]);
    Ok(std::mem::take(&mut values))
}

fn escrow_spend_inputs(
    plan: &Plan,
    state: &ChargedState<Db>,
    owner: &[u8; 32],
    spender: &[u8; 32],
    owner_key: EmbeddedGroupAffine,
    amount: u64,
) -> Result<BTreeMap<String, Json>> {
    let escrow = escrow_record(plan, state, owner, spender)?
        .context("escrow record missing before burnFrom")?;
    let spend_epoch = spend_epoch(plan, state, owner, spender)? + 1;
    Ok(BTreeMap::from([
        ("fromAddress".into(), bytes(owner)),
        ("spenderId".into(), bytes(spender)),
        ("value".into(), json!(amount.to_string())),
        ("ownerPk".into(), point_json(owner_key)),
        (
            "spenderC1".into(),
            point_json_from_fields([escrow[0], escrow[1]]),
        ),
        (
            "spenderC2".into(),
            point_json_from_fields([escrow[2], escrow[3]]),
        ),
        (
            "ownerC1".into(),
            point_json_from_fields([escrow[4], escrow[5]]),
        ),
        (
            "ownerC2".into(),
            point_json_from_fields([escrow[6], escrow[7]]),
        ),
        ("spendEpoch".into(), json!(spend_epoch.to_string())),
    ]))
}

fn assert_final_state(
    plan: &Plan,
    state: &ChargedState<Db>,
    alice: &[u8; 32],
    bob: &[u8; 32],
    alice_key: EmbeddedGroupAffine,
    bob_key: EmbeddedGroupAffine,
) -> Result<()> {
    ensure!(
        cell_scalar(plan, state, "totalSupply")? == 9,
        "unexpected final supply"
    );
    let alice_balance = ciphertext_from_fields(&map_record(plan, state, "balances", alice)?, 0)?;
    let alice_pending = ciphertext_from_fields(&map_record(plan, state, "pending", alice)?, 0)?;
    let bob_balance = ciphertext_from_fields(&map_record(plan, state, "balances", bob)?, 0)?;
    let bob_pending = ciphertext_from_fields(&map_record(plan, state, "pending", bob)?, 0)?;
    ensure!(
        decrypt_small(
            alice_balance,
            encryption_scalar(&ALICE.encryption_secret),
            MAX_FIXTURE_BALANCE
        )? == 1,
        "unexpected Alice spendable balance"
    );
    ensure!(
        decrypt_small(
            alice_pending,
            encryption_scalar(&ALICE.encryption_secret),
            MAX_FIXTURE_BALANCE
        )? == 1,
        "unexpected Alice pending balance"
    );
    ensure!(
        decrypt_small(
            bob_balance,
            encryption_scalar(&BOB.encryption_secret),
            MAX_FIXTURE_BALANCE
        )? == 0,
        "unexpected Bob spendable balance"
    );
    ensure!(
        decrypt_small(
            bob_pending,
            encryption_scalar(&BOB.encryption_secret),
            MAX_FIXTURE_BALANCE
        )? == 7,
        "unexpected Bob pending balance"
    );
    let escrow = escrow_record(plan, state, alice, bob)?.context("final escrow record missing")?;
    let spender_ciphertext = ciphertext_from_fields(&escrow, 0)?;
    let owner_ciphertext = ciphertext_from_fields(&escrow, 4)?;
    ensure!(
        decrypt_small(
            spender_ciphertext,
            encryption_scalar(&BOB.encryption_secret),
            MAX_FIXTURE_BALANCE
        )? == 0,
        "unexpected remaining spender escrow"
    );
    ensure!(
        decrypt_small(
            owner_ciphertext,
            encryption_scalar(&ALICE.encryption_secret),
            MAX_FIXTURE_BALANCE
        )? == 0,
        "unexpected remaining owner escrow"
    );
    let owner_memo = Memo {
        ephemeral: point_from_fields([escrow[8], escrow[9]])?,
        amount: escrow[10],
    };
    ensure!(
        decrypt_owner_memo(owner_memo, encryption_scalar(&ALICE.encryption_secret))? == 0,
        "unexpected owner escrow memo"
    );
    ensure!(
        counter(plan, state, "creditEpochs", bob)? == 2,
        "unexpected Bob credit epoch"
    );
    ensure!(
        spend_epoch(plan, state, alice, bob)? == 2,
        "unexpected escrow spend epoch"
    );
    let _ = (alice_key, bob_key);
    Ok(())
}

#[derive(Clone, Copy)]
struct Memo {
    ephemeral: EmbeddedGroupAffine,
    amount: Fr,
}

fn state_slot<'a>(
    plan: &Plan,
    state: &'a ChargedState<Db>,
    name: &str,
) -> Result<&'a StateValue<Db>> {
    let index = plan
        .state
        .iter()
        .position(|field| field.name == name)
        .with_context(|| format!("state field {name} missing"))?;
    let StateValue::Array(root) = state.get_ref() else {
        bail!("contract state is not an array")
    };
    root.get(index)
        .ok_or_else(|| anyhow!("state field {name} missing"))
}

fn map_record(
    plan: &Plan,
    state: &ChargedState<Db>,
    name: &str,
    key: &[u8; 32],
) -> Result<Vec<Fr>> {
    let StateValue::Map(map) = state_slot(plan, state, name)? else {
        bail!("state field {name} is not a map")
    };
    let key: AlignedValue = (*key).into();
    let value = map
        .get(&key)
        .with_context(|| format!("{name} account record missing"))?;
    let StateValue::Cell(cell) = &*value else {
        bail!("state field {name} record is not a cell")
    };
    let mut fields = Vec::new();
    cell.value_only_field_repr(&mut fields);
    Ok(fields)
}

fn escrow_record(
    plan: &Plan,
    state: &ChargedState<Db>,
    owner: &[u8; 32],
    spender: &[u8; 32],
) -> Result<Option<Vec<Fr>>> {
    let StateValue::Map(owners) = state_slot(plan, state, "escrow")? else {
        bail!("escrow state is not a map")
    };
    let owner: AlignedValue = (*owner).into();
    let Some(owner_value) = owners.get(&owner) else {
        return Ok(None);
    };
    let StateValue::Map(spenders) = &*owner_value else {
        bail!("escrow owner value is not a map")
    };
    let spender: AlignedValue = (*spender).into();
    let Some(value) = spenders.get(&spender) else {
        return Ok(None);
    };
    let StateValue::Cell(cell) = &*value else {
        bail!("escrow entry is not a cell")
    };
    let mut fields = Vec::new();
    cell.value_only_field_repr(&mut fields);
    Ok(Some(fields))
}

fn counter(plan: &Plan, state: &ChargedState<Db>, name: &str, key: &[u8; 32]) -> Result<u64> {
    let StateValue::Map(map) = state_slot(plan, state, name)? else {
        bail!("state field {name} is not a map")
    };
    let key: AlignedValue = (*key).into();
    let Some(value) = map.get(&key) else {
        return Ok(0);
    };
    let StateValue::Cell(cell) = &*value else {
        bail!("state field {name} counter is not a cell")
    };
    let mut fields = Vec::new();
    cell.value_only_field_repr(&mut fields);
    fields
        .first()
        .copied()
        .map(fr_u64)
        .transpose()?
        .context("counter value missing")
}

fn spend_epoch(
    plan: &Plan,
    state: &ChargedState<Db>,
    owner: &[u8; 32],
    spender: &[u8; 32],
) -> Result<u64> {
    let StateValue::Map(owners) = state_slot(plan, state, "escrowSpendEpochs")? else {
        bail!("escrow spend epoch state is not a map")
    };
    let owner: AlignedValue = (*owner).into();
    let Some(owner_value) = owners.get(&owner) else {
        return Ok(0);
    };
    let StateValue::Map(spenders) = &*owner_value else {
        bail!("escrow spend epoch owner is not a map")
    };
    let spender: AlignedValue = (*spender).into();
    let Some(value) = spenders.get(&spender) else {
        return Ok(0);
    };
    let StateValue::Cell(cell) = &*value else {
        bail!("escrow spend epoch is not a cell")
    };
    let mut fields = Vec::new();
    cell.value_only_field_repr(&mut fields);
    fields
        .first()
        .copied()
        .map(fr_u64)
        .transpose()?
        .context("spend epoch value missing")
}

fn cell_scalar(plan: &Plan, state: &ChargedState<Db>, name: &str) -> Result<u64> {
    let StateValue::Cell(cell) = state_slot(plan, state, name)? else {
        bail!("state field {name} is not a cell")
    };
    let mut fields = Vec::new();
    cell.value_only_field_repr(&mut fields);
    fields
        .first()
        .copied()
        .map(fr_u64)
        .transpose()?
        .context("scalar value missing")
}

fn fr_u64(value: Fr) -> Result<u64> {
    field_decimal(value)
        .parse()
        .context("fixture field does not fit u64")
}

fn ciphertext_from_fields(fields: &[Fr], offset: usize) -> Result<Ciphertext> {
    Ok(Ciphertext {
        c1: point_from_fields([fields[offset], fields[offset + 1]])?,
        c2: point_from_fields([fields[offset + 2], fields[offset + 3]])?,
    })
}

fn point_from_fields(fields: [Fr; 2]) -> Result<EmbeddedGroupAffine> {
    EmbeddedGroupAffine::new(fields[0], fields[1]).ok_or_else(|| anyhow!("invalid Jubjub point"))
}

fn point_from_json(value: &Json) -> Result<EmbeddedGroupAffine> {
    ensure!(value["kind"] == "jubjubPoint", "expected Jubjub point");
    let x = canonical_field(value["x"].as_str().context("point x missing")?)?;
    let y = canonical_field(value["y"].as_str().context("point y missing")?)?;
    point_from_fields([x, y])
}

fn decrypt_small(ciphertext: Ciphertext, secret: EmbeddedFr, maximum: u64) -> Result<u64> {
    let message = ciphertext.c2 + ciphertext.c1 * (EmbeddedFr::from(0u64) - secret);
    let generator = EmbeddedGroupAffine::generator();
    (0..=maximum)
        .find(|value| generator * EmbeddedFr::from(*value) == message)
        .ok_or_else(|| anyhow!("fixture plaintext exceeds the bounded balance range"))
}

fn decrypt_owner_memo(memo: Memo, secret: EmbeddedFr) -> Result<u64> {
    let shared = memo.ephemeral * secret;
    let digest = hash(&[
        &shared.x().context("ECDH identity x missing")?.as_le_bytes(),
        &shared.y().context("ECDH identity y missing")?.as_le_bytes(),
    ]);
    let mask_digest = hash(&[&digest, &tag("OZ_CFT_escrow_owner_v1")]);
    let mask =
        Fr::from_le_bytes(&mask_digest[..31]).ok_or_else(|| anyhow!("invalid ECDH memo mask"))?;
    let plaintext = memo.amount - mask;
    (0..=MAX_FIXTURE_BALANCE)
        .find(|value| Fr::from(*value) == plaintext)
        .ok_or_else(|| anyhow!("owner memo plaintext exceeds fixture range"))
}

fn insert_native_fields(values: &mut BTreeMap<String, Json>, names: &[&str], fields: &[Fr]) {
    for (name, value) in names.iter().zip(fields) {
        values.insert((*name).into(), json!(field_decimal(*value)));
    }
}

fn point_json_from_fields(fields: [Fr; 2]) -> Json {
    json!({
        "kind":"jubjubPoint",
        "x":field_decimal(fields[0]),
        "y":field_decimal(fields[1])
    })
}

fn point_json(point: EmbeddedGroupAffine) -> Json {
    point_json_from_fields(coordinates(point))
}

fn coordinates(point: EmbeddedGroupAffine) -> [Fr; 2] {
    [point.x().unwrap(), point.y().unwrap()]
}

fn bytes(value: &[u8; 32]) -> Json {
    json!({"kind":"bytes", "values":value.as_slice()})
}

fn hash(parts: &[&[u8]]) -> [u8; 32] {
    let mut digest = Sha256::new();
    for part in parts {
        digest.update(part);
    }
    digest.finalize().into()
}

fn account_id(secret: &[u8; 32]) -> [u8; 32] {
    hash(&[secret])
}

fn tag(text: &str) -> [u8; 32] {
    let mut value = [0; 32];
    value[..text.len()].copy_from_slice(text.as_bytes());
    value
}

fn scalar(parts: &[&[u8]]) -> EmbeddedFr {
    EmbeddedFr::from_le_bytes(&hash(parts)[..31]).expect("sha256 scalar fits embedded field")
}

fn encryption_scalar(secret: &[u8; 32]) -> EmbeddedFr {
    scalar(&[&tag("ElGamal:secretToScalar"), secret])
}
