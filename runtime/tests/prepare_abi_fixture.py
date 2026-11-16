"""Prepare public ABI input from an existing qualified native artifact bundle."""
import json
import pathlib
import sys

source = pathlib.Path(sys.argv[1])
plan = json.loads((source / "source-plan.json").read_text())
config = json.loads((source / "runtime-config.json").read_text())
contract = json.loads((source / "native-contract.json").read_text())
public_names = {
    item["name"] for item in plan["circuit"]["inputs"]
    if item["visibility"] == "public"
}
envelope = {
    "abiVersion": 1,
    "profile": "midnight-ledger-9-zkir-3.2.0",
    "plan": plan,
    "publicInputs": {key: value for key, value in config["inputs"].items()
                     if key in public_names},
    "state": config["state"],
    "ledgerParametersHex": (source / "ledger.params").read_bytes().hex(),
    "address": contract["address"],
    "circuit": json.loads((source / "zkir" / f"{plan['entrypoint']}.zkir").read_text()),
}
pathlib.Path(sys.argv[2]).write_text(json.dumps(envelope, separators=(",", ":")))
