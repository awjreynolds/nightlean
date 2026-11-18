#!/usr/bin/env python3
"""Noctium's scoped public PrivateClaim key/deployment identity controller.

The caller supplies independent authority, specification and deployment pins.
Key generation and public verification accept no private invocation configuration.
"""

from __future__ import annotations
import argparse, hashlib, json, os, re, shutil, stat, subprocess, tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
GUARANTEE = "PrivateClaimDeploymentIdentity/v1"
NATIVE_REVISION = "7a51b3385bbf4bce3604df87a7c70867c9ab43c0"
CLAIM_SRS = "b9009f1098bcefffec3c461ab3a5e3a17f7e5599f0f08c70fcdc55a89227bcbd"
MAX_JSON = 16 * 1024 * 1024


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for data in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(data)
    return h.hexdigest()


def retained(path: Path, pin: str | None = None, limit: int = MAX_JSON) -> bytes:
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    with os.fdopen(fd, "rb") as stream:
        info = os.fstat(stream.fileno())
        assert stat.S_ISREG(info.st_mode) and info.st_size <= limit, (
            "invalid_bounded_input"
        )
        data = stream.read(limit + 1)
    assert len(data) <= limit, "input_limit"
    if pin is not None:
        assert (
            re.fullmatch("[0-9a-f]{64}", pin)
            and hashlib.sha256(data).hexdigest() == pin
        ), "external_input_pin_mismatch"
    return data


def load(path: Path, pin: str | None = None) -> dict:
    data = retained(path, pin)
    value = json.loads(data)
    assert isinstance(value, dict), "public_object_required"
    return value


def trusted_authority_snapshot(
    authority: dict, authority_bytes: bytes, original: Path, destination: Path
) -> Path:
    destination.mkdir()
    (destination / "authority.json").write_bytes(authority_bytes)
    record = authority["record"]
    files = {
        "source-identity.json": None,
        "model.ndjson": record["modelSha256"],
        "base-proof-closure.ndjson": record["baseProofSha256"],
        "certificate.ndjson": authority["certificateSha256"],
        "source/.lake/build/bin/noctium": record["compilerSha256"],
    }
    for relative, digest in record["source"]["files"].items():
        files["source/" + relative] = digest
    for relative, digest in record["imports"]:
        files["products/" + relative] = digest
        prefix, name = relative.split("/", 1)
        files[
            (
                "source/.lake/build/lib/lean/"
                if prefix == "library"
                else "proof-imports/"
            )
            + name
        ] = digest
    for name, digest in record["artifacts"].items():
        files["artifacts/" + name] = digest
    for relative, pin in files.items():
        name = Path(relative)
        assert not name.is_absolute() and ".." not in name.parts, (
            "unsafe_authority_path"
        )
        data = retained(original / name, pin, 512 * 1024 * 1024)
        target = destination / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    return destination / "authority.json"


def save(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, sort_keys=True, indent=2) + "\n")


def run(
    command: list[str], log: Path, env: dict | None = None, cwd: Path = ROOT
) -> str:
    result = subprocess.run(
        command, cwd=cwd, env=env, text=True, capture_output=True, timeout=900
    )
    log.parent.mkdir(parents=True, exist_ok=True)
    log.write_text(result.stdout + result.stderr)
    assert result.returncode == 0, "qualified_process_rejected: " + log.name
    return result.stdout


def source_audit(args, work: Path) -> tuple[dict, dict, dict]:
    authority_bytes = retained(args.authority, args.authority_sha256)
    authority = json.loads(authority_bytes)
    assert isinstance(authority, dict), "public_authority_required"
    specification_bytes = retained(args.specification, args.specification_sha256)
    spec = json.loads(specification_bytes)
    assert isinstance(spec, dict), "public_specification_required"
    tool_bytes = retained(args.native_toolchain, spec["nativeToolchainSha256"])
    tool = json.loads(tool_bytes)
    assert re.fullmatch("[0-9a-f]{64}", args.rust_helper_sha256), (
        "invalid_rust_helper_pin"
    )
    # Retain every public input before any execution. The external pins remain
    # the authority, not digests inferred from newly reopened candidate files.
    (work / "verified-authority.json").write_bytes(authority_bytes)
    (work / "verified-specification.json").write_bytes(specification_bytes)
    (work / "verified-native-toolchain.json").write_bytes(tool_bytes)
    with tempfile.TemporaryDirectory(
        prefix="noctium-trusted-source-audit-", dir="/private/tmp"
    ) as directory:
        trusted = Path(directory) / "authority"
        snapshot = trusted_authority_snapshot(
            authority, authority_bytes, args.authority.parent, trusted
        )
        script = trusted / "source/scripts/proofs/check-private-claim-artifacts.py"
        checked = json.loads(
            run(
                [
                    "python3",
                    str(script),
                    "verify",
                    "--authority",
                    str(snapshot),
                    "--authority-sha256",
                    args.authority_sha256,
                    "--bundle",
                    str(args.audit_bundle),
                ],
                work / "source-audit.log",
            )
        )
    assert (
        checked["exactArtifactByteBuildBindingVerified"]
        and checked["retainedBytesKernelMatched"]
        and checked["externalAuthorityKernelMatched"]
    ), "exact_source_audit_required"
    assert (
        checked["sourceCommit"] == authority["build"]["sourceCommit"]
        and checked["sourceTree"] == authority["build"]["sourceTree"]
    ), "source_audit_identity_mismatch"
    assert spec["schemaVersion"] == 1 and spec["guaranteeVersion"] == GUARANTEE, (
        "unsupported_deployment_specification"
    )
    assert (
        spec["authoritySha256"] == args.authority_sha256
        and spec["sourceCommit"] == authority["build"]["sourceCommit"]
        and spec["sourceTree"] == authority["build"]["sourceTree"]
    ), "external_source_authority_mismatch"
    assert (
        spec["entrypoint"] == "claim"
        and spec["policy"]["profile"] == "midnight-ledger-9-zkir-3.2.1"
    ), "wrong_selected_target"
    assert (
        set(spec["initialization"]) == {"acceptedRoot", "campaignId", "spent"}
        and spec["initialization"]["spent"] == []
    ), "wrong_public_initialization"
    assert spec["srsSha256"] == CLAIM_SRS, "wrong_selected_srs"
    retained(args.srs, CLAIM_SRS, 128 * 1024 * 1024)
    assert (
        tool["repository"] == "https://github.com/midnightntwrk/midnight-zkir"
        and tool["revision"] == NATIVE_REVISION
        and tool["requestedVersion"] == "3.2.1"
        and tool["rust"] == "1.100.0"
    ), "wrong_keygen_tool_revision"
    save(work / "source-audit.json", checked)
    return authority, spec, tool


def helper(args, request: dict, work: Path, name: str) -> dict:
    with tempfile.TemporaryDirectory(
        prefix="noctium-private-invocation-", dir="/private/tmp"
    ) as directory:
        private = Path(directory)
        executable = private / "rust-helper"
        executable.write_bytes(
            retained(args.rust_helper, args.rust_helper_sha256, 512 * 1024 * 1024)
        )
        executable.chmod(0o700)
        request_file = private / "request.json"
        save(request_file, request)
        request_file.chmod(0o600)
        result = run([str(executable), str(request_file)], work / (name + ".log"))
    value = json.loads(result)
    save(work / (name + ".json"), value)
    return value


def common_request(args, bundle: Path, work: Path, manifest: str | None = None) -> dict:
    value = {
        "specification": str(work / "verified-specification.json"),
        "specificationSha256": args.specification_sha256,
        "authority": str(work / "verified-authority.json"),
        "nativeToolchain": str(work / "verified-native-toolchain.json"),
        "srs": str(work / "keygen/parameters/bls_midnight_2p9"),
        "nativeBundle": str(bundle),
    }
    if manifest:
        value["manifestSha256"] = manifest
    return value


def keygen(
    args,
    artifacts: Path,
    work: Path,
    expected_call_sha256: str,
    tool: dict,
    toolchain_sha256: str,
) -> dict:
    source = artifacts / "PrivateClaim.claim.zkir"
    expected_binary_sha256 = tool["binarySha256"]
    # Retain the checked input and SRS so the tool never reopens candidate paths.
    call_bytes = retained(source, expected_call_sha256, 65536)
    directory = work / "keygen"
    directory.mkdir()
    (directory / "PrivateClaim.claim.zkir").write_bytes(call_bytes)
    cache = directory / "parameters"
    cache.mkdir()
    (cache / "bls_midnight_2p9").write_bytes(
        retained(args.srs, CLAIM_SRS, 128 * 1024 * 1024)
    )
    env = os.environ.copy()
    env["MIDNIGHT_PP"] = str(cache)
    with tempfile.TemporaryDirectory(
        prefix="noctium-native-keygen-", dir="/private/tmp"
    ) as temporary:
        executable = Path(temporary) / "zkir"
        executable.write_bytes(
            retained(args.native_cli, expected_binary_sha256, 512 * 1024 * 1024)
        )
        executable.chmod(0o700)
        command = [
            str(executable),
            "compile",
            str(directory / "PrivateClaim.claim.zkir"),
            str(directory / "claim.prover"),
            str(directory / "claim.verifier"),
        ]
        run(command, work / "native-keygen.log", env)
    record = {
        "schemaVersion": 1,
        "operation": "native-cli-keygen",
        "toolchainManifestSha256": toolchain_sha256,
        "tool": tool,
        "invocation": [
            "zkir",
            "compile",
            "PrivateClaim.claim.zkir",
            "claim.prover",
            "claim.verifier",
        ],
        "inputCallSha256": hashlib.sha256(call_bytes).hexdigest(),
        "retainedInputCallSha256": sha(directory / "PrivateClaim.claim.zkir"),
        "srsSha256": CLAIM_SRS,
        "srsFile": "bls_midnight_2p9",
        "proverKeySha256": sha(directory / "claim.prover"),
        "verifierKeySha256": sha(directory / "claim.verifier"),
        "privateInvocationInputsConsumed": False,
    }
    save(work / "keygen-invocation.json", record)
    return record


def build(args) -> dict:
    assert not args.output.exists(), "fresh_public_output_required"
    args.output.mkdir(parents=True)
    authority, spec, tool = source_audit(args, args.output)
    assert sha(args.ledger_parameters) == spec["ledgerParametersSha256"], (
        "ledger_parameter_pin_mismatch"
    )
    artifact_dir = args.audit_bundle / "artifacts"
    invocation = keygen(
        args,
        artifact_dir,
        args.output,
        authority["record"]["artifacts"]["PrivateClaim.claim.zkir"],
        tool,
        spec["nativeToolchainSha256"],
    )
    save(
        args.output / "native-abi.json",
        {"abiVersion": 1, "profile": spec["policy"]["profile"]},
    )
    request = common_request(args, args.output / "native-bundle", args.output)
    request.update(
        mode="prepare",
        auditedArtifacts=str(artifact_dir),
        auditedSource=str(args.audit_bundle / "source"),
        proverKey=str(args.output / "keygen/claim.prover"),
        verifierKey=str(args.output / "keygen/claim.verifier"),
        ledgerParameters=str(args.ledger_parameters),
        abi=str(args.output / "native-abi.json"),
    )
    material = helper(args, request, args.output, "material")
    manifest = {
        "schemaVersion": 1,
        "guaranteeVersion": GUARANTEE,
        "specificationSha256": args.specification_sha256,
        "externalAuthoritySha256": args.authority_sha256,
        "sourceCommit": authority["build"]["sourceCommit"],
        "sourceTree": authority["build"]["sourceTree"],
        "sourceAudit": load(args.output / "source-audit.json"),
        "nativeManifestSha256": material["manifestSha256"],
        "keygenInvocationSha256": sha(args.output / "keygen-invocation.json"),
        "materialIdentity": material["materialIdentity"],
        "contractArtifactsRecompiledByDeploymentController": False,
        "nativeKeysFreshlyGenerated": True,
        "producerRustHelperSha256": args.rust_helper_sha256,
        "independentRustKeyRegenerationMatched": True,
        "publicBuild": True,
    }
    save(args.output / "manifest.json", manifest)
    return {
        "status": "public-deployment-material-built",
        "output": str(args.output),
        "manifestSha256": sha(args.output / "manifest.json"),
        "nativeManifestSha256": material["manifestSha256"],
    }


def check_package(args, work: Path) -> tuple[dict, dict]:
    authority, spec, tool = source_audit(args, work)
    package = load(args.deployment_bundle / "manifest.json")
    assert (
        package["schemaVersion"] == 1
        and package["guaranteeVersion"] == GUARANTEE
        and package["specificationSha256"] == args.specification_sha256
        and package["externalAuthoritySha256"] == args.authority_sha256
    ), "deployment_package_authority_mismatch"
    assert (
        package["sourceCommit"] == authority["build"]["sourceCommit"]
        and package["sourceTree"] == authority["build"]["sourceTree"]
    ), "deployment_package_source_mismatch"
    invocation = load(
        args.deployment_bundle / "keygen-invocation.json",
        package["keygenInvocationSha256"],
    )
    assert (
        invocation["inputCallSha256"]
        == authority["record"]["artifacts"]["PrivateClaim.claim.zkir"]
        and invocation["srsSha256"] == spec["srsSha256"]
        and invocation["toolchainManifestSha256"] == spec["nativeToolchainSha256"]
        and invocation["privateInvocationInputsConsumed"] is False
    ), "keygen_invocation_binding_mismatch"
    # Re-execute the actual CLI from trusted inputs on every public audit.
    regenerated = keygen(
        args,
        args.audit_bundle / "artifacts",
        work,
        authority["record"]["artifacts"]["PrivateClaim.claim.zkir"],
        tool,
        spec["nativeToolchainSha256"],
    )
    for key in [
        "schemaVersion",
        "operation",
        "toolchainManifestSha256",
        "tool",
        "invocation",
        "inputCallSha256",
        "retainedInputCallSha256",
        "srsSha256",
        "srsFile",
        "proverKeySha256",
        "verifierKeySha256",
        "privateInvocationInputsConsumed",
    ]:
        assert regenerated[key] == invocation[key], "independent_cli_keygen_mismatch"
    for suffix in ["prover", "verifier"]:
        actual = args.deployment_bundle / ("native-bundle/keys/entrypoint." + suffix)
        expected = work / ("keygen/claim." + suffix)
        assert (
            actual.is_file()
            and not actual.is_symlink()
            and actual.stat().st_size == expected.stat().st_size
            and actual.read_bytes() == expected.read_bytes()
        ), "cli_bundle_key_bytes_mismatch"
    return package, spec


def execute(args) -> dict:
    assert args.approve and args.public_development_genesis, (
        "explicit_development_execution_approval_required"
    )
    assert not args.output.exists(), "fresh_execution_output_required"
    args.output.mkdir(parents=True)
    package, _ = check_package(args, args.output)
    request = common_request(
        args,
        args.deployment_bundle / "native-bundle",
        args.output,
        package["nativeManifestSha256"],
    )
    request.update(
        mode="execute",
        endpoint=args.endpoint,
        privateConfig=str(args.private_config),
        journalDirectory=str(args.private_journal),
        parameterCache=str(args.parameter_cache),
        publicDevelopmentGenesis=True,
        approve=True,
        record=str(args.output / "deployment.json"),
    )
    result = helper(args, request, args.output, "execution")
    save(args.output / "execution-result.json", result)
    return result


def verify(args) -> dict:
    assert not args.output.exists(), "fresh_audit_output_required"
    args.output.mkdir(parents=True)
    package, _ = check_package(args, args.output)
    load(args.record, args.record_sha256)
    request = common_request(
        args,
        args.deployment_bundle / "native-bundle",
        args.output,
        package["nativeManifestSha256"],
    )
    request.update(
        mode="verify",
        endpoint=args.endpoint,
        record=str(args.record),
        recordSha256=args.record_sha256,
        expectedAddress=args.expected_address,
    )
    result = helper(args, request, args.output, "public-verification")
    result.update(
        auditorRustHelperSha256=args.rust_helper_sha256,
        sourceAudit=load(args.output / "source-audit.json"),
        sourceAuthoritySha256=args.authority_sha256,
        sourceAndKeyDeploymentJoinChecked=True,
        assumptions=[
            "qualified native key generation and selected Rust/parser/prover implementations",
            "SRS provenance and ceremony relations",
            "host toolchain and durable-store policy for execution",
            "trusted node canonical history and finality, not a consensus light client",
            "public initialization is caller-specified, not an unconditional business specification",
        ],
    )
    save(args.output / "audit.json", result)
    return result


def main() -> int:
    if not __debug__:
        print(
            json.dumps(
                {"status": "rejected", "error": "optimized_python_is_not_qualified"}
            )
        )
        return 1
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    for name in ["build", "execute", "verify"]:
        p = commands.add_parser(name)
        for argument in [
            "authority",
            "audit-bundle",
            "specification",
            "native-toolchain",
            "native-cli",
            "srs",
            "rust-helper",
            "output",
        ]:
            p.add_argument("--" + argument, type=Path, required=True)
        p.add_argument("--authority-sha256", required=True)
        p.add_argument("--specification-sha256", required=True)
        p.add_argument("--rust-helper-sha256", required=True)
        if name == "build":
            p.add_argument("--ledger-parameters", type=Path, required=True)
        else:
            p.add_argument("--deployment-bundle", type=Path, required=True)
            p.add_argument("--endpoint", required=True)
        if name == "execute":
            p.add_argument("--private-config", type=Path, required=True)
            p.add_argument("--private-journal", type=Path, required=True)
            p.add_argument("--parameter-cache", type=Path, required=True)
            p.add_argument("--approve", action="store_true")
            p.add_argument("--public-development-genesis", action="store_true")
        if name == "verify":
            p.add_argument("--record", type=Path, required=True)
            p.add_argument("--record-sha256", required=True)
            p.add_argument("--expected-address", required=True)
    args = parser.parse_args()
    for key, value in vars(args).items():
        if isinstance(value, Path):
            setattr(args, key, value.resolve())
    try:
        result = {"build": build, "execute": execute, "verify": verify}[args.command](
            args
        )
        print(json.dumps(result, sort_keys=True))
        return 0
    except (AssertionError, OSError, ValueError, subprocess.SubprocessError) as error:
        print(json.dumps({"status": "rejected", "error": str(error)}))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
