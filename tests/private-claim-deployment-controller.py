#!/usr/bin/env python3
"""Deterministic authentication/execution race regressions for the public controller."""

import hashlib, importlib.util, json, os, tempfile, unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

SCRIPT = (
    Path(__file__).resolve().parents[1]
    / "scripts/proofs/check-private-claim-deployment.py"
)
spec = importlib.util.spec_from_file_location("deployment_controller", SCRIPT)
controller = importlib.util.module_from_spec(spec)
spec.loader.exec_module(controller)


def digest(data):
    return hashlib.sha256(data).hexdigest()


class PinRaces(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(
            prefix="noctium-pin-race-", dir="/private/tmp"
        )
        self.root = Path(self.temp.name)

    def tearDown(self):
        self.temp.cleanup()

    def test_json_hash_and_parse_share_one_retained_read(self):
        path = self.root / "input.json"
        original = b'{"value":1}'
        path.write_bytes(original)
        real = controller.retained

        def changed(*args, **kwargs):
            data = real(*args, **kwargs)
            path.write_bytes(b'{"value":2}')
            return data

        with patch.object(controller, "retained", side_effect=changed):
            self.assertEqual(controller.load(path, digest(original)), {"value": 1})
        self.assertEqual(json.loads(path.read_bytes()), {"value": 2})

    def fixture(self):
        artifacts = self.root / "artifacts"
        artifacts.mkdir()
        call = b'{"audited":"call"}'
        (artifacts / "PrivateClaim.claim.zkir").write_bytes(call)
        srs = self.root / "parameters"
        srs.write_bytes(b"public parameter fixture")
        executable = self.root / "cli"
        original = b"original independently pinned CLI"
        executable.write_bytes(original)
        manifest = self.root / "tool.json"
        tool = {"binarySha256": digest(original)}
        manifest.write_text(json.dumps(tool))
        tool_pin = digest(manifest.read_bytes())
        args = SimpleNamespace(
            native_cli=executable, native_toolchain=manifest, srs=srs
        )
        return args, artifacts, call, srs, manifest, tool_pin, original

    def test_replaced_manifest_and_cli_do_not_change_authenticated_tool_pin(self):
        args, artifacts, call, srs, manifest, tool_pin, original = self.fixture()
        authenticated = controller.load(manifest, tool_pin)
        args.native_cli.write_bytes(b"replacement CLI")
        manifest.write_text(json.dumps({"binarySha256": digest(b"replacement CLI")}))
        work = self.root / "work"
        work.mkdir()
        with (
            patch.object(controller, "CLAIM_SRS", digest(srs.read_bytes())),
            patch.object(controller, "run") as execute,
        ):
            with self.assertRaises(AssertionError):
                controller.keygen(
                    args, artifacts, work, digest(call), authenticated, tool_pin
                )
            execute.assert_not_called()

    def test_cli_execution_uses_original_retained_bytes_after_path_replacement(self):
        args, artifacts, call, srs, manifest, tool_pin, original = self.fixture()
        authenticated = controller.load(manifest, tool_pin)
        real = controller.retained
        work = self.root / "work"
        work.mkdir()

        def changed(path, *a, **kw):
            data = real(path, *a, **kw)
            if path == args.native_cli:
                args.native_cli.write_bytes(b"replacement CLI")
                manifest.write_text(
                    json.dumps({"binarySha256": digest(b"replacement CLI")})
                )
            return data

        def execute(command, *a, **kw):
            self.assertNotEqual(Path(command[0]), args.native_cli)
            self.assertEqual(Path(command[0]).read_bytes(), original)
            Path(command[3]).write_bytes(b"generated proving key")
            Path(command[4]).write_bytes(b"generated verifier key")
            return ""

        with (
            patch.object(controller, "CLAIM_SRS", digest(srs.read_bytes())),
            patch.object(controller, "retained", side_effect=changed),
            patch.object(controller, "run", side_effect=execute),
        ):
            record = controller.keygen(
                args, artifacts, work, digest(call), authenticated, tool_pin
            )
        self.assertEqual(record["tool"]["binarySha256"], digest(original))
        self.assertEqual(record["toolchainManifestSha256"], tool_pin)
        self.assertFalse((work / "keygen/zkir").exists())

    def test_rust_helper_executes_verified_snapshot_and_retains_no_private_request(
        self,
    ):
        path = self.root / "helper"
        original = b"original independently pinned Rust helper"
        path.write_bytes(original)
        args = SimpleNamespace(rust_helper=path, rust_helper_sha256=digest(original))
        real = controller.retained
        work = self.root / "work"
        work.mkdir()

        def changed(*a, **kw):
            data = real(*a, **kw)
            path.write_bytes(b"replacement helper")
            return data

        def execute(command, *a, **kw):
            self.assertNotEqual(Path(command[0]), path)
            self.assertEqual(Path(command[0]).read_bytes(), original)
            self.assertNotEqual(Path(command[1]).parent, work)
            return '{"status":"checked"}'

        with (
            patch.object(controller, "retained", side_effect=changed),
            patch.object(controller, "run", side_effect=execute),
        ):
            self.assertEqual(
                controller.helper(
                    args,
                    {"mode": "execute", "privateConfig": "private path"},
                    work,
                    "native",
                ),
                {"status": "checked"},
            )
        self.assertEqual(sorted(p.name for p in work.iterdir()), ["native.json"])

    def test_replaced_rust_helper_never_executes(self):
        path = self.root / "helper"
        path.write_bytes(b"replacement helper")
        args = SimpleNamespace(
            rust_helper=path, rust_helper_sha256=digest(b"original helper")
        )
        work = self.root / "work"
        work.mkdir()
        with patch.object(controller, "run") as execute:
            with self.assertRaises(AssertionError):
                controller.helper(args, {"mode": "verify"}, work, "native")
            execute.assert_not_called()

    def test_call_replaced_with_fifo_immediately_before_open_rejects(self):
        args, artifacts, call, srs, manifest, tool_pin, original = self.fixture()
        authenticated = controller.load(manifest, tool_pin)
        source = artifacts / "PrivateClaim.claim.zkir"
        real_open = os.open
        work = self.root / "work"
        work.mkdir()

        def replace(path, flags, *a, **kw):
            if Path(path) == source:
                source.unlink()
                os.mkfifo(source)
            return real_open(path, flags, *a, **kw)

        with (
            patch.object(controller.os, "open", side_effect=replace),
            patch.object(controller, "run") as execute,
        ):
            with self.assertRaises(AssertionError):
                controller.keygen(
                    args, artifacts, work, digest(call), authenticated, tool_pin
                )
            execute.assert_not_called()

    def test_special_files_and_links_are_bounded_rejections(self):
        fifo = self.root / "fifo"
        os.mkfifo(fifo)
        with self.assertRaises(AssertionError):
            controller.retained(fifo)
        link = self.root / "link"
        link.symlink_to(self.root / "absent")
        with self.assertRaises(OSError):
            controller.retained(link)


if __name__ == "__main__":
    unittest.main()
