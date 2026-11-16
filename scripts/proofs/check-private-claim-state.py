#!/usr/bin/env python3
"""Check PrivateClaim native VM preservation and fresh plan/call JSON certificates."""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import runpy
import tempfile

ROOT = Path(__file__).resolve().parents[2]
HELPERS = runpy.run_path(str(ROOT / "scripts/proofs/check-private-claim-lowering.py"))
run = HELPERS["run"]
quote_tree = HELPERS["quote_tree"]
strict_json_bytes = HELPERS["strict_json_bytes"]
exported_axioms = HELPERS["exported_axioms"]
NS = "Nightlean.PrivateClaimNativeState"
PROOF_NAMES = ["actual_schema_order", "actual_effect_order", "groups_encoding", "execute_plan",
               "native_execution_sound", "source_native_preservation", "eligible_native_complete",
               "eligible_admitted_complete", "native_replay_rejected", "entries_frame", "native_frame",
               "invariant_preserved", "public_transcript_preserved", "decoded_execution_sound",
               "decoded_execution_complete"]


def certificate_source(plan: object, call: object, namespace: str) -> str:
    return f'''import proofs.PrivateClaimNativeState
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace {namespace}
open Nightlean Nightlean.PrivateClaimProofs Nightlean.PrivateClaimLowering
open Nightlean.Verification.NativeRelation Nightlean.Verification.NativeState
open Nightlean.PrivateClaimNativeState
def planJson : Lean.Json := {quote_tree(plan)}
def callJson : Lean.Json := {quote_tree(call)}
theorem planDecoded : Nightlean.Verification.NativeStateJson.decode planJson =
    .ok symbolicPlan := by
  have check : (Nightlean.Verification.NativeStateJson.decode planJson).toOption =
      some symbolicPlan := by decide +kernel
  cases h : Nightlean.Verification.NativeStateJson.decode planJson with
  | error message => rw [h] at check; contradiction
  | ok value => rw [h] at check; exact congrArg Except.ok (Option.some.inj check)
theorem callDecoded : Nightlean.Verification.NativeRelationJson.decode callJson =
    .ok callProgram := by
  have check : (Nightlean.Verification.NativeRelationJson.decode callJson).toOption =
      some callProgram := by decide +kernel
  cases h : Nightlean.Verification.NativeRelationJson.decode callJson with
  | error message => rw [h] at check; contradiction
  | ok value => rw [h] at check; exact congrArg Except.ok (Option.some.inj check)
theorem sound (ctx : EvalContext) (hash : Hash) (agreement : HashAgreement ctx hash)
    (input : Inputs) (sr sc presence : Scalar) (w : Assignment) (root campaign : Scalar)
    (entries : List (Scalar × _root_.Bool)) (publicGroups : List (List Scalar)) (after : Machine)
    (execution : DecodedExecution planJson callJson hash (callStreams input sr sc presence)
      w root campaign entries publicGroups after) :
    claimEntry.run ctx (inputEnvironment input.source) (state root.val campaign.val (sourceValues entries)) =
      .ok ([("nullifier", .native input.nullifier.val)],
        state input.root.val input.campaign.val (sourceValues (mark input.nullifier entries))) ∧
    after.stack = (initial input.root input.campaign (encodedEntries (mark input.nullifier entries))).stack :=
  {NS}.decoded_execution_sound planJson callJson planDecoded callDecoded
    ctx hash agreement input sr sc presence w root campaign entries publicGroups after execution
theorem complete (ctx : EvalContext) (hash : Hash) (agreement : HashAgreement ctx hash)
    (sourceInput : InputValues) (canonical : CanonicalInputs ctx sourceInput) (leaf node : Nat)
    (hashes : HashTrace ctx sourceInput leaf node) (entries : List (Scalar × _root_.Bool))
    (unused : (typedEntries (sourceValues entries)).lookup (.native sourceInput.nullifier) = none) :
    let input := Inputs.ofSource ctx sourceInput canonical agreement.modulus
    ∃ w after, DecodedExecution planJson callJson hash (callStreams input input.root input.campaign zero)
      w input.root input.campaign entries (groups (operations w)) after :=
  {NS}.decoded_execution_complete planJson callJson planDecoded callDecoded
    ctx hash agreement sourceInput canonical leaf node hashes entries unused
#print axioms planDecoded
#print axioms callDecoded
#print axioms sound
#print axioms complete
end {namespace}
'''


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=ROOT / ".nightlean/audits/private-claim-state")
    parser.add_argument("--native-checker", type=Path)
    args = parser.parse_args()
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    run(["lake", "build", "nightlean", "Nightlean", "Nightlean.Frontend",
         "Nightlean.Verification.NativeRelationJson", "Nightlean.Verification.NativeStateJson",
         "Nightlean.Verification"])
    run(["lake", "env", "lean", "tests/NativeState.lean"])
    with tempfile.TemporaryDirectory(prefix="nightlean-claim-state-") as directory:
        scratch = Path(directory)
        imports = scratch / "imports"
        for child in ["examples", "proofs"]:
            (imports / child).mkdir(parents=True)
        environment = dict(os.environ, LEAN_PATH=str(imports))
        for source in ["examples/PrivateClaim.lean", "proofs/PrivateClaim.lean", "proofs/PrivateClaimVerification.lean",
                       "proofs/PrivateClaimLowering.lean", "proofs/PrivateClaimNativeState.lean"]:
            built = run(["lake", "env", "lean", "-D", "Elab.async=false", "-o",
                         str(imports / Path(source).with_suffix(".olean")), source], environment)
            if source.endswith("PrivateClaimNativeState.lean"):
                (output / "direct-axioms.txt").write_text(built.stdout)
        emitted = output / "emitted"
        run([str(ROOT / ".lake/build/bin/nightlean"), "compile", "examples/PrivateClaim.lean",
             "--target", "profiles/midnight-ledger-9-zkir-3.2.1-target.json", "--output", str(emitted)])
        plan_bytes = (emitted / "PrivateClaim.claim.impact.json").read_bytes()
        call_bytes = (emitted / "PrivateClaim.claim.zkir").read_bytes()
        plan, call = strict_json_bytes(plan_bytes), strict_json_bytes(call_bytes)
        assert len(plan["operations"]) == 21 and len(call["instructions"]) == 55
        source_dir = scratch / "source"
        (source_dir / "proofs").mkdir(parents=True)

        def check_certificate(p: object, c: object, namespace: str, negative: str | None = None) -> str:
            contents = certificate_source(p, c, namespace)
            filename = namespace + ".lean"
            source = source_dir / "proofs" / filename
            source.write_text(contents)
            (output / filename).write_text(contents)
            result = run(["lake", "env", "lean", "-D", "Elab.async=false", "--root", str(source_dir),
                          "-o", str(imports / "proofs" / Path(filename).with_suffix(".olean")), str(source)],
                         environment, allow_failure=negative is not None)
            if negative:
                assert result.returncode, namespace
                marker = "some " + ("symbolicPlan" if negative == "plan" else "callProgram") + " := by decide +kernel"
                proof_line = next(i for i, line in enumerate(contents.splitlines(), 1) if marker in line)
                assert f"{filename}:{proof_line}:" in result.stdout, result.stdout + result.stderr
                assert "decide" in result.stdout and "error:" in result.stdout, result.stdout
                assert "unknown module" not in result.stdout and "unknown identifier" not in result.stdout
                assert "theorems cannot use" not in result.stdout
                (output / (filename + ".rejection.txt")).write_text(result.stdout + result.stderr)
            return result.stdout

        positive = check_certificate(plan, call, "PrivateClaimStateCertificate")
        (output / "certificate-axioms.txt").write_text(positive)
        mutants = []
        for name, edit in [
            ("WrongSlot", lambda p: p["operations"][7].update(slot=1)),
            ("WrongPath", lambda p: p["operations"][17].update(pushPath=False)),
            ("WrongKey", lambda p: p["operations"][18]["expression"].update(name="campaign")),
            ("WrongValue", lambda p: p["operations"][19]["expression"]["yes"].update(value="0")),
            ("WrongRead", lambda p: p["operations"][8]["expression"].update(name="storedCampaign")),
            ("WrongAlignment", lambda p: p["operations"][16].update(alignment="field")),
            ("WrongStorage", lambda p: p["operations"][19].update(storage=False)),
            ("WrongReadOrder", lambda p: p["reads"].reverse()),
        ]:
            changed = copy.deepcopy(plan)
            edit(changed)
            check_certificate(changed, call, name + "StateCertificate", negative="plan")
            mutants.append(name)
        changed_call = copy.deepcopy(call)
        first_impact = next(i for i, op in enumerate(changed_call["instructions"]) if op["op"] == "impact")
        changed_call["instructions"][first_impact], changed_call["instructions"][first_impact + 1] = (
            changed_call["instructions"][first_impact + 1], changed_call["instructions"][first_impact])
        check_certificate(plan, changed_call, "WrongOpcodeGroupStateCertificate", negative="call")
        mutants.append("WrongOpcodeGroup")
        inactive = copy.deepcopy(call)
        next(op for op in inactive["instructions"] if op["op"] == "impact")["guard"] = "0x00"
        check_certificate(plan, inactive, "InactiveGroupStateCertificate", negative="call")
        mutants.append("InactiveGroup")
        roots = [f"{NS}.{name}" for name in PROOF_NAMES] + [
            "PrivateClaimStateCertificate." + name for name in ["planDecoded", "callDecoded", "sound", "complete"]]
        export = run(["lake", "env", "leanexport", "proofs.PrivateClaimStateCertificate", "--", *roots], environment)
        exported = output / "proof-closure.ndjson"
        exported.write_text(export.stdout)
        axioms = exported_axioms(exported)
        replay = run(["lake", "env", "leanchecker", "--from-export", str(exported)])
        (output / "kernel-replay.txt").write_text(replay.stdout + replay.stderr)
        if args.native_checker:
            native = run(["node", "tests/private-claim-state-checker.mjs", str(args.native_checker.resolve()),
                          str(emitted / "PrivateClaim.claim.impact.json"), str(emitted / "PrivateClaim.claim.zkir")])
            (output / "native-checker.json").write_text(native.stdout)
        summary = {"status": "passed", "scope": "actual claim native state/public transcript preservation and decoded plan/call JSON trees",
                   "sourceSha256": hashlib.sha256((ROOT / "examples/PrivateClaim.lean").read_bytes()).hexdigest(),
                   "planSha256": hashlib.sha256(plan_bytes).hexdigest(), "callSha256": hashlib.sha256(call_bytes).hexdigest(),
                   "proofExportSha256": hashlib.sha256(exported.read_bytes()).hexdigest(), "axioms": axioms,
                   "kernelReplayed": True, "mutantsRejected": mutants,
                   "nativeSamplesChecked": bool(args.native_checker), "arbitrarySatisfyingWitnessAndTraceSoundness": True,
                   "eligibleSourceCompleteness": True, "nativeStatePreservationProved": True,
                   "resourceAdmission": "21 operations and map length + 1; actual ledger cost/size agreement remains explicit",
                   "byteParserCorrespondenceProved": False, "compilerBuildAuthenticated": False,
                   "compiledContractVerified": False, "retainedArtifacts": str(output)}
        (output / "summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
        print(json.dumps(summary, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
