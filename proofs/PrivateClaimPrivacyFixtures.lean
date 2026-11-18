import proofs.PrivateClaimNativePrivacy
import tests.Verification

namespace Noctium.PrivateClaimPrivacyFixtures
open Verification Verification.NativeRelation Verification.NativeState Verification.NativePrivacy

/-- Reuse DF-00's explicitly authorized source release, adding its exact typed
release function rather than granting no-release confidentiality. -/
def authorizedReleasePolicy : AuditPolicy := {
  VerificationFixture.releasingPolicy with
  privacy := {scope := .allOutcomes, releases := .declared (fun invocation =>
    [(invocation.inputs.lookup "secret").getD (.bool Bool.false)])}
}

theorem authorized_release_privacy : PrivacyObligation authorizedReleasePolicy := by
  intro left right leftAdmissible rightAdmissible equivalent released _covered
  rcases left with ⟨ctx, leftInputs, before⟩
  rcases right with ⟨rightCtx, rightInputs, rightBefore⟩
  obtain ⟨_, leftBit, leftEq⟩ := leftAdmissible
  obtain ⟨_, rightBit, rightEq⟩ := rightAdmissible
  obtain ⟨contextEq, stateEq, _⟩ := equivalent
  dsimp only at contextEq stateEq leftEq rightEq
  subst rightCtx rightBefore leftInputs rightInputs
  change [Value.bool leftBit] = [Value.bool rightBit] at released
  have bitEq : leftBit = rightBit := Value.bool.inj (List.cons.inj released).1
  subst rightBit
  rfl

theorem release_is_not_no_release_privacy : ¬ PrivacyObligation VerificationFixture.releasingPolicy :=
  VerificationFixture.releasingNotPrivate

theorem successful_scope_has_failure_counterexample :
    PrivacyObligation VerificationFixture.failurePolicy ∧
      ¬ PrivacyObligation VerificationFixture.failureAllOutcomesPolicy :=
  ⟨VerificationFixture.failureSuccessfulPrivacy, VerificationFixture.failureNotAllOutcomesPrivate⟩

private def rejects : Except ε α → _root_.Bool
  | .error _ => Bool.true
  | .ok _ => Bool.false
private def secret : Input := {name := "secret", ty := .native, visibility := .«private»}
private def outputCircuit (value : Expr .native) : Circuit := {
  name := "explicitLeakFixture", inputs := [secret], outputs := [{name := "visible", ty := .native, value}]}

theorem direct_leak_rejected : rejects (Disclosure.circuit (outputCircuit (.ref "secret"))) = Bool.true := by decide +kernel
theorem hash_leak_rejected : rejects (Disclosure.circuit
    (outputCircuit (.poseidon2 1 (.ref "secret") (.native 0)))) = Bool.true := by decide +kernel

private def queryEntry : Entrypoint := {
  name := "queryLeakFixture", circuit := {name := "query", inputs := [secret]},
  effects := [.requireAbsent "spent" .native (.ref "secret")]}

theorem query_leak_rejected : rejects (Disclosure.entrypoint queryEntry) = Bool.true := by decide +kernel

private def privateControl : Disclosure.Origins := [{name := "flag", kind := .parameter, span := {}}]
private def constantWrite : Entrypoint := {
  name := "guardInterfaceFixture", circuit := {name := "constant"},
  effects := [.writeCell "value" .native (.native 1)]}

/-- The current control-origin interface rejects even a constant public write.
This is not a claim that structured source guards/events have been implemented. -/
theorem constant_under_private_control_rejected :
    rejects (Disclosure.entrypoint constantWrite privateControl) = Bool.true := by decide +kernel

/-- Concrete observation differences explain the gate's finite negative cases. -/
theorem direct_payloads_differ : [field zero] ≠ [field one] := by decide +kernel
theorem activity_masks_differ : [Bool.false] ≠ [Bool.true] := by decide +kernel
theorem private_query_keys_differ :
    queries [.push (field zero) Bool.false, .member] ≠ queries [.push (field one) Bool.false, .member] := by decide +kernel

/-- Authorized equal hash releases do not imply equal private preimages. -/
theorem equal_hash_release_does_not_identify_secret :
    zero ≠ one ∧ PrivateClaimLowering.zeroHash [one,zero] = PrivateClaimLowering.zeroHash [one,one] :=
  ⟨zero_ne_one, rfl⟩

#print axioms authorized_release_privacy
#print axioms successful_scope_has_failure_counterexample
#print axioms constant_under_private_control_rejected
end Noctium.PrivateClaimPrivacyFixtures
