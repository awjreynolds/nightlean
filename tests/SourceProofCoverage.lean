import Noctium.Verification

open Noctium Noctium.Verification

namespace SourceProofCoverageFixture

def sourceContract : Contract := {
  name := "SourceProofCoverage"
  entrypoints := [
    {name := "first", circuit := {name := "emptyRelation"}},
    {name := "second", circuit := {name := "emptyRelation"}},
    {name := "ambiguous", circuit := {name := "emptyRelation"}},
    {name := "uncovered", circuit := {name := "emptyRelation"}}]
}

def sameNameContract : Contract := {
  name := "SourceProofCoverage"
  entrypoints := [{name := "different", circuit := {name := "differentRelation"}}]
}

def withoutSettlementEffects (state : LedgerState) : LedgerState :=
  {state with unshieldedInputs := [], unshieldedOutputs := [], unshieldedSpendClaims := []}

def specification : Specification := {
  initial := fun state => state = {}
  invariant := fun _ => True
  precondition := fun _ inputs _ => inputs = []
  enabled := fun _ _ _ => True
  postcondition := fun _ _ before outputs after =>
    outputs = [] ∧ after = withoutSettlementEffects before
}

def subjectFirst : Subject := {
  contract := sourceContract
  entrypoint := ⟨0, by decide⟩
  specification
}

def subjectSecond : Subject := {
  contract := sourceContract
  entrypoint := ⟨1, by decide⟩
  specification
}

def subjectAmbiguous : Subject := {
  contract := sourceContract
  entrypoint := ⟨2, by decide⟩
  specification
}

def subjectSameName : Subject := {
  contract := sameNameContract
  entrypoint := ⟨0, by decide⟩
  specification
}

theorem entryRunsFirst (context : EvalContext) (before : LedgerState) :
    subjectFirst.entry.run context [] before = .ok ([], withoutSettlementEffects before) := by
  rfl

theorem entryRunsSecond (context : EvalContext) (before : LedgerState) :
    subjectSecond.entry.run context [] before = .ok ([], withoutSettlementEffects before) := by
  rfl

theorem entryRunsAmbiguous (context : EvalContext) (before : LedgerState) :
    subjectAmbiguous.entry.run context [] before = .ok ([], withoutSettlementEffects before) := by
  rfl

theorem entryRunsSameName (context : EvalContext) (before : LedgerState) :
    subjectSameName.entry.run context [] before = .ok ([], withoutSettlementEffects before) := by
  rfl

theorem noOpCorrectness (subject : Subject)
    (specificationMatches : subject.specification = specification)
    (runs : ∀ context before,
      subject.entry.run context [] before = .ok ([], withoutSettlementEffects before)) :
    Correctness subject := by
  cases subject with
  | mk contract entrypoint actualSpecification =>
    cases specificationMatches
    constructor
    · intro _ _
      trivial
    · intro context inputs before outputs after _ hpre hrun
      change inputs = [] at hpre
      subst inputs
      rw [runs context before] at hrun
      cases hrun
      exact ⟨⟨rfl, rfl⟩, True.intro⟩
    · intro context inputs before _ hpre _
      change inputs = [] at hpre
      subst inputs
      exact ⟨[], withoutSettlementEffects before, runs context before⟩
    · exact ⟨
        {modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "unused"},
        [], {}, rfl, rfl, True.intro⟩

theorem noOpPrivacy (subject : Subject)
    (specificationMatches : subject.specification = specification) :
    PrivacyCorrect subject {scope := .allOutcomes} := by
  cases subject with
  | mk contract entrypoint actualSpecification =>
    cases specificationMatches
    intro left right hleft hright hpublic _ _
    have hleftInputs : left.inputs = [] := hleft.2
    have hrightInputs : right.inputs = [] := hright.2
    rcases hpublic with ⟨hcontext, hstate, _⟩
    change contract.entrypoints[entrypoint].run left.context left.inputs left.state =
      contract.entrypoints[entrypoint].run right.context right.inputs right.state
    rw [hleftInputs, hrightInputs, hcontext, hstate]

def policyFirst : AuditPolicy := {
  subject := subjectFirst
  privacy := {scope := .allOutcomes}
  functionalGuarantee := "The first no-op entrypoint succeeds and preserves the reviewed state invariant."
  privacyGuarantee := "Equal context and state produce equal no-op entrypoint outcomes."
}

def policyFirstAlias : AuditPolicy := policyFirst

def policySecondA : AuditPolicy := {
  subject := subjectSecond
  privacy := {scope := .allOutcomes}
  functionalGuarantee := "The second no-op entrypoint succeeds and preserves the reviewed state invariant."
  privacyGuarantee := "Equal context and state produce equal no-op entrypoint outcomes."
}

def policySecondB : AuditPolicy := {
  subject := subjectSecond
  privacy := {scope := .allOutcomes}
  functionalGuarantee := "A distinct full policy declaration cannot be paired with another policy's privacy proof."
  privacyGuarantee := "Equal context and state produce equal no-op entrypoint outcomes."
}

def policyAmbiguousA : AuditPolicy := {
  subject := subjectAmbiguous
  privacy := {scope := .allOutcomes}
  functionalGuarantee := "First functional policy for ambiguous coverage."
  privacyGuarantee := "Equal context and state produce equal no-op entrypoint outcomes."
}

def policyAmbiguousB : AuditPolicy := {
  subject := subjectAmbiguous
  privacy := {scope := .allOutcomes}
  functionalGuarantee := "Second functional policy for ambiguous coverage."
  privacyGuarantee := "Equal context and state produce equal no-op entrypoint outcomes."
}

def policySameName : AuditPolicy := {
  subject := subjectSameName
  privacy := {scope := .allOutcomes}
  functionalGuarantee := "The different same-name contract no-op succeeds."
  privacyGuarantee := "Equal context and state produce equal no-op entrypoint outcomes."
}

theorem functionalFirst : FunctionalObligation policyFirst :=
  noOpCorrectness subjectFirst rfl entryRunsFirst

theorem privacyFirst : PrivacyObligation policyFirst :=
  noOpPrivacy subjectFirst rfl

theorem functionalSecond : FunctionalObligation policySecondA :=
  noOpCorrectness subjectSecond rfl entryRunsSecond

theorem privacySecondB : PrivacyObligation policySecondB :=
  noOpPrivacy subjectSecond rfl

theorem functionalAmbiguous : FunctionalObligation policyAmbiguousA :=
  noOpCorrectness subjectAmbiguous rfl entryRunsAmbiguous

theorem functionalSameName : FunctionalObligation policySameName :=
  noOpCorrectness subjectSameName rfl entryRunsSameName

theorem privacySameName : PrivacyObligation policySameName :=
  noOpPrivacy subjectSameName rfl

#noctium_register_functional functionalFirst for policyFirst
#noctium_register_functional functionalFirst for policyFirst
#noctium_register_privacy privacyFirst for policyFirstAlias
#noctium_register_functional functionalSecond for policySecondA
#noctium_register_privacy privacySecondB for policySecondB
#noctium_register_functional functionalAmbiguous for policyAmbiguousA
#noctium_register_functional functionalAmbiguous for policyAmbiguousB
#noctium_register_functional functionalSameName for policySameName
#noctium_register_privacy privacySameName for policySameName

/-- "entrypoint":"first","index":0,"mismatchedPolicyPairs":[],"missingRoles":[],"policyPairing":"matched","roles":[{"duplicateRegistrationCount":1,"registrations":[{"policy":"SourceProofCoverageFixture.policyFirst","proof":"SourceProofCoverageFixture.functionalFirst"}],"role":"functional","status":"covered"},{"duplicateRegistrationCount":0,"registrations":[{"policy":"SourceProofCoverageFixture.policyFirstAlias","proof":"SourceProofCoverageFixture.privacyFirst"}],"role":"privacy","status":"covered"}],"status":"covered" -/
#guard_msgs (substring := true) in
#noctium_source_proof_coverage sourceContract

/-- "entrypoint":"second","index":1,"mismatchedPolicyPairs":[{"functionalPolicy":"SourceProofCoverageFixture.policySecondA","privacyPolicy":"SourceProofCoverageFixture.policySecondB"}],"missingRoles":[],"policyPairing":"mismatch","roles":[{"duplicateRegistrationCount":0,"registrations":[{"policy":"SourceProofCoverageFixture.policySecondA","proof":"SourceProofCoverageFixture.functionalSecond"}],"role":"functional","status":"covered"},{"duplicateRegistrationCount":0,"registrations":[{"policy":"SourceProofCoverageFixture.policySecondB","proof":"SourceProofCoverageFixture.privacySecondB"}],"role":"privacy","status":"covered"}],"status":"policy-mismatch" -/
#guard_msgs (substring := true) in
#noctium_source_proof_coverage sourceContract

/-- "contract":"SourceProofCoverageFixture.sameNameContract","deployedVerification":false,"entrypoints":[{"ambiguousRoles":[],"compatiblePolicyPairs":[{"functionalPolicy":"SourceProofCoverageFixture.policySameName","privacyPolicy":"SourceProofCoverageFixture.policySameName"}],"entrypoint":"different","index":0 -/
#guard_msgs (substring := true) in
#noctium_source_proof_coverage sameNameContract

end SourceProofCoverageFixture
