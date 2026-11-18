import Noctium.Semantics
import Lean

namespace Noctium.Verification

/-- These predicates are the reviewed specification, not inferred business intent. -/
structure Specification where
  initial : LedgerState → Prop
  invariant : LedgerState → Prop
  precondition : EvalContext → EvalEnv → LedgerState → Prop
  enabled : EvalContext → EvalEnv → LedgerState → Prop
  postcondition : EvalContext → EvalEnv → LedgerState → EvalEnv → LedgerState → Prop

/-- A finite index binds the obligation to an actual source contract entrypoint. -/
structure Subject where
  contract : Contract
  entrypoint : Fin contract.entrypoints.length
  specification : Specification

def Subject.entry (subject : Subject) : Entrypoint :=
  subject.contract.entrypoints[subject.entrypoint]

structure Correctness (subject : Subject) : Prop where
  initialization : ∀ before, subject.specification.initial before →
    subject.specification.invariant before
  preservation : ∀ ctx inputs before outputs after,
    subject.specification.invariant before →
    subject.specification.precondition ctx inputs before →
    subject.entry.run ctx inputs before = .ok (outputs, after) →
    subject.specification.postcondition ctx inputs before outputs after ∧
      subject.specification.invariant after
  progress : ∀ ctx inputs before,
    subject.specification.invariant before →
    subject.specification.precondition ctx inputs before →
    subject.specification.enabled ctx inputs before →
    ∃ outputs after, subject.entry.run ctx inputs before = .ok (outputs, after)
  nonvacuity : ∃ ctx inputs before,
    subject.specification.initial before ∧
    subject.specification.precondition ctx inputs before ∧
    subject.specification.enabled ctx inputs before

structure Invocation where
  context : EvalContext
  inputs : EvalEnv
  state : LedgerState

abbrev Outcome := Except String (EvalEnv × LedgerState)

def Subject.execute (subject : Subject) (invocation : Invocation) : Outcome :=
  subject.entry.run invocation.context invocation.inputs invocation.state

inductive ObservationScope where
  | successfulOnly
  | allOutcomes
  deriving Repr, BEq, DecidableEq

def ObservationScope.covers (scope : ObservationScope) (left right : Outcome) : Prop :=
  match scope with
  | .allOutcomes => True
  | .successfulOnly =>
    (∃ outputs state, left = .ok (outputs, state)) ∧
    (∃ outputs state, right = .ok (outputs, state))

def Subject.publicInputs (subject : Subject) (inputs : EvalEnv) : List (String × Option Value) :=
  (subject.entry.circuit.inputs.filter (·.visibility == .«public»)).map fun input =>
    (input.name, inputs.lookup input.name)

def Subject.publicEquivalent (subject : Subject) (left right : Invocation) : Prop :=
  left.context = right.context ∧ left.state = right.state ∧
    subject.publicInputs left.inputs = subject.publicInputs right.inputs

def Subject.admissible (subject : Subject) (invocation : Invocation) : Prop :=
  subject.specification.invariant invocation.state ∧
    subject.specification.precondition invocation.context invocation.inputs invocation.state

/-- A declared function is an explicit release assumption, not a source-authorization
certificate. Its equality cannot be an always-false hand-written relation. -/
inductive ReleasePolicy where
  | none
  | declared (release : Invocation → List Value)

def ReleasePolicy.agrees (policy : ReleasePolicy) (left right : Invocation) : Prop :=
  match policy with
  | .none => True
  | .declared release => release left = release right

theorem ReleasePolicy.agrees_refl (policy : ReleasePolicy) (invocation : Invocation) :
    policy.agrees invocation invocation := by cases policy <;> simp [agrees]

theorem Subject.publicEquivalent_refl (subject : Subject) (invocation : Invocation) :
    subject.publicEquivalent invocation invocation := ⟨rfl, rfl, rfl⟩

structure PrivacySpec where
  releases : ReleasePolicy := .none
  scope : ObservationScope

def PrivacyCorrect (subject : Subject) (privacy : PrivacySpec) : Prop :=
  ∀ left right,
    subject.admissible left → subject.admissible right →
    subject.publicEquivalent left right →
    privacy.releases.agrees left right →
    privacy.scope.covers (subject.execute left) (subject.execute right) →
    subject.execute left = subject.execute right

/-- The external audit authority pins this definition and its dependency closure. -/
structure AuditPolicy where
  subject : Subject
  privacy : PrivacySpec
  functionalGuarantee : String
  privacyGuarantee : String

def FunctionalObligation (policy : AuditPolicy) : Prop := Correctness policy.subject
def PrivacyObligation (policy : AuditPolicy) : Prop := PrivacyCorrect policy.subject policy.privacy

namespace Audit
open Lean

inductive Role where
  | functional
  | privacy
  deriving Repr, BEq

def Role.obligation : Role → Name
  | .functional => ``FunctionalObligation
  | .privacy => ``PrivacyObligation

structure Registration where
  policy : Name
  proof : Name
  role : Role
  axioms : Array Name
  deriving Repr

def approvedAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- Walk actual checked bodies, including imports. Do not use imported axiom metadata. -/
partial def axiomsIn (environment : Environment) (root : Name) : Except String (Array Name) :=
  visit [root] {} #[]
where
  visit : List Name → NameSet → Array Name → Except String (Array Name)
    | [], _, found => .ok (found.qsort Name.lt)
    | name :: rest, seen, found => do
      if seen.contains name then return ← visit rest seen found
      let some info := environment.toKernelEnv.find? name
        | throw s!"unknown_dependency: {name}"
      if info.isUnsafe || info.isPartial then throw s!"unsafe_dependency: {name}"
      let seen := seen.insert name
      let dependencies := info.type.getUsedConstants.toList ++
        (info.value? (allowOpaque := true)).toList.flatMap (·.getUsedConstants.toList)
      match info with
      | .axiomInfo _ =>
        unless approvedAxioms.contains name do throw s!"forbidden_axiom: {name}"
        visit (dependencies ++ rest) seen (found.push name)
      | .inductInfo value => visit (value.ctors ++ dependencies ++ rest) seen found
      | _ => visit (dependencies ++ rest) seen found

/-- This checks proof type and axioms in a checked environment. The caller must first
bind model declarations to the independently trusted export and replay candidate terms. -/
def check (environment : Environment) (policy proof : Name) (role : Role) : Except String Registration := do
  let some policyInfo := environment.toKernelEnv.find? policy | throw "unknown_policy"
  unless policyInfo.levelParams.isEmpty do throw "polymorphic_policy"
  match Kernel.isDefEq environment {} policyInfo.type (mkConst ``AuditPolicy) with
  | .ok true => pure ()
  | _ => throw "wrong_policy_type"
  let some proofInfo := environment.toKernelEnv.find? proof | throw "unknown_proof"
  unless proofInfo.levelParams.isEmpty do throw "polymorphic_proof"
  let expected := mkApp (mkConst role.obligation) (mkConst policy)
  match Kernel.isDefEq environment {} proofInfo.type expected with
  | .ok true => pure ()
  | _ => throw "wrong_obligation"
  let axioms ← axiomsIn environment proof
  return {policy, proof, role, axioms}

end Audit

open Lean Elab Command

initialize proofRegistry : SimplePersistentEnvExtension Audit.Registration (Array Audit.Registration) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }

private def register (proof policy : TSyntax `ident) (role : Audit.Role) : CommandElabM Unit := do
  let proofName ← liftCoreM <| resolveGlobalConstNoOverload proof
  let policyName ← liftCoreM <| resolveGlobalConstNoOverload policy
  match Audit.check (← getEnv) policyName proofName role with
  | .error message => throwError "{message}"
  | .ok registration =>
    modifyEnv fun environment => proofRegistry.addEntry environment registration
    logInfo m!"provisional source {repr role} proof registered: {proofName}; external model pin and export replay required"

elab "#noctium_register_functional " proof:ident " for " policy:ident : command =>
  register proof policy .functional

elab "#noctium_register_privacy " proof:ident " for " policy:ident : command =>
  register proof policy .privacy

end Noctium.Verification
