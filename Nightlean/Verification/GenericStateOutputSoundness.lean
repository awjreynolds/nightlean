import Nightlean.Verification.GenericStateCircuitParts
import Nightlean.Verification.GenericStateAliases
import Nightlean.Verification.ScalarCircuit
import Nightlean.Verification.GenericStateAdmission

namespace Nightlean.Verification.GenericStateOutputSoundness
open Backend.Native NativeRelation ScalarNormalization GenericStateCircuitParts

private theorem bind_ok {α β : Type} {first : Except ε α} {next : α → Except ε β}
    {result : β} : (first >>= next) = .ok result ↔
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

/-- One accepted production output-alias step evaluates the original source
expression. Its term denotes the exact typed result, and adding the fresh
alias leaves the original input environment well typed. -/
theorem appendOutput_sound (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (types : TypeEnv) (values : EvalEnv)
    (output : Output) (frame next : OutputFrame)
    (environment : TypedEnvironment hash inputs frame.1 values types)
    (valid : output.value.validate {poseidon2 := true} types = .ok ())
    (unused : values.lookup output.name = none)
    (accepted : appendOutput output frame = .ok next)
    (bounds : ∀ requirement ∈ next.2.1,
      (interpret hash inputs requirement.1).val ≤ requirement.2)
    (assertions : ∀ term ∈ next.2.2,
      interpret hash inputs term = one) :
    ∃ normalized value,
      normalize frame.1 output.value = .ok normalized ∧
      output.value.eval ctx values = .ok value ∧
      Canonical output.ty value ∧
      interpret hash inputs normalized.term = scalar (number output.ty value) ∧
      next.1 = (output.name, normalized.term) :: frame.1 ∧
      TypedEnvironment hash inputs next.1 values types := by
  unfold appendOutput at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨normalized, normalizedAccepted, result⟩
  cases result
  have normal : normalize frame.1 output.value = .ok normalized := by
    unfold normalizeOutput at normalizedAccepted
    cases checked : normalize frame.1 output.value with
    | error message =>
      rw [checked] at normalizedAccepted
      change (Except.error {span := output.span, message := message} :
        Except Diagnostic Normalized) = .ok normalized at normalizedAccepted
      cases normalizedAccepted
    | ok found =>
      simp [checked] at normalizedAccepted
      cases normalizedAccepted
      rfl
  have requirements : Requirements hash inputs normalized := by
    constructor
    · intro requirement member
      apply bounds requirement
      simp [member]
    · intro term member
      apply assertions term
      simp [member]
  obtain ⟨value, evaluated, canonical, _, meaning⟩ :=
    normalize_sound ctx hash implementation inputs types frame.1 values
      environment output.value normalized valid normal requirements
  refine ⟨normalized, value, normal, evaluated, canonical, meaning, rfl, ?_⟩
  exact GenericStateAliases.typedEnvironment_cons_unused hash inputs frame.1
    values types output.name normalized.term environment unused

/-- A produced output becomes a typed internal binding for later state
effects. The source expression still reads the original circuit inputs. -/
theorem appendOutput_binding (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (types : TypeEnv) (values : EvalEnv)
    (output : Output) (frame next : OutputFrame)
    (environment : TypedEnvironment hash inputs frame.1 values types)
    (valid : output.value.validate {poseidon2 := true} types = .ok ())
    (unused : values.lookup output.name = none)
    (accepted : appendOutput output frame = .ok next)
    (bounds : ∀ requirement ∈ next.2.1,
      (interpret hash inputs requirement.1).val ≤ requirement.2)
    (assertions : ∀ term ∈ next.2.2,
      interpret hash inputs term = one) :
    ∃ value, output.value.eval ctx values = .ok value ∧
      TypedEnvironment hash inputs next.1
        ((output.name, Value.pack output.ty value) :: values)
        ((output.name, output.ty) :: types) := by
  obtain ⟨normalized, value, _, evaluated, canonical, meaning,
    aliases, _⟩ :=
    appendOutput_sound ctx hash implementation inputs types values
      output frame next environment valid unused accepted bounds assertions
  refine ⟨value, evaluated, ?_⟩
  rw [aliases]
  exact TypedEnvironment.cons hash inputs frame.1 values types environment
    output.name output.ty value normalized.term canonical meaning

theorem outputFold_monotone (frame final : OutputFrame)
    (outputs : List Output) (accepted : outputFold frame outputs = .ok final) :
    (∀ requirement ∈ frame.2.1, requirement ∈ final.2.1) ∧
    (∀ term ∈ frame.2.2, term ∈ final.2.2) := by
  induction outputs generalizing frame with
  | nil =>
    simp [outputFold] at accepted
    cases accepted
    exact ⟨fun _ membership => membership, fun _ membership => membership⟩
  | cons output rest ih =>
    rw [outputFold_cons] at accepted
    change (appendOutput output frame >>= fun next => outputFold next rest) =
      .ok final at accepted
    simp only [bind_ok] at accepted
    rcases accepted with ⟨middle, first, later⟩
    have tail := ih middle later
    unfold appendOutput at first
    simp only [bind_ok] at first
    rcases first with ⟨normalized, _, result⟩
    cases result
    constructor
    · intro requirement member
      apply tail.1 requirement
      exact List.mem_append_left _ member
    · intro term member
      apply tail.2 term
      exact List.mem_append_left _ member

/-- The real output alias fold evaluates every source output in order under
the original circuit input environment. The normalizer may prepend fresh
aliases, but those aliases cannot change any existing input value. -/
theorem outputFold_sound (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (types : TypeEnv) (values : EvalEnv)
    (outputs : List Output) (frame final : OutputFrame)
    (environment : TypedEnvironment hash inputs frame.1 values types)
    (valid : ∀ output ∈ outputs,
      output.value.validate {poseidon2 := true} types = .ok ())
    (unused : ∀ output ∈ outputs, values.lookup output.name = none)
    (accepted : outputFold frame outputs = .ok final)
    (bounds : ∀ requirement ∈ final.2.1,
      (interpret hash inputs requirement.1).val ≤ requirement.2)
    (assertions : ∀ term ∈ final.2.2,
      interpret hash inputs term = one) :
    ∃ result, outputs.mapM (evalOutput ctx values) = .ok result ∧
      result.map Prod.fst = outputs.map (·.name) ∧
      TypedEnvironment hash inputs final.1 values types := by
  induction outputs generalizing frame with
  | nil =>
    simp [outputFold] at accepted
    cases accepted
    exact ⟨[], rfl, rfl, environment⟩
  | cons output rest ih =>
    rw [outputFold_cons] at accepted
    change (appendOutput output frame >>= fun next => outputFold next rest) =
      .ok final at accepted
    simp only [bind_ok] at accepted
    rcases accepted with ⟨middle, first, later⟩
    have monotone := outputFold_monotone middle final rest later
    obtain ⟨normalized, value, normal, evaluated, canonical, meaning,
      aliases, nextEnvironment⟩ :=
      appendOutput_sound ctx hash implementation inputs types values output frame middle
        environment (valid output (by simp)) (unused output (by simp)) first
        (fun requirement member => bounds requirement (monotone.1 requirement member))
        (fun term member => assertions term (monotone.2 term member))
    have restValid : ∀ item ∈ rest,
        item.value.validate {poseidon2 := true} types = .ok () := by
      intro item member
      exact valid item (by simp [member])
    have restUnused : ∀ item ∈ rest, values.lookup item.name = none := by
      intro item member
      exact unused item (by simp [member])
    obtain ⟨tail, tailEval, tailNames, finalEnvironment⟩ :=
      ih middle nextEnvironment restValid restUnused later
    refine ⟨(output.name, Value.pack output.ty value) :: tail, ?_, ?_,
      finalEnvironment⟩
    · simp [evalOutput, evaluated, tailEval,
        Except.bind, Except.map, Functor.map] <;> rfl
    · simp [tailNames]

/-- Accepted independent ledger-call output terms evaluate to the original
source circuit's outputs under admitted inputs. Bounds and assertions come
from the actual expected constructor and satisfying native assignment. -/
theorem expected_outputs_sound (state : List StateDecl) (entry : Entrypoint)
    (expected : Expected) (accepted : expectedEntrypoint state entry = .ok expected)
    (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (values : EvalEnv)
    (admitted : CanonicalInputs entry.circuit values inputs)
    (bounds : ∀ requirement ∈ expected.bounds,
      (interpret hash inputs requirement.1).val ≤ requirement.2)
    (assertions : ∀ term ∈ expected.assertions,
      interpret hash inputs term = one) :
    ∃ result, runConstraints ctx values entry.circuit.constraints = .ok () ∧
      entry.circuit.outputs.mapM (evalOutput ctx values) = .ok result ∧
      result.map Prod.fst = entry.circuit.outputs.map (·.name) := by
  obtain ⟨plan, outputFrame, conditions, guards, operationFrame,
    lowered, outputAccepted, conditionAccepted, guardAccepted, operationAccepted,
    inputShape, groupsShape, returnShape, modeShape, assertionShape, boundShape⟩ :=
    GenericStateCircuitParts.expectedEntrypoint_parts state entry expected accepted
  have circuitValid := GenericStateAdmission.lower_circuit_validated
    state entry plan lowered
  have valid := (circuit_validation_parts entry.circuit circuitValid).2
  have unused := GenericStateAdmission.lower_output_names_unused
    state entry plan values inputs admitted lowered
  have initialEnvironment := GenericStateAliases.initialTypedEnvironment
    hash inputs entry plan values admitted
  obtain ⟨pieces, collected, _, operationBounds, _⟩ :=
    GenericStateAdmission.expected_operation_groups entry.span outputFrame.1
      plan.operations outputFrame.2.1 operationFrame.1 operationFrame.2.1
      operationFrame.2.2 operationAccepted
  have outputBounds : ∀ requirement ∈ outputFrame.2.1,
      (interpret hash inputs requirement.1).val ≤ requirement.2 := by
    intro requirement member
    apply bounds requirement
    rw [boundShape, operationBounds]
    exact List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ member))
  have outputAssertions : ∀ term ∈ outputFrame.2.2,
      interpret hash inputs term = one := by
    intro term member
    apply assertions term
    rw [assertionShape]
    simp [member]
  obtain ⟨result, outputEval, names, finalEnvironment⟩ :=
    outputFold_sound ctx hash implementation inputs
      (entry.circuit.inputs.map (fun input => (input.name, input.ty)))
      values entry.circuit.outputs
      (GenericStateCircuitParts.initialAliases entry plan, [], []) outputFrame
      initialEnvironment valid unused outputAccepted outputBounds outputAssertions
  have conditionBounds : ∀ requirement ∈ conditions.flatMap (·.bounds),
      (interpret hash inputs requirement.1).val ≤ requirement.2 := by
    intro requirement member
    apply bounds requirement
    rw [boundShape]
    exact List.mem_append_left _ (List.mem_append_right _ member)
  have conditionAssertions : ∀ term ∈
      conditions.flatMap (fun item => item.assertions ++ [item.term]),
      interpret hash inputs term = one := by
    intro term member
    apply assertions term
    rw [assertionShape]
    exact List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ member))
  have constraints := constraints_sound ctx hash implementation inputs
    (entry.circuit.inputs.map (fun input => (input.name, input.ty)))
    outputFrame.1 values finalEnvironment entry.circuit.span
    entry.circuit.constraints conditions
    (circuit_validation_parts entry.circuit circuitValid).1 conditionAccepted
    conditionBounds conditionAssertions
  exact ⟨result, constraints, outputEval, names⟩

/-- The independent ledger-call statement's circuit bounds and assertions
force the original source circuit to run successfully. Its output bindings
remain internal inputs to the ordered state effects. -/
theorem expected_circuit_run_sound (state : List StateDecl) (entry : Entrypoint)
    (expected : Expected) (accepted : expectedEntrypoint state entry = .ok expected)
    (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (values : EvalEnv)
    (admitted : CanonicalInputs entry.circuit values inputs)
    (bounds : ∀ requirement ∈ expected.bounds,
      (interpret hash inputs requirement.1).val ≤ requirement.2)
    (assertions : ∀ term ∈ expected.assertions,
      interpret hash inputs term = one) :
    ∃ result, entry.circuit.run ctx values = .ok result ∧
      result.map Prod.fst = entry.circuit.outputs.map (·.name) := by
  obtain ⟨plan, _, _, _, _, lowered, _, _, _, _, _, _, _, _, _, _⟩ :=
    GenericStateCircuitParts.expectedEntrypoint_parts state entry expected accepted
  obtain ⟨result, constraints, outputs, names⟩ :=
    expected_outputs_sound state entry expected accepted ctx hash implementation
      inputs values admitted bounds assertions
  have validated := GenericStateAdmission.lower_circuit_validated
    state entry plan lowered
  exact ⟨result,
    circuit_run_preflight ctx implementation.modulus entry.circuit values result
      inputs admitted validated constraints outputs, names⟩

end Nightlean.Verification.GenericStateOutputSoundness
