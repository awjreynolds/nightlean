import Nightlean.Backend.NativeExpected

namespace Nightlean.Verification.GenericStateCircuitParts
open Backend.Native

abbrev OutputFrame := AliasEnvironment × List (Term × Nat) × List Term

def inputRequirements (entry : Entrypoint) (plan : Backend.Impact.Plan) : List InputRequirement :=
  entry.circuit.inputs.map (fun input =>
    {identifier := "%input_" ++ input.name, visibility := input.visibility, ty := input.ty}) ++
  (plan.reads.drop ((entry.circuit.inputs.filter (·.visibility == .«public»)).length)).map
    (fun read => {identifier := "%input_" ++ read.name, visibility := .«public», ty := read.ty})

def initialAliases (entry : Entrypoint) (plan : Backend.Impact.Plan) : AliasEnvironment :=
  (inputRequirements entry plan).map
    (fun input => (input.identifier.drop 7 |>.toString, .input input.identifier))

def normalizeOutput (aliases : AliasEnvironment) (output : Output) : Except Diagnostic Normalized :=
  (normalize aliases output.value).mapError (fun message => {span := output.span, message})

def appendOutput (output : Output) (frame : OutputFrame) : Except Diagnostic OutputFrame := do
  let result ← normalizeOutput frame.1 output
  pure ((output.name, result.term) :: frame.1,
    frame.2.1 ++ result.bounds, frame.2.2 ++ result.assertions)

def outputFold (frame : OutputFrame) (outputs : List Output) : Except Diagnostic OutputFrame :=
  outputs.foldlM (fun frame output => appendOutput output frame) frame

def normalizeOutputs (aliases : AliasEnvironment) (outputs : List Output) :
    Except Diagnostic OutputFrame := outputFold (aliases, [], []) outputs

@[simp] theorem outputFold_nil (frame : OutputFrame) : outputFold frame [] = .ok frame := rfl

theorem outputFold_cons (frame : OutputFrame) (output : Output) (rest : List Output) :
    outputFold frame (output :: rest) =
      (appendOutput output frame).bind (fun next => outputFold next rest) := rfl

private theorem bind_ok {α β : Type} {first : Except ε α} {next : α → Except ε β}
    {result : β} : (first >>= next) = .ok result ↔
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

theorem normalizeOutputs_loop (aliases : AliasEnvironment) (outputs : List Output) :
    (forIn outputs (aliases, [], []) fun output frame => do
      let result ← normalizeOutput frame.1 output
      pure (ForInStep.yield ((output.name, result.term) :: frame.1,
        frame.2.1 ++ result.bounds, frame.2.2 ++ result.assertions))) =
      normalizeOutputs aliases outputs := by
  simp [normalizeOutputs, outputFold, appendOutput]

/-- Exact projections of the production ledger-call expected constructor. -/
theorem expectedEntrypoint_parts (state : List StateDecl) (entry : Entrypoint)
    (expected : Expected) (accepted : expectedEntrypoint state entry = .ok expected) :
    ∃ (plan : Backend.Impact.Plan) (outputFrame : OutputFrame)
      (conditions guards : List Normalized) (operationFrame : List (List Term) × List (Term × Nat) × List Term),
      Backend.Impact.lower state entry = .ok plan ∧
      normalizeOutputs (initialAliases entry plan) entry.circuit.outputs = .ok outputFrame ∧
      entry.circuit.constraints.mapM (normalize outputFrame.1) = .ok conditions ∧
      plan.guards.mapM (normalize outputFrame.1) = .ok guards ∧
      collectOperations entry.span outputFrame.1 plan.operations outputFrame.2.1 = .ok operationFrame ∧
      expected.inputs = inputRequirements entry plan ∧
      expected.groups = operationFrame.1 ∧
      expected.returns = [] ∧
      expected.mode = .ledgerCall ∧
      expected.assertions = conditions.flatMap (fun item => item.assertions ++ [item.term]) ++
        outputFrame.2.2 ++ guards.flatMap (fun item => item.assertions ++ [item.term]) ++
        operationFrame.2.2 ∧
      expected.bounds = operationFrame.2.1 ++ conditions.flatMap (·.bounds) ++ guards.flatMap (·.bounds) := by
  unfold expectedEntrypoint at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨plan, lowered, outputFrame, outputAccepted,
    collected, collectedAccepted, conditions, conditionsAccepted,
    guardCollection, guardCollectionAccepted, guards, guardsAccepted,
    operationFrame, operationAccepted, produced⟩
  have conditionValues := (convert_ok _ _ _).mp conditionsAccepted
  have guardValues := (convert_ok _ _ _).mp guardsAccepted
  have collectedValues := (convert_ok _ _ _).mp collectedAccepted
  simp only [collect_eq, bind_ok] at collectedValues
  rcases collectedValues with ⟨conditionResults, conditionResultsAccepted, collectedEqual⟩
  rw [conditionValues] at conditionResultsAccepted
  cases conditionResultsAccepted
  have guardCollectedValues := (convert_ok _ _ _).mp guardCollectionAccepted
  simp only [collect_eq, bind_ok] at guardCollectedValues
  rcases guardCollectedValues with ⟨guardResults, guardResultsAccepted, guardCollectedEqual⟩
  rw [guardValues] at guardResultsAccepted
  cases guardResultsAccepted
  cases collectedEqual
  cases guardCollectedEqual
  cases produced
  refine ⟨plan, outputFrame, conditions, guards, operationFrame, lowered, ?_,
    conditionValues, guardValues, operationAccepted, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · rw [← normalizeOutputs_loop]
    simpa only [initialAliases, inputRequirements, normalizeOutput,
      inputAliases_eq, inputRequirement_function_eq, convert_eq_mapError,
      Except.mapError] using outputAccepted
  · simp [inputRequirements, inputRequirement_function_eq]

end Nightlean.Verification.GenericStateCircuitParts
