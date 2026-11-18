import Noctium.Verification.GenericStateOutputSoundness

namespace Noctium.Verification.GenericStateOutputBindings
open Backend.Native NativeRelation ScalarNormalization GenericStateCircuitParts
open GenericStateOutputSoundness

private theorem bind_ok {α β : Type} {first : Except ε α} {next : α → Except ε β}
    {result : β} : (first >>= next) = .ok result ↔
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

/-- The production output fold creates typed internal bindings in its alias
environment. Output expressions still evaluate against the original circuit
inputs, as the source circuit evaluator requires. -/
theorem outputFold_bindings (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (types : TypeEnv) (values : EvalEnv)
    (outputs : List Output) (frame final : OutputFrame)
    (priorValues : EvalEnv) (priorTypes : TypeEnv)
    (base : TypedEnvironment hash inputs frame.1 values types)
    (expanded : TypedEnvironment hash inputs frame.1 priorValues priorTypes)
    (valid : ∀ output ∈ outputs,
      output.value.validate {poseidon2 := true} types = .ok ())
    (unused : ∀ output ∈ outputs, values.lookup output.name = none)
    (accepted : outputFold frame outputs = .ok final)
    (bounds : ∀ requirement ∈ final.2.1,
      (interpret hash inputs requirement.1).val ≤ requirement.2)
    (assertions : ∀ term ∈ final.2.2,
      interpret hash inputs term = one) :
    ∃ result, outputs.mapM (evalOutput ctx values) = .ok result ∧
      TypedEnvironment hash inputs final.1
        (result.reverse ++ priorValues)
        ((outputs.map (fun output => (output.name, output.ty))).reverse ++ priorTypes) := by
  induction outputs generalizing frame priorValues priorTypes with
  | nil =>
    simp [outputFold] at accepted
    cases accepted
    exact ⟨[], rfl, by simpa using expanded⟩
  | cons output rest ih =>
    rw [outputFold_cons] at accepted
    change (appendOutput output frame >>= fun next => outputFold next rest) =
      .ok final at accepted
    simp only [bind_ok] at accepted
    obtain ⟨middle, first, later⟩ := accepted
    have monotone := outputFold_monotone middle final rest later
    obtain ⟨normalized, value, _, evaluated, canonical, meaning,
      aliases, nextBase⟩ :=
      appendOutput_sound ctx hash implementation inputs types values
        output frame middle base (valid output (by simp))
        (unused output (by simp)) first
        (fun requirement member => bounds requirement (monotone.1 requirement member))
        (fun term member => assertions term (monotone.2 term member))
    have nextExpanded : TypedEnvironment hash inputs middle.1
        ((output.name, Value.pack output.ty value) :: priorValues)
        ((output.name, output.ty) :: priorTypes) := by
      rw [aliases]
      exact TypedEnvironment.cons hash inputs frame.1 priorValues priorTypes
        expanded output.name output.ty value normalized.term canonical meaning
    obtain ⟨tail, tailRun, tailEnvironment⟩ :=
      ih middle _ _ nextBase nextExpanded
        (fun item member => valid item (by simp [member]))
        (fun item member => unused item (by simp [member])) later
    refine ⟨(output.name, Value.pack output.ty value) :: tail, ?_, ?_⟩
    · simp [List.mapM_cons, evalOutput, evaluated, tailRun, Except.map, Functor.map,
        bind, pure, Except.bind, Except.pure]
    · simpa [List.reverse_cons, List.append_assoc] using tailEnvironment

end Noctium.Verification.GenericStateOutputBindings
