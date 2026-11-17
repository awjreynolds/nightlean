import Nightlean.Verification.GenericStateOutputBindings
import Nightlean.Verification.GenericStateKeys

namespace Nightlean.Verification.GenericStateOutputOrder
open Backend.Native NativeRelation ScalarNormalization

private theorem lookup_none_of_key_not_mem (items : List (String × α))
    (name : String) (absent : name ∉ items.map Prod.fst) :
    items.lookup name = none := by
  apply List.lookup_eq_none_iff.mpr
  intro pair member
  have different : name ≠ pair.1 := by
    intro equal
    apply absent
    simpa [equal] using (List.mem_map.mpr ⟨pair, member, rfl⟩ :
      pair.1 ∈ items.map Prod.fst)
  simp [different]

/-- Reversing distinct named bindings does not change their first-match
lookup. This bridges the production alias stack and source output order. -/
theorem lookup_reverse_unique (items : List (String × α))
    (unique : (items.map Prod.fst).Nodup) (name : String) :
    items.reverse.lookup name = items.lookup name := by
  induction items with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨head, value⟩
    have distinct := List.nodup_cons.mp unique
    have noHead := lookup_none_of_key_not_mem rest head distinct.1
    have noHeadReverse := lookup_none_of_key_not_mem rest.reverse head (by
      simpa [List.map_reverse, List.mem_reverse] using distinct.1)
    simp only [List.reverse_cons, List.lookup_append]
    by_cases same : name = head
    · subst name
      simp [List.lookup_cons, noHead, noHeadReverse]
    · have different : (name == head) = false := by simp [same]
      simp only [List.lookup_cons, different, Option.or_none]
      simpa using ih distinct.2

/-- A typed alias environment depends on the first binding for each name,
so equal lookup functions preserve its proof. -/
theorem typedEnvironment_lookup_ext (hash : Hash) (inputs : Assignment)
    (aliases : AliasEnvironment) (values replacement : EvalEnv)
    (types replacementTypes : TypeEnv)
    (environment : TypedEnvironment hash inputs aliases values types)
    (sameValues : ∀ name, replacement.lookup name = values.lookup name)
    (sameTypes : ∀ name, replacementTypes.lookup name = types.lookup name) :
    TypedEnvironment hash inputs aliases replacement replacementTypes := by
  constructor
  · intro name ty raw value lookup typed
    exact environment.aliases name ty raw value
      (by rw [← sameValues]; exact lookup) typed
  · intro name ty lookup
    obtain ⟨raw, value, old, packed⟩ :=
      environment.complete name ty (by rw [← sameTypes]; exact lookup)
    exact ⟨raw, value, by rw [sameValues]; exact old, packed⟩

/-- The output values in original source order have the same typed meaning
as the reversed stack order used while building production aliases. -/
theorem typedEnvironment_output_order (hash : Hash) (inputs : Assignment)
    (aliases : AliasEnvironment) (results values : EvalEnv)
    (outputTypes types : TypeEnv)
    (uniqueResults : (results.map Prod.fst).Nodup)
    (uniqueTypes : (outputTypes.map Prod.fst).Nodup)
    (stack : TypedEnvironment hash inputs aliases
      (results.reverse ++ values) (outputTypes.reverse ++ types)) :
    TypedEnvironment hash inputs aliases
      (results ++ values) (outputTypes ++ types) := by
  apply typedEnvironment_lookup_ext hash inputs aliases
    (results.reverse ++ values) (results ++ values)
    (outputTypes.reverse ++ types) (outputTypes ++ types) stack
  · intro name
    simp only [List.lookup_append]
    rw [lookup_reverse_unique results uniqueResults name]
  · intro name
    simp only [List.lookup_append]
    rw [lookup_reverse_unique outputTypes uniqueTypes name]

/-- Accepted production output aliases supply the exact typed environment
used by the original ordered state evaluator. -/
theorem outputFold_source_bindings (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (types : TypeEnv) (values : EvalEnv)
    (outputs : List Output) (frame final : GenericStateCircuitParts.OutputFrame)
    (environment : TypedEnvironment hash inputs frame.1 values types)
    (unique : (outputs.map (·.name)).Nodup)
    (valid : ∀ output ∈ outputs,
      output.value.validate {poseidon2 := true} types = .ok ())
    (unused : ∀ output ∈ outputs, values.lookup output.name = none)
    (accepted : GenericStateCircuitParts.outputFold frame outputs = .ok final)
    (bounds : ∀ requirement ∈ final.2.1,
      (interpret hash inputs requirement.1).val ≤ requirement.2)
    (assertions : ∀ term ∈ final.2.2,
      interpret hash inputs term = one) :
    ∃ result, outputs.mapM (evalOutput ctx values) = .ok result ∧
      TypedEnvironment hash inputs final.1 (result ++ values)
        (outputs.map (fun output => (output.name, output.ty)) ++ types) := by
  obtain ⟨result, evaluated, stack⟩ :=
    GenericStateOutputBindings.outputFold_bindings ctx hash implementation
      inputs types values outputs frame final values types environment
      environment valid unused accepted bounds assertions
  obtain ⟨sameResult, sameEval, names, _⟩ :=
    GenericStateOutputSoundness.outputFold_sound ctx hash implementation
      inputs types values outputs frame final environment valid unused accepted
      bounds assertions
  rw [evaluated] at sameEval
  cases sameEval
  have resultUnique : (result.map Prod.fst).Nodup := by
    rw [names]
    exact unique
  have typeUnique : ((outputs.map (fun output =>
      (output.name, output.ty))).map Prod.fst).Nodup := by
    simpa [List.map_map, Function.comp_def] using unique
  exact ⟨result, evaluated,
    typedEnvironment_output_order hash inputs final.1 result values
      (outputs.map (fun output => (output.name, output.ty))) types
      resultUnique typeUnique stack⟩

/-- The source circuit validator supplies unique output names to the
source-order binding transport. -/
theorem validated_output_names_unique (circuit : Circuit)
    (valid : circuit.validate {poseidon2 := true} = .ok ()) :
    (circuit.outputs.map (·.name)).Nodup := by
  cases inputNames : uniqueNames (circuit.inputs.map (·.name)) with
  | false => simp [Circuit.validate, inputNames, bind, Except.bind] at valid
  | true =>
    cases outputNames : uniqueNames (circuit.outputs.map (·.name)) with
    | false => simp [Circuit.validate, inputNames, outputNames, bind, Except.bind] at valid
    | true =>
      apply GenericStateKeys.nodup_of_eraseDups_length_eq
      apply beq_iff_eq.mp
      simpa [uniqueNames] using outputNames

theorem outputFold_source_bindings_validated (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (circuit : Circuit) (values : EvalEnv)
    (frame final : GenericStateCircuitParts.OutputFrame)
    (environment : TypedEnvironment hash inputs frame.1 values
      (circuit.inputs.map (fun input => (input.name, input.ty))))
    (validated : circuit.validate {poseidon2 := true} = .ok ())
    (unused : ∀ output ∈ circuit.outputs, values.lookup output.name = none)
    (accepted : GenericStateCircuitParts.outputFold frame circuit.outputs = .ok final)
    (bounds : ∀ requirement ∈ final.2.1,
      (interpret hash inputs requirement.1).val ≤ requirement.2)
    (assertions : ∀ term ∈ final.2.2,
      interpret hash inputs term = one) :
    ∃ result, circuit.outputs.mapM (evalOutput ctx values) = .ok result ∧
      TypedEnvironment hash inputs final.1 (result ++ values)
        (circuit.outputs.map (fun output => (output.name, output.ty)) ++
          circuit.inputs.map (fun input => (input.name, input.ty))) := by
  exact outputFold_source_bindings ctx hash implementation inputs
    (circuit.inputs.map (fun input => (input.name, input.ty))) values
    circuit.outputs frame final environment
    (validated_output_names_unique circuit validated)
    (ScalarNormalization.circuit_validation_parts circuit validated).2
    unused accepted bounds assertions

end Nightlean.Verification.GenericStateOutputOrder
