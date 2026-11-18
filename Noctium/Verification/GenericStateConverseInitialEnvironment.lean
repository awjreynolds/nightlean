import Noctium.Verification.GenericStatePrefixEnvironment
import Noctium.Verification.GenericStateReadFreshness
import Noctium.Verification.GenericStateEffectValidation

namespace Noctium.Verification.GenericStateConverseInitialEnvironment
open Backend NativeRelation ScalarNormalization GenericStatePrefixEnvironment

private theorem lookup_present_of_name_mem (items : List (String × α))
    (name : String) (member : name ∈ items.map Prod.fst) :
    ∃ value, items.lookup name = some value := by
  cases found : items.lookup name with
  | some value => exact ⟨value, rfl⟩
  | none =>
    obtain ⟨pair, present, equal⟩ := List.mem_map.mp member
    have absent := List.lookup_eq_none_iff.mp found pair present
    simp [equal] at absent

/-- Successful original circuit execution supplies every declared initial
effect binding. Future authenticated reads therefore preserve those bindings. -/
theorem source_initial_agreement (ctx : EvalContext) (entry : Entrypoint)
    (values result future : EvalEnv) (inputs : Assignment)
    (admitted : CanonicalInputs entry.circuit values inputs)
    (source : entry.circuit.run ctx values = .ok result) :
    AgreesOnTypes (GenericStateEffectValidation.initialEffectTypeEnv entry)
      (result ++ values) ((result ++ values) ++ future) := by
  apply initial_agreement
  intro name ty typed
  have member : (name, ty) ∈
      GenericStateEffectValidation.initialEffectTypeEnv entry := by
    obtain ⟨before, after, equal, _⟩ := List.lookup_eq_some_iff.mp typed
    rw [equal]
    simp
  simp only [GenericStateEffectValidation.initialEffectTypeEnv,
    List.mem_append] at member
  rcases member with inputMember | outputMember
  · obtain ⟨input, inputPresent, pairEqual⟩ := List.mem_map.mp inputMember
    have inputName : input.name = name := congrArg Prod.fst pairEqual
    obtain ⟨value, found, _⟩ := admitted.complete input inputPresent
    rw [inputName] at found
    cases resultLookup : result.lookup name with
    | some raw => exact ⟨raw, by simp [List.lookup_append, resultLookup]⟩
    | none =>
      exact ⟨Value.pack input.ty value,
        by simp [List.lookup_append, resultLookup, found]⟩
  · obtain ⟨output, outputPresent, pairEqual⟩ := List.mem_map.mp outputMember
    have outputName : output.name = name := congrArg Prod.fst pairEqual
    obtain ⟨_, outputEval⟩ :=
      ScalarNormalization.circuit_run_steps ctx entry.circuit values result source
    have names := GenericStateReadFreshness.source_outputs_names ctx values
      entry.circuit.outputs result outputEval
    have namePresent : name ∈ result.map Prod.fst := by
      rw [names]
      exact List.mem_map.mpr ⟨output, outputPresent, outputName⟩
    obtain ⟨raw, found⟩ := lookup_present_of_name_mem result name namePresent
    exact ⟨raw, by simp [List.lookup_append, found]⟩

end Noctium.Verification.GenericStateConverseInitialEnvironment
