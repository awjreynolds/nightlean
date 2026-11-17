import Nightlean.Verification.GenericStateOutputOrder
import Nightlean.Verification.GenericStateAliases

namespace Nightlean.Verification.GenericStateTypeOrder
open Backend.Native NativeRelation ScalarNormalization

private theorem lookup_append_comm_of_disjoint (left right : List (String × α))
    (disjoint : ∀ name, left.lookup name = none ∨ right.lookup name = none)
    (name : String) :
    (left ++ right).lookup name = (right ++ left).lookup name := by
  rcases disjoint name with first | second
  · simp [List.lookup_append, first]
  · simp [List.lookup_append, second]

/-- The source circuit validator keeps output type names distinct from input
names, so their order in the normalizer type list is immaterial. -/
theorem validated_input_output_type_order (circuit : Circuit)
    (valid : circuit.validate {poseidon2 := true} = .ok ())
    (name : String) :
    (circuit.outputs.map (fun output => (output.name, output.ty)) ++
      circuit.inputs.map (fun input => (input.name, input.ty))).lookup name =
    (circuit.inputs.map (fun input => (input.name, input.ty)) ++
      circuit.outputs.map (fun output => (output.name, output.ty))).lookup name := by
  apply lookup_append_comm_of_disjoint
  intro found
  cases outputLookup :
      (circuit.outputs.map (fun output => (output.name, output.ty))).lookup found with
  | none => exact Or.inl rfl
  | some ty =>
    obtain ⟨before, after, membership, _⟩ :=
      List.lookup_eq_some_iff.mp outputLookup
    have pairMember : (found, ty) ∈
        circuit.outputs.map (fun output => (output.name, output.ty)) := by
      rw [membership]
      simp
    obtain ⟨output, outputMember, pairEqual⟩ := List.mem_map.mp pairMember
    cases pairEqual
    exact Or.inr (GenericStateAliases.validated_outputs_unshadowed circuit
      valid output outputMember)

theorem typedEnvironment_input_output_order (circuit : Circuit)
    (valid : circuit.validate {poseidon2 := true} = .ok ())
    (hash : Hash) (witness : Assignment)
    (aliases : AliasEnvironment) (values : EvalEnv)
    (environment : TypedEnvironment hash witness aliases values
      (circuit.outputs.map (fun output => (output.name, output.ty)) ++
        circuit.inputs.map (fun input => (input.name, input.ty)))) :
    TypedEnvironment hash witness aliases values
      (circuit.inputs.map (fun input => (input.name, input.ty)) ++
        circuit.outputs.map (fun output => (output.name, output.ty))) := by
  apply GenericStateOutputOrder.typedEnvironment_lookup_ext hash witness aliases
    values values _ _ environment
  · intro name; rfl
  · intro name
    exact (validated_input_output_type_order circuit valid name).symm

end Nightlean.Verification.GenericStateTypeOrder
