import Nightlean.Verification.GenericStateReadTape
import Nightlean.Verification.GenericStateReadFreshness
import Nightlean.Verification.GenericStateReadAdmission
import Nightlean.Verification.GenericStatePrefixEnvironment

namespace Nightlean.Verification.GenericStateReadCandidates
open Backend NativeRelation ScalarNormalization

/-- Every source cell read contributes its exact destination and type to the
production read metadata, even after preceding reads change the ordinal. -/
theorem readCell_in_readChunks (effects : List Effect) (ordinal : Nat)
    (name destination : String) (ty : Ty)
    (member : Effect.readCell name destination ty ∈ effects) :
    ({name := destination, ty} : Impact.Read) ∈
      (GenericStateReadTape.readChunks effects ordinal).flatten := by
  induction effects generalizing ordinal with
  | nil => cases member
  | cons effect rest ih =>
    rcases List.mem_cons.mp member with first | later
    · subst effect
      simp [GenericStateReadTape.readChunks,
        GenericStateReadTape.effectReadChunk]
    · simp only [GenericStateReadTape.readChunks, List.flatten_cons,
        List.mem_append]
      exact Or.inr (ih _ later)

/-- Accepted lowering puts each source cell read in the strict post-public
read suffix, with the same destination and source type. -/
theorem lower_readCell_member (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (name destination : String) (ty : Ty)
    (accepted : Impact.lower state entry = .ok plan)
    (member : Effect.readCell name destination ty ∈ entry.effects) :
    ({name := destination, ty} : Impact.Read) ∈
      plan.reads.drop ((entry.circuit.inputs.filter
        (·.visibility == .«public»)).length) := by
  rw [GenericStateReadTape.lower_read_chunks state entry plan accepted]
  exact readCell_in_readChunks entry.effects _ name destination ty member

/-- A source cell read selects the same typed canonical candidate as the
relation witness's exact post-public read input. The source evaluator does
not accept the value until the native read segment authenticates it. -/
theorem readCell_candidate (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (ctx : EvalContext) (values result : EvalEnv)
    (witness : Assignment) (name destination : String) (ty : Ty)
    (admitted : CanonicalInputs entry.circuit values witness)
    (accepted : Impact.lower state entry = .ok plan)
    (source : entry.circuit.run ctx values = .ok result)
    (member : Effect.readCell name destination ty ∈ entry.effects)
    (typedBounded : ∀ read ∈ plan.reads.drop
      ((entry.circuit.inputs.filter (·.visibility == .«public»)).length),
      read.ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} =
        .ok () ∧
      (witness ("%input_" ++ read.name)).val ≤ Backend.Native.sourceMaximum read.ty) :
    ∃ candidate : ty.Denote,
      ((result ++ values) ++ GenericStateInputValues.decodeReads
        (plan.reads.drop ((entry.circuit.inputs.filter
          (·.visibility == .«public»)).length)) witness).lookup destination =
        some (Value.pack ty candidate) ∧
      Canonical ty candidate := by
  let reads := plan.reads.drop
    ((entry.circuit.inputs.filter (·.visibility == .«public»)).length)
  have present : ({name := destination, ty} : Impact.Read) ∈ reads :=
    lower_readCell_member state entry plan name destination ty accepted member
  have distinct := GenericStateReadFreshness.lower_read_pairwise
    state entry plan accepted
  have fresh := (GenericStateReadFreshness.lower_read_base_fresh state entry
    plan ctx values result witness admitted accepted source
    {name := destination, ty} present).1
  let candidate := GenericStateInputValues.sourceValue ty
    (witness ("%input_" ++ destination))
  refine ⟨candidate, ?_, ?_⟩
  · exact GenericStatePrefixEnvironment.candidate_read_lookup
      (result ++ values) reads witness distinct
      {name := destination, ty} present fresh
  · exact (GenericStateInputValues.sourceValue_canonical ty
      (witness ("%input_" ++ destination))
      (typedBounded {name := destination, ty} present).1
      (typedBounded {name := destination, ty} present).2).1

end Nightlean.Verification.GenericStateReadCandidates
