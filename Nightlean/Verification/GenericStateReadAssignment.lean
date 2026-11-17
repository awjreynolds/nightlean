import Nightlean.Verification.GenericStateSourceReadInputs

namespace Nightlean.Verification.GenericStateReadAssignment
open Backend NativeRelation

def identifier (read : Impact.Read) : String := "%input_" ++ read.name

def keys (entries : List (Impact.Read × Scalar)) : List String :=
  entries.map (fun item => identifier item.1)

theorem keys_nodup_of_names (entries : List (Impact.Read × Scalar))
    (names : (entries.map (fun item => item.1.name)).Nodup) :
    (keys entries).Nodup := by
  have pairwiseNames := List.nodup_iff_pairwise_ne.mp names
  have pairwiseIdentifiers :
      List.Pairwise (fun left right : String => left ≠ right)
        ((entries.map (fun item => item.1.name)).map
          (fun name => "%input_" ++ name)) := List.Pairwise.map
    (fun name : String => "%input_" ++ name)
    (fun left right different => by
      intro same
      exact different ((String.append_right_inj "%input_").mp same))
    pairwiseNames
  apply List.nodup_iff_pairwise_ne.mpr
  simpa only [keys, identifier, List.map_map, Function.comp_def]
    using pairwiseIdentifiers

/-- Accepted Impact lowering and successful source instrumentation make all
read input identifiers distinct, including generated absence aliases. -/
theorem sourceReadInputs_distinct (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (ctx : EvalContext)
    (before after : SourceEffects.Frame)
    (entries : List (Impact.Read × Scalar))
    (accepted : Impact.lower state entry = .ok plan)
    (source : GenericStateSourceReadInputs.sourceReadInputs ctx entry.effects
      ((entry.circuit.inputs.filter (·.visibility == .«public»)).length)
      before = .ok (entries, after)) :
    (keys entries).Nodup := by
  have names := GenericStateSourceReadInputs.sourceReadInputs_names ctx
    entry.effects ((entry.circuit.inputs.filter
      (·.visibility == .«public»)).length) before after entries source
  rw [← GenericStateReadTape.lower_read_chunks state entry plan accepted] at names
  have distinct :=
    (GenericStateNativeReadNames.lower_native_read_names state entry plan accepted).1
  have suffixDistinct : ((plan.reads.drop
      ((entry.circuit.inputs.filter (·.visibility == .«public»)).length)).map
        (·.name)).Nodup := by
    rw [List.map_drop]
    exact List.Nodup.sublist
      (List.drop_sublist _ (plan.reads.map (·.name))) distinct
  have entryDistinct : (entries.map (fun item => item.1.name)).Nodup := by
    rw [← names] at suffixDistinct
    simpa only [List.map_map, Function.comp_def] using suffixDistinct
  exact keys_nodup_of_names entries entryDistinct

/-- Extend a canonical source-input assignment with the actual source read
values. Unmentioned identifiers retain their original assignment. -/
def assign (inputs : Assignment) (entries : List (Impact.Read × Scalar)) :
    Assignment :=
  fun name =>
    ((entries.map (fun item => (identifier item.1, item.2))).lookup name).getD
      (inputs name)

theorem assign_fresh (inputs : Assignment)
    (entries : List (Impact.Read × Scalar)) (name : String)
    (fresh : name ∉ keys entries) :
    assign inputs entries name = inputs name := by
  unfold assign
  have missing : (entries.map (fun item => (identifier item.1, item.2))).lookup
      name = none := by
    apply List.lookup_eq_none_iff.mpr
    intro pair member
    obtain ⟨entry, present, equal⟩ := List.mem_map.mp member
    subst pair
    have different : name ≠ identifier entry.1 := by
      intro same
      exact fresh (List.mem_map.mpr ⟨entry, present, same.symm⟩)
    simp [different]
  rw [missing]
  rfl

/-- New state-read inputs cannot overwrite any declared circuit input in the
constructed relation assignment. Freshness follows from actual Impact.lower. -/
theorem assign_circuit_input (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (ctx : EvalContext)
    (before after : SourceEffects.Frame)
    (entries : List (Impact.Read × Scalar)) (inputs : Assignment)
    (input : Input) (member : input ∈ entry.circuit.inputs)
    (accepted : Impact.lower state entry = .ok plan)
    (source : GenericStateSourceReadInputs.sourceReadInputs ctx entry.effects
      ((entry.circuit.inputs.filter (·.visibility == .«public»)).length)
      before = .ok (entries, after)) :
    assign inputs entries ("%input_" ++ input.name) =
      inputs ("%input_" ++ input.name) := by
  apply assign_fresh
  intro collision
  obtain ⟨entryRead, entryMember, sameIdentifier⟩ :=
    List.mem_map.mp collision
  have names := GenericStateSourceReadInputs.sourceReadInputs_names ctx
    entry.effects ((entry.circuit.inputs.filter
      (·.visibility == .«public»)).length) before after entries source
  rw [← GenericStateReadTape.lower_read_chunks state entry plan accepted] at names
  have readMember : entryRead.1 ∈ plan.reads.drop
      ((entry.circuit.inputs.filter (·.visibility == .«public»)).length) := by
    rw [← names]
    exact List.mem_map.mpr ⟨entryRead, entryMember, rfl⟩
  have sameName : entryRead.1.name = input.name := by
    exact (String.append_right_inj "%input_").mp sameIdentifier
  have avoided :=
    (GenericStateNativeReadNames.lower_native_read_names state entry plan accepted).2
      entryRead.1 readMember
  exact avoided (List.mem_append_left _
    (List.mem_map.mpr ⟨input, member, sameName.symm⟩))

theorem assign_member (inputs : Assignment)
    (entries : List (Impact.Read × Scalar))
    (distinct : (keys entries).Nodup)
    (read : Impact.Read) (value : Scalar)
    (member : (read, value) ∈ entries) :
    assign inputs entries (identifier read) = value := by
  induction entries with
  | nil => cases member
  | cons head tail ih =>
    simp only [keys, List.map_cons, List.nodup_cons] at distinct
    rcases List.mem_cons.mp member with same | later
    · subst head
      simp [assign, identifier]
    · have different : identifier read ≠ identifier head.1 := by
        intro same
        exact distinct.1 (List.mem_map.mpr
          ⟨(read, value), later, by simpa [keys] using same⟩)
      have unequal : (identifier read == identifier head.1) = false := by
        simp [different]
      simp only [assign, List.map_cons, List.lookup_cons, unequal]
      exact ih distinct.2 later

end Nightlean.Verification.GenericStateReadAssignment
