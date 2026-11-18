import Noctium.Verification.GenericStateReadNames
import Noctium.Verification.GenericStateSourceNames
import Std.Data.String.ToNat

namespace Noctium.Verification.GenericStateNativeReadNames
open Backend

/-- This is the exact generated alias spelling in production appendEffect. -/
def absenceName (ordinal : Nat) : String := s!"_noctium_absence_{ordinal}"

theorem absenceName_injective {left right : Nat}
    (same : absenceName left = absenceName right) : left = right := by
  apply Nat.repr_injective
  exact (String.append_right_inj "_noctium_absence_").mp same

theorem absenceName_reserved (ordinal : Nat) :
    (absenceName ordinal).startsWith "_noctium_" = true := by
  rw [String.startsWith_string_iff]
  change "_noctium_".toList <+: ("_noctium_" ++ "absence_" ++ toString ordinal).toList
  rw [String.toList_append, String.toList_append]
  exact ⟨"absence_".toList ++ (toString ordinal).toList, by simp⟩

private def SuffixFresh (initial reads : List Impact.Read) (base : List String) : Prop :=
  ∃ added, reads = initial ++ added ∧ ∀ read ∈ added, read.name ∉ base

private theorem suffixFresh_append (initial reads : List Impact.Read) (base : List String)
    (newRead : Impact.Read) (before : SuffixFresh initial reads base)
    (fresh : newRead.name ∉ base) :
    SuffixFresh initial (reads ++ [newRead]) base := by
  obtain ⟨added, equal, prior⟩ := before
  refine ⟨added ++ [newRead], by simp [equal, List.append_assoc], ?_⟩
  intro read member
  rcases List.mem_append.mp member with old | last
  · exact prior read old
  · simp only [List.mem_singleton] at last
    subst read
    exact fresh

private structure ReadInvariant (remaining : List String)
    (initial reads : List Impact.Read) (base : List String) : Prop where
  distinct : (reads.map (·.name)).Nodup
  avoidRemaining : ∀ read ∈ reads, read.name ∉ remaining
  origin : ∀ read ∈ reads,
    read.name.startsWith "_noctium_" = false ∨
      ∃ ordinal < reads.length, read.name = absenceName ordinal
  suffix : SuffixFresh initial reads base

private theorem generated_fresh (reads : List Impact.Read)
    (origin : ∀ read ∈ reads,
      read.name.startsWith "_noctium_" = false ∨
        ∃ ordinal < reads.length, read.name = absenceName ordinal) :
    absenceName reads.length ∉ reads.map (·.name) := by
  intro member
  obtain ⟨read, present, equal⟩ := List.mem_map.mp member
  rcases origin read present with source | ⟨ordinal, earlier, named⟩
  · have reserved := absenceName_reserved reads.length
    rw [← equal] at reserved
    rw [source] at reserved
    cases reserved
  · have same := absenceName_injective (named.symm.trans equal)
    omega

private theorem append_source (remaining : List String)
    (initial reads : List Impact.Read) (base : List String) (newRead : Impact.Read)
    (before : ReadInvariant (newRead.name :: remaining) initial reads base)
    (sourceDistinct : (newRead.name :: remaining).Nodup)
    (unreserved : newRead.name.startsWith "_noctium_" = false)
    (baseFresh : newRead.name ∉ base) :
    ReadInvariant remaining initial (reads ++ [newRead]) base := by
  have unused : newRead.name ∉ reads.map (·.name) := by
    intro member
    obtain ⟨read, present, equal⟩ := List.mem_map.mp member
    exact before.avoidRemaining read present (by simp [equal])
  constructor
  · simpa only [List.map_append, List.map_cons, List.map_nil] using
      (List.nodup_append.mpr ⟨before.distinct, by simp, by
        intro name old other last equal
        simp only [List.mem_singleton] at last
        subst other
        subst name
        exact unused old⟩)
  · intro read member
    rcases List.mem_append.mp member with prior | last
    · intro present
      exact before.avoidRemaining read prior (List.mem_cons_of_mem _ present)
    · simp only [List.mem_singleton] at last
      subst read
      exact (List.nodup_cons.mp sourceDistinct).1
  · intro read member
    rcases List.mem_append.mp member with prior | last
    · rcases before.origin read prior with source | ⟨ordinal, bounded, named⟩
      · exact Or.inl source
      · exact Or.inr ⟨ordinal, by simp; omega, named⟩
    · simp only [List.mem_singleton] at last
      subst read
      exact Or.inl unreserved
  · exact suffixFresh_append initial reads base newRead before.suffix baseFresh

private theorem absence_not_in (ordinal : Nat) (names : List String)
    (unreserved : ∀ name ∈ names, name.startsWith "_noctium_" = false) :
    absenceName ordinal ∉ names := by
  intro member
  have source := unreserved (absenceName ordinal) member
  rw [absenceName_reserved] at source
  cases source

private theorem append_absence (remaining : List String)
    (initial reads : List Impact.Read) (base : List String)
    (before : ReadInvariant remaining initial reads base)
    (sourceUnreserved : ∀ name ∈ remaining, name.startsWith "_noctium_" = false)
    (baseUnreserved : ∀ name ∈ base, name.startsWith "_noctium_" = false) :
    ReadInvariant remaining initial
      (reads ++ [{name := absenceName reads.length, ty := .bool}]) base := by
  have unused := generated_fresh reads before.origin
  constructor
  · simpa only [List.map_append, List.map_cons, List.map_nil] using
      (List.nodup_append.mpr ⟨before.distinct, by simp, by
        intro name old other last equal
        simp only [List.mem_singleton] at last
        subst other
        subst name
        exact unused old⟩)
  · intro read member
    rcases List.mem_append.mp member with prior | last
    · exact before.avoidRemaining read prior
    · simp only [List.mem_singleton] at last
      subst read
      exact absence_not_in reads.length remaining sourceUnreserved
  · intro read member
    rcases List.mem_append.mp member with prior | last
    · rcases before.origin read prior with source | ⟨ordinal, bounded, named⟩
      · exact Or.inl source
      · exact Or.inr ⟨ordinal, by simp; omega, named⟩
    · simp only [List.mem_singleton] at last
      subst read
      exact Or.inr ⟨reads.length, by simp, rfl⟩
  · exact suffixFresh_append initial reads base _ before.suffix
      (absence_not_in reads.length base baseUnreserved)

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private def addedReads (effect : Effect) (ordinal : Nat) : List Impact.Read :=
  match effect with
  | .readCell _ destination ty => [{name := destination, ty}]
  | .requireAbsent .. => [{name := absenceName ordinal, ty := .bool}]
  | _ => []

private theorem appendEffect_reads (state : List StateDecl) (effect : Effect)
    (before after : Impact.Plan)
    (accepted : Impact.appendEffect state effect before = .ok after) :
    after.reads = before.reads ++ addedReads effect before.reads.length := by
  have same :
      Impact.Plan.reads <$> Impact.appendEffect state effect before =
      (fun _ => before.reads ++ addedReads effect before.reads.length) <$>
        Impact.appendEffect state effect before := by
    cases effect <;>
      simp only [Impact.appendEffect, addedReads, absenceName, map_bind,
        LawfulApplicative.map_pure, List.append_nil] <;> rfl
  rw [accepted] at same
  exact Except.ok.inj same

private theorem appendEffects_invariant (state : List StateDecl)
    (effects : List Effect) (before after : Impact.Plan)
    (initial : List Impact.Read) (base : List String)
    (admitted : ReadInvariant (GenericStateReadNames.sourceReadNames effects)
      initial before.reads base)
    (sourceDistinct : (GenericStateReadNames.sourceReadNames effects).Nodup)
    (sourceUnreserved : ∀ name ∈ GenericStateReadNames.sourceReadNames effects,
      name.startsWith "_noctium_" = false)
    (sourceFresh : ∀ name ∈ GenericStateReadNames.sourceReadNames effects, name ∉ base)
    (baseUnreserved : ∀ name ∈ base, name.startsWith "_noctium_" = false)
    (accepted : Impact.appendEffects state effects before = .ok after) :
    ReadInvariant [] initial after.reads base := by
  induction effects generalizing before with
  | nil =>
    change Except.ok before = .ok after at accepted
    cases accepted
    exact admitted
  | cons effect rest ih =>
    simp only [Impact.appendEffects, List.foldlM_cons, bind_ok] at accepted
    obtain ⟨middle, first, later⟩ := accepted
    have shape := appendEffect_reads state effect before middle first
    cases effect with
    | readCell name destination ty =>
      have following := append_source (GenericStateReadNames.sourceReadNames rest)
        initial before.reads base {name := destination, ty} admitted sourceDistinct
        (sourceUnreserved destination (by change destination ∈ destination :: GenericStateReadNames.sourceReadNames rest; exact List.mem_cons_self))
        (sourceFresh destination (by change destination ∈ destination :: GenericStateReadNames.sourceReadNames rest; exact List.mem_cons_self))
      simp only [addedReads] at shape
      rw [← shape] at following
      apply ih middle following (List.nodup_cons.mp sourceDistinct).2
        (fun found member => sourceUnreserved found (List.mem_cons_of_mem _ member))
        (fun found member => sourceFresh found (List.mem_cons_of_mem _ member)) later
    | readMap name destination keyTy valueTy key =>
      change Except.error _ = .ok middle at first
      cases first
    | requireAbsent name keyTy key =>
      have following := append_absence (GenericStateReadNames.sourceReadNames rest)
        initial before.reads base admitted sourceUnreserved baseUnreserved
      simp only [addedReads] at shape
      rw [← shape] at following
      exact ih middle following sourceDistinct sourceUnreserved sourceFresh later
    | require condition | writeCell name ty value | writeMap name keyTy valueTy key value =>
      simp only [addedReads, List.append_nil] at shape
      have following : ReadInvariant (GenericStateReadNames.sourceReadNames rest)
          initial middle.reads base := by
        rw [shape]
        exact admitted
      exact ih middle following sourceDistinct sourceUnreserved sourceFresh later

/-- The production public-input prefix retains input declaration order. -/
theorem publicInputPlan_reads (inputs : List Input) (initial : Impact.Plan) :
    (Impact.publicInputPlan inputs initial).reads = initial.reads ++
      (inputs.filter (·.visibility == .«public»)).map
        (fun input => ({name := input.name, ty := input.ty} : Impact.Read)) := by
  induction inputs generalizing initial with
  | nil => simp [Impact.publicInputPlan]
  | cons input rest ih =>
    let middle := Impact.publicInputPlan [input] initial
    have foldShape : Impact.publicInputPlan (input :: rest) initial =
        Impact.publicInputPlan rest middle := rfl
    rw [foldShape, ih middle]
    cases input with
    | mk name ty visibility span =>
      cases visibility with
      | «public» =>
        have one : middle.reads = initial.reads ++ [{name := name, ty := ty}] := rfl
        rw [one]
        simp [List.append_assoc, BEq.beq, instBEqVisibility.beq]
      | «private» =>
        have one : middle.reads = initial.reads := rfl
        rw [one]
        rfl

private theorem lower_names_from_source (state : List StateDecl) (ep : Entrypoint)
    (plan : Impact.Plan) (accepted : Impact.lower state ep = .ok plan)
    (sourceClear : ∀ name ∈ ep.circuit.inputs.map (·.name) ++
      ep.circuit.outputs.map (·.name) ++ GenericStateReadNames.sourceReadNames ep.effects,
      name.startsWith "_noctium_" = false)
    (prefixDistinct : ((ep.circuit.inputs.filter (·.visibility == .«public»)).map (·.name)).Nodup) :
    (plan.reads.map (·.name)).Nodup ∧
      ∀ read ∈ plan.reads.drop
        ((ep.circuit.inputs.filter (·.visibility == .«public»)).length),
        read.name ∉ ep.circuit.inputs.map (·.name) ++ ep.circuit.outputs.map (·.name) := by
  let base := ep.circuit.inputs.map (·.name) ++ ep.circuit.outputs.map (·.name)
  let initial := Impact.publicInputPlan ep.circuit.inputs {}
  have initialShape : initial.reads =
      (ep.circuit.inputs.filter (·.visibility == .«public»)).map
        (fun input => ({name := input.name, ty := input.ty} : Impact.Read)) := by
    simpa only [initial, List.nil_append] using publicInputPlan_reads ep.circuit.inputs {}
  obtain ⟨sourceDistinct, sourceFresh⟩ :=
    GenericStateReadNames.lower_source_read_names state ep plan accepted
  have sourceUnreserved : ∀ name ∈ GenericStateReadNames.sourceReadNames ep.effects,
      name.startsWith "_noctium_" = false := by
    intro name member
    exact sourceClear name (by simp only [List.mem_append]; exact Or.inr member)
  have baseUnreserved : ∀ name ∈ base, name.startsWith "_noctium_" = false := by
    intro name member
    exact sourceClear name (List.mem_append_left _ member)
  have initialSource : ∀ read ∈ initial.reads,
      read.name ∈ ep.circuit.inputs.map (·.name) := by
    intro read member
    rw [initialShape] at member
    obtain ⟨input, present, same⟩ := List.mem_map.mp member
    subst read
    exact List.mem_map.mpr ⟨input, (List.mem_filter.mp present).1, rfl⟩
  have before : ReadInvariant (GenericStateReadNames.sourceReadNames ep.effects)
      initial.reads initial.reads base := by
    constructor
    · simpa only [initialShape, List.map_map, Function.comp_def] using prefixDistinct
    · intro read member inSource
      exact sourceFresh read.name inSource (List.mem_append_left _ (initialSource read member))
    · intro read member
      exact Or.inl (baseUnreserved read.name (List.mem_append_left _ (initialSource read member)))
    · exact ⟨[], by simp, by simp⟩
  have final := appendEffects_invariant state ep.effects initial plan initial.reads base
    before sourceDistinct sourceUnreserved sourceFresh baseUnreserved
    (GenericStateAdmission.lower_effect_fold state ep plan accepted)
  refine ⟨final.distinct, ?_⟩
  obtain ⟨added, readShape, fresh⟩ := final.suffix
  have initialLength : initial.reads.length =
      (ep.circuit.inputs.filter (·.visibility == .«public»)).length := by
    rw [initialShape, List.length_map]
  intro read member
  rw [readShape, ← initialLength, List.drop_left] at member
  exact fresh read member

private theorem sourceReadNames_eq (effects : List Effect) :
    GenericStateReadNames.sourceReadNames effects = effects.filterMap
      (fun effect => match effect with
        | .readCell _ destination _ | .readMap _ destination .. => some destination
        | _ => none) := by
  induction effects with
  | nil => rfl
  | cons effect rest ih =>
    cases effect <;> first
      | exact ih
      | exact congrArg (List.cons _) ih

/-- Accepted production lowering gives distinct native transcript read names.
Every non-prefix read is fresh against all original inputs and output bindings,
including generated absence aliases. No witness or source-success premise. -/
theorem lower_native_read_names (state : List StateDecl) (ep : Entrypoint)
    (plan : Impact.Plan) (accepted : Impact.lower state ep = .ok plan) :
    (plan.reads.map (·.name)).Nodup ∧
      ∀ read ∈ plan.reads.drop
        ((ep.circuit.inputs.filter (·.visibility == .«public»)).length),
        read.name ∉ ep.circuit.inputs.map (·.name) ++ ep.circuit.outputs.map (·.name) := by
  apply lower_names_from_source state ep plan accepted
  · intro name member
    rw [sourceReadNames_eq] at member
    exact GenericStateSourceNames.lower_source_names_unreserved state ep plan accepted name member
  · exact GenericStateSourceNames.lower_public_input_names_unique state ep plan accepted

end Noctium.Verification.GenericStateNativeReadNames
