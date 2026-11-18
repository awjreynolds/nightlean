import Noctium.Verification.GenericStateReadNames
import Noctium.Verification.GenericStateKeys

namespace Noctium.Verification.GenericStateSourceNames
open Backend

def sourceNames (entry : Entrypoint) : List String :=
  entry.circuit.inputs.map (·.name) ++
  entry.circuit.outputs.map (·.name) ++
  entry.effects.filterMap (fun effect => match effect with
    | .readCell _ destination _ | .readMap _ destination .. => some destination
    | _ => none)

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

/-- The actual Impact.lower reserved-name gate rejects every source symbol
whose prefix belongs to generated native transcript names. -/
theorem lower_reserved_clear (state : List StateDecl) (ep : Entrypoint)
    (plan : Impact.Plan) (accepted : Impact.lower state ep = .ok plan) :
    (sourceNames ep).any (·.startsWith "_noctium_") = false := by
  unfold Impact.lower at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨_, _, _, _, finished⟩
  cases reserved :
      (ep.circuit.inputs.map (·.name) ++ ep.circuit.outputs.map (·.name) ++
        ep.effects.filterMap (fun effect => match effect with
          | .readCell _ destination _ | .readMap _ destination .. => some destination
          | _ => none)).any (·.startsWith "_noctium_") with
  | false => simpa only [sourceNames] using reserved
  | true =>
    exfalso
    unfold Impact.finishPlan at finished
    split at finished
    · rename_i result candidate resultEq
      split at resultEq
      · simp [bind, Except.bind, throw, throwThe] at resultEq
      · rename_i guard
        exact guard reserved
    · simp [throw, throwThe] at finished

theorem lower_source_names_unreserved (state : List StateDecl)
    (ep : Entrypoint) (plan : Impact.Plan)
    (accepted : Impact.lower state ep = .ok plan) :
    ∀ name ∈ sourceNames ep, name.startsWith "_noctium_" = false := by
  have clear := List.any_eq_false.mp (lower_reserved_clear state ep plan accepted)
  intro name member
  cases checked : name.startsWith "_noctium_" with
  | false => rfl
  | true => exact False.elim (clear name member checked)

/-- Source circuit validation makes the actual public-input prefix names
distinct before the native effect plan appends its reads. -/
theorem lower_public_input_names_unique (state : List StateDecl)
    (ep : Entrypoint) (plan : Impact.Plan)
    (accepted : Impact.lower state ep = .ok plan) :
    ((ep.circuit.inputs.filter (·.visibility == .«public»)).map (·.name)).Nodup := by
  have validated := GenericStateAdmission.lower_circuit_validated
    state ep plan accepted
  have inputNames : uniqueNames (ep.circuit.inputs.map (·.name)) = true := by
    cases unique : uniqueNames (ep.circuit.inputs.map (·.name)) with
    | true => rfl
    | false => simp [Circuit.validate, unique, bind, Except.bind] at validated
  have inputDistinct : (ep.circuit.inputs.map (·.name)).Nodup := by
    apply GenericStateKeys.nodup_of_eraseDups_length_eq
    apply beq_iff_eq.mp
    simpa [uniqueNames] using inputNames
  exact List.Nodup.sublist
    ((List.filter_sublist (l := ep.circuit.inputs)
      (p := fun input => input.visibility == .«public»)).map (·.name))
    inputDistinct

end Noctium.Verification.GenericStateSourceNames
