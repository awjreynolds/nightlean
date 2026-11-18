import Noctium.Verification.ScalarNormalizationSoundness
import Noctium.Backend.NativeProducer
import Noctium.Backend.Impact
import Noctium.Verification.GenericStateAliases

namespace Noctium.Verification.GenericStateInputValues
open NativeRelation ScalarNormalization Backend.Native

/-- Decode one canonical native relation input into its declared source type.
The producer supplies the numeric bound; source validation supplies the type. -/
def sourceValue : (ty : Ty) → Scalar → ty.Denote
  | .native, number => number.val
  | .bool, number => number.val == 1
  | .uint _, number => number.val

theorem sourceValue_canonical (ty : Ty) (number : Scalar)
    (typed : ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok ())
    (bounded : number.val ≤ sourceMaximum ty) :
    Canonical ty (sourceValue ty number) ∧
      scalar (ScalarNormalization.number ty (sourceValue ty number)) = number := by
  cases ty with
  | native =>
    constructor
    · exact ⟨number.isLt, trivial⟩
    · apply Fin.ext
      simp [sourceValue, ScalarNormalization.number,
        scalar_no_wrap _ number.isLt]

  | bool =>
    rcases number with ⟨number, fieldBound⟩
    have valueZeroOrOne : number = 0 ∨ number = 1 := by
      simpa [sourceMaximum] using (Nat.le_one_iff_eq_zero_or_eq_one.mp bounded)
    rcases valueZeroOrOne with zero | one
    · subst number
      constructor
      · simp [Canonical, sourceValue, ScalarNormalization.number, Field.modulus]
      · apply Fin.ext
        simp [sourceValue, ScalarNormalization.number, zero, Field.modulus]
    · subst number
      constructor
      · simp [Canonical, sourceValue, ScalarNormalization.number, Field.modulus]
      · apply Fin.ext
        simp [sourceValue, ScalarNormalization.number, one, Field.modulus]
  | uint maximum =>
    have maximumBound : maximum ≤ ScalarPolicy.maxUint := by
      by_cases limit : maximum ≤ ScalarPolicy.maxUint
      · exact limit
      · have fail : ScalarPolicy.validate (.uint maximum) =
            .error "unsigned type exceeds target maximum" := by
          simp [ScalarPolicy.validate, limit]
        change (do
          let _ ← ScalarPolicy.validate (.uint maximum)
          if maximum < Field.modulus then pure ()
          else throw "unsigned type exceeds native representation") = .ok () at typed
        rw [fail] at typed
        cases typed
    constructor
    · exact ⟨number.isLt, maximumBound, by simpa [sourceValue, sourceMaximum] using bounded⟩
    · apply Fin.ext
      simp [sourceValue, ScalarNormalization.number,
        scalar_no_wrap _ number.isLt]

/-- Candidate typed ledger-read values supplied by the satisfying relation
witness. Checked VM reads must authenticate these candidates before source
effects use them. -/
def decodeReads (reads : List Backend.Impact.Read) (witness : Assignment) : EvalEnv :=
  reads.map fun read =>
    (read.name, Value.pack read.ty
      (sourceValue read.ty (witness ("%input_" ++ read.name))))

def readAliases (reads : List Backend.Impact.Read) : Backend.Native.AliasEnvironment :=
  reads.map fun read => (read.name, .input ("%input_" ++ read.name))

def readTypes (reads : List Backend.Impact.Read) : TypeEnv :=
  reads.map fun read => (read.name, read.ty)

theorem initialAliases_readAliases (entry : Entrypoint)
    (plan : Backend.Impact.Plan) :
    GenericStateCircuitParts.initialAliases entry plan =
      circuitAliases entry.circuit ++
      readAliases (plan.reads.drop
        ((entry.circuit.inputs.filter (·.visibility == .«public»)).length)) := by
  simpa only [readAliases] using GenericStateAliases.initialAliases_eq entry plan

theorem decodeReads_lookup (reads : List Backend.Impact.Read)
    (witness : Assignment)
    (distinct : reads.Pairwise (fun left right => left.name ≠ right.name))
    (read : Backend.Impact.Read) (member : read ∈ reads) :
    (decodeReads reads witness).lookup read.name =
      some (Value.pack read.ty
        (sourceValue read.ty (witness ("%input_" ++ read.name)))) := by
  induction reads with
  | nil => cases member
  | cons head tail ih =>
    simp only [List.pairwise_cons] at distinct
    rcases List.mem_cons.mp member with same | later
    · subst read
      simp [decodeReads, List.lookup_cons]
    · have different : read.name ≠ head.name :=
        (distinct.1 read later).symm
      simp only [decodeReads, List.map_cons, List.lookup_cons]
      have unequal : (read.name == head.name) = false := by simp [different]
      simp only [unequal]
      exact ih distinct.2 later

theorem decodeReads_canonical (reads : List Backend.Impact.Read)
    (witness : Assignment)
    (typed : ∀ read ∈ reads,
      read.ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok ())
    (bounded : ∀ read ∈ reads,
      (witness ("%input_" ++ read.name)).val ≤ sourceMaximum read.ty) :
    ∀ read ∈ reads,
      Canonical read.ty (sourceValue read.ty
        (witness ("%input_" ++ read.name))) ∧
      scalar (ScalarNormalization.number read.ty
        (sourceValue read.ty (witness ("%input_" ++ read.name)))) =
        witness ("%input_" ++ read.name) := by
  intro read member
  exact sourceValue_canonical read.ty (witness ("%input_" ++ read.name))
    (typed read member) (bounded read member)

/-- Relation input bounds plus source type validation build a typed alias
environment for all candidate ledger reads. Native transcript checks still
need to authenticate each candidate against the current state slot. -/
theorem decodedReads_typedEnvironment (reads : List Backend.Impact.Read)
    (hash : Hash) (witness : Assignment)
    (typed : ∀ read ∈ reads,
      read.ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok ())
    (bounded : ∀ read ∈ reads,
      (witness ("%input_" ++ read.name)).val ≤ sourceMaximum read.ty) :
    TypedEnvironment hash witness (readAliases reads)
      (decodeReads reads witness) (readTypes reads) := by
  induction reads with
  | nil =>
    constructor
    · intro name ty raw value lookup _
      simp [readAliases, decodeReads] at lookup
    · intro name ty lookup
      simp [readTypes] at lookup
  | cons read rest ih =>
    have restTyped : ∀ item ∈ rest,
        item.ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok () := by
      intro item member
      exact typed item (by simp [member])
    have restBounded : ∀ item ∈ rest,
        (witness ("%input_" ++ item.name)).val ≤ sourceMaximum item.ty := by
      intro item member
      exact bounded item (by simp [member])
    have previous := ih restTyped restBounded
    obtain ⟨canonical, meaning⟩ := sourceValue_canonical read.ty
      (witness ("%input_" ++ read.name))
      (typed read (by simp)) (bounded read (by simp))
    change TypedEnvironment hash witness
      ((read.name, .input ("%input_" ++ read.name)) :: readAliases rest)
      ((read.name, Value.pack read.ty
        (sourceValue read.ty (witness ("%input_" ++ read.name)))) ::
        decodeReads rest witness)
      ((read.name, read.ty) :: readTypes rest)
    apply TypedEnvironment.cons hash witness (readAliases rest)
      (decodeReads rest witness) (readTypes rest) previous
      read.name read.ty (sourceValue read.ty (witness ("%input_" ++ read.name)))
      (.input ("%input_" ++ read.name)) canonical
    simpa only [interpret_input] using meaning.symm

end Noctium.Verification.GenericStateInputValues
