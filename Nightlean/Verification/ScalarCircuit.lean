import Nightlean.Verification.ScalarNormalizationSoundness
import Nightlean.Backend.Zkir

namespace Nightlean.Verification.ScalarNormalization
open Backend.Native NativeRelation

private theorem bind_ok (first : Except ε α) (next : α → Except ε β) (value : β) :
    Except.bind first next = .ok value ↔ ∃ intermediate, first = .ok intermediate ∧ next intermediate = .ok value := by
  cases first <;> simp [Except.bind]

private theorem mapM_ok_transfer (left : α → Except ε β) (right : α → Except δ β)
    (agreement : ∀ value result, left value = .ok result ↔ right value = .ok result)
    (values : List α) (results : List β) :
    values.mapM left = .ok results ↔ values.mapM right = .ok results := by
  induction values generalizing results with
  | nil => simp [List.mapM_nil, pure, Except.pure]
  | cons value rest ih =>
    simp only [List.mapM_cons, bind, bind_ok]
    simp only [agreement, ih, pure, Except.pure, Except.ok.injEq]

private theorem forIn_all (body : α → PUnit → Except ε (ForInStep PUnit)) (values : List α)
    (actions : ∀ value ∈ values, body value .unit = .ok (.yield .unit)) :
    forIn values PUnit.unit body = .ok .unit := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    rw [List.forIn_cons, actions value (by simp)]
    change forIn rest PUnit.unit body = .ok .unit
    exact ih (fun value member => actions value (List.mem_cons_of_mem _ member))

private theorem forIn_extract (body : α → PUnit → Except ε (ForInStep PUnit))
    (property : α → Prop) (values : List α)
    (actions : ∀ value step, body value .unit = .ok step → step = .yield .unit ∧ property value)
    (success : forIn values PUnit.unit body = .ok .unit) : ∀ value ∈ values, property value := by
  induction values with
  | nil => simp
  | cons value rest ih =>
    rw [List.forIn_cons] at success
    cases checked : body value .unit with
    | error message => simp [checked, bind, Except.bind] at success
    | ok step =>
      obtain ⟨equal, holds⟩ := actions value step checked
      subst step
      simp only [checked, bind, Except.bind] at success
      intro found member
      rcases List.mem_cons.mp member with equal | member
      · simpa [equal] using holds
      · exact ih success found member

def circuitAliases (circuit : Circuit) : AliasEnvironment :=
  circuit.inputs.map (fun input => (input.name, .input ("%input_" ++ input.name)))

/-- Invert the actual independent expected-statement constructor. -/
theorem expectedCircuit_parts (circuit : Circuit) (expected : Expected)
    (accepted : expectedCircuit circuit = .ok expected) :
    circuit.validate {poseidon2 := true} = .ok () ∧
    ∃ (conditions outputs : List Normalized),
      circuit.constraints.mapM (normalize (circuitAliases circuit)) = .ok conditions ∧
      circuit.outputs.mapM (fun output => normalize (circuitAliases circuit) output.value) = .ok outputs ∧
      expected.assertions = conditions.flatMap (fun normalized => normalized.assertions ++ [normalized.term]) ++ outputs.flatMap (·.assertions) ∧
      expected.bounds = conditions.flatMap (·.bounds) ++ outputs.flatMap (·.bounds) ∧
      expected.returns = outputs.map (·.term) ∧
      expected.groups = (circuit.inputs.filter (·.visibility == .«public»)).map
        (fun input => [Term.input ("%input_" ++ input.name)]) ++
          (if outputs.isEmpty then [] else [outputs.map (·.term)]) ∧
      expected.inputs = circuit.inputs.map (fun input =>
        {identifier := "%input_" ++ input.name, visibility := input.visibility, ty := input.ty}) ∧
      expected.mode = .relation := by
  simp only [expectedCircuit, bind, bind_ok, Except.pure] at accepted
  rcases accepted with ⟨_, validation, _, disclosure, collected, collectSuccess, conditions,
    conditionSuccess, outputs, outputSuccess, equal⟩
  have collection := (convert_ok _ _ _).mp collectSuccess
  simp only [collect_eq, bind, bind_ok, Except.pure] at collection
  rcases collection with ⟨collectedResults, collectedSuccess, collectedEqual⟩
  have conditionsSuccess := (convert_ok _ _ _).mp conditionSuccess
  rw [conditionsSuccess] at collectedSuccess
  cases collectedSuccess
  cases collectedEqual
  cases equal
  refine ⟨validation, conditions, outputs, ?_, ?_, rfl, rfl, rfl, ?_, rfl, rfl⟩
  · simpa only [inputAliases_source, circuitAliases] using conditionsSuccess
  · apply (mapM_ok_transfer _ _ _ _ _).mp outputSuccess
    intro output normalized
    rw [convert_ok]
    simp only [inputAliases_source, circuitAliases]
  · simp only [List.isEmpty_map, inputRequirement_eq, List.filter_map, List.map_map, Function.comp_apply]
    rfl

private theorem constraints_sound (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (types : TypeEnv) (aliases : AliasEnvironment) (values : EvalEnv)
    (environment : TypedEnvironment hash inputs aliases values types)
    (span : SourceSpan) (conditions : List (Expr .bool)) (normalized : List Normalized)
    (valid : validateConstraints {poseidon2 := true} types span conditions = .ok ())
    (normal : conditions.mapM (normalize aliases) = .ok normalized)
    (bounds : ∀ requirement ∈ normalized.flatMap (·.bounds),
      (interpret hash inputs requirement.1).val ≤ requirement.2)
    (assertions : ∀ term ∈ normalized.flatMap (fun result => result.assertions ++ [result.term]),
      interpret hash inputs term = one) :
    runConstraints ctx values conditions = .ok () := by
  induction conditions generalizing normalized with
  | nil => rfl
  | cons condition rest ih =>
    simp only [List.mapM_cons, bind, bind_ok, Except.pure] at normal
    rcases normal with ⟨cn, nc, tail, tailNormal, equal⟩
    cases equal
    have conditionValid : condition.validate {poseidon2 := true} types = .ok () := by
      cases checked : condition.validate {poseidon2 := true} types with
      | error message => simp [validateConstraints, checked] at valid
      | ok result => cases result; rfl
    have restValid : validateConstraints {poseidon2 := true} types span rest = .ok () := by
      simpa [validateConstraints, conditionValid] using valid
    have requirements : Requirements hash inputs cn := by
      constructor
      · intro requirement member
        exact bounds requirement (by simp [List.mem_flatMap, member])
      · intro term member
        exact assertions term (by simp [List.mem_flatMap, member])
    obtain ⟨value, success, canonical, required, meaning⟩ := normalize_sound ctx hash implementation inputs types aliases values
      environment condition cn conditionValid nc requirements
    have asserted : interpret hash inputs cn.term = one := assertions cn.term (by simp)
    have trueValue : value = true := by
      rw [meaning] at asserted
      cases value
      · exact False.elim (zero_ne_one (by simpa using asserted))
      · rfl
    subst value
    simp only [runConstraints, success]
    apply ih tail restValid tailNormal
    · intro requirement member
      exact bounds requirement (by simp [List.mem_flatMap] at member ⊢; exact Or.inr member)
    · intro term member
      exact assertions term (by simp [List.mem_flatMap] at member ⊢; exact Or.inr (Or.inr member))

def valueNumber : Value → Nat
  | .native value | .uint _ value => value
  | .bool value => if value then 1 else 0

@[simp] theorem valueNumber_pack (ty : Ty) (value : ty.Denote) :
    valueNumber (Value.pack ty value) = number ty value := by
  cases ty <;> rfl

def evalOutput (ctx : EvalContext) (values : EvalEnv) (output : Output) : Except String (String × Value) := do
  pure (output.name, Value.pack output.ty (← output.value.eval ctx values))

private theorem outputs_sound (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (types : TypeEnv) (aliases : AliasEnvironment) (values : EvalEnv)
    (environment : TypedEnvironment hash inputs aliases values types)
    (outputs : List Output) (normalized : List Normalized)
    (valid : ∀ output ∈ outputs, output.value.validate {poseidon2 := true} types = .ok ())
    (normal : outputs.mapM (fun output => normalize aliases output.value) = .ok normalized)
    (bounds : ∀ requirement ∈ normalized.flatMap (·.bounds),
      (interpret hash inputs requirement.1).val ≤ requirement.2)
    (assertions : ∀ term ∈ normalized.flatMap (·.assertions), interpret hash inputs term = one) :
    ∃ result, outputs.mapM (evalOutput ctx values) = .ok result ∧
      result.map Prod.fst = outputs.map (·.name) ∧
      result.map (fun pair => scalar (valueNumber pair.2)) = normalized.map (fun output => interpret hash inputs output.term) := by
  induction outputs generalizing normalized with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at normal
    subst normalized
    exact ⟨[], rfl, rfl, rfl⟩
  | cons output rest ih =>
    simp only [List.mapM_cons, bind, bind_ok] at normal
    rcases normal with ⟨on, no, tail, tailNormal, equal⟩
    cases equal
    have requirements : Requirements hash inputs on := by
      constructor
      · intro requirement member
        exact bounds requirement (by simp [List.mem_flatMap, member])
      · intro term member
        exact assertions term (by simp [List.mem_flatMap, member])
    obtain ⟨value, success, canonical, required, meaning⟩ := normalize_sound ctx hash implementation inputs types aliases values
      environment output.value on (valid output (by simp)) no requirements
    obtain ⟨result, resultSuccess, names, resultMeaning⟩ := ih tail
      (fun found member => valid found (List.mem_cons_of_mem _ member)) tailNormal
      (fun requirement member => bounds requirement (by simp [List.mem_flatMap] at member ⊢; exact Or.inr member))
      (fun term member => assertions term (by simp [List.mem_flatMap] at member ⊢; exact Or.inr member))
    refine ⟨(output.name, Value.pack output.ty value) :: result, ?_, ?_, ?_⟩
    · simp only [List.mapM_cons, evalOutput, success, bind, Except.bind, pure, Except.pure, resultSuccess]
    · simp only [List.map_cons, names]
    · simp only [List.map_cons, valueNumber_pack, resultMeaning, meaning]

theorem circuit_validation_parts (circuit : Circuit)
    (valid : circuit.validate {poseidon2 := true} = .ok ()) :
    validateConstraints {poseidon2 := true} (circuit.inputs.map (fun input => (input.name, input.ty))) circuit.span circuit.constraints = .ok () ∧
    ∀ output ∈ circuit.outputs, output.value.validate {poseidon2 := true}
      (circuit.inputs.map (fun input => (input.name, input.ty))) = .ok () := by
  cases inputNames : uniqueNames (circuit.inputs.map (·.name)) with
  | false => simp [Circuit.validate, inputNames, bind, Except.bind] at valid
  | true =>
    cases outputNames : uniqueNames (circuit.outputs.map (·.name)) with
    | false => simp [Circuit.validate, inputNames, outputNames, bind, Except.bind] at valid
    | true =>
      simp only [Circuit.validate, inputNames, outputNames, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at valid
      simp only [bind, bind_ok] at valid
      rcases valid with ⟨_, inputChecks, _, constraints, _, outputChecks, finish⟩
      refine ⟨constraints, ?_⟩
      refine forIn_extract _ (fun output => output.value.validate {poseidon2 := true}
        (circuit.inputs.map (fun input => (input.name, input.ty))) = .ok ()) circuit.outputs ?_ outputChecks
      intro output step success
      cases typeChecked : output.ty.validate {poseidon2 := true} with
      | error message => simp [typeChecked, bind, Except.bind] at success
      | ok result =>
        simp only [typeChecked] at success
        split at success
        next shadow => cases success
        next unshadowed =>
          cases expressionChecked : output.value.validate {poseidon2 := true}
              (circuit.inputs.map (fun input => (input.name, input.ty))) with
          | error message => simp [expressionChecked, bind, Except.bind] at success
          | ok result =>
            simp only [expressionChecked] at success
            cases success
            exact ⟨rfl, by cases result; rfl⟩

/-- Input admission is the executable source preflight plus field-level input
agreement. No source constraints or outputs occur in these premises. -/
structure CanonicalInputs (circuit : Circuit) (values : EvalEnv) (inputs : Assignment) : Prop where
  unique : uniqueNames (values.map Prod.fst) = true
  declared : ∀ name raw, (name, raw) ∈ values → ∃ input ∈ circuit.inputs, input.name = name
  complete : ∀ input ∈ circuit.inputs, ∃ value : input.ty.Denote,
    values.lookup input.name = some (Value.pack input.ty value) ∧ Canonical input.ty value
  binding : ∀ input ∈ circuit.inputs, ∀ value : input.ty.Denote,
    values.lookup input.name = some (Value.pack input.ty value) →
      inputs ("%input_" ++ input.name) = scalar (number input.ty value)

private theorem lookup_member (values : List (String × α)) (name : String) (value : α)
    (lookup : values.lookup name = some value) : (name, value) ∈ values := by
  obtain ⟨before, after, equal, _⟩ := List.lookup_eq_some_iff.mp lookup
  rw [equal]
  simp

theorem aliases_lookup (inputs : List Input) (name : String)
    (member : ∃ input ∈ inputs, input.name = name) :
    (inputs.map (fun input => (input.name, Term.input ("%input_" ++ input.name)))).lookup name =
      some (.input ("%input_" ++ name)) := by
  induction inputs with
  | nil => simpa using member
  | cons input rest ih =>
    by_cases same : name = input.name
    · simp [same]
    · have unequal : (name == input.name) = false := by simp [same]
      simp only [List.map_cons, List.lookup_cons, unequal]
      apply ih
      obtain ⟨found, foundMember, foundName⟩ := member
      rcases List.mem_cons.mp foundMember with equal | foundMember
      · subst found
        exact False.elim (same foundName.symm)
      · exact ⟨found, foundMember, foundName⟩

private theorem packed_as_canonical (ty found : Ty) (value : ty.Denote) (result : found.Denote)
    (canonical : Canonical ty value) (typed : (Value.pack ty value).as found = some result) :
    Canonical found result ∧ number found result = number ty value := by
  cases ty <;> cases found <;> simp_all [Value.pack, Value.as]
  rcases typed with ⟨rfl, _⟩
  exact ⟨canonical, rfl⟩

/-- Establish alias and range invariants from input admission, including the
normalizer's concrete `%input_` alias construction. -/
theorem CanonicalInputs.typedEnvironment (circuit : Circuit) (values : EvalEnv) (inputs : Assignment)
    (admitted : CanonicalInputs circuit values inputs) (hash : Hash) :
    TypedEnvironment hash inputs (circuitAliases circuit) values
      (circuit.inputs.map (fun input => (input.name, input.ty))) := by
  constructor
  · intro name ty raw value lookup typed
    obtain ⟨input, member, inputName⟩ := admitted.declared name raw (lookup_member _ _ _ lookup)
    obtain ⟨inputValue, inputLookup, canonical⟩ := admitted.complete input member
    have rawEqual : raw = Value.pack input.ty inputValue := by
      rw [inputName] at inputLookup
      rw [lookup] at inputLookup
      exact Option.some.inj inputLookup
    subst raw
    obtain ⟨canonicalFound, numberFound⟩ := packed_as_canonical _ _ _ _ canonical typed
    refine ⟨canonicalFound, .input ("%input_" ++ name), ?_, ?_⟩
    · exact aliases_lookup _ _ ⟨input, member, inputName⟩
    · simp only [interpret_input]
      rw [← inputName, admitted.binding input member inputValue inputLookup, numberFound]
  · intro name ty lookup
    have member := lookup_member _ _ _ lookup
    obtain ⟨input, inputMember, pairEqual⟩ := List.mem_map.mp member
    have inputName : input.name = name := congrArg Prod.fst pairEqual
    have inputTy : input.ty = ty := congrArg Prod.snd pairEqual
    obtain ⟨value, rawLookup, canonical⟩ := admitted.complete input inputMember
    subst ty
    exact ⟨Value.pack input.ty value, value, by simpa [inputName] using rawLookup, number_pack_as _ _⟩

private theorem bind_ok_intro (first : Except ε α) (next : α → Except ε β) (value : α) (result : β)
    (checked : first = .ok value) (rest : next value = .ok result) :
    Except.bind first next = .ok result := by
  rw [checked]
  exact rest

private theorem circuit_run_preflight (ctx : EvalContext) (modulus : ctx.modulus = Field.modulus)
    (circuit : Circuit) (values result : EvalEnv) (inputs : Assignment)
    (admitted : CanonicalInputs circuit values inputs)
    (valid : circuit.validate {poseidon2 := true} = .ok ())
    (constraints : runConstraints ctx values circuit.constraints = .ok ())
    (outputs : circuit.outputs.mapM (evalOutput ctx values) = .ok result) :
    circuit.run ctx values = .ok result := by
  have validation : circuit.validate {nativeModulus := ctx.modulus, poseidon2 := true} = .ok () := by
    simpa only [modulus] using valid
  simp only [Circuit.run, validation, admitted.unique, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  refine bind_ok_intro _ _ PUnit.unit _ ?_ ?_
  · apply forIn_all
    intro pair member
    obtain ⟨input, inputMember, inputName⟩ := admitted.declared pair.1 pair.2 member
    have declared : (circuit.inputs.any (fun input => input.name == pair.1)) = true := by
      apply List.any_eq_true.mpr
      exact ⟨input, inputMember, by simp [inputName]⟩
    simp only [declared, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rfl
  · refine bind_ok_intro _ _ PUnit.unit _ ?_ ?_
    · apply forIn_all
      intro input member
      rcases input with ⟨name, ty, visibility, span⟩
      obtain ⟨value, lookup, canonical⟩ := admitted.complete _ member
      simp only [lookup, number_pack_as, canonical_eq]
      cases ty with
      | native =>
        have bound : value < ctx.modulus := by simpa [modulus, number] using canonical.1
        simp [bound] <;> rfl
      | bool => rfl
      | uint maximum =>
        have bound : value < ctx.modulus := by simpa [modulus, number] using canonical.1
        simp [canonical.2.1, canonical.2.2, bound] <;> rfl
    · change Except.bind (runConstraints ctx values circuit.constraints)
        (fun _ => circuit.outputs.mapM (evalOutput ctx values)) = .ok result
      rw [constraints]
      exact outputs

/-- Independent statement semantics imply successful execution of the original
source circuit and its exact return and always-active Impact group values. -/
theorem expectedCircuit_sound (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (circuit : Circuit) (values : EvalEnv) (expected : Expected)
    (admitted : CanonicalInputs circuit values inputs)
    (accepted : expectedCircuit circuit = .ok expected)
    (bounds : ∀ requirement ∈ expected.bounds, (interpret hash inputs requirement.1).val ≤ requirement.2)
    (assertions : ∀ term ∈ expected.assertions, interpret hash inputs term = one) :
    ∃ result, circuit.run ctx values = .ok result ∧
      result.map Prod.fst = circuit.outputs.map (·.name) ∧
      result.map (fun pair => scalar (valueNumber pair.2)) = expected.returns.map (interpret hash inputs) ∧
      expected.groups.map (fun group => group.map (interpret hash inputs)) =
        (circuit.inputs.filter (·.visibility == .«public»)).map
          (fun input => [inputs ("%input_" ++ input.name)]) ++
        (if result.isEmpty then [] else [result.map (fun pair => scalar (valueNumber pair.2))]) := by
  obtain ⟨validation, conditions, outputs, conditionNormals, outputNormals, assertionShape, boundShape,
    returnShape, groupShape, inputShape, modeShape⟩ := expectedCircuit_parts circuit expected accepted
  have environment := admitted.typedEnvironment circuit values inputs hash
  obtain ⟨conditionValidation, outputValidation⟩ := circuit_validation_parts circuit validation
  have constraintSuccess := constraints_sound ctx hash implementation inputs _ _ values environment
    circuit.span circuit.constraints conditions conditionValidation conditionNormals
    (fun requirement member => bounds requirement (by rw [boundShape]; exact List.mem_append_left _ member))
    (fun term member => assertions term (by rw [assertionShape]; exact List.mem_append_left _ member))
  obtain ⟨result, outputSuccess, names, outputMeaning⟩ := outputs_sound ctx hash implementation inputs _ _ values environment
    circuit.outputs outputs outputValidation outputNormals
    (fun requirement member => bounds requirement (by rw [boundShape]; exact List.mem_append_right _ member))
    (fun term member => assertions term (by rw [assertionShape]; exact List.mem_append_right _ member))
  refine ⟨result, circuit_run_preflight ctx implementation.modulus circuit values result inputs admitted validation
    constraintSuccess outputSuccess, names, ?_, ?_⟩
  · simpa only [returnShape, List.map_map, Function.comp_def] using outputMeaning
  · rw [groupShape]
    simp only [List.map_append, List.map_map, Function.comp_def, List.map_cons, List.map_nil, interpret_input]
    have empty : outputs.isEmpty = result.isEmpty := by
      have same := congrArg List.isEmpty outputMeaning
      simpa only [List.isEmpty_map] using same.symm
    rw [empty]
    split <;> simp [List.map_map, Function.comp_def, interpret_input, ← outputMeaning]


theorem circuit_run_steps (ctx : EvalContext) (circuit : Circuit) (values result : EvalEnv)
    (success : circuit.run ctx values = .ok result) :
    runConstraints ctx values circuit.constraints = .ok () ∧
      circuit.outputs.mapM (evalOutput ctx values) = .ok result := by
  cases validation : circuit.validate {nativeModulus := ctx.modulus, poseidon2 := true} with
  | error diagnostic => simp [Circuit.run, validation, bind, Except.bind] at success
  | ok value =>
    cases unique : uniqueNames (values.map Prod.fst) with
    | false => simp [Circuit.run, validation, unique, bind, Except.bind] at success
    | true =>
      simp only [Circuit.run, validation, unique, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        bind, bind_ok] at success
      rcases success with ⟨_, declared, _, checked, unit, constraints, output⟩
      cases unit
      exact ⟨constraints, output⟩

private theorem constraints_complete (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (aliases : AliasEnvironment) (values : EvalEnv)
    (agreement : AliasAgreement hash inputs aliases values)
    (conditions : List (Expr .bool)) (normalized : List Normalized)
    (normal : conditions.mapM (normalize aliases) = .ok normalized)
    (success : runConstraints ctx values conditions = .ok ()) :
    (∀ requirement ∈ normalized.flatMap (·.bounds), (interpret hash inputs requirement.1).val ≤ requirement.2) ∧
    (∀ term ∈ normalized.flatMap (fun result => result.assertions ++ [result.term]), interpret hash inputs term = one) := by
  induction conditions generalizing normalized with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at normal
    subst normalized
    simp
  | cons condition rest ih =>
    cases conditionResult : condition.eval ctx values with
    | error message => simp [runConstraints, conditionResult] at success
    | ok result =>
      cases result with
      | false => simp [runConstraints, conditionResult] at success
      | true =>
        have restSuccess : runConstraints ctx values rest = .ok () := by
          simpa only [runConstraints, conditionResult] using success
        simp only [List.mapM_cons, bind, bind_ok] at normal
        rcases normal with ⟨cn, nc, tail, nt, equal⟩
        cases equal
        obtain ⟨actual, actualNormal, canonical, requirements, meaning⟩ := normalize_success ctx hash implementation inputs
          aliases values agreement condition true conditionResult
        rw [nc] at actualNormal
        cases actualNormal
        obtain ⟨tailBounds, tailAssertions⟩ := ih tail nt restSuccess
        constructor
        · intro requirement member
          simp only [List.flatMap_cons, List.mem_append] at member
          rcases member with member | member
          · exact requirements.1 requirement member
          · exact tailBounds requirement member
        · intro term member
          simp only [List.flatMap_cons, List.mem_append, List.mem_singleton] at member
          rcases member with (member | equal) | member
          · exact requirements.2 term member
          · subst term
            simpa using meaning
          · exact tailAssertions term member

private theorem outputs_complete (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (aliases : AliasEnvironment) (values : EvalEnv)
    (agreement : AliasAgreement hash inputs aliases values)
    (outputs : List Output) (normalized : List Normalized) (result : EvalEnv)
    (normal : outputs.mapM (fun output => normalize aliases output.value) = .ok normalized)
    (success : outputs.mapM (evalOutput ctx values) = .ok result) :
    (∀ requirement ∈ normalized.flatMap (·.bounds), (interpret hash inputs requirement.1).val ≤ requirement.2) ∧
    (∀ term ∈ normalized.flatMap (·.assertions), interpret hash inputs term = one) := by
  induction outputs generalizing normalized result with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at normal
    subst normalized
    simp
  | cons output rest ih =>
    simp only [List.mapM_cons, bind, bind_ok] at normal success
    rcases normal with ⟨on, no, tail, nt, equal⟩
    cases equal
    rcases success with ⟨first, firstResult, remaining, tailResult, equal⟩
    simp only [evalOutput, bind, bind_ok] at firstResult
    rcases firstResult with ⟨value, evaluation, equal⟩
    obtain ⟨actual, actualNormal, canonical, requirements, meaning⟩ := normalize_success ctx hash implementation inputs
      aliases values agreement output.value value evaluation
    rw [no] at actualNormal
    cases actualNormal
    obtain ⟨tailBounds, tailAssertions⟩ := ih tail remaining nt tailResult
    constructor
    · intro requirement member
      simp only [List.flatMap_cons, List.mem_append] at member
      rcases member with member | member
      · exact requirements.1 requirement member
      · exact tailBounds requirement member
    · intro term member
      simp only [List.flatMap_cons, List.mem_append] at member
      rcases member with member | member
      · exact requirements.2 term member
      · exact tailAssertions term member

/-- Successful source execution satisfies every requirement of the actual
expected-statement constructor. Native witness existence remains a separate
lowerer completeness obligation. -/
theorem expectedCircuit_complete (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (circuit : Circuit) (values result : EvalEnv) (expected : Expected)
    (admitted : CanonicalInputs circuit values inputs)
    (accepted : expectedCircuit circuit = .ok expected)
    (success : circuit.run ctx values = .ok result) :
    (∀ requirement ∈ expected.bounds, (interpret hash inputs requirement.1).val ≤ requirement.2) ∧
    (∀ term ∈ expected.assertions, interpret hash inputs term = one) := by
  obtain ⟨validation, conditions, outputs, conditionNormals, outputNormals, assertionShape, boundShape,
    returnShape, groupShape, inputShape, modeShape⟩ := expectedCircuit_parts circuit expected accepted
  obtain ⟨conditionSuccess, outputSuccess⟩ := circuit_run_steps ctx circuit values result success
  have environment := admitted.typedEnvironment circuit values inputs hash
  obtain ⟨conditionBounds, conditionAssertions⟩ := constraints_complete ctx hash implementation inputs _ values
    environment.aliases circuit.constraints conditions conditionNormals conditionSuccess
  obtain ⟨outputBounds, outputAssertions⟩ := outputs_complete ctx hash implementation inputs _ values
    environment.aliases circuit.outputs outputs result outputNormals outputSuccess
  constructor
  · intro requirement member
    rw [boundShape] at member
    rcases List.mem_append.mp member with member | member
    · exact conditionBounds requirement member
    · exact outputBounds requirement member
  · intro term member
    rw [assertionShape] at member
    rcases List.mem_append.mp member with member | member
    · exact conditionAssertions term member
    · exact outputAssertions term member

end Nightlean.Verification.ScalarNormalization
