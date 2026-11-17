import Nightlean.IR

namespace Nightlean.Disclosure

structure Origin where
  name : String
  kind : PrivateOriginKind
  span : SourceSpan
  deriving Repr, BEq

abbrev Origins := List Origin
abbrev Environment := List (String × Origins)

structure Sink where
  description : String
  span : SourceSpan

private def merge (left right : Origins) : Origins := (left ++ right).eraseDups

private def kindName : PrivateOriginKind → String
  | .parameter => "parameter"
  | .provider => "provider result"
  | .privateState => "private-state read"

private def location (span : SourceSpan) : String :=
  s!"{if span.file.isEmpty then "<typed-ir>" else span.file}:{span.line}:{span.column}"

/-- Payload disclosure never clears the separate, active control context.
Structured guards must pass their accumulated predicate origins here. -/
def checkSink (sink : Sink) (payload : Origins) (control : Origins := []) : Except Diagnostic Unit :=
  match control.head?, payload.head? with
  | some origin, _ => .error {span := sink.span, message :=
      s!"undisclosed private control from {kindName origin.kind} '{origin.name}' at {location origin.span} reaches {sink.description}; disclose the controlling value explicitly"}
  | none, some origin => .error {span := sink.span, message :=
      s!"undisclosed private {kindName origin.kind} '{origin.name}' at {location origin.span} reaches {sink.description}; use disclose(...) for the released value"}
  | none, none => .ok ()

/-- Every scalar/native constructor has an explicit rule. Hashing propagates
origins. Missing references fail closed instead of becoming public values. -/
def origins (env : Environment) : Expr ty → Except String Origins
  | .native _ | .bool _ | .uint _ _ => pure []
  | .ref name => match env.lookup name with
    | some result => pure result
    | none => .error s!"missing disclosure origin rule for reference '{name}'"
  | .add a b | .sub a b | .mul a b | .uadd a b | .usub a b | .umul a b
  | .eq a b | .poseidon2 _ a b => do
    pure (merge (← origins env a) (← origins env b))
  | .cast _ value => origins env value
  | .select condition yes no => do
    pure (merge (← origins env condition) (merge (← origins env yes) (← origins env no)))
  | .letE name value body => do
    let value ← origins env value
    origins ((name, value) :: env) body
  | .assertE condition body => do
    discard (origins env condition)
    origins env body
  | .disclose _ value => do
    discard (origins env value)
    pure []

private def expression (env : Environment) (span : SourceSpan) (value : Expr ty) :
    Except Diagnostic Origins :=
  match origins env value with
  | .ok result => .ok result
  | .error message => .error {span, message}

def inputEnvironment (circuit : Circuit) : Except Diagnostic Environment := do
  if !uniqueNames (circuit.inputs.map (·.name)) then
    throw {span := circuit.span, message := "duplicate disclosure input"}
  if !uniqueNames (circuit.privateOrigins.map Prod.fst) then
    throw {span := circuit.span, message := "duplicate declared private origin"}
  for (name, _) in circuit.privateOrigins do
    unless circuit.inputs.any (·.name == name) do
      throw {span := circuit.span, message := s!"private origin '{name}' has no declared input"}
  circuit.inputs.mapM fun input => do
    let declared := circuit.privateOrigins.lookup input.name
    let privateValue := input.visibility == .«private» || declared.isSome
    let result := if privateValue then
      [{name := input.name, kind := declared.getD .parameter, span := input.span}]
      else []
    if input.visibility == .«public» then
      checkSink {description := s!"public input '{input.name}'", span := input.span} result
    pure (input.name, result)

def checkConstraints (env : Environment) (span : SourceSpan) :
    List (Expr .bool) → Except Diagnostic Unit
  | [] => pure ()
  | condition :: rest => do
    discard (expression env span condition)
    checkConstraints env span rest

theorem checkConstraints_literal (env : Environment) (span : SourceSpan) (bit : Bool)
    (rest : List (Expr .bool)) :
    checkConstraints env span (.bool bit :: rest) = checkConstraints env span rest := by rfl

def circuit (value : Circuit) (control : Origins := []) : Except Diagnostic Unit := do
  let env ← inputEnvironment value
  -- Assertions state the intended relation. This pass does not classify proof
  -- success, failure, or timing as ordinary public value-flow sinks.
  checkConstraints env value.span value.constraints
  for output in value.outputs do
    let payload ← expression env output.span output.value
    checkSink {description := s!"public output '{output.name}'", span := output.span} payload control

def entrypoint (value : Entrypoint) (control : Origins := []) : Except Diagnostic Unit := do
  unless value.effectSpans.isEmpty || value.effectSpans.length == value.effects.length do
    throw {span := value.span, message := "effect source-span metadata length mismatch"}
  circuit value.circuit control
  let mut env ← inputEnvironment value.circuit
  for output in value.circuit.outputs do
    env := env ++ [(output.name, [])]
  for (effect, index) in value.effects.zipIdx do
    let span := value.effectSpans[index]?.getD value.span
    let activityControl ← match value.effectGuardAt index, effect with
      | none, _ => pure []
      | some condition, .writeCell .. | some condition, .writeMap .. =>
        expression env span condition
      | some condition, .require _ =>
        discard (expression env span condition)
        pure []
      | some _, _ =>
        throw {span, message := "native guards are supported only on writes and require effects"}
    let activeControl := merge control activityControl
    match effect with
    | .readCell state destination _ =>
      checkSink {description := s!"public cell read '{state}'", span} [] control
      env := env ++ [(destination, [])]
    | .readMap state destination _ _ key =>
      checkSink {description := s!"public map read path '{state}'", span}
        (← expression env span key) control
      env := env ++ [(destination, [])]
    | .readMember state destination _ _ key =>
      checkSink {description := s!"public map membership path '{state}'", span}
        (← expression env span key) control
      env := env ++ [(destination, [])]
    | .require condition => discard (expression env span condition)
    | .writeCell state _ payload =>
      checkSink {description := s!"public cell write '{state}'", span}
        (← expression env span payload) activeControl
    | .writeMap state _ _ key payload =>
      checkSink {description := s!"public map write key '{state}'", span}
        (← expression env span key) activeControl
      checkSink {description := s!"public map write value '{state}'", span}
        (← expression env span payload) activeControl
    | .requireAbsent state _ key =>
      checkSink {description := s!"public map query path '{state}'", span}
        (← expression env span key) control

def contract (value : Contract) : Except Diagnostic Unit := do
  for entry in value.entrypoints do entrypoint entry

theorem disclosed_value_origins (env : Environment) (span : SourceSpan) (value : Expr ty)
    (result : Origins) (h : origins env value = .ok result) :
    origins env (.disclose span value) = .ok [] := by
  simp [origins, h]
  rfl

theorem sink_accepts_iff (sink : Sink) (payload control : Origins) :
    checkSink sink payload control = .ok () ↔ payload = [] ∧ control = [] := by
  cases payload <;> cases control <;> simp [checkSink]

theorem payload_release_preserves_control_rejection (sink : Sink) (origin : Origin) (rest : Origins) :
    checkSink sink [] (origin :: rest) ≠ .ok () := by simp [checkSink]

end Nightlean.Disclosure
