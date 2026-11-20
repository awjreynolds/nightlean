import Noctium.IR

namespace Noctium.Disclosure

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
  | .bytesField value _ | .bytesAt value _ => origins env value
  | .bytesLiteral _ _ => pure []
  | .reverseBytes value | .sliceBytes value .. => origins env value
  | .concatBytes left right => do
    pure (merge (← origins env left) (← origins env right))
  | .sha512 value | .keccak256 value => origins env value
  | .reverseBytes32 value => origins env value
  | .persistentHash32 value => origins env value
  | .bytes32Literal _ => pure []
  | .persistentHashVector32 values => do
    let mut result : Origins := []
    for value in values do result := merge result (← origins env value)
    pure result
  | .persistentHashNative value => origins env value
  | .persistentHashNativeVector values | .transientHash values => do
    let mut result : Origins := []
    for value in values do result := merge result (← origins env value)
    pure result
  | .toBytes32 value => origins env value
  | .fromBytes32 value => origins env value
  | .fromBytes value => origins env value
  | .jubjubScalarFromNative value | .jubjubMulGenerator value => origins env value
  | .jubjubScalarToNative value | .jubjubNeg value => origins env value
  | .jubjubCoordinate value _ => origins env value
  | .jubjubMul point scalar => do
    pure (merge (← origins env point) (← origins env scalar))
  | .jubjubAdd left right => do
    pure (merge (← origins env left) (← origins env right))
  | .jubjubFromCoordinates x y => do
    pure (merge (← origins env x) (← origins env y))
  | .hashToCurve values => do
    let mut result : Origins := []
    for value in values do result := merge result (← origins env value)
    pure result
  | .foreignBase _ _ | .foreignScalar _ _ | .foreignIdentity _ => pure []
  | .foreignEncodedField value _ => origins env value
  | .foreignUnary _ value | .foreignToBytes value => origins env value
  | .foreignBinary _ left right => do
    pure (merge (← origins env left) (← origins env right))
  | .foreignFromBytes _ value => origins env value
  | .boolAnd left right | .boolOr left right | .boolXor left right => do
    pure (merge (← origins env left) (← origins env right))
  | .ref name => match env.lookup name with
    | some result => pure result
    | none => .error s!"missing disclosure origin rule for reference '{name}'"
  | .add a b | .sub a b | .mul a b | .uadd a b | .usub a b | .umul a b
  | .eq a b | .poseidon2 _ a b => do
    pure (merge (← origins env a) (← origins env b))
  | .inv value => origins env value
  | .copyValue value | .cast _ value => origins env value
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

private theorem expression_bool (env : Environment) (span : SourceSpan) (bit : Bool) :
    expression env span (.bool bit) = .ok [] := by
  unfold expression
  rw [origins.eq_2]
  rfl

private def pathExpression (env : Environment) (span : SourceSpan)
    (keys : List PathKey) : Except Diagnostic Origins := do
  let mut result : Origins := []
  for key in keys do
    match key with
    | .mk _ value => result := merge result (← expression env span value)
  pure result

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
    checkConstraints env span (.bool bit :: rest) = checkConstraints env span rest := by
  change (do discard (expression env span (.bool bit)); checkConstraints env span rest) = _
  rw [expression_bool]
  simp [Except.map, Except.bind, Bind.bind, Functor.discard, Functor.mapConst]

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
      | some condition, .readCell .. | some condition, .readMap .. | some condition, .readMember ..
      | some condition, .readContractAddress ..
      | some condition, .writeCell .. | some condition, .writeMap ..
      | some condition, .readTokenBalance ..
      | some condition, .claimContractCall .. | some condition, .mintShielded ..
      | some condition, .mintUnshielded .. | some condition, .incUnshieldedInputs ..
      | some condition, .incUnshieldedOutputs .. | some condition, .claimUnshieldedCoinSpend ..
      | some condition, .requireContractCaller ..
      | some condition, .emitEvent ..
      | some condition, .readPath .. | some condition, .memberPath ..
      | some condition, .insertPath .. | some condition, .writePath ..
      | some condition, .readCompositePath .. | some condition, .writeCompositePath ..
      | some condition, .emptyMapPath .. | some condition, .counterRead ..
      | some condition, .counterAdjust .. | some condition, .counterReset ..
      | some condition, .removePath ..
      | some condition, .listLength .. | some condition, .listHead ..
      | some condition, .listPushFront .. | some condition, .listPopFront ..
      | some condition, .listReset .. | some condition, .merkleTreeIsFull ..
      | some condition, .merkleTreeInsertHash .. | some condition, .merkleTreeReset .. =>
        expression env span condition
      | some condition, .require _ =>
        discard (expression env span condition)
        pure []
      | some _, _ =>
        throw {span, message := "native guards are supported only on ledger reads, writes, and require effects"}
    let activeControl := merge control activityControl
    match effect with
    | .readCell state destination _ =>
      if value.effectGuardAt index |>.isSome then
        checkSink {description := s!"public state read guard '{state}'", span} [] activeControl
      checkSink {description := s!"public cell read '{state}'", span} [] control
      env := env ++ [(destination, [])]
    | .readMap state destination _ _ key =>
      if value.effectGuardAt index |>.isSome then
        checkSink {description := s!"public map read guard '{state}'", span} [] activeControl
      checkSink {description := s!"public map read path '{state}'", span}
        (← expression env span key) activeControl
      env := env ++ [(destination, [])]
    | .readMember state destination _ _ key =>
      if value.effectGuardAt index |>.isSome then
        checkSink {description := s!"public map membership guard '{state}'", span} [] activeControl
      checkSink {description := s!"public map membership path '{state}'", span}
        (← expression env span key) activeControl
      env := env ++ [(destination, [])]
    | .readContractAddress destination =>
      if value.effectGuardAt index |>.isSome then
        checkSink {description := "public contract address read guard", span} [] activeControl
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
    | .claimContractCall address entryPointHash commitment =>
      checkSink {description := "contract-call claim address", span}
        (← expression env span address) activeControl
      checkSink {description := "contract-call claim entrypoint hash", span}
        (← expression env span entryPointHash) activeControl
      checkSink {description := "contract-call claim commitment", span}
        (← expression env span commitment) activeControl
    | .mintShielded domain amount =>
      let sink := {description := "public shielded mint", span}
      checkSink sink (← expression env span domain) activeControl
      checkSink sink (← expression env span amount) activeControl
    | .mintUnshielded domain amount =>
      let sink := {description := "public unshielded mint", span}
      checkSink sink (← expression env span domain) activeControl
      checkSink sink (← expression env span amount) activeControl
    | .incUnshieldedInputs color amount isUnshielded =>
      let sink := {description := "public unshielded input", span}
      checkSink sink (← expression env span color) activeControl
      checkSink sink (← expression env span amount) activeControl
      checkSink sink (← expression env span isUnshielded) activeControl
    | .incUnshieldedOutputs color amount isUnshielded =>
      let sink := {description := "public unshielded output", span}
      checkSink sink (← expression env span color) activeControl
      checkSink sink (← expression env span amount) activeControl
      checkSink sink (← expression env span isUnshielded) activeControl
    | .claimUnshieldedCoinSpend color amount isUnshielded isContract recipient =>
      let sink := {description := "public unshielded spend claim", span}
      checkSink sink (← expression env span color) activeControl
      checkSink sink (← expression env span amount) activeControl
      checkSink sink (← expression env span isUnshielded) activeControl
      checkSink sink (← expression env span isContract) activeControl
      checkSink sink (← expression env span recipient) activeControl
    | .requireContractCaller address =>
      checkSink {description := "required contract caller", span}
        (← expression env span address) activeControl
    | .readTokenBalance destination color isUnshielded query =>
      let sink := {description := "public token balance read", span}
      checkSink sink (← expression env span color) activeControl
      checkSink sink (← expression env span isUnshielded) activeControl
      if let .compare _ limit := query then
        checkSink sink (← expression env span limit) activeControl
      env := env ++ [(destination, [])]
    | .emitEvent _ payload =>
      checkSink {description := "public contract event", span}
        (← expression env span payload) activeControl
    | .requireAbsent state _ key =>
      checkSink {description := s!"public map query path '{state}'", span}
        (← expression env span key) control
    | .readPath state destination keys _ =>
      if value.effectGuardAt index |>.isSome then
        checkSink {description := s!"public nested map read guard '{state}'", span} [] activeControl
      checkSink {description := s!"public nested map read path '{state}'", span}
        (← pathExpression env span keys) activeControl
      env := env ++ [(destination, [])]
    | .readCompositePath state _ keys _ destinations =>
      if value.effectGuardAt index |>.isSome then
        checkSink {description := s!"public nested composite read guard '{state}'", span} [] activeControl
      checkSink {description := s!"public nested composite read path '{state}'", span}
        (← pathExpression env span keys) activeControl
      env := env ++ destinations.map fun destination => (destination, [])
    | .memberPath state destination keys =>
      if value.effectGuardAt index |>.isSome then
        checkSink {description := s!"public nested map membership guard '{state}'", span} [] activeControl
      checkSink {description := s!"public nested map membership path '{state}'", span}
        (← pathExpression env span keys) activeControl
      env := env ++ [(destination, [])]
    | .counterRead state destination keys =>
      if value.effectGuardAt index |>.isSome then
        checkSink {description := s!"public Counter read guard '{state}'", span} [] activeControl
      checkSink {description := s!"public Counter read path '{state}'", span}
        (← pathExpression env span keys) activeControl
      env := env ++ [(destination, [])]
    | .counterAdjust state keys .. | .counterReset state keys =>
      checkSink {description := s!"public Counter mutation path '{state}'", span}
        (← pathExpression env span keys) activeControl
    | .listLength state destination keys =>
      if value.effectGuardAt index |>.isSome then
        checkSink {description := s!"public List length guard '{state}'", span} [] activeControl
      checkSink {description := s!"public List length path '{state}'", span}
        (← pathExpression env span keys) activeControl
      env := env ++ [(destination, [])]
    | .listHead state _ keys _ destinations =>
      if value.effectGuardAt index |>.isSome then
        checkSink {description := s!"public List head guard '{state}'", span} [] activeControl
      checkSink {description := s!"public List head path '{state}'", span}
        (← pathExpression env span keys) activeControl
      env := env ++ destinations.map fun destination => (destination, [])
    | .listPushFront state keys _ payloads =>
      checkSink {description := s!"public List push path '{state}'", span}
        (← pathExpression env span keys) activeControl
      for (payload, index) in payloads.zipIdx do
        checkSink {description := s!"public List push field {index} of '{state}'", span}
          (← expression env span payload) activeControl
    | .listPopFront state keys | .listReset state keys =>
      checkSink {description := s!"public List mutation path '{state}'", span}
        (← pathExpression env span keys) activeControl
    | .merkleTreeIsFull state destination =>
      if value.effectGuardAt index |>.isSome then
        checkSink {description := s!"public MerkleTree fullness guard '{state}'", span} [] activeControl
      env := env ++ [(destination, [])]
    | .merkleTreeInsertHash state hash =>
      checkSink {description := s!"public MerkleTree inserted hash '{state}'", span}
        (← expression env span hash) activeControl
    | .merkleTreeReset state =>
      checkSink {description := s!"public MerkleTree mutation guard '{state}'", span}
        [] activeControl
    | .insertPath state keys _ payload | .writePath state keys _ payload =>
      checkSink {description := s!"public nested map write path '{state}'", span}
        (← pathExpression env span keys) activeControl
      checkSink {description := s!"public nested map write value '{state}'", span}
        (← expression env span payload) activeControl
    | .writeCompositePath state keys _ payloads =>
      checkSink {description := s!"public nested composite write path '{state}'", span}
        (← pathExpression env span keys) activeControl
      for (payload, index) in payloads.zipIdx do
        checkSink {description := s!"public nested composite write field {index} of '{state}'", span}
          (← expression env span payload) activeControl
    | .emptyMapPath state keys =>
      checkSink {description := s!"public empty-map path '{state}'", span}
        (← pathExpression env span keys) activeControl
    | .removePath state keys =>
      checkSink {description := s!"public nested map removal path '{state}'", span}
        (← pathExpression env span keys) activeControl
  for output in value.returns do
    checkSink {description := s!"public entrypoint return '{output.name}'", span := output.span}
      (← expression env output.span output.value) control

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

end Noctium.Disclosure
