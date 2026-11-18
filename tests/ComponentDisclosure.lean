import Noctium.ComponentDisclosure
import Noctium.Control
open Noctium Noctium.Helpers

private def recordType : Types.CompositeType := .structure "Demo.Record"

private def disclosureTypes : Types.CompositeEnv := {
  structures := [
    {id := "Demo.Record", fields := [
      ⟨"secret", .scalar .native, {}⟩,
      ⟨"marker", .scalar .native, {}⟩]},
    {id := "Demo.OtherRecord", fields := [
      ⟨"secret", .scalar .native, {}⟩,
      ⟨"marker", .scalar .native, {}⟩]}],
  enumerations := [{id := "Demo.Choice", variants := [
    {name := "Full", fields := [⟨"secret", .scalar .native, {}⟩]},
    {name := "Empty", fields := [⟨"nothing", .unit, {}⟩]}]}]
}

private def recordParameter (name : String := "record") : Parameter := {
  name, ty := .native
}

private def withCompositeParameters (declaration : Declaration)
    (parameters : List (String × Types.CompositeType)) : Declaration :=
  {declaration with compositeParameters := parameters}

private def exportedProgram (declarations : List Declaration) (inputs : List Input := [])
    (compositeInputs : List AggregateInput := []) (types : Types.CompositeEnv := disclosureTypes)
    (target : DeclarationId := ⟨0, 0⟩) : Program := {
  declarations,
  exports := [{name := "entry", target, inputs, compositeInputs}],
  composites := types
}

private def recordEntry (body : List Statement) (result : ResultType := .scalar .native) : Program :=
  exportedProgram [withCompositeParameters
    {id := ⟨0, 0⟩, name := "entry", parameters := [recordParameter], result, body}
    [("record", recordType)]]
    [] [{name := "record", type := recordType, visibility := .private}]

private def rejectedWith (result : Except Diagnostic α) (part : String) : Bool :=
  match result with
  | .error diagnostic => (diagnostic.message.splitOn part).length > 1
  | .ok _ => false

private def accepted (result : Except Diagnostic α) : Bool :=
  match result with | .ok _ => true | .error _ => false

private def field (name : String) : Term := .project (.ref "record") (.field name)

-- Components keep separate parameter paths, and an aggregate release covers its payload leaves.
#guard rejectedWith
  (ComponentDisclosure.checkProgram (recordEntry [.return (some (.ref "record"))] (.composite recordType)) "entry")
  "public output 'result.secret'"
#guard accepted (ComponentDisclosure.checkProgram
  (recordEntry [.return (some (.disclose {} (.ref "record")))] (.composite recordType)) "entry")
#guard rejectedWith
  (ComponentDisclosure.checkProgram (recordEntry [.return (some (field "secret"))]) "entry")
  "private parameter 'record.secret'"
#guard accepted (ComponentDisclosure.checkProgram
  (recordEntry [.return (some (.disclose {} (field "secret")))]) "entry")
#guard rejectedWith (Control.compile (recordEntry [.return (some (.ref "record"))] (.composite recordType)) "entry")
  "aggregate inputs are not supported by the portable control plan"

-- Tuple and nested vector projections retain the precise leaf path.
private def tupleType : Types.CompositeType := .tuple [
  .scalar .native, .vector 2 (.scalar .native)]
private def tupleProgram : Program := exportedProgram [
  withCompositeParameters
    {id := ⟨0, 0⟩, name := "entry", parameters := [recordParameter "bundle"],
      result := .scalar .native,
      body := [.return (some (.project
        (.project (.ref "bundle") (.tupleIndex 1)) (.vectorIndex 1)))]}
    [("bundle", tupleType)]
  ] [] [{name := "bundle", type := tupleType, visibility := .private}]

#guard rejectedWith (ComponentDisclosure.checkProgram tupleProgram "entry")
  "private parameter 'bundle.1.1'"

-- Hashes preserve source origins. Helper parameter and result paths remain visible in diagnostics.
private def helperFlow : Program := exportedProgram [
  withCompositeParameters
    {id := ⟨0, 0⟩, name := "identity", parameters := [recordParameter],
      result := .composite recordType, body := [.return (some (.ref "record"))]}
    [("record", recordType)],
  withCompositeParameters
    {id := ⟨0, 1⟩, name := "entry", parameters := [recordParameter],
      result := .scalar .native,
      body := [.return (some (.poseidon2 7 (.project (.call "identity" [.ref "record"]) (.field "secret")) (.native 0)))]}
    [("record", recordType)]
  ] [] [{name := "record", type := recordType, visibility := .private}] disclosureTypes ⟨0, 1⟩

#guard rejectedWith (ComponentDisclosure.checkProgram helperFlow "entry") "helper identity"
#guard rejectedWith
  (ComponentDisclosure.checkProgram (recordEntry [.return (some
    (.poseidon2 7 (field "secret") (.native 0)))]) "entry")
  "public output 'result'"

-- Nominal struct identity is checked before source aggregates flatten to native leaves.
private def nominalMismatch : Program := exportedProgram [
  withCompositeParameters
    {id := ⟨0, 0⟩, name := "acceptRecord", parameters := [recordParameter],
      result := .composite recordType, body := [.return (some (.ref "record"))]}
    [("record", recordType)],
  withCompositeParameters
    {id := ⟨0, 1⟩, name := "entry", parameters := [{name := "other", ty := .native}],
      result := .scalar .native,
      body := [.return (some (.project (.call "acceptRecord" [.ref "other"]) (.field "secret")))]}
    [("other", .structure "Demo.OtherRecord")]
  ] [] [{name := "other", type := .structure "Demo.OtherRecord", visibility := .private}]
  disclosureTypes ⟨0, 1⟩

#guard rejectedWith (ComponentDisclosure.checkProgram nominalMismatch "entry")
  "no compatible helper overload 'acceptRecord'"

-- Scalar subtyping follows the source signature and preserves private origins.
private def scalarWideningProgram (visibility : Visibility) (release : Bool := false) : Program :=
  exportedProgram [
    {id := ⟨0, 0⟩, name := "entry", parameters := [{name := "value", ty := .native}],
      result := .scalar .native,
      body := [.return (some (if release then .disclose {} (.ref "value") else .ref "value"))]}
  ] [{name := "source", ty := .uint 7, visibility}]

#guard accepted (Helpers.compile (scalarWideningProgram .public) "entry")
#guard accepted (ComponentDisclosure.checkProgram (scalarWideningProgram .public) "entry")
#guard rejectedWith (ComponentDisclosure.checkProgram (scalarWideningProgram .private) "entry")
  "private parameter 'source'"
#guard accepted (ComponentDisclosure.checkProgram (scalarWideningProgram .private true) "entry")

-- An export's declaration identity wins over an ambiguous same-name overload set.
private def selectedExportOverload : Program := {
  declarations := [
    {id := ⟨0, 0⟩, name := "release", parameters := [{name := "value", ty := .uint 7}],
      result := .scalar (.uint 7),
      body := [.return (some (.disclose {} (.ref "value")))]},
    {id := ⟨0, 1⟩, name := "release", parameters := [{name := "value", ty := .native}],
      result := .scalar .native, body := [.return (some (.native 9))]}
  ],
  exports := [{name := "selected", target := ⟨0, 0⟩, inputs := [
    {name := "secret", ty := .uint 7, visibility := .private}]}]
}

#guard accepted (Helpers.compile selectedExportOverload "selected")
#guard accepted (ComponentDisclosure.checkProgram selectedExportOverload "selected")
#guard match ComponentDisclosure.analyzeEntry selectedExportOverload "selected" with
  | .ok (_, value) => value.type == .scalar (.uint 7) && value.components == [[]]
  | .error _ => false

-- A declared Native binding stays Native when its initializer is UInt7.
private def declaredNativeOverload : Program := {
  declarations := [
    {id := ⟨0, 0⟩, name := "choose", parameters := [{name := "value", ty := .native}],
      result := .scalar .native, body := [.return (some (.native 8))]},
    {id := ⟨0, 1⟩, name := "choose", parameters := [{name := "value", ty := .uint 7}],
      result := .scalar (.uint 7), body := [.return (some (.uint 7 3))]},
    {id := ⟨0, 2⟩, name := "entry", result := .scalar .native, body := [
      .bind "value" (.scalar .native) (.uint 7 1),
      .return (some (.call "choose" [.ref "value"]))]}
  ],
  exports := [{name := "entry", target := ⟨0, 2⟩}]
}

#guard accepted (Helpers.compile declaredNativeOverload "entry")
#guard accepted (ComponentDisclosure.checkProgram declaredNativeOverload "entry")
#guard match ComponentDisclosure.analyzeEntry declaredNativeOverload "entry" with
  | .ok (_, value) => value.type == .scalar .native
  | .error _ => false

-- Runtime selectors retain both predicate and index origins. Literal false selects only its live arm.
private def vectorProgram (body : List Statement) (visibility : Visibility := .private)
    (indexVisibility : Visibility := .private) : Program := exportedProgram [
  withCompositeParameters
    {id := ⟨0, 0⟩, name := "entry",
      parameters := [{name := "items", ty := .native}, {name := "position", ty := .native}],
      result := .scalar .native, body}
    [("items", .vector 2 (.scalar .native))]
  ] [
    {name := "position", ty := .native, visibility := indexVisibility}
  ] [
    {name := "items", type := .vector 2 (.scalar .native), visibility}
  ]

#guard rejectedWith
  (ComponentDisclosure.checkProgram (vectorProgram [.return (some (.index (.ref "items") (.ref "position")))]) "entry")
  "undisclosed private control from parameter 'position'"
#guard accepted (ComponentDisclosure.checkProgram (vectorProgram [
  .return (some (.ite (.bool false) (.native 9) (.index (.ref "items") (.ref "position"))))]
  .public .public) "entry")
#guard rejectedWith
  (ComponentDisclosure.checkProgram (vectorProgram [
    .return (some (.ite (.ref "position") (.native 9) (.native 0)))]) "entry")
  "condition requires Bool"

private def runtimeConditional : Program := exportedProgram [
  {id := ⟨0, 0⟩, name := "entry",
    parameters := [{name := "flag", ty := .bool}, {name := "secret", ty := .native}],
    result := .scalar .native,
    body := [.return (some (.ite (.ref "flag") (.ref "secret") (.native 0)))]}
  ] [
    {name := "flag", ty := .bool, visibility := .private},
    {name := "secret", ty := .native, visibility := .private}]

#guard rejectedWith (ComponentDisclosure.checkProgram runtimeConditional "entry")
  "undisclosed private control from parameter 'flag'"
#guard accepted (ComponentDisclosure.checkProgram (exportedProgram [
  {id := ⟨0, 0⟩, name := "entry", parameters := [{name := "secret", ty := .native}],
    result := .scalar .native,
    body := [.return (some (.ite (.bool false) (.ref "secret") (.native 0)))]}
  ] [{name := "secret", ty := .native, visibility := .private}]) "entry")

-- A continuing unknown branch must not hide the source return after the branch.
private def branchContinuationProgram (secretVisibility : Visibility) : Program := exportedProgram [
  {id := ⟨0, 0⟩, name := "entry",
    parameters := [{name := "flag", ty := .bool}, {name := "secret", ty := .native}],
    result := .scalar .native,
    body := [
      .branch (.ref "flag") [.evaluate (.native 1)] [.evaluate (.native 2)],
      .return (some (.ref "secret"))]}
  ] [
    {name := "flag", ty := .bool, visibility := .public},
    {name := "secret", ty := .native, visibility := secretVisibility}]

#guard accepted (Helpers.prepareWithLimits {} (branchContinuationProgram .private))
#guard rejectedWith (ComponentDisclosure.checkProgram (branchContinuationProgram .private) "entry")
  "private parameter 'secret'"
#guard accepted (ComponentDisclosure.checkProgram (branchContinuationProgram .public) "entry")

-- Mixed early-return and continuation paths both contribute to the exported result.
private def earlyReturnPrivate : Program := exportedProgram [
  {id := ⟨0, 0⟩, name := "entry",
    parameters := [{name := "flag", ty := .bool}, {name := "secret", ty := .native}],
    result := .scalar .native,
    body := [
      .branch (.ref "flag") [.return (some (.ref "secret"))] [.evaluate (.native 2)],
      .return (some (.native 0))]}
  ] [
    {name := "flag", ty := .bool, visibility := .public},
    {name := "secret", ty := .native, visibility := .private}]

#guard accepted (Helpers.prepareWithLimits {} earlyReturnPrivate)
#guard rejectedWith (ComponentDisclosure.checkProgram earlyReturnPrivate "entry")
  "private parameter 'secret'"

private def nestedEarlyReturnPrivate : Program := exportedProgram [
  {id := ⟨0, 0⟩, name := "entry",
    parameters := [
      {name := "outer", ty := .bool}, {name := "inner", ty := .bool},
      {name := "secret", ty := .native}],
    result := .scalar .native,
    body := [
      .branch (.ref "outer") [
        .branch (.ref "inner") [.return (some (.ref "secret"))] [.evaluate (.native 1)],
        .evaluate (.native 2)]
        [.evaluate (.native 3)],
      .return (some (.native 0))]}
  ] [
    {name := "outer", ty := .bool, visibility := .public},
    {name := "inner", ty := .bool, visibility := .public},
    {name := "secret", ty := .native, visibility := .private}]

#guard accepted (Helpers.prepareWithLimits {} nestedEarlyReturnPrivate)
#guard rejectedWith (ComponentDisclosure.checkProgram nestedEarlyReturnPrivate "entry")
  "private parameter 'secret'"

private def earlyReturnPrivateControl : Program := exportedProgram [
  {id := ⟨0, 0⟩, name := "entry", parameters := [{name := "flag", ty := .bool}],
    result := .scalar .native,
    body := [
      .branch (.ref "flag") [.return (some (.native 1))] [.evaluate (.native 2)],
      .return (some (.native 0))]}
  ] [{name := "flag", ty := .bool, visibility := .private}]

#guard rejectedWith (ComponentDisclosure.checkProgram earlyReturnPrivateControl "entry")
  "undisclosed private control from parameter 'flag'"

-- Branch-local bindings end with the branch. A continuation binding of the same name starts fresh.
private def branchLocalScope : Program := exportedProgram [
  {id := ⟨0, 0⟩, name := "entry",
    parameters := [
      {name := "flag", ty := .bool}, {name := "publicValue", ty := .native},
      {name := "secret", ty := .native}],
    result := .scalar .native,
    body := [
      .branch (.ref "flag") [
        .bind "scratch" (.scalar .native) (.ref "secret"),
        .evaluate (.ref "scratch")]
        [.evaluate (.native 0)],
      .bind "scratch" (.scalar .native) (.ref "publicValue"),
      .return (some (.ref "scratch"))]}
  ] [
    {name := "flag", ty := .bool, visibility := .public},
    {name := "publicValue", ty := .native, visibility := .public},
    {name := "secret", ty := .native, visibility := .private}]

#guard accepted (Helpers.prepareWithLimits {} branchLocalScope)
#guard accepted (ComponentDisclosure.checkProgram branchLocalScope "entry")

-- Disclosing a selected payload does not authorize a private index or enum tag.
private def indexedRecord : Program := exportedProgram [
  withCompositeParameters
    {id := ⟨0, 0⟩, name := "entry",
      parameters := [{name := "items", ty := .native}, {name := "position", ty := .native}],
      result := .scalar .native,
      body := [.return (some (.disclose {} (.project
        (.index (.ref "items") (.ref "position")) (.field "secret"))))]}
    [("items", .vector 2 recordType)]
  ] [{name := "position", ty := .native, visibility := .private}]
  [{name := "items", type := .vector 2 recordType, visibility := .public}]

#guard rejectedWith (ComponentDisclosure.checkProgram indexedRecord "entry")
  "undisclosed private control from parameter 'position'"

private def enumProgram : Program := exportedProgram [
  withCompositeParameters
    {id := ⟨0, 0⟩, name := "entry", parameters := [{name := "choice", ty := .native}],
      result := .scalar .native,
      body := [.return (some (.disclose {} (.project (.ref "choice") (.enumField "Full" "secret"))))]}
    [("choice", .enumeration "Demo.Choice")]
  ] [] [{name := "choice", type := .enumeration "Demo.Choice", visibility := .private}]

#guard rejectedWith (ComponentDisclosure.checkProgram enumProgram "entry")
  "undisclosed private control from parameter 'choice.$tag'"

private def publicEnumProjection : Program := exportedProgram [
  withCompositeParameters
    {id := ⟨0, 0⟩, name := "entry", parameters := [{name := "choice", ty := .native}],
      result := .scalar .native,
      body := [.return (some (.project (.ref "choice") (.enumField "Full" "secret")))]}
    [("choice", .enumeration "Demo.Choice")]
  ] [] [{name := "choice", type := .enumeration "Demo.Choice", visibility := .public}]

private def enumProjectionAccepts (tag : Nat) : Bool :=
  match Helpers.compile publicEnumProjection "entry" with
  | .error _ => false
  | .ok circuit =>
    match circuit.run
        {modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "unused"} [
          ("choice.$tag", .native tag), ("choice.$payload0", .native 0)] with
    | .ok _ => true
    | .error _ => false

#guard enumProjectionAccepts 0
#guard !enumProjectionAccepts 1

-- Empty aggregate selections keep their hidden selector metadata even without component leaves.
private def emptyVectorProgram : Program := exportedProgram [
  withCompositeParameters
    {id := ⟨0, 0⟩, name := "entry",
      parameters := [{name := "items", ty := .native}, {name := "position", ty := .native}],
      result := .unit,
      body := [.return (some (.index (.ref "items") (.ref "position")))]}
    [("items", .vector 2 .unit)]
  ] [{name := "position", ty := .native, visibility := .private}]
  [{name := "items", type := .vector 2 .unit, visibility := .public}]

#guard match ComponentDisclosure.analyzeEntry emptyVectorProgram "entry" with
  | .ok (_, value) => value.type == .unit && value.components.isEmpty &&
      value.indexOrigins.map (·.origin.name) == ["position"]
  | .error _ => false

private def emptyEnumProgram : Program := exportedProgram [
  withCompositeParameters
    {id := ⟨0, 0⟩, name := "entry", parameters := [{name := "choice", ty := .native}],
      result := .unit,
      body := [.return (some (.project (.ref "choice") (.enumField "Empty" "nothing")))]}
    [("choice", .enumeration "Demo.Choice")]
  ] [] [{name := "choice", type := .enumeration "Demo.Choice", visibility := .private}]

#guard match ComponentDisclosure.analyzeEntry emptyEnumProgram "entry" with
  | .ok (_, value) => value.components.isEmpty &&
      value.tagOrigins.map (·.origin.name) == ["choice.$tag"]
  | .error _ => false

-- A provider witness is a real private source input. Native compilation records its provenance.
private def providerProgram : Program := exportedProgram [
  {id := ⟨0, 0⟩, name := "entry", result := .scalar .native,
    body := [.return (some (.disclose {} (.witness "attestation" .native)))]}
  ]

#guard accepted (ComponentDisclosure.checkProgram providerProgram "entry")
#guard match Helpers.compile providerProgram "entry" with
  | .ok circuit =>
    match circuit.inputs with
    | [input] => input.visibility == Visibility.private &&
      circuit.privateOrigins == [(input.name, PrivateOriginKind.provider)]
    | _ => false
  | .error _ => false

-- Private-state source effects carry state-derived origins, but do not claim a native read implementation.
private def privateStateProgram (value : Term) : Program := exportedProgram [
  {id := ⟨0, 0⟩, name := "entry", result := .scalar .native,
    body := [.return (some value)]}
  ]

#guard rejectedWith
  (ComponentDisclosure.checkProgram (privateStateProgram (.effect .privateState "account.balance" (.native 1))) "entry")
  "private-state read 'account.balance'"
#guard accepted (ComponentDisclosure.checkProgram
  (privateStateProgram (.disclose {} (.effect .privateState "account.balance" (.native 1)))) "entry")
#guard rejectedWith
  (Helpers.compile (privateStateProgram (.disclose {} (.effect .privateState "account.balance" (.native 1)))) "entry")
  "native helper capability unavailable"
