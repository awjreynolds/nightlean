import Nightlean.Backend.Zkir

open Nightlean

private def originSpan : SourceSpan := {file := "private-source.lean", line := 4, column := 7}
private def sinkSpan : SourceSpan := {file := "public-sink.lean", line := 12, column := 3}
private def releaseSpan : SourceSpan := {file := "authorization.lean", line := 9, column := 5}
private def secret : Input := {name := "secret", ty := .native, visibility := .«private», span := originSpan}
private def flag : Input := {name := "flag", ty := .bool, visibility := .«private», span := originSpan}
private def publicValue : Input := {name := "publicValue", ty := .native, visibility := .«public»}
private def result (value : Expr ty) : Output := {name := "result", ty, value, span := sinkSpan}
private def relation (value : Expr ty) : Circuit := {
  name := "disclosure", inputs := [secret, flag, publicValue], outputs := [result value], span := sinkSpan}
private def has (text fragment : String) : Bool := (text.splitOn fragment).length > 1
private def rejected (value : Except Diagnostic α) : Bool := match value with | .error _ => true | _ => false
private def accepted (value : Except Diagnostic α) : Bool := match value with | .ok _ => true | _ => false

-- DISC-DATA and NL-DISC-PRIVATE-ARG-OUTPUT.
#guard match Disclosure.circuit (relation (.ref "secret" : Expr .native)) with
  | .error diagnostic => diagnostic.span == sinkSpan && has diagnostic.message "secret" &&
      has diagnostic.message "private-source.lean:4:7" && has diagnostic.message "public output 'result'"
  | _ => false
#guard accepted (Disclosure.circuit (relation (.ref "publicValue" : Expr .native)))

-- No primitive, comparison, cast or hash grants automatic declassification.
#guard rejected (Disclosure.circuit (relation (.poseidon2 1 (.ref "secret") (.native 0))))
#guard rejected (Disclosure.circuit (relation (.eq (.ref "secret" : Expr .native) (.native 0))))
#guard rejected (Disclosure.circuit (relation (.cast .bool (.ref "secret" : Expr .native))))
#guard rejected (Disclosure.circuit (relation (.add (.ref "secret") (.native 1))))
#guard rejected (Disclosure.circuit (relation (.sub (.ref "secret") (.native 1))))
#guard rejected (Disclosure.circuit (relation (.mul (.ref "secret") (.native 1))))
#guard rejected (Disclosure.circuit (relation (.select (.ref "flag") (.native 1) (.native 0))))

private def unsignedInput : Input := {name := "small", ty := .uint 255, visibility := .«private»}
private def unsignedRelation (value : Expr ty) : Circuit := {
  name := "unsigned", inputs := [unsignedInput], outputs := [result value]}
#guard rejected (Disclosure.circuit (unsignedRelation (.uadd (.ref "small" : Expr (.uint 255)) (.uint 1 1))))
#guard rejected (Disclosure.circuit (unsignedRelation (.usub (.ref "small" : Expr (.uint 255)) (.uint 1 1))))
#guard rejected (Disclosure.circuit (unsignedRelation (.umul (.ref "small" : Expr (.uint 255)) (.uint 1 1))))

-- Authorizing a payload alone leaves a private selection predicate private.
#guard rejected (Disclosure.circuit (relation (
  .select (.ref "flag") (.disclose releaseSpan (.native 1)) (.native 0))))
#guard accepted (Disclosure.circuit (relation (
  .select (.disclose releaseSpan (.ref "flag")) (.native 1) (.native 0))))
#guard accepted (Disclosure.circuit (relation (
  .disclose releaseSpan (.select (.ref "flag") (.native 1) (.native 0)))))
#guard rejected (Disclosure.circuit (relation (
  .select (.disclose releaseSpan (.ref "flag")) (.ref "secret") (.native 0))))

-- An authorization affects the wrapped value, never another occurrence.
#guard rejected (Disclosure.circuit {
  name := "scoped", inputs := [secret], outputs := [
    {name := "authorized", ty := .native, value := .disclose releaseSpan (.ref "secret")},
    {name := "unrelated", ty := .native, value := .ref "secret"}]})

-- Provider/private-state declarations strengthen private origins for this slice.
#guard match Disclosure.circuit {relation (.ref "secret" : Expr .native) with
    privateOrigins := [("secret", .provider)]} with
  | .error diagnostic => has diagnostic.message "provider result 'secret'"
  | _ => false
#guard match Disclosure.circuit {relation (.ref "secret" : Expr .native) with
    privateOrigins := [("secret", .privateState)]} with
  | .error diagnostic => has diagnostic.message "private-state read 'secret'"
  | _ => false
#guard rejected (Disclosure.circuit {relation (.ref "secret" : Expr .native) with
  privateOrigins := [("secret", .parameter)]})
#guard rejected (Disclosure.circuit {relation (.native 0) with
  privateOrigins := [("missing", .provider)]})
#guard rejected (Disclosure.circuit {relation (.native 0) with
  privateOrigins := [("secret", .provider), ("secret", .privateState)]})
#guard rejected (Disclosure.circuit {relation (.native 0) with
  privateOrigins := [("publicValue", .provider)]})
#guard rejected (Disclosure.circuit {relation (.native 0) with inputs := [publicValue, secret, secret]})
#guard match Disclosure.origins [] (.disclose releaseSpan (.ref "unknown" : Expr .native)) with
  | .error _ => true | _ => false

private def state : List StateDecl := [
  {name := "cell", kind := .cell .native}, {name := "map", kind := .map .native .native}]
private def entry (effects : List Effect) : Entrypoint := {
  name := "entry", circuit := {name := "local", inputs := [secret, flag]}, effects,
  span := originSpan, effectSpans := effects.map (fun _ => sinkSpan)}
private def caps : Capabilities := {stateCells := true, stateMaps := true, poseidon2 := true}

#guard accepted ((entry [.writeCell "cell" .native (.ref "secret")]).validate caps state)
#guard match Disclosure.entrypoint (entry [.writeCell "cell" .native (.ref "secret")]) with
  | .error diagnostic => diagnostic.span == sinkSpan && has diagnostic.message "public cell write 'cell'"
  | _ => false
#guard accepted (Disclosure.entrypoint (entry [
  .writeCell "cell" .native (.disclose releaseSpan (.ref "secret"))]))
#guard rejected (Disclosure.entrypoint (entry [
  .writeCell "cell" .native (.select (.ref "flag") (.native 1) (.native 0))]))
#guard rejected (Disclosure.entrypoint (entry [
  .writeMap "map" .native .native (.ref "secret") (.native 1)]))
#guard rejected (Disclosure.entrypoint (entry [
  .writeMap "map" .native .native (.native 1) (.ref "secret")]))
#guard rejected (Disclosure.entrypoint (entry [
  .readMap "map" "read" .native .native (.ref "secret")]))
#guard rejected (Disclosure.entrypoint (entry [
  .requireAbsent "map" .native (.ref "secret")]))
#guard accepted (Disclosure.entrypoint (entry [
  .readCell "cell" "old" .native, .writeCell "cell" .native (.ref "old")]))
#guard rejected (Disclosure.entrypoint {entry [.readCell "cell" "old" .native] with
  effectSpans := [sinkSpan, originSpan]})

-- Assertions remain intended relation constraints, separate from value sinks.
#guard accepted (Disclosure.circuit {relation (.native 0) with
  constraints := [.eq (.ref "secret" : Expr .native) (.native 7)]})
#guard accepted (Disclosure.entrypoint (entry [
  .require (.eq (.ref "secret" : Expr .native) (.native 7)),
  .writeCell "cell" .native (.native 1)]))

private def privateControl : Disclosure.Origins := [{name := "flag", kind := .parameter, span := originSpan}]
private def futureSink : Disclosure.Sink := {description := "future guarded public write", span := sinkSpan}
-- NL-DISC-GUARD-CONSTANT. Structured source guards are unsupported, but the
-- control interface already rejects writing a constant under a private guard.
#guard rejected (Disclosure.checkSink futureSink [] privateControl)
#guard rejected (Disclosure.entrypoint (entry [.writeCell "cell" .native (.native 1)]) privateControl)
#guard rejected (Disclosure.entrypoint (entry [
  .writeCell "cell" .native (.disclose releaseSpan (.native 1))]) privateControl)

-- Public backend entrypoints cannot bypass the mandatory pass through typed IR.
#guard rejected (Backend.Zkir.lowerCircuit (relation (.ref "secret" : Expr .native)))
#guard rejected (Backend.Impact.lower state (entry [.writeCell "cell" .native (.ref "secret")]))
#guard rejected (Backend.Zkir.lowerEntrypoint state (entry [.writeCell "cell" .native (.ref "secret")]))
#guard accepted (Backend.Zkir.lowerCircuit (relation (.disclose releaseSpan (.ref "secret" : Expr .native))))

example (sink : Disclosure.Sink) (payload control : Disclosure.Origins) :
    Disclosure.checkSink sink payload control = .ok () ↔ payload = [] ∧ control = [] :=
  Disclosure.sink_accepts_iff sink payload control

example (ctx : EvalContext) (env : EvalEnv) (value : Expr ty) :
    (Expr.disclose releaseSpan value).eval ctx env = value.eval ctx env :=
  disclose_evaluation ctx env releaseSpan value
