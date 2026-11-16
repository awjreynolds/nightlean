import Nightlean.Semantics

namespace Nightlean.Passes

/-- Remove only literal true constraints. No evaluation, hash oracle, field
identity, or target capability assumption is needed. -/
def pruneCircuit (c : Circuit) : Circuit :=
  {c with constraints := pruneTrue c.constraints}

theorem prune_validation (caps : Capabilities) (env : TypeEnv) (span : SourceSpan)
    (conditions : List (Expr .bool)) :
    validateConstraints caps env span (pruneTrue conditions) =
      validateConstraints caps env span conditions := by
  induction conditions with
  | nil => rfl
  | cons condition rest ih =>
    cases condition with
    | bool b => cases b <;> simp [pruneTrue, validateConstraints, Expr.validate, ih]
    | ref name => simp only [pruneTrue, validateConstraints, ih]
    | eq a b => simp only [pruneTrue, validateConstraints, ih]
    | select condition a b => simp only [pruneTrue, validateConstraints, ih]
    | cast target value => simp only [pruneTrue, validateConstraints, ih]

theorem prune_evaluation (ctx : EvalContext) (env : EvalEnv)
    (conditions : List (Expr .bool)) :
    runConstraints ctx env (pruneTrue conditions) = runConstraints ctx env conditions := by
  induction conditions with
  | nil => rfl
  | cons condition rest ih =>
    cases condition with
    | bool b => cases b <;> simp [pruneTrue, runConstraints, Expr.eval, ih]
    | ref name => simp only [pruneTrue, runConstraints, ih]
    | eq a b => simp only [pruneTrue, runConstraints, ih]
    | select condition a b => simp only [pruneTrue, runConstraints, ih]
    | cast target value => simp only [pruneTrue, runConstraints, ih]

theorem pruneCircuit_validate (caps : Capabilities) (c : Circuit) :
    (pruneCircuit c).validate caps = c.validate caps := by
  simp only [Circuit.validate, pruneCircuit, prune_validation]
  rfl

/-- Complete executable semantics equality includes input validation, exact errors,
constraint failure order, hash-oracle errors, and named outputs. -/
theorem pruneCircuit_run (ctx : EvalContext) (env : EvalEnv) (c : Circuit) :
    (pruneCircuit c).run ctx env = c.run ctx env := by
  unfold Circuit.run
  rw [pruneCircuit_validate]
  simp only [pruneCircuit, prune_evaluation]
  rfl

/-- Preserve state effects verbatim while optimizing the associated relation. -/
def pruneEntrypoint (entry : Entrypoint) : Entrypoint :=
  {entry with circuit := pruneCircuit entry.circuit}

theorem pruneEntrypoint_validate (caps : Capabilities) (state : List StateDecl) (entry : Entrypoint) :
    (pruneEntrypoint entry).validate caps state = entry.validate caps state := by
  unfold Entrypoint.validate
  dsimp only [pruneEntrypoint]
  rw [pruneCircuit_validate]
  rfl

theorem pruneEntrypoint_run (ctx : EvalContext) (env : EvalEnv)
    (state : LedgerState) (entry : Entrypoint) :
    (pruneEntrypoint entry).run ctx env state = entry.run ctx env state := by
  unfold Entrypoint.run
  dsimp only [pruneEntrypoint]
  rw [pruneCircuit_run]
  rfl

end Nightlean.Passes
