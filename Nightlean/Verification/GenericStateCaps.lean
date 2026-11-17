import Nightlean.IR

namespace Nightlean.Verification.GenericStateCaps

private theorem type_validate_state_caps (ty : Ty) :
    ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} =
      ty.validate {poseidon2 := true} := by rfl

private theorem expr_validate_state_caps (expression : Expr ty) (env : TypeEnv) :
    expression.validate {poseidon2 := true, stateCells := true, stateMaps := true} env =
      expression.validate {poseidon2 := true} env := by
  induction expression generalizing env <;>
    simp [Expr.validate, type_validate_state_caps, *]

private theorem constraints_validate_state_caps (env : TypeEnv)
    (span : SourceSpan) (conditions : List (Expr .bool)) :
    validateConstraints {poseidon2 := true, stateCells := true, stateMaps := true}
      env span conditions =
    validateConstraints {poseidon2 := true} env span conditions := by
  induction conditions with
  | nil => rfl
  | cons condition rest ih =>
    simp [validateConstraints, expr_validate_state_caps, ih]

/-- Ledger capability flags do not affect a circuit's own type checks.
The production entrypoint validator enables those flags for state effects. -/
theorem circuit_validate_state_caps (circuit : Circuit) :
    circuit.validate {poseidon2 := true, stateCells := true, stateMaps := true} =
      circuit.validate {poseidon2 := true} := by
  unfold Circuit.validate
  simp [type_validate_state_caps, expr_validate_state_caps,
    constraints_validate_state_caps]

end Nightlean.Verification.GenericStateCaps
