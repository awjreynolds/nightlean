import Noctium.Verification.ScalarTranslation

namespace ScalarTranslationTests
open Lean Noctium Noctium.Backend Noctium.Verification
open NativeRelation ScalarNormalization ScalarTranslation

private def ctx : EvalContext := {modulus := Field.modulus, poseidon2 := fun _ _ _ => .ok 0}
private def hash : Hash := fun _ => zero
private theorem implementation : HashAgreement ctx hash := by
  constructor
  · rfl
  · intro domain left right
    rfl

private def discardedUnderflow : Circuit := {
  name := "discardedUnderflow"
  outputs := [{name := "result", ty := .native, value := .letE "ignored" (.usub (.uint 7 1) (.uint 7 2)) (.native 9)}]
}

private def shadowed : Circuit := {
  name := "shadowed"
  outputs := [{name := "result", ty := .native, value := .letE "x" (.native 2) (.letE "x" (.add (.ref "x") (.native 3))
      (.mul (.ref "x") (.ref "x")))}]
}

#guard (Zkir.lowerCircuit discardedUnderflow).isOk
#guard (Zkir.lowerCircuit shadowed).isOk

example : discardedUnderflow.run ctx [] = .error "unsigned subtraction underflow" := by rfl
example : shadowed.run ctx [] = .ok [("result", .native 25)] := by rfl

private theorem emptyInputs (circuit : Circuit) (empty : circuit.inputs = []) (witness : Assignment) :
    CanonicalInputs circuit [] witness := by
  constructor
  · rfl
  · simp
  · simp [empty]
  · simp [empty]

/-- Every satisfying assignment would force successful source execution. An
unused partial expression therefore has no satisfying native assignment. -/
example (json : Json) (program : Program) (streams : InputStreams) (witness : Assignment)
    (groups : List (List Scalar))
    (lowered : Zkir.lowerCircuit discardedUnderflow = .ok json)
    (decoded : NativeRelationJson.decode json = .ok program)
    (satisfies : CircuitSatisfies hash program streams witness groups) : False := by
  obtain ⟨result, successful, _⟩ := lowerCircuit_sound ctx hash implementation discardedUnderflow []
    json program streams witness groups (emptyInputs discardedUnderflow rfl witness) lowered decoded satisfies
  have failed : discardedUnderflow.run ctx [] = .error "unsigned subtraction underflow" := by rfl
  rw [failed] at successful
  cases successful

#print axioms Noctium.Verification.ScalarTranslation.lowerCircuit_sound

/-- Completeness supplies a witness for the actual emitted CSE/shadowing program,
with an authenticated final Impact vector and exact host returns. -/
example (json : Json) (program : Program)
    (lowered : Zkir.lowerCircuit shadowed = .ok json)
    (decoded : NativeRelationJson.decode json = .ok program) :
    ∃ witness, Satisfies hash program {publicValues := [], privateValues := []}
      witness [[scalar 25]] [scalar 25] := by
  obtain ⟨witness, frame, satisfies⟩ := lowerCircuit_complete ctx hash implementation shadowed []
    [("result", .native 25)] (fun _ => zero) json program
    (emptyInputs shadowed rfl _) lowered decoded (by rfl)
  exact ⟨witness, by simpa [shadowed, valueNumber] using satisfies⟩

#print axioms Noctium.Verification.ScalarTranslation.lowerCircuit_complete

end ScalarTranslationTests
