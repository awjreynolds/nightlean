import DirectedDisclosure
import Noctium.Semantics

namespace DirectedDisclosure

open Noctium

private def publish : Entrypoint := Inbox.entrypoints.headD {name := "", circuit := encrypt}

private theorem bind_success {ε α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private def packet (ephemeral ciphertext : Nat × Nat) : EvalEnv :=
  [("ephemeral", Value.pack .jubjubPoint ephemeral), ("ciphertext", Value.pack .jubjubPoint ciphertext)]

private def ephemeralExpr : Expr .jubjubPoint := .jubjubMulGenerator (.ref "nonce")
private def ciphertextExpr : Expr .jubjubPoint :=
  .jubjubAdd (.jubjubMulGenerator (.jubjubScalarFromNative
    (.cast (source := .uint 255) .native (.ref "value")))) (.jubjubMul (.ref "recipient") (.ref "nonce"))

/-- Successful circuit evaluation produces the two stated encryption expressions. -/
theorem encrypt_outputs (ctx : EvalContext) (env : EvalEnv) (outputs : EvalEnv)
    (success : encrypt.run ctx env = .ok outputs) :
    ∃ ephemeral ciphertext,
      ephemeralExpr.eval ctx env = .ok ephemeral ∧ ciphertextExpr.eval ctx env = .ok ciphertext ∧
      outputs = packet ephemeral ciphertext := by
  unfold Circuit.run at success
  split at success <;> split at success
  all_goals try (change Except.error _ = _ at success; cases success)
  simp only [bind_success] at success
  obtain ⟨_, _, _, _, _, _, written⟩ := success
  simp only [encrypt, List.mapM_cons, List.mapM_nil, disclose_evaluation] at written
  simp only [bind_assoc, pure_bind] at written
  change (do
    let e ← ephemeralExpr.eval ctx env
    let c ← ciphertextExpr.eval ctx env
    pure (packet e c)) = .ok outputs at written
  simp only [bind_success] at written
  obtain ⟨e, he, c, hc, hout⟩ := written
  exact ⟨e, c, he, hc, (Except.ok.inj hout).symm⟩

def inputs (recipient : Nat × Nat) (value nonce : Nat) : EvalEnv :=
  [("recipient", Value.pack .jubjubPoint recipient), ("value", .uint 255 value), ("nonce", .jubjubScalar nonce)]

def state (recipient ephemeral ciphertext : Nat × Nat) : LedgerState :=
  { cells := [("lastCiphertext", Value.pack .jubjubPoint ciphertext),
              ("lastEphemeral", Value.pack .jubjubPoint ephemeral),
              ("receiver", Value.pack .jubjubPoint recipient)] }

private theorem throw_error {α : Type} (message : String) :
    (throw message : Except String α) = .error message := rfl

private theorem map_error {α β : Type} (f : α → β) (message : String) :
    f <$> (Except.error message : Except String α) = Except.error message := rfl

private theorem bind_error {α β : Type} (next : α → Except String β) (message : String) :
    (Except.error message >>= next) = Except.error message := rfl

/-- A successful source call uses the sealed key and updates exactly the two ciphertext cells. -/
theorem successful_publish (ctx : EvalContext) (recipient registered pastEphemeral pastCiphertext : Nat × Nat)
    (value nonce : Nat) (next : LedgerState) (observed : EvalEnv)
    (success : publish.run ctx (inputs recipient value nonce)
      (state registered pastEphemeral pastCiphertext) = .ok (observed, next)) :
    recipient = registered ∧ ∃ e c,
      ephemeralExpr.eval ctx (inputs recipient value nonce) = .ok e ∧
      ciphertextExpr.eval ctx (inputs recipient value nonce) = .ok c ∧
      observed = packet e c ∧ next = state registered e c := by
  have noReturn : publish.returns = [] := rfl
  unfold Entrypoint.run at success
  split at success
  · change Except.error _ = _ at success
    cases success
  · simp only [noReturn, List.mapM_nil, pure_bind, List.append_nil, bind_success] at success
    obtain ⟨result, run, final, effects, equal⟩ := success
    have ran : encrypt.run ctx (inputs recipient value nonce) = .ok result := run
    have observedEq := congrArg Prod.fst (Except.ok.inj equal)
    have nextEq := congrArg Prod.snd (Except.ok.inj equal)
    dsimp at observedEq nextEq
    subst observed
    subst next
    obtain ⟨e, c, he, hc, rfl⟩ := encrypt_outputs _ _ _ ran
    rcases registered with ⟨kx, ky⟩
    rcases recipient with ⟨rx, ry⟩
    rcases pastEphemeral with ⟨px, py⟩
    rcases pastCiphertext with ⟨cx, cy⟩
    rcases e with ⟨ex, ey⟩
    rcases c with ⟨tx, ty⟩
    simp [publish, Inbox, inputs, packet, state, Value.pack, Value.as,
      runEffectsWithGuardsAndEnv,
      List.forIn_cons, List.forIn_nil, List.lookup, canonical_eq, Expr.eval, bind_assoc, pure_bind] at effects
    repeat first
      | (simp +failIfUnchanged [List.lookup, updateAssoc, pure_bind,
          throw_error, map_error, bind_error] at effects)
      | split at effects
    have sameRecipient : ((rx, ry) : Nat × Nat) = (kx, ky) := by
      have admitted : (((rx, ry) : Nat × Nat) == (kx, ky)) ≠ _root_.Bool.false := by assumption
      apply beq_iff_eq.mp
      cases compared : (((rx, ry) : Nat × Nat) == (kx, ky)) <;>
        first | rfl | exact False.elim (admitted compared)
    refine ⟨sameRecipient, (ex, ey), (tx, ty), he, hc, rfl, ?_⟩
    exact (congrArg Prod.snd (Except.ok.inj effects)).symm

end DirectedDisclosure
