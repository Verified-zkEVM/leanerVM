/-
  LeanVM.E2E.KS.Split

  A forgery the deployed verifier accepts is either a failure of knowledge soundness or a known
  forgery of leanXMSS or leanSPHINCS before verification (decision E2E-15).
-/

module

public import LeanVM.E2E.KS.Marginal

/-!
# The split of a forgery

`prEvent_dForged_le`: under knowledge soundness with error `ε`, the deployed verifier accepts a
forged claim with probability at most `ε` plus the probabilities of a known leanXMSS and a known
leanSPHINCS forgery in the game before verification. If the adversary knows a signature for every
claim (`ClaimsKnown`), a forged claim's signature is a known forgery (`knownForged_of_dForged`).
-/

namespace LeanVM.E2E.KS

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom
open LeanVM.E2E OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

variable {nx ns : ℕ} [Sphincs.Params]

/-- **A forged claim the adversary knows a signature for is a known forgery.** -/
theorem knownForged_of_dForged {z : DOutcome nx ns} (hk : ClaimsKnown z) (hf : DForged z) :
    KnownForgedX z.pre ∨ KnownForgedS z.pre := by
  rcases hf with ⟨j, msg, hmem, hreq⟩ | ⟨j, msg, hmem, hreq⟩
  · obtain ⟨σ, hσ⟩ := hk.1 _ hmem
    exact Or.inl ⟨j, msg, σ, hmem, hreq, hσ⟩
  · obtain ⟨σ, hσ⟩ := hk.2 _ hmem
    exact Or.inr ⟨j, msg, σ, hmem, hreq, hσ⟩

/-- **The split.** Under knowledge soundness with error `ε`, the deployed verifier accepts a
forged claim with probability at most `ε` plus the probabilities of a known leanXMSS and a known
leanSPHINCS forgery before verification. -/
theorem prEvent_dForged_le (guest : Program) (A : DAdversary nx ns) {ε : ℝ≥0∞}
    (hks : KnowledgeSound guest A ε) :
    Pr{let z ← dGame guest A}[z.1.accepted = true ∧ DForged z.1] ≤
      ε + Pr{let z ← pGame A}[KnownForgedX z.1] + Pr{let z ← pGame A}[KnownForgedS z.1] := by
  classical
  calc Pr{let z ← dGame guest A}[z.1.accepted = true ∧ DForged z.1]
      ≤ Pr{let z ← dGame guest A}[(z.1.accepted = true ∧ ¬ ClaimsKnown z.1) ∨
          KnownForgedX z.1.pre ∨ KnownForgedS z.1.pre] :=
        prEvent_mono_of_support _ _ _ fun z _ h ↦ by
          by_cases hk : ClaimsKnown z.1
          · exact Or.inr (knownForged_of_dForged hk h.2)
          · exact Or.inl ⟨h.1, hk⟩
    _ ≤ Pr{let z ← dGame guest A}[z.1.accepted = true ∧ ¬ ClaimsKnown z.1] +
          (Pr{let z ← dGame guest A}[KnownForgedX z.1.pre] +
            Pr{let z ← dGame guest A}[KnownForgedS z.1.pre]) :=
        (prEvent_or_le _ _ _).trans (add_le_add le_rfl (prEvent_or_le _ _ _))
    _ ≤ ε + Pr{let z ← pGame A}[KnownForgedX z.1] + Pr{let z ← pGame A}[KnownForgedS z.1] := by
        rw [prEvent_dGame_pre, prEvent_dGame_pre, ← add_assoc]
        exact add_le_add (add_le_add hks le_rfl) le_rfl

end
end LeanVM.E2E.KS
