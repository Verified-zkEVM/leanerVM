import LeanVM.E2E.KS.XmssProved
import LeanVM.E2E.KS.Split
import LeanVM.E2E.KS.Fold
import LeanVM.E2E.KS.SphincsHeadline

/-!
# Unforgeability of the deployed aggregation, under knowledge soundness

Decision E2E-15 of `docs/roadmap/e2e-security.md`: the headline about the deployed verifier.

`aggregate_unforgeable_ks`: for every proved leanSPHINCS parameter set, every numbers `n_x`, `n_s`
of honest keys and every adversary `A` of the deployed game whose game makes at most `q` hash
evaluations before verification (`DHashEvals`), if the deployed aggregation is knowledge sound
against `A` with error `ε` (`KnowledgeSound`), the deployed verifier `verifyAggregate`, run with
the random oracle, accepts a root statement with a forged claim of an honest key with probability
at most `ε + (n_s + n_x/2^23 + 4) · q / 2^127`. The proof: a forged claim the adversary knows a
signature for is a forgery of leanXMSS or leanSPHINCS (`prEvent_dForged_le`), bounded by their
multi-user security (`prEvent_knownForgedX_le_proved`, `prEvent_knownForgedS_le_set`), folded
into one term (`signatureBounds_le`).
-/

namespace LeanVM.E2E.KS

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.E2E OracleComp
open scoped ENNReal

/-- The leanSPHINCS part as a hypothesis (instantiated by `aggregate_unforgeable_ks`). -/
theorem aggregate_unforgeable_ks_of [P : Sphincs.Params] [S : SphincsSet P] {nx ns q : ℕ}
    {ε : ℝ≥0∞} (guest : Program) (A : DAdversary nx ns) (hq : DHashEvals A q)
    (hks : KnowledgeSound guest A ε)
    (hS : ∀ {qH sX sS : ℕ}, DAdvBounds A qH sX sS → Pr{let z ← pGame A}[KnownForgedS z.1] ≤
      (ns : ℝ≥0∞) * (((preQueries nx ns qH sX sS + 686 : ℕ) : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞))) :
    Pr{let z ← dGame guest A}[z.1.accepted = true ∧ DForged z.1] ≤
      ε + ((ns : ℝ≥0∞) + nx / 2 ^ 23 + 4) * q / 2 ^ 127 := by
  obtain ⟨qH, sX, sS, hA, hQ⟩ := hq
  set Q := preQueries nx ns qH sX sS
  by_cases hl : q * (2 ^ 129 * ns + 2 ^ 106 * nx + 2 ^ 131) < 2 ^ 256
  · have hq125 : q < 2 ^ 125 := by
      by_contra h
      have : 2 ^ 125 * 2 ^ 131 ≤ q * (2 ^ 129 * ns + 2 ^ 106 * nx + 2 ^ 131) :=
        Nat.mul_le_mul (by omega) (by omega)
      norm_num at this hl
      omega
    have hQq : Q ≤ q := hQ
    have hQ126 : Q + 384 < 2 ^ 126 := by omega
    have hkey : nx * 2 ^ 23 + ns * 2 ^ 15 ≤ Q := by
      have h := keygens_le_gameQueries nx ns qH sX sS 0
      rwa [gameQueries, Nat.add_zero] at h
    have hX : Pr{let z ← pGame A}[KnownForgedX z.1] ≤
        (if nx = 0 then 0 else xmssMultiError nx (Q + 384)) := by
      split_ifs with hnx
      · subst hnx
        exact le_of_eq (prEvent_eq_zero_of_forall_not _ _ fun z h ↦ by
          obtain ⟨j, -⟩ := h; exact j.elim0)
      · exact prEvent_knownForgedX_le_proved A hA hQ126
    refine (prEvent_dForged_le guest A hks).trans ?_
    rw [add_assoc]
    exact add_le_add le_rfl ((add_le_add hX (hS hA)).trans (signatureBounds_le hkey hQq hl))
  · refine (prEvent_le_one _).trans (le_add_left ?_)
    rw [unforgeableBound_eq]
    have h0 : (2 : ℝ≥0∞) ^ 256 ≠ 0 := pow_ne_zero _ two_ne_zero
    have ht : (2 : ℝ≥0∞) ^ 256 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
    rw [← ENNReal.div_self h0 ht]
    exact ENNReal.div_le_div_right (by exact_mod_cast not_lt.mp hl) _

/-- **Unforgeability of the deployed aggregation, under knowledge soundness.** For every proved
leanSPHINCS parameter set, every numbers `n_x`, `n_s` of honest keys, every guest and every
adversary `A` of the deployed game whose game makes at most `q` hash evaluations before
verification: if the deployed aggregation is knowledge sound against `A` with error `ε`, the
deployed verifier, run with the random oracle, accepts a root statement with a forged claim of an
honest key with probability at most `ε + (n_s + n_x/2^23 + 4) · q / 2^127`. -/
theorem aggregate_unforgeable_ks [P : Sphincs.Params] [S : SphincsSet P] {nx ns q : ℕ}
    {ε : ℝ≥0∞} (guest : Program) (A : DAdversary nx ns) (hq : DHashEvals A q)
    (hks : KnowledgeSound guest A ε) :
    Pr{let z ← dGame guest A}[z.1.accepted = true ∧ DForged z.1] ≤
      ε + ((ns : ℝ≥0∞) + nx / 2 ^ 23 + 4) * q / 2 ^ 127 :=
  aggregate_unforgeable_ks_of guest A hq hks fun hA ↦ prEvent_knownForgedS_le_set A hA

/-- **At `2^20 + 2^20` keys: `ε + q / 2^106`**, every parameter set. -/
theorem aggregate_unforgeable_ks_deployed [P : Sphincs.Params] [S : SphincsSet P] {q : ℕ}
    {ε : ℝ≥0∞} (guest : Program) (A : DAdversary (2 ^ 20) (2 ^ 20)) (hq : DHashEvals A q)
    (hks : KnowledgeSound guest A ε) :
    Pr{let z ← dGame guest A}[z.1.accepted = true ∧ DForged z.1] ≤ ε + q / 2 ^ 106 := by
  refine (aggregate_unforgeable_ks guest A hq hks).trans (add_le_add le_rfl ?_)
  rw [unforgeableBound_eq, show (256 : ℕ) = 106 + 150 from rfl, ← cast_mul_two_pow_div q 106 150]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr (Nat.mul_le_mul_left _ (by norm_num))) _

end LeanVM.E2E.KS
