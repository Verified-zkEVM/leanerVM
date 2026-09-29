/-
  Probe for task code-layer1, deliverables D and E: which Layer 1 statements are already in
  CompPoly at the pin (3468b38c), and which are instances of one another.

  Run from the repository root:
    flock .claude/reports/blueprint-review/logs/lean.lock \
      lake env lean .claude/reports/blueprint-review/probes/code-layer1/DuplicatesProbe.lean
-/
import LeanerVM.Protocol.ToCompPoly.BitProductTable
import LeanerVM.Protocol.ToCompPoly.AmbientStacking

open LeanerVM.Protocol CompPoly CMlPolynomialEval

namespace Probe

variable {R : Type*} [CommRing R]

/-- `evalMle_lagrangeBasis` is CompPoly's `eqTilde_eq_prod` (`Multilinear/Basic.lean:600`),
with the factors written in the other order. -/
example {n : ℕ} (w x : Vector R n) :
    evalMle (lagrangeBasis w) x = ∏ k : Fin n, ((1 - x[k]) * (1 - w[k]) + x[k] * w[k]) := by
  have h := eqTilde_eq_prod w x
  rw [eqTilde, ← eval_mle_eq_eval] at h
  rw [h]
  exact Finset.prod_congr rfl fun i _ ↦ by ring

/-- `unstack_eval` is `unstack_eval₂` at the identity map. -/
example (B : Blocks) {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (q : CMlPolynomialEval R μ) (b : Fin B.n)
    (z : Vector R (B.size b)) :
    evalMle q (B.extendPoint hμ b z) = evalMle (B.unstack hμ q b) z := by
  have h := B.unstack_eval₂ (RingHom.id R) hμ q b z
  simpa [eval₂Mle, CMlPolynomialEval.map] using h

/-- `stack_eval` is `unstack_eval` on a stack. -/
example (B : Blocks) (t : B.Tables R) {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (pad : R) (b : Fin B.n)
    (z : Vector R (B.size b)) :
    evalMle (B.stackAt t μ pad) (B.extendPoint hμ b z) = evalMle (t b) z := by
  rw [B.unstack_eval hμ, B.unstack_stackAt]

/-- `stack_eval_ambient_zero` is `stack_eval_ambient` at pad zero. -/
example (B : Blocks) (t : B.Tables R) {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (z : Vector R μ) :
    evalMle (B.stackAt t μ 0) z =
      ∑ b : Fin B.n, B.selectorWeight hμ b z * evalMle (t b) (B.lowPoint hμ b z) := by
  simpa using B.stack_eval_ambient t hμ 0 z

/-- The largest-first order is sufficient for alignment, not necessary: sizes 1, 1, 2 are
aligned at offsets 0, 2, 4 and are no `Blocks`. -/
example : ¬ Antitone (![1, 1, 2] : Fin 3 → ℕ) := fun h ↦
  absurd (h (show (0 : Fin 3) ≤ 2 by decide)) (by decide)

#guard (2 ^ 1 ∣ 0) ∧ (2 ^ 1 ∣ 2) ∧ (2 ^ 2 ∣ 4)

end Probe
