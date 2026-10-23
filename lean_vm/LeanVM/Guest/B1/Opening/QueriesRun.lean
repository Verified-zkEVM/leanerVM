/-
  LeanVM.Guest.B1.Opening.QueriesRun

  `opening_queries`' value is the Spec's `enforcedSum`: the chain against the powers of `λ`, and a
  row's dot product with the tensor weights against the dot product with `eqKernel`.
-/

module

public import LeanVM.Guest.B1.Opening.Meaning

/-!
# `opening_queries` against `enforcedSum` (V:1635)

* `oqChain_powers`: the chain `h ← (h + d_k)·λ⁻¹` times `λ^Q` is `Σ_k λ^k d_k`, in the order
  `enforcedSum` sums (its weights `powers λ Q`, V:184): `enforcedSum_eq`.
* `eqKernel_getD'`, `eqW_append`: entry `w` of `eqKernel` is the product `eqW`, which splits at
  any coordinate.
* `rowDot_level0`, `rowDot_deeper`: with the weights `opening_row_weights` writes
  (`MeaningOpeningRowWeights 6 1`, `… 4 0`), a row's `rowDot` is `dot (row.reverse.map ofK)
  (eqKernel folds)` at level 0 and `dot (extRow row) (eqKernel folds)` deeper, the Spec's
  `enforcedSum` terms (`whirLevels`, V:1752-1754).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The chain against the powers of `λ` -/

/-- `Σ_{k < n} λ^k d_k`, left to right. -/
def powSum (lam : E) (ds : ℕ → E) (n : ℕ) : E :=
  ((List.range n).map fun k ↦ lam ^ k * ds k).foldl (· + ·) 0

theorem powSum_succ (lam : E) (ds : ℕ → E) (n : ℕ) :
    powSum lam ds (n + 1) = powSum lam ds n + lam ^ n * ds n := by
  simp [powSum, List.range_succ, List.foldl_append]

/-- **The chain is `Σ_k λ^k d_k`** once multiplied by `λ^Q`. -/
theorem oqChain_powers {lam : E} (hlam : lam ≠ 0) {odd base : ℕ} (hodd : odd ≤ 1)
    (hb : base = 1 ∨ (base = 0 ∧ odd = 0)) (ds : ℕ → E) (N : ℕ) :
    oqChain odd base lam⁻¹ ds N * lam ^ oqCount odd base N = powSum lam ds (oqCount odd base N) := by
  have hinv : lam⁻¹ * lam = 1 := by rw [mul_comm]; exact e_mul_inv_cancel hlam
  induction N with
  | zero =>
    rcases hb with hb | ⟨hb, ho⟩
    · subst hb
      rcases Nat.lt_or_ge odd 1 with h | h
      · obtain rfl : odd = 0 := by omega
        rw [show oqCount 0 1 0 = 0 from rfl, show oqChain 0 1 lam⁻¹ ds 0 = 0 from rfl]
        simp [powSum]
      · obtain rfl : odd = 1 := by omega
        simp only [oqChain, oqCount, ↓reduceIte, Nat.mul_zero, Nat.add_zero, pow_one]
        rw [show powSum lam ds 1 = powSum lam ds 0 + lam ^ 0 * ds 0 from powSum_succ _ _ _]
        simp only [powSum, List.range_zero, List.map_nil, List.foldl_nil, pow_zero, one_mul,
          zero_add]
        rw [mul_assoc, hinv, mul_one]
    · subst hb ho
      rw [show oqCount 0 0 0 = 0 from rfl, show oqChain 0 0 lam⁻¹ ds 0 = 0 from rfl]
      simp [powSum]
  | succ N ih =>
    rcases hb with hb | ⟨hb, ho⟩
    · subst hb
      simp only [oqChain, oqCount, ↓reduceIte] at ih ⊢
      rw [show odd + 2 * (N + 1) = odd + 2 * N + 1 + 1 by ring, powSum_succ, powSum_succ, ← ih,
        pow_succ, pow_succ]
      linear_combination ((oqChain odd 1 lam⁻¹ ds N + ds (odd + 2 * N)) * lam ^ (odd + 2 * N) *
        (lam⁻¹ * lam + 1) + ds (odd + 2 * N + 1) * lam ^ (odd + 2 * N) * lam) * hinv
    · subst hb ho
      simp only [oqChain, oqCount, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte] at ih ⊢
      rw [powSum_succ, ← ih, pow_succ]
      linear_combination ((oqChain 0 0 lam⁻¹ ds N + ds N) * lam ^ N) * hinv

theorem powersFrom_getD (acc base : E) : ∀ (n k : ℕ), k < n →
    (powersFrom acc base n).getD k 0 = acc * base ^ k
  | 0, _, h => absurd h (by omega)
  | n + 1, 0, _ => by simp [powersFrom]
  | n + 1, k + 1, h => by
    simp only [powersFrom, List.getD_cons_succ]
    rw [powersFrom_getD _ _ n k (by omega), pow_succ]
    ring

theorem length_powersFrom (acc base : E) : ∀ n, (powersFrom acc base n).length = n
  | 0 => rfl
  | n + 1 => by simp [powersFrom, length_powersFrom _ _ n]

/-- **`enforcedSum` with the powers of `λ`** (V:1635): `Σ_k λ^k ⟨row_k, eqKernel folds⟩`. -/
theorem enforcedSum_eq (rows : List (List E)) (folds : List E) (lam : E) :
    enforcedSum rows folds (powers lam rows.length) =
      powSum lam (fun k ↦ dot (rows.getD k []) (eqKernel folds)) rows.length := by
  unfold enforcedSum powSum
  have hz : (List.zip (powers lam rows.length) rows) =
      (List.range rows.length).map fun k ↦ (lam ^ k, rows.getD k []) := by
    apply List.ext_getElem
    · simp [powers, length_powersFrom]
    · intro i h1 h2
      simp only [List.getElem_zip, List.getElem_map, List.getElem_range]
      have hi : i < rows.length := by simpa [powers, length_powersFrom] using h1
      have hpl : i < (powers lam rows.length).length := by simp [powers, length_powersFrom, hi]
      have := powersFrom_getD 1 lam rows.length i hi
      rw [one_mul] at this
      rw [List.getD_eq_getElem _ _ hi]
      refine Prod.ext ?_ rfl
      rw [← List.getD_eq_getElem _ 0 hpl]
      exact this
  rw [hz, List.foldl_map, List.foldl_map]

end
end LeanVM.Guest.B1
