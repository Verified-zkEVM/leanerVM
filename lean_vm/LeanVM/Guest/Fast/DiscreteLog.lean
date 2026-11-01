/-
  LeanVM.Guest.Fast.DiscreteLog

  The decoder's two discrete-logarithm readers, `gLog` and `cursorLen`, restated through the
  computable `discreteLog` and proved equal to the originals.
-/

module

public import LeanVM.Protocol.Extraction.Fast.DiscreteLog
public import LeanVM.Guest.B1.Main.Interface
public import LeanVM.Guest.B1.VerifySub.Proof

/-!
# The decoder's logarithms, computable

* `gLog` (`B1/Main/Interface.lean`) reads the exponent below `2^34` of a word's low limb through
  `addressIndex? 34`, a classical choice; **`gLogFast_eq`**: `gLogFast`, `discreteLog` of the limb
  kept below `2^34`, is `gLog` on every word.
* `cursorLen` (`B1/VerifySub/Proof.lean`) scans `n ≤ 2^32` for `q = p · gen^n`;
  **`cursorLenFast_eq`**: `cursorLenFast` divides a nonzero limb of `q` by `p`'s (`limbQuot`),
  takes `discreteLog` of the quotient and checks `q = p · g^n` limb by limb, and is `cursorLen`
  on every pair.

Both read `discreteLog`'s result through `Option.filter` and `Option.getD`, not a `match`: a
`match` on `discreteLog a`, unfolded, sends the kernel evaluating `discreteLog`'s closed tables.
-/

namespace LeanVM.Guest.Fast

open LeanVM.Parameters LeanVM.Semantics LeanVM.Extraction.Fast LeanVM.Protocol.Verifier
open LeanVM.Guest.Value LeanVM.Guest.B1

public section

/-- **`gLog`, computable**: the exponent below `2^34` of the low limb, `0` for other words. -/
@[expose] def gLogFast (x : E) : ℕ := ((discreteLog (x.limb 0)).filter (· < 2 ^ 34)).getD 0

theorem gLogFast_eq (x : E) : gLogFast x = Main.gLog x := by
  unfold Main.gLog gLogFast
  cases h : discreteLog (x.limb 0) with
  | none =>
    rw [(gLog?_eq_none_iff (κ := 34)).2 fun i hi ↦ by
      rw [discreteLog_complete hi.symm (by have := i.isLt; omega)] at h
      exact absurd h (by simp)]
    rfl
  | some n =>
    obtain ⟨hx, hn⟩ := discreteLog_sound h
    rw [Option.filter_some]
    by_cases hn34 : n < 2 ^ 34
    · rw [(gLog?_spec (κ := 34) (i := ⟨n, hn34⟩) (by norm_num)).2 hx.symm]
      simp only [Option.map_some, Option.getD_some]
      split <;> simp_all
    · rw [← hx, gLog?_gpow_eq_none (by omega) hn]
      simp only [Option.map_none, Option.getD_none]
      split
      · simp only [decide_eq_true_eq] at *
        omega
      · rfl

/-- `q / p` on the first nonzero limb of `p` (`0` when `p = 0`): `g^n` when `q = p · gen^n`. -/
@[expose] def limbQuot (p q : E) : K :=
  if p.limb 0 ≠ 0 then q.limb 0 * (p.limb 0)⁻¹
  else if p.limb 1 ≠ 0 then q.limb 1 * (p.limb 1)⁻¹ else q.limb 2 * (p.limb 2)⁻¹

/-- **`cursorLen`, computable**: the logarithm `n` of `a = q / p` (`limbQuot`), kept when
`n ≤ 2^32` and `q = p · a` limb by limb; `0` otherwise. -/
@[expose] def cursorLenFast (p q : E) : ℕ :=
  let a := limbQuot p q
  ((discreteLog a).filter fun n ↦
    n ≤ 2 ^ 32 ∧ q = E.ofLimbs (p.limb 0 * a) (p.limb 1 * a) (p.limb 2 * a)).getD 0

theorem mul_gen_pow_eq (p : E) (n : ℕ) :
    p * gen ^ n = E.ofLimbs (p.limb 0 * g ^ n) (p.limb 1 * g ^ n) (p.limb 2 * g ^ n) := by
  rw [gen_pow_eq_ofK, eq_ofLimbs p, ofLimbs_mul_ofK]
  simp only [ofLimbs_limb0, ofLimbs_limb1, ofLimbs_limb2]

theorem limbQuot_mul_gen_pow {p : E} (hp : p ≠ 0) (n : ℕ) : limbQuot p (p * gen ^ n) = g ^ n := by
  unfold limbQuot
  rw [mul_gen_pow_eq]
  simp only [ofLimbs_limb0, ofLimbs_limb1, ofLimbs_limb2]
  split_ifs with h0 h1
  · field_simp
  · field_simp
  · have h2 : p.limb 2 ≠ 0 := fun h2 ↦ hp (by
      rw [eq_ofLimbs p, eq_ofLimbs (0 : E), ofLimbs_inj]
      simp only [limb_zero]
      exact ⟨not_not.1 h0, not_not.1 h1, h2⟩)
    field_simp

theorem limbQuot_zero (q : E) : limbQuot 0 q = 0 := by
  simp [limbQuot, limb_zero]

theorem cursorLenFast_eq (p q : E) : cursorLenFast p q = VerifySub.cursorLen p q := by
  simp only [cursorLenFast]
  cases h : discreteLog (limbQuot p q) with
  | none =>
    rw [Option.filter_none, Option.getD_none]
    by_cases hex : ∃ n ≤ 2 ^ 32, q = p * gen ^ n
    · obtain ⟨n, hn, rfl⟩ := hex
      by_cases hp : p = 0
      · subst hp
        unfold VerifySub.cursorLen
        rw [zero_mul, List.range_succ_eq_map, List.find?_cons]
        simp
      · rw [limbQuot_mul_gen_pow hp, discreteLog_complete rfl (by omega)] at h
        exact absurd h (by simp)
    · unfold VerifySub.cursorLen
      rw [List.find?_eq_none.2 fun n hn h ↦ hex ⟨n, by simpa [Nat.lt_succ_iff] using hn,
        of_decide_eq_true h⟩]
      rfl
  | some n =>
    obtain ⟨hx, hn⟩ := discreteLog_sound h
    rw [Option.filter_some]
    by_cases hc : n ≤ 2 ^ 32 ∧ q = E.ofLimbs (p.limb 0 * limbQuot p q) (p.limb 1 * limbQuot p q)
        (p.limb 2 * limbQuot p q)
    · simp only [decide_eq_true hc, ↓reduceIte, Option.getD_some]
      obtain ⟨hn32, hq⟩ := hc
      rw [← hx, ← mul_gen_pow_eq] at hq
      by_cases hp : p = 0
      · subst hp
        rw [limbQuot_zero] at hx
        exact absurd hx (pow_ne_zero n g_ne_zero)
      · rw [VerifySub.cursorLen_eq hp hq hn32]
    · simp only [decide_eq_false hc, Bool.false_eq_true, ↓reduceIte, Option.getD_none]
      by_cases hex : ∃ m ≤ 2 ^ 32, q = p * gen ^ m
      · obtain ⟨m, hm, rfl⟩ := hex
        by_cases hp : p = 0
        · subst hp
          rw [limbQuot_zero] at hx
          exact absurd hx (pow_ne_zero n g_ne_zero)
        · rw [limbQuot_mul_gen_pow hp, discreteLog_complete rfl (by omega)] at h
          obtain rfl := Option.some.inj h
          exact absurd ⟨hm, by rw [limbQuot_mul_gen_pow hp, ← mul_gen_pow_eq]⟩ hc
      · unfold VerifySub.cursorLen
        rw [List.find?_eq_none.2 fun n hn h ↦ hex ⟨n, by simpa [Nat.lt_succ_iff] using hn,
          of_decide_eq_true h⟩]
        rfl

end

end LeanVM.Guest.Fast
