module

public import LeanVM.Cost.Bounds.Basic
public import LeanVM.Cost.Extractor.GsRun

/-!
# Bounds: the field's functions, compiled

One bound per function of `K = GF(2^64)` (CompPoly's `BF64`, `Cost/Rules.lean`'s `powSq`) as the
extractor's chain compiles it, for every bound that calls it:

* `powTwoPow_cost`: `a^(2^k)` by `k` squarings, `6 + 270·k` exactly (a square is a product of
  price `256`);
* **`invK_cost`**: the inverse (Itoh–Tsujii), at most `19676`;
* `powSq_cost`: `a^n` by squaring, `535` per bit and `6` (`powSq_cost_le`, `powSq_cost_le'`: for
  `n ≤ 3`, `n ≤ 15`).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Library LeanVM.Parameters

public section

variable (P : MachineProgram)

/-- `a^(2^k)` by `k` squarings (`powTwoPow.c10`): `6 + 270·k` exactly. -/
theorem powTwoPow_cost (hP : Includes P Auto.BF64.powTwoPow.c10.costDeps) :
    ∀ (k : ℕ) (a : BF64), k < 2 ^ 64 →
      machineCost P Auto.BF64.powTwoPow.c10.costIdx [encodeValue a, encodeValue k] = 6 + 270 * k := by
  intro k
  induction k with
  | zero => intro a _; rw [Auto.BF64.powTwoPow.c10.costEq_zero P hP]
  | succ k ih =>
    intro a hk
    rw [Auto.BF64.powTwoPow.c10.costEq_succ P hP, ih (a * a) (by omega)]
    cost_simp
    omega

/-- **The inverse in `K`** (Itoh–Tsujii, `invItohTsujii.c9`): at most `19676`. -/
theorem invK_cost (hP : Includes P Auto.BF64.invItohTsujii.c9.costDeps) (a : BF64) :
    machineCost P Auto.BF64.invItohTsujii.c9.costIdx [encodeValue a] ≤ 19676 := by
  have h6 : Includes P Auto.BF64.powTwoPow.c10.costDeps := by includes
  rw [Auto.BF64.invItohTsujii.c9.costEq P hP]
  simp (disch := omega) only [powTwoPow_cost P h6]
  split_ifs <;> omega

/-- `a^n` by squaring (`powSq.c100`): `535` per bit, `6` at the end. -/
theorem powSq_cost (hP : Includes P Auto.LeanVM.Cost.Rewrite.powSq.c100.costDeps) (a : K) (n : ℕ)
    (hn : n < 2 ^ 64) :
    machineCost P Auto.LeanVM.Cost.Rewrite.powSq.c100.costIdx [encodeValue a, encodeValue n] ≤
      6 + 535 * (Nat.log2 n + 1) := by
  have := le_of_halving (fun x : K × ℕ ↦ x.2 < 2 ^ 64) (fun x ↦ x.2)
    (fun x ↦ machineCost P Auto.LeanVM.Cost.Rewrite.powSq.c100.costIdx [encodeValue x.1, encodeValue x.2]) 535 6
    (fun x hx h0 ↦ by
      try dsimp only at hx h0 ⊢
      rw [Auto.LeanVM.Cost.Rewrite.powSq.c100.costEq P hP, h0]
      simp)
    (fun x hx hpos ↦ by
      try dsimp only at hx hpos ⊢
      right
      refine ⟨(x.1 * x.1, x.2 / 2), by dsimp only; omega, le_refl _, ?_⟩
      rw [Auto.LeanVM.Cost.Rewrite.powSq.c100.costEq P hP, limbs_of_lt hx,
        limbs_of_lt (by omega : x.2 % 2 < 2 ^ 64)]
      simp only [show x.2 ≠ 0 by omega, ↓reduceIte]
      split_ifs <;> omega)
    (a, n) hn
  simpa using this

theorem powSq_cost_le (hP : Includes P Auto.LeanVM.Cost.Rewrite.powSq.c100.costDeps) (a : K) (n : ℕ)
    (hn : n ≤ 3) : machineCost P Auto.LeanVM.Cost.Rewrite.powSq.c100.costIdx [encodeValue a, encodeValue n] ≤ 1076 := by
  refine (powSq_cost P hP a n (by omega)).trans ?_
  have := log2_lt_of (k := 2) (by norm_num) (by omega : n < 2 ^ 2)
  omega

theorem powSq_cost_le' (hP : Includes P Auto.LeanVM.Cost.Rewrite.powSq.c100.costDeps) (a : K) (n : ℕ)
    (hn : n ≤ 15) : machineCost P Auto.LeanVM.Cost.Rewrite.powSq.c100.costIdx [encodeValue a, encodeValue n] ≤ 2146 := by
  refine (powSq_cost P hP a n (by omega)).trans ?_
  have := log2_lt_of (k := 4) (by norm_num) (by omega : n < 2 ^ 4)
  omega

end

end LeanVM.Cost.Bounds
