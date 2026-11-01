module

public import LeanVM.Cost.Bounds.Basic
import all LeanVM.Cost.Library

/-!
# Prices of the field operations

`K` and `E` arithmetic compiled once (functions of their own), with their exact prices: the
constants every bound of the extractor's arithmetic is made of.

* `K`: `+` and `−` are one `xor` (inline, `3` with their operands), `·` one `GF(2^64)` product
  (`kMulC_cost`: `258`), the inverse Itoh–Tsujii's `62` squarings and `11` products
  (`kInvC_cost`: at most `19676`, `19674` measured on a nonzero input);
* `E = K[X]/(cubic)`: `+` three `xor`s (`eAddC_cost`: `19`), `·` nine products and the reduction
  (`eMulC_cost`: `2358`).

Inline, the compiler prices `K`'s `·` in a caller's recurrence as `1 + 1 + 256` plus its operands;
a call of `E`'s or of the inverse is a `machineCost` of these functions (or of the on-demand copy
the caller's compilation made: the same recurrence, the same price).
-/

namespace LeanVM.Cost.Bounds.Prices

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Parameters

public section

cost_compile kMulC := fun (x y : K) ↦ x * y

cost_compile kInvC := fun (a : K) ↦ a⁻¹

cost_compile eAddC := fun (x y : E) ↦ x + y

cost_compile eMulC := fun (x y : E) ↦ x * y

variable (P : Program)

theorem kMulC_cost (hP : Includes P kMulC.costDeps) (x y : K) :
    machineCost P 3 [enc x, enc y] = 258 := by
  rw [kMulC.costEq P hP]

theorem powTwoPow_cost (hP : Includes P Auto.BF64.powTwoPow.c6.costDeps) :
    ∀ (k : ℕ) (a : BF64), k < 2 ^ 64 → machineCost P 6 [enc a, enc k] = 6 + 270 * k := by
  intro k
  induction k with
  | zero => intro a _; rw [Auto.BF64.powTwoPow.c6.costEq P hP]; cost_simp
  | succ k ih =>
    intro a hk
    rw [Auto.BF64.powTwoPow.c6.costEq P hP]
    cost_simp
    rw [ih (a * a) (by omega)]
    omega

theorem kInvC_cost (hP : Includes P kInvC.costDeps) (a : K) :
    machineCost P 4 [enc a] ≤ 19676 := by
  have h6 : Includes P Auto.BF64.powTwoPow.c6.costDeps := by includes
  rw [kInvC.costEq P hP, Auto.BF64.invItohTsujii.c5.costEq P (by includes)]
  simp (disch := omega) only [powTwoPow_cost P h6]
  split_ifs <;> omega

theorem eAddC_cost (hP : Includes P eAddC.costDeps) (x y : E) :
    machineCost P 7 [enc x, enc y] = 19 := by
  rw [eAddC.costEq P hP]

theorem eMulC_cost (hP : Includes P eMulC.costDeps) (x y : E) :
    machineCost P 8 [enc x, enc y] = 2358 := by
  rw [eMulC.costEq P hP]

end

end LeanVM.Cost.Bounds.Prices
