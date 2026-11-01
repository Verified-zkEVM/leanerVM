module

public import LeanVM.Cost.Bounds.Basic
public import LeanVM.Cost.Extractor.Transcript

/-!
# Bounds: the committed word's reader

* `replicate_cost`: `List.replicate n a` costs at most `17·n + 6`, for word-sized `n`;
* **`leafAt_cost`**: reading a position of the committed word (`leafAt leaves h w v`, the leaf
  `v mod 2^h`, or `w` zeros) costs at most `17·w + 19`, for `h < 64` and word-sized `v`, `w`.

The committed leaves themselves are bounded by the sample's `committedLeaves_cost`
(`Bounds/Samples/CommittedLeaves.lean`): at most `2^h·(2·L + 617·w + 12060 + 8·h) + 7`, `L` the
preimage lookup's price (`preimageLookup_cost`: `40 + |levels|·(18 + 192·(log₂ N + 2))`, at most
`log₂(N + 1)` levels after `N` insertions by `sm_two_pow_levels_le`).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Extraction LeanVM.Extraction.Fast

public section

variable (P : Program)

/-- `List.replicate n a`: at most `17·n + 6`. -/
theorem replicate_cost (hP : Includes P Auto.List.replicate.c9.costDeps) {α : Type} [Enc α]
    (a : α) : ∀ n, n < 2 ^ 64 →
      machineCost P Auto.List.replicate.c9.costIdx [enc n, enc a] ≤ 17 * n + 6 := by
  intro n
  induction n with
  | zero => intro _; rw [Auto.List.replicate.c9.costEq_zero P hP]
  | succ n ih =>
    intro hn
    rw [Auto.List.replicate.c9.costEq_succ P hP, limbs_of_lt hn]
    have := ih (by omega)
    omega

/-- **A position of the committed word**: at most `17·w + 19`. -/
theorem leafAt_cost (hP : Includes P leafAtC.costDeps) (leaves : Array (List K)) (h w v : ℕ)
    (hh : h < 64) (hv : v < 2 ^ 64) (hw : w < 2 ^ 64) :
    machineCost P leafAtC.costIdx [enc leaves, enc h, enc w, enc v] ≤ 17 * w + 19 := by
  rw [leafAtC.costEq P hP]
  have h2 : 2 ^ h < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hh
  have hr := replicate_cost P (by includes) (0 : K) w hw
  rw [Nat.one_shiftLeft, limbs_of_lt h2, limbs_of_lt (by omega : h < 2 ^ 64), limbs_of_lt hv]
  omega

end

end LeanVM.Cost.Bounds
