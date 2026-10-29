/-
  LeanVM.Guest.B1.Bits.Log2PlacedAll

  The deployed specializations of `log2_ceil_in_the_exponent` (floors `0` and `15`), placed and
  bounded, and their `CompleteAtD` / `CompleteAtDTB` forms.
-/

module

public import LeanVM.Guest.B1.Bits.Log2Placed

/-!
# `log2_ceil_in_the_exponent__L{0,15}_L34`, placed

For `6 ≤ κ`, `N < 2^34` and `L = max fl (log2Ceil N) < 34`: on `g^N` and the exponent tables
(`log2Lin lpE sqE`), `log2_ceil_in_the_exponent__L{fl}_L34` returns `g^L` within
`fs name + 34 + (fs callee + 35)` words (`log2_L0_completeAtB`, `log2_L15_completeAtB`); without the
bound (`…_completeAt`, `CompleteAtD`) and with the trivial tree predicate (`…_completeAtDTB`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen log2Ceil)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

set_option maxRecDepth 100000 in
theorem find_lce_L0 : coreProgram.find? "log2_ceil_in_the_exponent__L0_L34" = some Data.core290 :=
  Program.find?_of_indexOf? (j := 290) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem find_lce_L15 : coreProgram.find? "log2_ceil_in_the_exponent__L15_L34" = some Data.core291 :=
  Program.find?_of_indexOf? (j := 291) (by decide +kernel) rfl

theorem loop_lce_L0 : coreProgram.loop "log2_ceil_in_the_exponent__L0_L34" = false := by
  rw [Program.loop_of_find? find_lce_L0]; decide +kernel

theorem loop_lce_L15 : coreProgram.loop "log2_ceil_in_the_exponent__L15_L34" = false := by
  rw [Program.loop_of_find? find_lce_L15]; decide +kernel

theorem loop_vl_L0 : coreProgram.loop "verify_log2_ceil__L0_L34" = false := by
  rw [Program.loop_of_find? find_verify_log2_ceil_L0_L34]; decide +kernel

theorem loop_vl_L15 : coreProgram.loop "verify_log2_ceil__L15_L34" = false := by
  rw [Program.loop_of_find? find_verify_log2_ceil_L15_L34]; decide +kernel

/-- **`log2_ceil_in_the_exponent__L0_L34`, placed and bounded.** -/
theorem log2_L0_completeAtB (κ : ℕ) (hκ6 : 6 ≤ κ) (N lpE sqE : ℕ) (hN : N < 2 ^ 34)
    (hL : max 0 (log2Ceil N) < 34) :
    CompleteAtB fs cert κ "log2_ceil_in_the_exponent__L0_L34" (log2Lin lpE sqE)
      [gen ^ N, ofK (Parameters.gpow lpE), ofK (Parameters.gpow sqE)]
      (Returns [gen ^ max 0 (log2Ceil N)])
      (fs "log2_ceil_in_the_exponent__L0_L34" + 34 + (fs "verify_log2_ceil__L0_L34" + 35)) :=
  lce_completeAtB 0 (by norm_num) find_lce_L0 rfl rfl loop_lce_L0 find_verify_log2_ceil_L0_L34 rfl
    core406_body loop_vl_L0 κ hκ6 N lpE sqE hN hL

/-- **`log2_ceil_in_the_exponent__L15_L34`, placed and bounded.** -/
theorem log2_L15_completeAtB (κ : ℕ) (hκ6 : 6 ≤ κ) (N lpE sqE : ℕ) (hN : N < 2 ^ 34)
    (hL : max 15 (log2Ceil N) < 34) :
    CompleteAtB fs cert κ "log2_ceil_in_the_exponent__L15_L34" (log2Lin lpE sqE)
      [gen ^ N, ofK (Parameters.gpow lpE), ofK (Parameters.gpow sqE)]
      (Returns [gen ^ max 15 (log2Ceil N)])
      (fs "log2_ceil_in_the_exponent__L15_L34" + 34 + (fs "verify_log2_ceil__L15_L34" + 35)) :=
  lce_completeAtB 15 (by norm_num) find_lce_L15 rfl rfl loop_lce_L15 find_verify_log2_ceil_L15_L34
    rfl core407_body loop_vl_L15 κ hκ6 N lpE sqE hN hL

/-- **`log2_ceil_in_the_exponent__L0_L34`, placed** (the shape of fork c4's `Log2CompleteAt`). -/
theorem log2_L0_completeAt (κ : ℕ) (hκ6 : 6 ≤ κ) : ∀ (N lpE sqE : ℕ), N < 2 ^ 34 →
    max 0 (log2Ceil N) < 34 →
    CompleteAtD fs cert κ "log2_ceil_in_the_exponent__L0_L34" (log2Lin lpE sqE)
      [gen ^ N, ofK (Parameters.gpow lpE), ofK (Parameters.gpow sqE)]
      (Returns [gen ^ max 0 (log2Ceil N)]) :=
  fun N lpE sqE hN hL => (log2_L0_completeAtB κ hκ6 N lpE sqE hN hL).toCompleteAtD

/-- **`log2_ceil_in_the_exponent__L15_L34`, placed** (the shape of fork c4's `Log2CompleteAt`). -/
theorem log2_L15_completeAt (κ : ℕ) (hκ6 : 6 ≤ κ) : ∀ (N lpE sqE : ℕ), N < 2 ^ 34 →
    max 15 (log2Ceil N) < 34 →
    CompleteAtD fs cert κ "log2_ceil_in_the_exponent__L15_L34" (log2Lin lpE sqE)
      [gen ^ N, ofK (Parameters.gpow lpE), ofK (Parameters.gpow sqE)]
      (Returns [gen ^ max 15 (log2Ceil N)]) :=
  fun N lpE sqE hN hL => (log2_L15_completeAtB κ hκ6 N lpE sqE hN hL).toCompleteAtD

/-- `log2_ceil_in_the_exponent__L0_L34`, placed, bounded, any tree. -/
theorem log2_L0_completeAtDTB (κ : ℕ) (hκ6 : 6 ≤ κ) (N lpE sqE : ℕ) (hN : N < 2 ^ 34)
    (hL : max 0 (log2Ceil N) < 34) :
    CompleteAtDTB fs cert κ "log2_ceil_in_the_exponent__L0_L34" (log2Lin lpE sqE)
      [gen ^ N, ofK (Parameters.gpow lpE), ofK (Parameters.gpow sqE)]
      (Returns [gen ^ max 0 (log2Ceil N)]) (fun _ => True)
      (fs "log2_ceil_in_the_exponent__L0_L34" + 34 + (fs "verify_log2_ceil__L0_L34" + 35)) :=
  (log2_L0_completeAtB κ hκ6 N lpE sqE hN hL).toDTB

/-- `log2_ceil_in_the_exponent__L15_L34`, placed, bounded, any tree. -/
theorem log2_L15_completeAtDTB (κ : ℕ) (hκ6 : 6 ≤ κ) (N lpE sqE : ℕ) (hN : N < 2 ^ 34)
    (hL : max 15 (log2Ceil N) < 34) :
    CompleteAtDTB fs cert κ "log2_ceil_in_the_exponent__L15_L34" (log2Lin lpE sqE)
      [gen ^ N, ofK (Parameters.gpow lpE), ofK (Parameters.gpow sqE)]
      (Returns [gen ^ max 15 (log2Ceil N)]) (fun _ => True)
      (fs "log2_ceil_in_the_exponent__L15_L34" + 34 + (fs "verify_log2_ceil__L15_L34" + 35)) :=
  (log2_L15_completeAtB κ hκ6 N lpE sqE hN hL).toDTB

end
end LeanVM.Guest.B1
