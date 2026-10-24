/-
  LeanVM.Guest.Count.VsBound

  **`verify_sub`'s words per child at the deployed instance**, at the child's candidate:
  `260516 + osC (candidate μ r)` (`vsBoundAt_eq`), its callees' bounds evaluated by the kernel
  (`open_stacked`'s per candidate, `Count/VsOs*`).
-/

module

public import LeanVM.Guest.Count.VsOsAll
public import LeanVM.Guest.Count.VsMax
public import LeanVM.Guest.B1.VerifySub.CompleteBT

namespace LeanVM.Guest.Count

open LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem bg_eq : vsWords.Bg = 50 := by
  show wSB "g_power_of_word" = 50
  rw [← wSBFast_eq]; decide +kernel

set_option maxRecDepth 100000 in
theorem ba_eq : vsWords.Ba = 10 := by
  show wSB "assert_canonical" = 10
  rw [← wSBFast_eq]; decide +kernel

set_option maxRecDepth 100000 in
theorem vkBound_eq : B1.VerifySub.vkBound = 87672 := by
  show B2C.fs "verify_keccak" + 464 + 81723 = 87672
  rw [← fsFast_eq]; decide +kernel

set_option maxRecDepth 100000 in
theorem termBound_eq : B1.VerifySub.termBound B2C.fs vsWords.Beqc vsWords.K15 vsWords.Bcs vsWords.Brs = 38888 := by
  show B2C.fs "check_opening_terminal" + 146 + 3 * 184 + max (B2C.fs "__loop15") (32 * 38) +
    (B2C.fs "selector_tables" + 322) + 99 * 157 + (B2C.fs "ring_switch_weight" + 2240 + 16433) = 38888
  rw [← fsFast_eq]; decide +kernel

set_option maxRecDepth 100000 in
/-- The frames `verify_sub`'s bound names. -/
theorem vs_frames : B2C.fs "verify_sub" = 1390 ∧ B2C.fs "log2_ceil_in_the_exponent__L0_L34" = 14 ∧
    B2C.fs "verify_log2_ceil__L0_L34" = 381 ∧ B2C.fs "ring_switch_target" = 12 ∧
    B2C.fs "certify_placement" = 2293 ∧ B2C.fs "log2_ceil_in_the_exponent__L15_L34" = 14 ∧
    B2C.fs "verify_log2_ceil__L15_L34" = 382 := by
  rw [← fsFast_eq]; decide +kernel

set_option maxRecDepth 100000 in
/-- **`verify_sub`'s words for a child at candidate `candidate μ r`** at the deployed instance:
its frame `1390`, its buffers `9156`, `g_power_of_word` (`50`, twice), the two `log2_ceil` chains
(`464`, `465`), `assert_canonical` (`10`, twice), `verify_bus_gkr` (`49403`), `verify_tables`
(`59762`), `verify_keccak` (`87672`), `ring_switch_target` (`10606`), `certify_placement` (`2590`)
and the terminal (`38888`), `260516` in all, and `open_stacked` at the candidate (`osC`). -/
theorem vsBoundAt_eq {μ r : ℕ} (h : candidate μ r < 28) :
    B1.VerifySub.vsBoundAt vsWords B1.VerifySub.vkBound μ r = 260516 + osC (candidate μ r) := by
  rw [B1.VerifySub.vsBoundAt.eq_1, B1.VerifySub.vsBsAt.eq_1, vbgMax_eq, vtMax_eq, bg_eq, ba_eq,
    vkBound_eq, termBound_eq]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := vs_frames
  rw [h1, h2, h3, h4, h5, h6, h7, show vsWords.B14 = 10576 from rfl,
    show vsWords.Bnd = osBnd from rfl, show vsWords.Kr = wSK from rfl, osBosAt_eq h]
  simp only [List.sum_cons, List.sum_nil]
  omega

end
end LeanVM.Guest.Count
