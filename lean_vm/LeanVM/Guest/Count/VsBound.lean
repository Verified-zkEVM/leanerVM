/-
  LeanVM.Guest.Count.VsBound

  **`verify_sub`'s words per child at the deployed instance**: `Budget.deployedBv = 661678`, its
  callees' maxima evaluated by the kernel (`open_stacked`'s per candidate, `Count/VsOs*`).
-/

module

public import LeanVM.Guest.Count.VsOs00
public import LeanVM.Guest.Count.VsOs01
public import LeanVM.Guest.Count.VsOs02
public import LeanVM.Guest.Count.VsOs03
public import LeanVM.Guest.Count.VsOs04
public import LeanVM.Guest.Count.VsOs05
public import LeanVM.Guest.Count.VsOs06
public import LeanVM.Guest.Count.VsOs07
public import LeanVM.Guest.Count.VsOs08
public import LeanVM.Guest.Count.VsOs09
public import LeanVM.Guest.Count.VsOs10
public import LeanVM.Guest.Count.VsOs11
public import LeanVM.Guest.Count.VsOs12
public import LeanVM.Guest.Count.VsOs13
public import LeanVM.Guest.Count.VsOs14
public import LeanVM.Guest.Count.VsOs15
public import LeanVM.Guest.Count.VsOs16
public import LeanVM.Guest.Count.VsOs17
public import LeanVM.Guest.Count.VsOs18
public import LeanVM.Guest.Count.VsOs19
public import LeanVM.Guest.Count.VsOs20
public import LeanVM.Guest.Count.VsOs21
public import LeanVM.Guest.Count.VsOs22
public import LeanVM.Guest.Count.VsOs23
public import LeanVM.Guest.Count.VsOs24
public import LeanVM.Guest.Count.VsOs25
public import LeanVM.Guest.Count.VsOs26
public import LeanVM.Guest.Count.VsOs27
public import LeanVM.Guest.Count.VsMax

namespace LeanVM.Guest.Count

open LeanVM.Guest.B1.Whir

@[expose] public section

/-- Every candidate within candidate `6`'s (`μ = 28`, rate `1`). -/
theorem osC_le : ∀ c < 28, osC c ≤ 401162 := by
  intro c hc
  interval_cases c
  · have := osC_0; omega
  · have := osC_1; omega
  · have := osC_2; omega
  · have := osC_3; omega
  · have := osC_4; omega
  · have := osC_5; omega
  · have := osC_6; omega
  · have := osC_7; omega
  · have := osC_8; omega
  · have := osC_9; omega
  · have := osC_10; omega
  · have := osC_11; omega
  · have := osC_12; omega
  · have := osC_13; omega
  · have := osC_14; omega
  · have := osC_15; omega
  · have := osC_16; omega
  · have := osC_17; omega
  · have := osC_18; omega
  · have := osC_19; omega
  · have := osC_20; omega
  · have := osC_21; omega
  · have := osC_22; omega
  · have := osC_23; omega
  · have := osC_24; omega
  · have := osC_25; omega
  · have := osC_26; omega
  · have := osC_27; omega

/-- **`open_stacked`'s largest bound over the candidates.** -/
theorem osMax_eq : B1.VerifySub.osMax B2C.fs wSB wSK = 401162 := by
  apply le_antisymm
  · unfold B1.VerifySub.osMax
    apply lmax_le
    intro x hx
    simp only [List.mem_flatMap, List.mem_range, List.mem_map] at hx
    obtain ⟨μ, hμ, r, hr, rfl⟩ := hx
    have hc : candidate μ r < 28 := by unfold candidate; omega
    rw [osBosAt_eq hc]
    exact osC_le _ hc
  · have h := B1.VerifySub.le_lmax2 (B1.osBosAt B2C.fs wSB wSK) (show 28 < 29 by omega)
      (show 1 < 5 by omega)
    have hc : candidate 28 1 < 28 := by unfold candidate; omega
    rw [osBosAt_eq hc, show candidate 28 1 = 6 by rfl, osC_6] at h
    unfold B1.VerifySub.osMax
    exact h

theorem osMax_eq' : B1.VerifySub.osMax B2C.fs vsWords.Bnd vsWords.Kr = 401162 := osMax_eq

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
/-- **`verify_sub`'s words per child at the deployed instance**: its frame `1390`, its buffers
`9156`, `g_power_of_word` (`50`, twice), the two `log2_ceil` chains (`464`, `465`),
`assert_canonical` (`10`, twice), `verify_bus_gkr` (`49403`), `verify_tables` (`59762`),
`verify_keccak` (`87672`), `ring_switch_target` (`10606`), `certify_placement` (`2590`),
`open_stacked` (`401162`) and the terminal (`38888`). -/
theorem deployedBv_eq : Budget.deployedBv = 661678 := by
  rw [show Budget.deployedBv = B1.VerifySub.vsBound vsWords B1.VerifySub.vkBound from rfl,
    B1.VerifySub.vsBound.eq_1, B1.VerifySub.vsBs.eq_1, vbgMax_eq, vtMax_eq, osMax_eq', bg_eq, ba_eq,
    vkBound_eq, termBound_eq]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := vs_frames
  rw [h1, h2, h3, h4, h5, h6, h7, show vsWords.B14 = 10576 from rfl]
  rfl

end
end LeanVM.Guest.Count
