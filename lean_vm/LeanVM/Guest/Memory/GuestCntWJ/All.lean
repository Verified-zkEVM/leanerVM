/-
  LeanVM.Guest.Memory.GuestCntWJ.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntWJ.Part00
public import LeanVM.Guest.Memory.GuestCntWJ.Part01
public import LeanVM.Guest.Memory.GuestCntWJ.Part02
public import LeanVM.Guest.Memory.GuestCntWJ.Part03
public import LeanVM.Guest.Memory.GuestCntWJ.Part04
public import LeanVM.Guest.Memory.GuestCntWJ.Part05

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kujchkIdx_all : ∀ j < 878, kujchkIdx j = true := by
  intro j hj
  by_cases h0 : j < 10
  · exact kujstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kujstaticRange_10.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kujstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 73
  · exact kujstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 102
  · exact kujstaticRange_73.get (by omega) (by omega)
  by_cases h5 : j < 128
  · exact kujstaticRange_102.get (by omega) (by omega)
  by_cases h6 : j < 155
  · exact kujstaticRange_128.get (by omega) (by omega)
  by_cases h7 : j < 178
  · exact kujstaticRange_155.get (by omega) (by omega)
  by_cases h8 : j < 204
  · exact kujstaticRange_178.get (by omega) (by omega)
  by_cases h9 : j < 230
  · exact kujstaticRange_204.get (by omega) (by omega)
  by_cases h10 : j < 260
  · exact kujstaticRange_230.get (by omega) (by omega)
  by_cases h11 : j < 286
  · exact kujstaticRange_260.get (by omega) (by omega)
  by_cases h12 : j < 299
  · exact kujstaticRange_286.get (by omega) (by omega)
  by_cases h13 : j < 306
  · exact kujstaticRange_299.get (by omega) (by omega)
  by_cases h14 : j < 313
  · exact kujstaticRange_306.get (by omega) (by omega)
  by_cases h15 : j < 343
  · exact kujstaticRange_313.get (by omega) (by omega)
  by_cases h16 : j < 373
  · exact kujstaticRange_343.get (by omega) (by omega)
  by_cases h17 : j < 403
  · exact kujstaticRange_373.get (by omega) (by omega)
  by_cases h18 : j < 433
  · exact kujstaticRange_403.get (by omega) (by omega)
  by_cases h19 : j < 463
  · exact kujstaticRange_433.get (by omega) (by omega)
  by_cases h20 : j < 493
  · exact kujstaticRange_463.get (by omega) (by omega)
  by_cases h21 : j < 523
  · exact kujstaticRange_493.get (by omega) (by omega)
  by_cases h22 : j < 553
  · exact kujstaticRange_523.get (by omega) (by omega)
  by_cases h23 : j < 583
  · exact kujstaticRange_553.get (by omega) (by omega)
  by_cases h24 : j < 613
  · exact kujstaticRange_583.get (by omega) (by omega)
  by_cases h25 : j < 643
  · exact kujstaticRange_613.get (by omega) (by omega)
  by_cases h26 : j < 673
  · exact kujstaticRange_643.get (by omega) (by omega)
  by_cases h27 : j < 703
  · exact kujstaticRange_673.get (by omega) (by omega)
  by_cases h28 : j < 733
  · exact kujstaticRange_703.get (by omega) (by omega)
  by_cases h29 : j < 763
  · exact kujstaticRange_733.get (by omega) (by omega)
  by_cases h30 : j < 793
  · exact kujstaticRange_763.get (by omega) (by omega)
  by_cases h31 : j < 823
  · exact kujstaticRange_793.get (by omega) (by omega)
  by_cases h32 : j < 853
  · exact kujstaticRange_823.get (by omega) (by omega)
  exact kujstaticRange_853.get (by omega) (by omega)

end
end LeanVM.Guest
