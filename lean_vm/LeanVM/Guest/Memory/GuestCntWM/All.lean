/-
  LeanVM.Guest.Memory.GuestCntWM.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntWM.Part00
public import LeanVM.Guest.Memory.GuestCntWM.Part01
public import LeanVM.Guest.Memory.GuestCntWM.Part02
public import LeanVM.Guest.Memory.GuestCntWM.Part03
public import LeanVM.Guest.Memory.GuestCntWM.Part04
public import LeanVM.Guest.Memory.GuestCntWM.Part05

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kumchkIdx_all : ∀ j < 878, kumchkIdx j = true := by
  intro j hj
  by_cases h0 : j < 10
  · exact kumstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kumstaticRange_10.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kumstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 73
  · exact kumstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 102
  · exact kumstaticRange_73.get (by omega) (by omega)
  by_cases h5 : j < 128
  · exact kumstaticRange_102.get (by omega) (by omega)
  by_cases h6 : j < 155
  · exact kumstaticRange_128.get (by omega) (by omega)
  by_cases h7 : j < 178
  · exact kumstaticRange_155.get (by omega) (by omega)
  by_cases h8 : j < 204
  · exact kumstaticRange_178.get (by omega) (by omega)
  by_cases h9 : j < 230
  · exact kumstaticRange_204.get (by omega) (by omega)
  by_cases h10 : j < 260
  · exact kumstaticRange_230.get (by omega) (by omega)
  by_cases h11 : j < 286
  · exact kumstaticRange_260.get (by omega) (by omega)
  by_cases h12 : j < 299
  · exact kumstaticRange_286.get (by omega) (by omega)
  by_cases h13 : j < 306
  · exact kumstaticRange_299.get (by omega) (by omega)
  by_cases h14 : j < 313
  · exact kumstaticRange_306.get (by omega) (by omega)
  by_cases h15 : j < 343
  · exact kumstaticRange_313.get (by omega) (by omega)
  by_cases h16 : j < 373
  · exact kumstaticRange_343.get (by omega) (by omega)
  by_cases h17 : j < 403
  · exact kumstaticRange_373.get (by omega) (by omega)
  by_cases h18 : j < 433
  · exact kumstaticRange_403.get (by omega) (by omega)
  by_cases h19 : j < 463
  · exact kumstaticRange_433.get (by omega) (by omega)
  by_cases h20 : j < 493
  · exact kumstaticRange_463.get (by omega) (by omega)
  by_cases h21 : j < 523
  · exact kumstaticRange_493.get (by omega) (by omega)
  by_cases h22 : j < 553
  · exact kumstaticRange_523.get (by omega) (by omega)
  by_cases h23 : j < 583
  · exact kumstaticRange_553.get (by omega) (by omega)
  by_cases h24 : j < 613
  · exact kumstaticRange_583.get (by omega) (by omega)
  by_cases h25 : j < 643
  · exact kumstaticRange_613.get (by omega) (by omega)
  by_cases h26 : j < 673
  · exact kumstaticRange_643.get (by omega) (by omega)
  by_cases h27 : j < 703
  · exact kumstaticRange_673.get (by omega) (by omega)
  by_cases h28 : j < 733
  · exact kumstaticRange_703.get (by omega) (by omega)
  by_cases h29 : j < 763
  · exact kumstaticRange_733.get (by omega) (by omega)
  by_cases h30 : j < 793
  · exact kumstaticRange_763.get (by omega) (by omega)
  by_cases h31 : j < 823
  · exact kumstaticRange_793.get (by omega) (by omega)
  by_cases h32 : j < 853
  · exact kumstaticRange_823.get (by omega) (by omega)
  exact kumstaticRange_853.get (by omega) (by omega)

end
end LeanVM.Guest
