/-
  LeanVM.Guest.Memory.GuestCntWD.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntWD.Part00
public import LeanVM.Guest.Memory.GuestCntWD.Part01
public import LeanVM.Guest.Memory.GuestCntWD.Part02
public import LeanVM.Guest.Memory.GuestCntWD.Part03
public import LeanVM.Guest.Memory.GuestCntWD.Part04
public import LeanVM.Guest.Memory.GuestCntWD.Part05

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kudchkIdx_all : ∀ j < 878, kudchkIdx j = true := by
  intro j hj
  by_cases h0 : j < 10
  · exact kudstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kudstaticRange_10.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kudstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 73
  · exact kudstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 102
  · exact kudstaticRange_73.get (by omega) (by omega)
  by_cases h5 : j < 128
  · exact kudstaticRange_102.get (by omega) (by omega)
  by_cases h6 : j < 155
  · exact kudstaticRange_128.get (by omega) (by omega)
  by_cases h7 : j < 178
  · exact kudstaticRange_155.get (by omega) (by omega)
  by_cases h8 : j < 204
  · exact kudstaticRange_178.get (by omega) (by omega)
  by_cases h9 : j < 230
  · exact kudstaticRange_204.get (by omega) (by omega)
  by_cases h10 : j < 260
  · exact kudstaticRange_230.get (by omega) (by omega)
  by_cases h11 : j < 286
  · exact kudstaticRange_260.get (by omega) (by omega)
  by_cases h12 : j < 299
  · exact kudstaticRange_286.get (by omega) (by omega)
  by_cases h13 : j < 306
  · exact kudstaticRange_299.get (by omega) (by omega)
  by_cases h14 : j < 313
  · exact kudstaticRange_306.get (by omega) (by omega)
  by_cases h15 : j < 343
  · exact kudstaticRange_313.get (by omega) (by omega)
  by_cases h16 : j < 373
  · exact kudstaticRange_343.get (by omega) (by omega)
  by_cases h17 : j < 403
  · exact kudstaticRange_373.get (by omega) (by omega)
  by_cases h18 : j < 433
  · exact kudstaticRange_403.get (by omega) (by omega)
  by_cases h19 : j < 463
  · exact kudstaticRange_433.get (by omega) (by omega)
  by_cases h20 : j < 493
  · exact kudstaticRange_463.get (by omega) (by omega)
  by_cases h21 : j < 523
  · exact kudstaticRange_493.get (by omega) (by omega)
  by_cases h22 : j < 553
  · exact kudstaticRange_523.get (by omega) (by omega)
  by_cases h23 : j < 583
  · exact kudstaticRange_553.get (by omega) (by omega)
  by_cases h24 : j < 613
  · exact kudstaticRange_583.get (by omega) (by omega)
  by_cases h25 : j < 643
  · exact kudstaticRange_613.get (by omega) (by omega)
  by_cases h26 : j < 673
  · exact kudstaticRange_643.get (by omega) (by omega)
  by_cases h27 : j < 703
  · exact kudstaticRange_673.get (by omega) (by omega)
  by_cases h28 : j < 733
  · exact kudstaticRange_703.get (by omega) (by omega)
  by_cases h29 : j < 763
  · exact kudstaticRange_733.get (by omega) (by omega)
  by_cases h30 : j < 793
  · exact kudstaticRange_763.get (by omega) (by omega)
  by_cases h31 : j < 823
  · exact kudstaticRange_793.get (by omega) (by omega)
  by_cases h32 : j < 853
  · exact kudstaticRange_823.get (by omega) (by omega)
  exact kudstaticRange_853.get (by omega) (by omega)

end
end LeanVM.Guest
