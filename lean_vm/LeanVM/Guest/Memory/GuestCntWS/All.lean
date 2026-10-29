/-
  LeanVM.Guest.Memory.GuestCntWS.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntWS.Part00
public import LeanVM.Guest.Memory.GuestCntWS.Part01
public import LeanVM.Guest.Memory.GuestCntWS.Part02
public import LeanVM.Guest.Memory.GuestCntWS.Part03
public import LeanVM.Guest.Memory.GuestCntWS.Part04
public import LeanVM.Guest.Memory.GuestCntWS.Part05

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kuschkIdx_all : ∀ j < 878, kuschkIdx j = true := by
  intro j hj
  by_cases h0 : j < 10
  · exact kusstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kusstaticRange_10.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kusstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 73
  · exact kusstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 102
  · exact kusstaticRange_73.get (by omega) (by omega)
  by_cases h5 : j < 128
  · exact kusstaticRange_102.get (by omega) (by omega)
  by_cases h6 : j < 155
  · exact kusstaticRange_128.get (by omega) (by omega)
  by_cases h7 : j < 178
  · exact kusstaticRange_155.get (by omega) (by omega)
  by_cases h8 : j < 204
  · exact kusstaticRange_178.get (by omega) (by omega)
  by_cases h9 : j < 230
  · exact kusstaticRange_204.get (by omega) (by omega)
  by_cases h10 : j < 260
  · exact kusstaticRange_230.get (by omega) (by omega)
  by_cases h11 : j < 286
  · exact kusstaticRange_260.get (by omega) (by omega)
  by_cases h12 : j < 299
  · exact kusstaticRange_286.get (by omega) (by omega)
  by_cases h13 : j < 306
  · exact kusstaticRange_299.get (by omega) (by omega)
  by_cases h14 : j < 313
  · exact kusstaticRange_306.get (by omega) (by omega)
  by_cases h15 : j < 343
  · exact kusstaticRange_313.get (by omega) (by omega)
  by_cases h16 : j < 373
  · exact kusstaticRange_343.get (by omega) (by omega)
  by_cases h17 : j < 403
  · exact kusstaticRange_373.get (by omega) (by omega)
  by_cases h18 : j < 433
  · exact kusstaticRange_403.get (by omega) (by omega)
  by_cases h19 : j < 463
  · exact kusstaticRange_433.get (by omega) (by omega)
  by_cases h20 : j < 493
  · exact kusstaticRange_463.get (by omega) (by omega)
  by_cases h21 : j < 523
  · exact kusstaticRange_493.get (by omega) (by omega)
  by_cases h22 : j < 553
  · exact kusstaticRange_523.get (by omega) (by omega)
  by_cases h23 : j < 583
  · exact kusstaticRange_553.get (by omega) (by omega)
  by_cases h24 : j < 613
  · exact kusstaticRange_583.get (by omega) (by omega)
  by_cases h25 : j < 643
  · exact kusstaticRange_613.get (by omega) (by omega)
  by_cases h26 : j < 673
  · exact kusstaticRange_643.get (by omega) (by omega)
  by_cases h27 : j < 703
  · exact kusstaticRange_673.get (by omega) (by omega)
  by_cases h28 : j < 733
  · exact kusstaticRange_703.get (by omega) (by omega)
  by_cases h29 : j < 763
  · exact kusstaticRange_733.get (by omega) (by omega)
  by_cases h30 : j < 793
  · exact kusstaticRange_763.get (by omega) (by omega)
  by_cases h31 : j < 823
  · exact kusstaticRange_793.get (by omega) (by omega)
  by_cases h32 : j < 853
  · exact kusstaticRange_823.get (by omega) (by omega)
  exact kusstaticRange_853.get (by omega) (by omega)

end
end LeanVM.Guest
