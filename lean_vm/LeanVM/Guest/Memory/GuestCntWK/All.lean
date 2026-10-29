/-
  LeanVM.Guest.Memory.GuestCntWK.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntWK.Part00
public import LeanVM.Guest.Memory.GuestCntWK.Part01
public import LeanVM.Guest.Memory.GuestCntWK.Part02
public import LeanVM.Guest.Memory.GuestCntWK.Part03
public import LeanVM.Guest.Memory.GuestCntWK.Part04
public import LeanVM.Guest.Memory.GuestCntWK.Part05

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kukchkIdx_all : ∀ j < 878, kukchkIdx j = true := by
  intro j hj
  by_cases h0 : j < 10
  · exact kukstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kukstaticRange_10.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kukstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 73
  · exact kukstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 102
  · exact kukstaticRange_73.get (by omega) (by omega)
  by_cases h5 : j < 128
  · exact kukstaticRange_102.get (by omega) (by omega)
  by_cases h6 : j < 155
  · exact kukstaticRange_128.get (by omega) (by omega)
  by_cases h7 : j < 178
  · exact kukstaticRange_155.get (by omega) (by omega)
  by_cases h8 : j < 204
  · exact kukstaticRange_178.get (by omega) (by omega)
  by_cases h9 : j < 230
  · exact kukstaticRange_204.get (by omega) (by omega)
  by_cases h10 : j < 260
  · exact kukstaticRange_230.get (by omega) (by omega)
  by_cases h11 : j < 286
  · exact kukstaticRange_260.get (by omega) (by omega)
  by_cases h12 : j < 299
  · exact kukstaticRange_286.get (by omega) (by omega)
  by_cases h13 : j < 306
  · exact kukstaticRange_299.get (by omega) (by omega)
  by_cases h14 : j < 313
  · exact kukstaticRange_306.get (by omega) (by omega)
  by_cases h15 : j < 343
  · exact kukstaticRange_313.get (by omega) (by omega)
  by_cases h16 : j < 373
  · exact kukstaticRange_343.get (by omega) (by omega)
  by_cases h17 : j < 403
  · exact kukstaticRange_373.get (by omega) (by omega)
  by_cases h18 : j < 433
  · exact kukstaticRange_403.get (by omega) (by omega)
  by_cases h19 : j < 463
  · exact kukstaticRange_433.get (by omega) (by omega)
  by_cases h20 : j < 493
  · exact kukstaticRange_463.get (by omega) (by omega)
  by_cases h21 : j < 523
  · exact kukstaticRange_493.get (by omega) (by omega)
  by_cases h22 : j < 553
  · exact kukstaticRange_523.get (by omega) (by omega)
  by_cases h23 : j < 583
  · exact kukstaticRange_553.get (by omega) (by omega)
  by_cases h24 : j < 613
  · exact kukstaticRange_583.get (by omega) (by omega)
  by_cases h25 : j < 643
  · exact kukstaticRange_613.get (by omega) (by omega)
  by_cases h26 : j < 673
  · exact kukstaticRange_643.get (by omega) (by omega)
  by_cases h27 : j < 703
  · exact kukstaticRange_673.get (by omega) (by omega)
  by_cases h28 : j < 733
  · exact kukstaticRange_703.get (by omega) (by omega)
  by_cases h29 : j < 763
  · exact kukstaticRange_733.get (by omega) (by omega)
  by_cases h30 : j < 793
  · exact kukstaticRange_763.get (by omega) (by omega)
  by_cases h31 : j < 823
  · exact kukstaticRange_793.get (by omega) (by omega)
  by_cases h32 : j < 853
  · exact kukstaticRange_823.get (by omega) (by omega)
  exact kukstaticRange_853.get (by omega) (by omega)

end
end LeanVM.Guest
