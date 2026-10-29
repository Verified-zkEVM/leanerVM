/-
  LeanVM.Guest.Memory.GuestCntWX.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntWX.Part00
public import LeanVM.Guest.Memory.GuestCntWX.Part01
public import LeanVM.Guest.Memory.GuestCntWX.Part02
public import LeanVM.Guest.Memory.GuestCntWX.Part03
public import LeanVM.Guest.Memory.GuestCntWX.Part04
public import LeanVM.Guest.Memory.GuestCntWX.Part05

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kuxchkIdx_all : ∀ j < 878, kuxchkIdx j = true := by
  intro j hj
  by_cases h0 : j < 10
  · exact kuxstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kuxstaticRange_10.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kuxstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 73
  · exact kuxstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 102
  · exact kuxstaticRange_73.get (by omega) (by omega)
  by_cases h5 : j < 128
  · exact kuxstaticRange_102.get (by omega) (by omega)
  by_cases h6 : j < 155
  · exact kuxstaticRange_128.get (by omega) (by omega)
  by_cases h7 : j < 178
  · exact kuxstaticRange_155.get (by omega) (by omega)
  by_cases h8 : j < 204
  · exact kuxstaticRange_178.get (by omega) (by omega)
  by_cases h9 : j < 230
  · exact kuxstaticRange_204.get (by omega) (by omega)
  by_cases h10 : j < 260
  · exact kuxstaticRange_230.get (by omega) (by omega)
  by_cases h11 : j < 286
  · exact kuxstaticRange_260.get (by omega) (by omega)
  by_cases h12 : j < 299
  · exact kuxstaticRange_286.get (by omega) (by omega)
  by_cases h13 : j < 306
  · exact kuxstaticRange_299.get (by omega) (by omega)
  by_cases h14 : j < 313
  · exact kuxstaticRange_306.get (by omega) (by omega)
  by_cases h15 : j < 343
  · exact kuxstaticRange_313.get (by omega) (by omega)
  by_cases h16 : j < 373
  · exact kuxstaticRange_343.get (by omega) (by omega)
  by_cases h17 : j < 403
  · exact kuxstaticRange_373.get (by omega) (by omega)
  by_cases h18 : j < 433
  · exact kuxstaticRange_403.get (by omega) (by omega)
  by_cases h19 : j < 463
  · exact kuxstaticRange_433.get (by omega) (by omega)
  by_cases h20 : j < 493
  · exact kuxstaticRange_463.get (by omega) (by omega)
  by_cases h21 : j < 523
  · exact kuxstaticRange_493.get (by omega) (by omega)
  by_cases h22 : j < 553
  · exact kuxstaticRange_523.get (by omega) (by omega)
  by_cases h23 : j < 583
  · exact kuxstaticRange_553.get (by omega) (by omega)
  by_cases h24 : j < 613
  · exact kuxstaticRange_583.get (by omega) (by omega)
  by_cases h25 : j < 643
  · exact kuxstaticRange_613.get (by omega) (by omega)
  by_cases h26 : j < 673
  · exact kuxstaticRange_643.get (by omega) (by omega)
  by_cases h27 : j < 703
  · exact kuxstaticRange_673.get (by omega) (by omega)
  by_cases h28 : j < 733
  · exact kuxstaticRange_703.get (by omega) (by omega)
  by_cases h29 : j < 763
  · exact kuxstaticRange_733.get (by omega) (by omega)
  by_cases h30 : j < 793
  · exact kuxstaticRange_763.get (by omega) (by omega)
  by_cases h31 : j < 823
  · exact kuxstaticRange_793.get (by omega) (by omega)
  by_cases h32 : j < 853
  · exact kuxstaticRange_823.get (by omega) (by omega)
  exact kuxstaticRange_853.get (by omega) (by omega)

end
end LeanVM.Guest
