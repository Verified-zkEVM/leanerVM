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

theorem kuschkIdx_all : ∀ j < 899, kuschkIdx j = true := by
  intro j hj
  by_cases h0 : j < 10
  · exact kusstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kusstaticRange_10.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kusstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 74
  · exact kusstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 103
  · exact kusstaticRange_74.get (by omega) (by omega)
  by_cases h5 : j < 129
  · exact kusstaticRange_103.get (by omega) (by omega)
  by_cases h6 : j < 156
  · exact kusstaticRange_129.get (by omega) (by omega)
  by_cases h7 : j < 180
  · exact kusstaticRange_156.get (by omega) (by omega)
  by_cases h8 : j < 206
  · exact kusstaticRange_180.get (by omega) (by omega)
  by_cases h9 : j < 232
  · exact kusstaticRange_206.get (by omega) (by omega)
  by_cases h10 : j < 262
  · exact kusstaticRange_232.get (by omega) (by omega)
  by_cases h11 : j < 288
  · exact kusstaticRange_262.get (by omega) (by omega)
  by_cases h12 : j < 302
  · exact kusstaticRange_288.get (by omega) (by omega)
  by_cases h13 : j < 309
  · exact kusstaticRange_302.get (by omega) (by omega)
  by_cases h14 : j < 316
  · exact kusstaticRange_309.get (by omega) (by omega)
  by_cases h15 : j < 346
  · exact kusstaticRange_316.get (by omega) (by omega)
  by_cases h16 : j < 376
  · exact kusstaticRange_346.get (by omega) (by omega)
  by_cases h17 : j < 406
  · exact kusstaticRange_376.get (by omega) (by omega)
  by_cases h18 : j < 436
  · exact kusstaticRange_406.get (by omega) (by omega)
  by_cases h19 : j < 466
  · exact kusstaticRange_436.get (by omega) (by omega)
  by_cases h20 : j < 496
  · exact kusstaticRange_466.get (by omega) (by omega)
  by_cases h21 : j < 526
  · exact kusstaticRange_496.get (by omega) (by omega)
  by_cases h22 : j < 556
  · exact kusstaticRange_526.get (by omega) (by omega)
  by_cases h23 : j < 586
  · exact kusstaticRange_556.get (by omega) (by omega)
  by_cases h24 : j < 616
  · exact kusstaticRange_586.get (by omega) (by omega)
  by_cases h25 : j < 646
  · exact kusstaticRange_616.get (by omega) (by omega)
  by_cases h26 : j < 676
  · exact kusstaticRange_646.get (by omega) (by omega)
  by_cases h27 : j < 706
  · exact kusstaticRange_676.get (by omega) (by omega)
  by_cases h28 : j < 736
  · exact kusstaticRange_706.get (by omega) (by omega)
  by_cases h29 : j < 766
  · exact kusstaticRange_736.get (by omega) (by omega)
  by_cases h30 : j < 796
  · exact kusstaticRange_766.get (by omega) (by omega)
  by_cases h31 : j < 826
  · exact kusstaticRange_796.get (by omega) (by omega)
  by_cases h32 : j < 856
  · exact kusstaticRange_826.get (by omega) (by omega)
  by_cases h33 : j < 886
  · exact kusstaticRange_856.get (by omega) (by omega)
  exact kusstaticRange_886.get (by omega) (by omega)

end
end LeanVM.Guest
