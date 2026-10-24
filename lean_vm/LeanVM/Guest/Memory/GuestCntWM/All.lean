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

theorem kumchkIdx_all : ∀ j < 899, kumchkIdx j = true := by
  intro j hj
  by_cases h0 : j < 10
  · exact kumstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kumstaticRange_10.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kumstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 74
  · exact kumstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 103
  · exact kumstaticRange_74.get (by omega) (by omega)
  by_cases h5 : j < 129
  · exact kumstaticRange_103.get (by omega) (by omega)
  by_cases h6 : j < 156
  · exact kumstaticRange_129.get (by omega) (by omega)
  by_cases h7 : j < 180
  · exact kumstaticRange_156.get (by omega) (by omega)
  by_cases h8 : j < 206
  · exact kumstaticRange_180.get (by omega) (by omega)
  by_cases h9 : j < 232
  · exact kumstaticRange_206.get (by omega) (by omega)
  by_cases h10 : j < 262
  · exact kumstaticRange_232.get (by omega) (by omega)
  by_cases h11 : j < 288
  · exact kumstaticRange_262.get (by omega) (by omega)
  by_cases h12 : j < 302
  · exact kumstaticRange_288.get (by omega) (by omega)
  by_cases h13 : j < 309
  · exact kumstaticRange_302.get (by omega) (by omega)
  by_cases h14 : j < 316
  · exact kumstaticRange_309.get (by omega) (by omega)
  by_cases h15 : j < 346
  · exact kumstaticRange_316.get (by omega) (by omega)
  by_cases h16 : j < 376
  · exact kumstaticRange_346.get (by omega) (by omega)
  by_cases h17 : j < 406
  · exact kumstaticRange_376.get (by omega) (by omega)
  by_cases h18 : j < 436
  · exact kumstaticRange_406.get (by omega) (by omega)
  by_cases h19 : j < 466
  · exact kumstaticRange_436.get (by omega) (by omega)
  by_cases h20 : j < 496
  · exact kumstaticRange_466.get (by omega) (by omega)
  by_cases h21 : j < 526
  · exact kumstaticRange_496.get (by omega) (by omega)
  by_cases h22 : j < 556
  · exact kumstaticRange_526.get (by omega) (by omega)
  by_cases h23 : j < 586
  · exact kumstaticRange_556.get (by omega) (by omega)
  by_cases h24 : j < 616
  · exact kumstaticRange_586.get (by omega) (by omega)
  by_cases h25 : j < 646
  · exact kumstaticRange_616.get (by omega) (by omega)
  by_cases h26 : j < 676
  · exact kumstaticRange_646.get (by omega) (by omega)
  by_cases h27 : j < 706
  · exact kumstaticRange_676.get (by omega) (by omega)
  by_cases h28 : j < 736
  · exact kumstaticRange_706.get (by omega) (by omega)
  by_cases h29 : j < 766
  · exact kumstaticRange_736.get (by omega) (by omega)
  by_cases h30 : j < 796
  · exact kumstaticRange_766.get (by omega) (by omega)
  by_cases h31 : j < 826
  · exact kumstaticRange_796.get (by omega) (by omega)
  by_cases h32 : j < 856
  · exact kumstaticRange_826.get (by omega) (by omega)
  by_cases h33 : j < 886
  · exact kumstaticRange_856.get (by omega) (by omega)
  exact kumstaticRange_886.get (by omega) (by omega)

end
end LeanVM.Guest
