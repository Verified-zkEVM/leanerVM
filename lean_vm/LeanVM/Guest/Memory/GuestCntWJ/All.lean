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

theorem kujchkIdx_all : ∀ j < 899, kujchkIdx j = true := by
  intro j hj
  by_cases h0 : j < 10
  · exact kujstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kujstaticRange_10.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kujstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 74
  · exact kujstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 103
  · exact kujstaticRange_74.get (by omega) (by omega)
  by_cases h5 : j < 129
  · exact kujstaticRange_103.get (by omega) (by omega)
  by_cases h6 : j < 156
  · exact kujstaticRange_129.get (by omega) (by omega)
  by_cases h7 : j < 180
  · exact kujstaticRange_156.get (by omega) (by omega)
  by_cases h8 : j < 206
  · exact kujstaticRange_180.get (by omega) (by omega)
  by_cases h9 : j < 232
  · exact kujstaticRange_206.get (by omega) (by omega)
  by_cases h10 : j < 262
  · exact kujstaticRange_232.get (by omega) (by omega)
  by_cases h11 : j < 288
  · exact kujstaticRange_262.get (by omega) (by omega)
  by_cases h12 : j < 302
  · exact kujstaticRange_288.get (by omega) (by omega)
  by_cases h13 : j < 309
  · exact kujstaticRange_302.get (by omega) (by omega)
  by_cases h14 : j < 316
  · exact kujstaticRange_309.get (by omega) (by omega)
  by_cases h15 : j < 346
  · exact kujstaticRange_316.get (by omega) (by omega)
  by_cases h16 : j < 376
  · exact kujstaticRange_346.get (by omega) (by omega)
  by_cases h17 : j < 406
  · exact kujstaticRange_376.get (by omega) (by omega)
  by_cases h18 : j < 436
  · exact kujstaticRange_406.get (by omega) (by omega)
  by_cases h19 : j < 466
  · exact kujstaticRange_436.get (by omega) (by omega)
  by_cases h20 : j < 496
  · exact kujstaticRange_466.get (by omega) (by omega)
  by_cases h21 : j < 526
  · exact kujstaticRange_496.get (by omega) (by omega)
  by_cases h22 : j < 556
  · exact kujstaticRange_526.get (by omega) (by omega)
  by_cases h23 : j < 586
  · exact kujstaticRange_556.get (by omega) (by omega)
  by_cases h24 : j < 616
  · exact kujstaticRange_586.get (by omega) (by omega)
  by_cases h25 : j < 646
  · exact kujstaticRange_616.get (by omega) (by omega)
  by_cases h26 : j < 676
  · exact kujstaticRange_646.get (by omega) (by omega)
  by_cases h27 : j < 706
  · exact kujstaticRange_676.get (by omega) (by omega)
  by_cases h28 : j < 736
  · exact kujstaticRange_706.get (by omega) (by omega)
  by_cases h29 : j < 766
  · exact kujstaticRange_736.get (by omega) (by omega)
  by_cases h30 : j < 796
  · exact kujstaticRange_766.get (by omega) (by omega)
  by_cases h31 : j < 826
  · exact kujstaticRange_796.get (by omega) (by omega)
  by_cases h32 : j < 856
  · exact kujstaticRange_826.get (by omega) (by omega)
  by_cases h33 : j < 886
  · exact kujstaticRange_856.get (by omega) (by omega)
  exact kujstaticRange_886.get (by omega) (by omega)

end
end LeanVM.Guest
