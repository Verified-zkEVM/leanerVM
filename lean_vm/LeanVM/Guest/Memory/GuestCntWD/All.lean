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

theorem kudchkIdx_all : ∀ j < 899, kudchkIdx j = true := by
  intro j hj
  by_cases h0 : j < 10
  · exact kudstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kudstaticRange_10.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kudstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 74
  · exact kudstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 103
  · exact kudstaticRange_74.get (by omega) (by omega)
  by_cases h5 : j < 129
  · exact kudstaticRange_103.get (by omega) (by omega)
  by_cases h6 : j < 156
  · exact kudstaticRange_129.get (by omega) (by omega)
  by_cases h7 : j < 180
  · exact kudstaticRange_156.get (by omega) (by omega)
  by_cases h8 : j < 206
  · exact kudstaticRange_180.get (by omega) (by omega)
  by_cases h9 : j < 232
  · exact kudstaticRange_206.get (by omega) (by omega)
  by_cases h10 : j < 262
  · exact kudstaticRange_232.get (by omega) (by omega)
  by_cases h11 : j < 288
  · exact kudstaticRange_262.get (by omega) (by omega)
  by_cases h12 : j < 302
  · exact kudstaticRange_288.get (by omega) (by omega)
  by_cases h13 : j < 309
  · exact kudstaticRange_302.get (by omega) (by omega)
  by_cases h14 : j < 316
  · exact kudstaticRange_309.get (by omega) (by omega)
  by_cases h15 : j < 346
  · exact kudstaticRange_316.get (by omega) (by omega)
  by_cases h16 : j < 376
  · exact kudstaticRange_346.get (by omega) (by omega)
  by_cases h17 : j < 406
  · exact kudstaticRange_376.get (by omega) (by omega)
  by_cases h18 : j < 436
  · exact kudstaticRange_406.get (by omega) (by omega)
  by_cases h19 : j < 466
  · exact kudstaticRange_436.get (by omega) (by omega)
  by_cases h20 : j < 496
  · exact kudstaticRange_466.get (by omega) (by omega)
  by_cases h21 : j < 526
  · exact kudstaticRange_496.get (by omega) (by omega)
  by_cases h22 : j < 556
  · exact kudstaticRange_526.get (by omega) (by omega)
  by_cases h23 : j < 586
  · exact kudstaticRange_556.get (by omega) (by omega)
  by_cases h24 : j < 616
  · exact kudstaticRange_586.get (by omega) (by omega)
  by_cases h25 : j < 646
  · exact kudstaticRange_616.get (by omega) (by omega)
  by_cases h26 : j < 676
  · exact kudstaticRange_646.get (by omega) (by omega)
  by_cases h27 : j < 706
  · exact kudstaticRange_676.get (by omega) (by omega)
  by_cases h28 : j < 736
  · exact kudstaticRange_706.get (by omega) (by omega)
  by_cases h29 : j < 766
  · exact kudstaticRange_736.get (by omega) (by omega)
  by_cases h30 : j < 796
  · exact kudstaticRange_766.get (by omega) (by omega)
  by_cases h31 : j < 826
  · exact kudstaticRange_796.get (by omega) (by omega)
  by_cases h32 : j < 856
  · exact kudstaticRange_826.get (by omega) (by omega)
  by_cases h33 : j < 886
  · exact kudstaticRange_856.get (by omega) (by omega)
  exact kudstaticRange_886.get (by omega) (by omega)

end
end LeanVM.Guest
