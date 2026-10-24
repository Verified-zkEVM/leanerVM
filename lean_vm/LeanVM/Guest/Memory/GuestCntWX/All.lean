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

theorem kuxchkIdx_all : ∀ j < 899, kuxchkIdx j = true := by
  intro j hj
  by_cases h0 : j < 10
  · exact kuxstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kuxstaticRange_10.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kuxstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 74
  · exact kuxstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 103
  · exact kuxstaticRange_74.get (by omega) (by omega)
  by_cases h5 : j < 129
  · exact kuxstaticRange_103.get (by omega) (by omega)
  by_cases h6 : j < 156
  · exact kuxstaticRange_129.get (by omega) (by omega)
  by_cases h7 : j < 180
  · exact kuxstaticRange_156.get (by omega) (by omega)
  by_cases h8 : j < 206
  · exact kuxstaticRange_180.get (by omega) (by omega)
  by_cases h9 : j < 232
  · exact kuxstaticRange_206.get (by omega) (by omega)
  by_cases h10 : j < 262
  · exact kuxstaticRange_232.get (by omega) (by omega)
  by_cases h11 : j < 288
  · exact kuxstaticRange_262.get (by omega) (by omega)
  by_cases h12 : j < 302
  · exact kuxstaticRange_288.get (by omega) (by omega)
  by_cases h13 : j < 309
  · exact kuxstaticRange_302.get (by omega) (by omega)
  by_cases h14 : j < 316
  · exact kuxstaticRange_309.get (by omega) (by omega)
  by_cases h15 : j < 346
  · exact kuxstaticRange_316.get (by omega) (by omega)
  by_cases h16 : j < 376
  · exact kuxstaticRange_346.get (by omega) (by omega)
  by_cases h17 : j < 406
  · exact kuxstaticRange_376.get (by omega) (by omega)
  by_cases h18 : j < 436
  · exact kuxstaticRange_406.get (by omega) (by omega)
  by_cases h19 : j < 466
  · exact kuxstaticRange_436.get (by omega) (by omega)
  by_cases h20 : j < 496
  · exact kuxstaticRange_466.get (by omega) (by omega)
  by_cases h21 : j < 526
  · exact kuxstaticRange_496.get (by omega) (by omega)
  by_cases h22 : j < 556
  · exact kuxstaticRange_526.get (by omega) (by omega)
  by_cases h23 : j < 586
  · exact kuxstaticRange_556.get (by omega) (by omega)
  by_cases h24 : j < 616
  · exact kuxstaticRange_586.get (by omega) (by omega)
  by_cases h25 : j < 646
  · exact kuxstaticRange_616.get (by omega) (by omega)
  by_cases h26 : j < 676
  · exact kuxstaticRange_646.get (by omega) (by omega)
  by_cases h27 : j < 706
  · exact kuxstaticRange_676.get (by omega) (by omega)
  by_cases h28 : j < 736
  · exact kuxstaticRange_706.get (by omega) (by omega)
  by_cases h29 : j < 766
  · exact kuxstaticRange_736.get (by omega) (by omega)
  by_cases h30 : j < 796
  · exact kuxstaticRange_766.get (by omega) (by omega)
  by_cases h31 : j < 826
  · exact kuxstaticRange_796.get (by omega) (by omega)
  by_cases h32 : j < 856
  · exact kuxstaticRange_826.get (by omega) (by omega)
  by_cases h33 : j < 886
  · exact kuxstaticRange_856.get (by omega) (by omega)
  exact kuxstaticRange_886.get (by omega) (by omega)

end
end LeanVM.Guest
