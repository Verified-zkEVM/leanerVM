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

theorem kuxchkIdx_all : ∀ j < 883, kuxchkIdx j = true := by
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
  by_cases h7 : j < 179
  · exact kuxstaticRange_156.get (by omega) (by omega)
  by_cases h8 : j < 205
  · exact kuxstaticRange_179.get (by omega) (by omega)
  by_cases h9 : j < 231
  · exact kuxstaticRange_205.get (by omega) (by omega)
  by_cases h10 : j < 261
  · exact kuxstaticRange_231.get (by omega) (by omega)
  by_cases h11 : j < 287
  · exact kuxstaticRange_261.get (by omega) (by omega)
  by_cases h12 : j < 301
  · exact kuxstaticRange_287.get (by omega) (by omega)
  by_cases h13 : j < 308
  · exact kuxstaticRange_301.get (by omega) (by omega)
  by_cases h14 : j < 315
  · exact kuxstaticRange_308.get (by omega) (by omega)
  by_cases h15 : j < 345
  · exact kuxstaticRange_315.get (by omega) (by omega)
  by_cases h16 : j < 375
  · exact kuxstaticRange_345.get (by omega) (by omega)
  by_cases h17 : j < 405
  · exact kuxstaticRange_375.get (by omega) (by omega)
  by_cases h18 : j < 435
  · exact kuxstaticRange_405.get (by omega) (by omega)
  by_cases h19 : j < 465
  · exact kuxstaticRange_435.get (by omega) (by omega)
  by_cases h20 : j < 495
  · exact kuxstaticRange_465.get (by omega) (by omega)
  by_cases h21 : j < 525
  · exact kuxstaticRange_495.get (by omega) (by omega)
  by_cases h22 : j < 555
  · exact kuxstaticRange_525.get (by omega) (by omega)
  by_cases h23 : j < 585
  · exact kuxstaticRange_555.get (by omega) (by omega)
  by_cases h24 : j < 615
  · exact kuxstaticRange_585.get (by omega) (by omega)
  by_cases h25 : j < 645
  · exact kuxstaticRange_615.get (by omega) (by omega)
  by_cases h26 : j < 675
  · exact kuxstaticRange_645.get (by omega) (by omega)
  by_cases h27 : j < 705
  · exact kuxstaticRange_675.get (by omega) (by omega)
  by_cases h28 : j < 735
  · exact kuxstaticRange_705.get (by omega) (by omega)
  by_cases h29 : j < 765
  · exact kuxstaticRange_735.get (by omega) (by omega)
  by_cases h30 : j < 795
  · exact kuxstaticRange_765.get (by omega) (by omega)
  by_cases h31 : j < 825
  · exact kuxstaticRange_795.get (by omega) (by omega)
  by_cases h32 : j < 855
  · exact kuxstaticRange_825.get (by omega) (by omega)
  exact kuxstaticRange_855.get (by omega) (by omega)

end
end LeanVM.Guest
