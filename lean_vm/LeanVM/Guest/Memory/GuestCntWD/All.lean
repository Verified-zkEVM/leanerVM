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

theorem kudchkIdx_all : ∀ j < 883, kudchkIdx j = true := by
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
  by_cases h7 : j < 179
  · exact kudstaticRange_156.get (by omega) (by omega)
  by_cases h8 : j < 205
  · exact kudstaticRange_179.get (by omega) (by omega)
  by_cases h9 : j < 231
  · exact kudstaticRange_205.get (by omega) (by omega)
  by_cases h10 : j < 261
  · exact kudstaticRange_231.get (by omega) (by omega)
  by_cases h11 : j < 287
  · exact kudstaticRange_261.get (by omega) (by omega)
  by_cases h12 : j < 301
  · exact kudstaticRange_287.get (by omega) (by omega)
  by_cases h13 : j < 308
  · exact kudstaticRange_301.get (by omega) (by omega)
  by_cases h14 : j < 315
  · exact kudstaticRange_308.get (by omega) (by omega)
  by_cases h15 : j < 345
  · exact kudstaticRange_315.get (by omega) (by omega)
  by_cases h16 : j < 375
  · exact kudstaticRange_345.get (by omega) (by omega)
  by_cases h17 : j < 405
  · exact kudstaticRange_375.get (by omega) (by omega)
  by_cases h18 : j < 435
  · exact kudstaticRange_405.get (by omega) (by omega)
  by_cases h19 : j < 465
  · exact kudstaticRange_435.get (by omega) (by omega)
  by_cases h20 : j < 495
  · exact kudstaticRange_465.get (by omega) (by omega)
  by_cases h21 : j < 525
  · exact kudstaticRange_495.get (by omega) (by omega)
  by_cases h22 : j < 555
  · exact kudstaticRange_525.get (by omega) (by omega)
  by_cases h23 : j < 585
  · exact kudstaticRange_555.get (by omega) (by omega)
  by_cases h24 : j < 615
  · exact kudstaticRange_585.get (by omega) (by omega)
  by_cases h25 : j < 645
  · exact kudstaticRange_615.get (by omega) (by omega)
  by_cases h26 : j < 675
  · exact kudstaticRange_645.get (by omega) (by omega)
  by_cases h27 : j < 705
  · exact kudstaticRange_675.get (by omega) (by omega)
  by_cases h28 : j < 735
  · exact kudstaticRange_705.get (by omega) (by omega)
  by_cases h29 : j < 765
  · exact kudstaticRange_735.get (by omega) (by omega)
  by_cases h30 : j < 795
  · exact kudstaticRange_765.get (by omega) (by omega)
  by_cases h31 : j < 825
  · exact kudstaticRange_795.get (by omega) (by omega)
  by_cases h32 : j < 855
  · exact kudstaticRange_825.get (by omega) (by omega)
  exact kudstaticRange_855.get (by omega) (by omega)

end
end LeanVM.Guest
