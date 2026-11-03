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

theorem kujchkIdx_all : ∀ j < 883, kujchkIdx j = true := by
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
  by_cases h7 : j < 179
  · exact kujstaticRange_156.get (by omega) (by omega)
  by_cases h8 : j < 205
  · exact kujstaticRange_179.get (by omega) (by omega)
  by_cases h9 : j < 231
  · exact kujstaticRange_205.get (by omega) (by omega)
  by_cases h10 : j < 261
  · exact kujstaticRange_231.get (by omega) (by omega)
  by_cases h11 : j < 287
  · exact kujstaticRange_261.get (by omega) (by omega)
  by_cases h12 : j < 301
  · exact kujstaticRange_287.get (by omega) (by omega)
  by_cases h13 : j < 308
  · exact kujstaticRange_301.get (by omega) (by omega)
  by_cases h14 : j < 315
  · exact kujstaticRange_308.get (by omega) (by omega)
  by_cases h15 : j < 345
  · exact kujstaticRange_315.get (by omega) (by omega)
  by_cases h16 : j < 375
  · exact kujstaticRange_345.get (by omega) (by omega)
  by_cases h17 : j < 405
  · exact kujstaticRange_375.get (by omega) (by omega)
  by_cases h18 : j < 435
  · exact kujstaticRange_405.get (by omega) (by omega)
  by_cases h19 : j < 465
  · exact kujstaticRange_435.get (by omega) (by omega)
  by_cases h20 : j < 495
  · exact kujstaticRange_465.get (by omega) (by omega)
  by_cases h21 : j < 525
  · exact kujstaticRange_495.get (by omega) (by omega)
  by_cases h22 : j < 555
  · exact kujstaticRange_525.get (by omega) (by omega)
  by_cases h23 : j < 585
  · exact kujstaticRange_555.get (by omega) (by omega)
  by_cases h24 : j < 615
  · exact kujstaticRange_585.get (by omega) (by omega)
  by_cases h25 : j < 645
  · exact kujstaticRange_615.get (by omega) (by omega)
  by_cases h26 : j < 675
  · exact kujstaticRange_645.get (by omega) (by omega)
  by_cases h27 : j < 705
  · exact kujstaticRange_675.get (by omega) (by omega)
  by_cases h28 : j < 735
  · exact kujstaticRange_705.get (by omega) (by omega)
  by_cases h29 : j < 765
  · exact kujstaticRange_735.get (by omega) (by omega)
  by_cases h30 : j < 795
  · exact kujstaticRange_765.get (by omega) (by omega)
  by_cases h31 : j < 825
  · exact kujstaticRange_795.get (by omega) (by omega)
  by_cases h32 : j < 855
  · exact kujstaticRange_825.get (by omega) (by omega)
  exact kujstaticRange_855.get (by omega) (by omega)

end
end LeanVM.Guest
