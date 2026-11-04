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

theorem kumchkIdx_all : ∀ j < 883, kumchkIdx j = true := by
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
  by_cases h7 : j < 179
  · exact kumstaticRange_156.get (by omega) (by omega)
  by_cases h8 : j < 205
  · exact kumstaticRange_179.get (by omega) (by omega)
  by_cases h9 : j < 231
  · exact kumstaticRange_205.get (by omega) (by omega)
  by_cases h10 : j < 261
  · exact kumstaticRange_231.get (by omega) (by omega)
  by_cases h11 : j < 287
  · exact kumstaticRange_261.get (by omega) (by omega)
  by_cases h12 : j < 301
  · exact kumstaticRange_287.get (by omega) (by omega)
  by_cases h13 : j < 308
  · exact kumstaticRange_301.get (by omega) (by omega)
  by_cases h14 : j < 315
  · exact kumstaticRange_308.get (by omega) (by omega)
  by_cases h15 : j < 345
  · exact kumstaticRange_315.get (by omega) (by omega)
  by_cases h16 : j < 375
  · exact kumstaticRange_345.get (by omega) (by omega)
  by_cases h17 : j < 405
  · exact kumstaticRange_375.get (by omega) (by omega)
  by_cases h18 : j < 435
  · exact kumstaticRange_405.get (by omega) (by omega)
  by_cases h19 : j < 465
  · exact kumstaticRange_435.get (by omega) (by omega)
  by_cases h20 : j < 495
  · exact kumstaticRange_465.get (by omega) (by omega)
  by_cases h21 : j < 525
  · exact kumstaticRange_495.get (by omega) (by omega)
  by_cases h22 : j < 555
  · exact kumstaticRange_525.get (by omega) (by omega)
  by_cases h23 : j < 585
  · exact kumstaticRange_555.get (by omega) (by omega)
  by_cases h24 : j < 615
  · exact kumstaticRange_585.get (by omega) (by omega)
  by_cases h25 : j < 645
  · exact kumstaticRange_615.get (by omega) (by omega)
  by_cases h26 : j < 675
  · exact kumstaticRange_645.get (by omega) (by omega)
  by_cases h27 : j < 705
  · exact kumstaticRange_675.get (by omega) (by omega)
  by_cases h28 : j < 735
  · exact kumstaticRange_705.get (by omega) (by omega)
  by_cases h29 : j < 765
  · exact kumstaticRange_735.get (by omega) (by omega)
  by_cases h30 : j < 795
  · exact kumstaticRange_765.get (by omega) (by omega)
  by_cases h31 : j < 825
  · exact kumstaticRange_795.get (by omega) (by omega)
  by_cases h32 : j < 855
  · exact kumstaticRange_825.get (by omega) (by omega)
  exact kumstaticRange_855.get (by omega) (by omega)

end
end LeanVM.Guest
