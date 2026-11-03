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

theorem kuschkIdx_all : ∀ j < 883, kuschkIdx j = true := by
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
  by_cases h7 : j < 179
  · exact kusstaticRange_156.get (by omega) (by omega)
  by_cases h8 : j < 205
  · exact kusstaticRange_179.get (by omega) (by omega)
  by_cases h9 : j < 231
  · exact kusstaticRange_205.get (by omega) (by omega)
  by_cases h10 : j < 261
  · exact kusstaticRange_231.get (by omega) (by omega)
  by_cases h11 : j < 287
  · exact kusstaticRange_261.get (by omega) (by omega)
  by_cases h12 : j < 301
  · exact kusstaticRange_287.get (by omega) (by omega)
  by_cases h13 : j < 308
  · exact kusstaticRange_301.get (by omega) (by omega)
  by_cases h14 : j < 315
  · exact kusstaticRange_308.get (by omega) (by omega)
  by_cases h15 : j < 345
  · exact kusstaticRange_315.get (by omega) (by omega)
  by_cases h16 : j < 375
  · exact kusstaticRange_345.get (by omega) (by omega)
  by_cases h17 : j < 405
  · exact kusstaticRange_375.get (by omega) (by omega)
  by_cases h18 : j < 435
  · exact kusstaticRange_405.get (by omega) (by omega)
  by_cases h19 : j < 465
  · exact kusstaticRange_435.get (by omega) (by omega)
  by_cases h20 : j < 495
  · exact kusstaticRange_465.get (by omega) (by omega)
  by_cases h21 : j < 525
  · exact kusstaticRange_495.get (by omega) (by omega)
  by_cases h22 : j < 555
  · exact kusstaticRange_525.get (by omega) (by omega)
  by_cases h23 : j < 585
  · exact kusstaticRange_555.get (by omega) (by omega)
  by_cases h24 : j < 615
  · exact kusstaticRange_585.get (by omega) (by omega)
  by_cases h25 : j < 645
  · exact kusstaticRange_615.get (by omega) (by omega)
  by_cases h26 : j < 675
  · exact kusstaticRange_645.get (by omega) (by omega)
  by_cases h27 : j < 705
  · exact kusstaticRange_675.get (by omega) (by omega)
  by_cases h28 : j < 735
  · exact kusstaticRange_705.get (by omega) (by omega)
  by_cases h29 : j < 765
  · exact kusstaticRange_735.get (by omega) (by omega)
  by_cases h30 : j < 795
  · exact kusstaticRange_765.get (by omega) (by omega)
  by_cases h31 : j < 825
  · exact kusstaticRange_795.get (by omega) (by omega)
  by_cases h32 : j < 855
  · exact kusstaticRange_825.get (by omega) (by omega)
  exact kusstaticRange_855.get (by omega) (by omega)

end
end LeanVM.Guest
