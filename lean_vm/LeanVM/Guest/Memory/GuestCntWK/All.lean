/-
  LeanVM.Guest.Memory.GuestCntWK.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntWK.Part00
public import LeanVM.Guest.Memory.GuestCntWK.Part01
public import LeanVM.Guest.Memory.GuestCntWK.Part02
public import LeanVM.Guest.Memory.GuestCntWK.Part03
public import LeanVM.Guest.Memory.GuestCntWK.Part04
public import LeanVM.Guest.Memory.GuestCntWK.Part05

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kukchkIdx_all : ∀ j < 883, kukchkIdx j = true := by
  intro j hj
  by_cases h0 : j < 10
  · exact kukstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kukstaticRange_10.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kukstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 74
  · exact kukstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 103
  · exact kukstaticRange_74.get (by omega) (by omega)
  by_cases h5 : j < 129
  · exact kukstaticRange_103.get (by omega) (by omega)
  by_cases h6 : j < 156
  · exact kukstaticRange_129.get (by omega) (by omega)
  by_cases h7 : j < 179
  · exact kukstaticRange_156.get (by omega) (by omega)
  by_cases h8 : j < 205
  · exact kukstaticRange_179.get (by omega) (by omega)
  by_cases h9 : j < 231
  · exact kukstaticRange_205.get (by omega) (by omega)
  by_cases h10 : j < 261
  · exact kukstaticRange_231.get (by omega) (by omega)
  by_cases h11 : j < 287
  · exact kukstaticRange_261.get (by omega) (by omega)
  by_cases h12 : j < 301
  · exact kukstaticRange_287.get (by omega) (by omega)
  by_cases h13 : j < 308
  · exact kukstaticRange_301.get (by omega) (by omega)
  by_cases h14 : j < 315
  · exact kukstaticRange_308.get (by omega) (by omega)
  by_cases h15 : j < 345
  · exact kukstaticRange_315.get (by omega) (by omega)
  by_cases h16 : j < 375
  · exact kukstaticRange_345.get (by omega) (by omega)
  by_cases h17 : j < 405
  · exact kukstaticRange_375.get (by omega) (by omega)
  by_cases h18 : j < 435
  · exact kukstaticRange_405.get (by omega) (by omega)
  by_cases h19 : j < 465
  · exact kukstaticRange_435.get (by omega) (by omega)
  by_cases h20 : j < 495
  · exact kukstaticRange_465.get (by omega) (by omega)
  by_cases h21 : j < 525
  · exact kukstaticRange_495.get (by omega) (by omega)
  by_cases h22 : j < 555
  · exact kukstaticRange_525.get (by omega) (by omega)
  by_cases h23 : j < 585
  · exact kukstaticRange_555.get (by omega) (by omega)
  by_cases h24 : j < 615
  · exact kukstaticRange_585.get (by omega) (by omega)
  by_cases h25 : j < 645
  · exact kukstaticRange_615.get (by omega) (by omega)
  by_cases h26 : j < 675
  · exact kukstaticRange_645.get (by omega) (by omega)
  by_cases h27 : j < 705
  · exact kukstaticRange_675.get (by omega) (by omega)
  by_cases h28 : j < 735
  · exact kukstaticRange_705.get (by omega) (by omega)
  by_cases h29 : j < 765
  · exact kukstaticRange_735.get (by omega) (by omega)
  by_cases h30 : j < 795
  · exact kukstaticRange_765.get (by omega) (by omega)
  by_cases h31 : j < 825
  · exact kukstaticRange_795.get (by omega) (by omega)
  by_cases h32 : j < 855
  · exact kukstaticRange_825.get (by omega) (by omega)
  exact kukstaticRange_855.get (by omega) (by omega)

end
end LeanVM.Guest
