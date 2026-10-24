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

theorem kukchkIdx_all : ∀ j < 899, kukchkIdx j = true := by
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
  by_cases h7 : j < 180
  · exact kukstaticRange_156.get (by omega) (by omega)
  by_cases h8 : j < 206
  · exact kukstaticRange_180.get (by omega) (by omega)
  by_cases h9 : j < 232
  · exact kukstaticRange_206.get (by omega) (by omega)
  by_cases h10 : j < 262
  · exact kukstaticRange_232.get (by omega) (by omega)
  by_cases h11 : j < 288
  · exact kukstaticRange_262.get (by omega) (by omega)
  by_cases h12 : j < 302
  · exact kukstaticRange_288.get (by omega) (by omega)
  by_cases h13 : j < 309
  · exact kukstaticRange_302.get (by omega) (by omega)
  by_cases h14 : j < 316
  · exact kukstaticRange_309.get (by omega) (by omega)
  by_cases h15 : j < 346
  · exact kukstaticRange_316.get (by omega) (by omega)
  by_cases h16 : j < 376
  · exact kukstaticRange_346.get (by omega) (by omega)
  by_cases h17 : j < 406
  · exact kukstaticRange_376.get (by omega) (by omega)
  by_cases h18 : j < 436
  · exact kukstaticRange_406.get (by omega) (by omega)
  by_cases h19 : j < 466
  · exact kukstaticRange_436.get (by omega) (by omega)
  by_cases h20 : j < 496
  · exact kukstaticRange_466.get (by omega) (by omega)
  by_cases h21 : j < 526
  · exact kukstaticRange_496.get (by omega) (by omega)
  by_cases h22 : j < 556
  · exact kukstaticRange_526.get (by omega) (by omega)
  by_cases h23 : j < 586
  · exact kukstaticRange_556.get (by omega) (by omega)
  by_cases h24 : j < 616
  · exact kukstaticRange_586.get (by omega) (by omega)
  by_cases h25 : j < 646
  · exact kukstaticRange_616.get (by omega) (by omega)
  by_cases h26 : j < 676
  · exact kukstaticRange_646.get (by omega) (by omega)
  by_cases h27 : j < 706
  · exact kukstaticRange_676.get (by omega) (by omega)
  by_cases h28 : j < 736
  · exact kukstaticRange_706.get (by omega) (by omega)
  by_cases h29 : j < 766
  · exact kukstaticRange_736.get (by omega) (by omega)
  by_cases h30 : j < 796
  · exact kukstaticRange_766.get (by omega) (by omega)
  by_cases h31 : j < 826
  · exact kukstaticRange_796.get (by omega) (by omega)
  by_cases h32 : j < 856
  · exact kukstaticRange_826.get (by omega) (by omega)
  by_cases h33 : j < 886
  · exact kukstaticRange_856.get (by omega) (by omega)
  exact kukstaticRange_886.get (by omega) (by omega)

end
end LeanVM.Guest
