/-
  LeanVM.Guest.Memory.GuestCntD.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntD.Part00
public import LeanVM.Guest.Memory.GuestCntD.Part01
public import LeanVM.Guest.Memory.GuestCntD.Part02
public import LeanVM.Guest.Memory.GuestCntD.Part03
public import LeanVM.Guest.Memory.GuestCntD.Part04
public import LeanVM.Guest.Memory.GuestCntD.Part05
public import LeanVM.Guest.Memory.GuestCntD.Part06
public import LeanVM.Guest.Memory.GuestCntD.Part07

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwdchkIdx_19 : kwdchkIdx 19 = true := by
  have hb : blockB (kwdlookJ 19) (kwdomLookJ 19) false [] Data.core19.params Data.core19.name ([], []) Data.core19.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core19.body)]
    rw [blockB_dropE _ _ _ 0 533 533 kwdsplit_19_0.1 rfl kwdsplit_19_0.2.2,
      ← blockR_eq ((Data.core19.body.drop 0).take 533), kwdsplit_19_0.2.1]
    rw [← blockR_eq (Data.core19.body.drop 533), kwdsplit_19_533]
    rfl
  exact kwdchkIdx_of_split (fn := Data.core19) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kwdchkIdx_20 : kwdchkIdx 20 = true := by
  have hb : blockB (kwdlookJ 20) (kwdomLookJ 20) false [] Data.core20.params Data.core20.name ([], []) Data.core20.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core20.body)]
    rw [blockB_dropE _ _ _ 0 246 246 kwdsplit_20_0.1 rfl kwdsplit_20_0.2.2,
      ← blockR_eq ((Data.core20.body.drop 0).take 246), kwdsplit_20_0.2.1]
    rw [blockB_dropE _ _ _ 246 63 309 kwdsplit_20_246.1 rfl kwdsplit_20_246.2.2,
      ← blockR_eq ((Data.core20.body.drop 246).take 63), kwdsplit_20_246.2.1]
    rw [blockB_dropE _ _ _ 309 48 357 kwdsplit_20_309.1 rfl kwdsplit_20_309.2.2,
      ← blockR_eq ((Data.core20.body.drop 309).take 48), kwdsplit_20_309.2.1]
    rw [blockB_dropE _ _ _ 357 63 420 kwdsplit_20_357.1 rfl kwdsplit_20_357.2.2,
      ← blockR_eq ((Data.core20.body.drop 357).take 63), kwdsplit_20_357.2.1]
    rw [blockB_dropE _ _ _ 420 48 468 kwdsplit_20_420.1 rfl kwdsplit_20_420.2.2,
      ← blockR_eq ((Data.core20.body.drop 420).take 48), kwdsplit_20_420.2.1]
    rw [blockB_dropE _ _ _ 468 110 578 kwdsplit_20_468.1 rfl kwdsplit_20_468.2.2,
      ← blockR_eq ((Data.core20.body.drop 468).take 110), kwdsplit_20_468.2.1]
    rw [← blockR_eq (Data.core20.body.drop 578), kwdsplit_20_578]
    rfl
  exact kwdchkIdx_of_split (fn := Data.core20) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kwdchkIdx_all : ∀ j < 899, kwdchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 19
  · subst h1000; exact kwdchkIdx_19
  by_cases h1001 : j = 20
  · subst h1001; exact kwdchkIdx_20
  by_cases h0 : j < 10
  · exact kwdstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kwdstaticRange_10.get (by omega) (by omega)
  by_cases h2 : j < 19
  · exact kwdstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 51
  · exact kwdstaticRange_21.get (by omega) (by omega)
  by_cases h4 : j < 81
  · exact kwdstaticRange_51.get (by omega) (by omega)
  by_cases h5 : j < 111
  · exact kwdstaticRange_81.get (by omega) (by omega)
  by_cases h6 : j < 141
  · exact kwdstaticRange_111.get (by omega) (by omega)
  by_cases h7 : j < 171
  · exact kwdstaticRange_141.get (by omega) (by omega)
  by_cases h8 : j < 201
  · exact kwdstaticRange_171.get (by omega) (by omega)
  by_cases h9 : j < 231
  · exact kwdstaticRange_201.get (by omega) (by omega)
  by_cases h10 : j < 261
  · exact kwdstaticRange_231.get (by omega) (by omega)
  by_cases h11 : j < 291
  · exact kwdstaticRange_261.get (by omega) (by omega)
  by_cases h12 : j < 302
  · exact kwdstaticRange_291.get (by omega) (by omega)
  by_cases h13 : j < 309
  · exact kwdstaticRange_302.get (by omega) (by omega)
  by_cases h14 : j < 316
  · exact kwdstaticRange_309.get (by omega) (by omega)
  by_cases h15 : j < 346
  · exact kwdstaticRange_316.get (by omega) (by omega)
  by_cases h16 : j < 376
  · exact kwdstaticRange_346.get (by omega) (by omega)
  by_cases h17 : j < 406
  · exact kwdstaticRange_376.get (by omega) (by omega)
  by_cases h18 : j < 436
  · exact kwdstaticRange_406.get (by omega) (by omega)
  by_cases h19 : j < 466
  · exact kwdstaticRange_436.get (by omega) (by omega)
  by_cases h20 : j < 496
  · exact kwdstaticRange_466.get (by omega) (by omega)
  by_cases h21 : j < 526
  · exact kwdstaticRange_496.get (by omega) (by omega)
  by_cases h22 : j < 556
  · exact kwdstaticRange_526.get (by omega) (by omega)
  by_cases h23 : j < 586
  · exact kwdstaticRange_556.get (by omega) (by omega)
  by_cases h24 : j < 616
  · exact kwdstaticRange_586.get (by omega) (by omega)
  by_cases h25 : j < 646
  · exact kwdstaticRange_616.get (by omega) (by omega)
  by_cases h26 : j < 676
  · exact kwdstaticRange_646.get (by omega) (by omega)
  by_cases h27 : j < 706
  · exact kwdstaticRange_676.get (by omega) (by omega)
  by_cases h28 : j < 736
  · exact kwdstaticRange_706.get (by omega) (by omega)
  by_cases h29 : j < 766
  · exact kwdstaticRange_736.get (by omega) (by omega)
  by_cases h30 : j < 796
  · exact kwdstaticRange_766.get (by omega) (by omega)
  by_cases h31 : j < 826
  · exact kwdstaticRange_796.get (by omega) (by omega)
  by_cases h32 : j < 856
  · exact kwdstaticRange_826.get (by omega) (by omega)
  by_cases h33 : j < 886
  · exact kwdstaticRange_856.get (by omega) (by omega)
  exact kwdstaticRange_886.get (by omega) (by omega)

end
end LeanVM.Guest
