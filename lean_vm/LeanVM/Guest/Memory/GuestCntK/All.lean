/-
  LeanVM.Guest.Memory.GuestCntK.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntK.Part00
public import LeanVM.Guest.Memory.GuestCntK.Part01
public import LeanVM.Guest.Memory.GuestCntK.Part02
public import LeanVM.Guest.Memory.GuestCntK.Part03
public import LeanVM.Guest.Memory.GuestCntK.Part04
public import LeanVM.Guest.Memory.GuestCntK.Part05

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwkchkIdx_19 : kwkchkIdx 19 = true := by
  have hb : blockB (kwklookJ 19) (kwkomLookJ 19) false [] Data.core19.params Data.core19.name ([], []) Data.core19.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core19.body)]
    rw [blockB_dropE _ _ _ 0 533 533 kwksplit_19_0.1 rfl kwksplit_19_0.2.2,
      ← blockR_eq ((Data.core19.body.drop 0).take 533), kwksplit_19_0.2.1]
    rw [← blockR_eq (Data.core19.body.drop 533), kwksplit_19_533]
    rfl
  exact kwkchkIdx_of_split (fn := Data.core19) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kwkchkIdx_20 : kwkchkIdx 20 = true := by
  have hb : blockB (kwklookJ 20) (kwkomLookJ 20) false [] Data.core20.params Data.core20.name ([], []) Data.core20.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core20.body)]
    rw [blockB_dropE _ _ _ 0 61 61 kwksplit_20_0.1 rfl kwksplit_20_0.2.2,
      ← blockR_eq ((Data.core20.body.drop 0).take 61), kwksplit_20_0.2.1]
    rw [← blockR_eq (Data.core20.body.drop 61), kwksplit_20_61]
    rfl
  exact kwkchkIdx_of_split (fn := Data.core20) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kwkchkIdx_all : ∀ j < 884, kwkchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 19
  · subst h1000; exact kwkchkIdx_19
  by_cases h1001 : j = 20
  · subst h1001; exact kwkchkIdx_20
  by_cases h0 : j < 10
  · exact kwkstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kwkstaticRange_10.get (by omega) (by omega)
  by_cases h2 : j < 19
  · exact kwkstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 51
  · exact kwkstaticRange_21.get (by omega) (by omega)
  by_cases h4 : j < 81
  · exact kwkstaticRange_51.get (by omega) (by omega)
  by_cases h5 : j < 111
  · exact kwkstaticRange_81.get (by omega) (by omega)
  by_cases h6 : j < 141
  · exact kwkstaticRange_111.get (by omega) (by omega)
  by_cases h7 : j < 171
  · exact kwkstaticRange_141.get (by omega) (by omega)
  by_cases h8 : j < 201
  · exact kwkstaticRange_171.get (by omega) (by omega)
  by_cases h9 : j < 231
  · exact kwkstaticRange_201.get (by omega) (by omega)
  by_cases h10 : j < 261
  · exact kwkstaticRange_231.get (by omega) (by omega)
  by_cases h11 : j < 291
  · exact kwkstaticRange_261.get (by omega) (by omega)
  by_cases h12 : j < 302
  · exact kwkstaticRange_291.get (by omega) (by omega)
  by_cases h13 : j < 309
  · exact kwkstaticRange_302.get (by omega) (by omega)
  by_cases h14 : j < 316
  · exact kwkstaticRange_309.get (by omega) (by omega)
  by_cases h15 : j < 346
  · exact kwkstaticRange_316.get (by omega) (by omega)
  by_cases h16 : j < 376
  · exact kwkstaticRange_346.get (by omega) (by omega)
  by_cases h17 : j < 406
  · exact kwkstaticRange_376.get (by omega) (by omega)
  by_cases h18 : j < 436
  · exact kwkstaticRange_406.get (by omega) (by omega)
  by_cases h19 : j < 466
  · exact kwkstaticRange_436.get (by omega) (by omega)
  by_cases h20 : j < 496
  · exact kwkstaticRange_466.get (by omega) (by omega)
  by_cases h21 : j < 526
  · exact kwkstaticRange_496.get (by omega) (by omega)
  by_cases h22 : j < 556
  · exact kwkstaticRange_526.get (by omega) (by omega)
  by_cases h23 : j < 586
  · exact kwkstaticRange_556.get (by omega) (by omega)
  by_cases h24 : j < 616
  · exact kwkstaticRange_586.get (by omega) (by omega)
  by_cases h25 : j < 646
  · exact kwkstaticRange_616.get (by omega) (by omega)
  by_cases h26 : j < 676
  · exact kwkstaticRange_646.get (by omega) (by omega)
  by_cases h27 : j < 706
  · exact kwkstaticRange_676.get (by omega) (by omega)
  by_cases h28 : j < 736
  · exact kwkstaticRange_706.get (by omega) (by omega)
  by_cases h29 : j < 766
  · exact kwkstaticRange_736.get (by omega) (by omega)
  by_cases h30 : j < 796
  · exact kwkstaticRange_766.get (by omega) (by omega)
  by_cases h31 : j < 826
  · exact kwkstaticRange_796.get (by omega) (by omega)
  by_cases h32 : j < 856
  · exact kwkstaticRange_826.get (by omega) (by omega)
  exact kwkstaticRange_856.get (by omega) (by omega)

end
end LeanVM.Guest
