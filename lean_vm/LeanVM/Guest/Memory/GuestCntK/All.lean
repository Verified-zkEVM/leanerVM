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
public import LeanVM.Guest.Memory.GuestCntK.Part06

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwkchkIdx_19 : kwkchkIdx 19 = true := by
  have hb : blockB (kwklookJ 19) (kwkomLookJ 19) false [] Data.core19.params Data.core19.name ([], []) Data.core19.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core19.body)]
    rw [blockB_dropE _ _ _ 0 558 558 kwksplit_19_0.1 rfl kwksplit_19_0.2.2,
      ← blockR_eq ((Data.core19.body.drop 0).take 558), kwksplit_19_0.2.1]
    rw [← blockR_eq (Data.core19.body.drop 558), kwksplit_19_558]
    rfl
  exact kwkchkIdx_of_split (fn := Data.core19) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kwkchkIdx_20 : kwkchkIdx 20 = true := by
  have hb : blockB (kwklookJ 20) (kwkomLookJ 20) false [] Data.core20.params Data.core20.name ([], []) Data.core20.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core20.body)]
    rw [blockB_dropE _ _ _ 0 94 94 kwksplit_20_0.1 rfl kwksplit_20_0.2.2,
      ← blockR_eq ((Data.core20.body.drop 0).take 94), kwksplit_20_0.2.1]
    rw [← blockR_eq (Data.core20.body.drop 94), kwksplit_20_94]
    rfl
  exact kwkchkIdx_of_split (fn := Data.core20) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kwkchkIdx_all : ∀ j < 947, kwkchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 19
  · subst h1000; exact kwkchkIdx_19
  by_cases h1001 : j = 20
  · subst h1001; exact kwkchkIdx_20
  by_cases h0 : j < 11
  · exact kwkstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kwkstaticRange_11.get (by omega) (by omega)
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
  by_cases h12 : j < 310
  · exact kwkstaticRange_291.get (by omega) (by omega)
  by_cases h13 : j < 317
  · exact kwkstaticRange_310.get (by omega) (by omega)
  by_cases h14 : j < 324
  · exact kwkstaticRange_317.get (by omega) (by omega)
  by_cases h15 : j < 354
  · exact kwkstaticRange_324.get (by omega) (by omega)
  by_cases h16 : j < 384
  · exact kwkstaticRange_354.get (by omega) (by omega)
  by_cases h17 : j < 414
  · exact kwkstaticRange_384.get (by omega) (by omega)
  by_cases h18 : j < 444
  · exact kwkstaticRange_414.get (by omega) (by omega)
  by_cases h19 : j < 474
  · exact kwkstaticRange_444.get (by omega) (by omega)
  by_cases h20 : j < 504
  · exact kwkstaticRange_474.get (by omega) (by omega)
  by_cases h21 : j < 534
  · exact kwkstaticRange_504.get (by omega) (by omega)
  by_cases h22 : j < 564
  · exact kwkstaticRange_534.get (by omega) (by omega)
  by_cases h23 : j < 594
  · exact kwkstaticRange_564.get (by omega) (by omega)
  by_cases h24 : j < 624
  · exact kwkstaticRange_594.get (by omega) (by omega)
  by_cases h25 : j < 654
  · exact kwkstaticRange_624.get (by omega) (by omega)
  by_cases h26 : j < 684
  · exact kwkstaticRange_654.get (by omega) (by omega)
  by_cases h27 : j < 714
  · exact kwkstaticRange_684.get (by omega) (by omega)
  by_cases h28 : j < 744
  · exact kwkstaticRange_714.get (by omega) (by omega)
  by_cases h29 : j < 774
  · exact kwkstaticRange_744.get (by omega) (by omega)
  by_cases h30 : j < 804
  · exact kwkstaticRange_774.get (by omega) (by omega)
  by_cases h31 : j < 834
  · exact kwkstaticRange_804.get (by omega) (by omega)
  by_cases h32 : j < 864
  · exact kwkstaticRange_834.get (by omega) (by omega)
  by_cases h33 : j < 894
  · exact kwkstaticRange_864.get (by omega) (by omega)
  by_cases h34 : j < 924
  · exact kwkstaticRange_894.get (by omega) (by omega)
  exact kwkstaticRange_924.get (by omega) (by omega)

end
end LeanVM.Guest
