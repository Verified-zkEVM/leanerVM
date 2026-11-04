/-
  LeanVM.Guest.Memory.GuestCntX.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntX.Part00
public import LeanVM.Guest.Memory.GuestCntX.Part01
public import LeanVM.Guest.Memory.GuestCntX.Part02
public import LeanVM.Guest.Memory.GuestCntX.Part03
public import LeanVM.Guest.Memory.GuestCntX.Part04
public import LeanVM.Guest.Memory.GuestCntX.Part05
public import LeanVM.Guest.Memory.GuestCntX.Part06

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwxchkIdx_19 : kwxchkIdx 19 = true := by
  have hb : blockB (kwxlookJ 19) (kwxomLookJ 19) false [] Data.core19.params Data.core19.name ([], []) Data.core19.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core19.body)]
    rw [blockB_dropE _ _ _ 0 558 558 kwxsplit_19_0.1 rfl kwxsplit_19_0.2.2,
      ← blockR_eq ((Data.core19.body.drop 0).take 558), kwxsplit_19_0.2.1]
    rw [← blockR_eq (Data.core19.body.drop 558), kwxsplit_19_558]
    rfl
  exact kwxchkIdx_of_split (fn := Data.core19) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kwxchkIdx_20 : kwxchkIdx 20 = true := by
  have hb : blockB (kwxlookJ 20) (kwxomLookJ 20) false [] Data.core20.params Data.core20.name ([], []) Data.core20.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core20.body)]
    rw [blockB_dropE _ _ _ 0 94 94 kwxsplit_20_0.1 rfl kwxsplit_20_0.2.2,
      ← blockR_eq ((Data.core20.body.drop 0).take 94), kwxsplit_20_0.2.1]
    rw [← blockR_eq (Data.core20.body.drop 94), kwxsplit_20_94]
    rfl
  exact kwxchkIdx_of_split (fn := Data.core20) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kwxchkIdx_all : ∀ j < 947, kwxchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 19
  · subst h1000; exact kwxchkIdx_19
  by_cases h1001 : j = 20
  · subst h1001; exact kwxchkIdx_20
  by_cases h0 : j < 11
  · exact kwxstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kwxstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 19
  · exact kwxstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 51
  · exact kwxstaticRange_21.get (by omega) (by omega)
  by_cases h4 : j < 81
  · exact kwxstaticRange_51.get (by omega) (by omega)
  by_cases h5 : j < 111
  · exact kwxstaticRange_81.get (by omega) (by omega)
  by_cases h6 : j < 141
  · exact kwxstaticRange_111.get (by omega) (by omega)
  by_cases h7 : j < 171
  · exact kwxstaticRange_141.get (by omega) (by omega)
  by_cases h8 : j < 201
  · exact kwxstaticRange_171.get (by omega) (by omega)
  by_cases h9 : j < 231
  · exact kwxstaticRange_201.get (by omega) (by omega)
  by_cases h10 : j < 261
  · exact kwxstaticRange_231.get (by omega) (by omega)
  by_cases h11 : j < 291
  · exact kwxstaticRange_261.get (by omega) (by omega)
  by_cases h12 : j < 310
  · exact kwxstaticRange_291.get (by omega) (by omega)
  by_cases h13 : j < 317
  · exact kwxstaticRange_310.get (by omega) (by omega)
  by_cases h14 : j < 324
  · exact kwxstaticRange_317.get (by omega) (by omega)
  by_cases h15 : j < 354
  · exact kwxstaticRange_324.get (by omega) (by omega)
  by_cases h16 : j < 384
  · exact kwxstaticRange_354.get (by omega) (by omega)
  by_cases h17 : j < 414
  · exact kwxstaticRange_384.get (by omega) (by omega)
  by_cases h18 : j < 444
  · exact kwxstaticRange_414.get (by omega) (by omega)
  by_cases h19 : j < 474
  · exact kwxstaticRange_444.get (by omega) (by omega)
  by_cases h20 : j < 504
  · exact kwxstaticRange_474.get (by omega) (by omega)
  by_cases h21 : j < 534
  · exact kwxstaticRange_504.get (by omega) (by omega)
  by_cases h22 : j < 564
  · exact kwxstaticRange_534.get (by omega) (by omega)
  by_cases h23 : j < 594
  · exact kwxstaticRange_564.get (by omega) (by omega)
  by_cases h24 : j < 624
  · exact kwxstaticRange_594.get (by omega) (by omega)
  by_cases h25 : j < 654
  · exact kwxstaticRange_624.get (by omega) (by omega)
  by_cases h26 : j < 684
  · exact kwxstaticRange_654.get (by omega) (by omega)
  by_cases h27 : j < 714
  · exact kwxstaticRange_684.get (by omega) (by omega)
  by_cases h28 : j < 744
  · exact kwxstaticRange_714.get (by omega) (by omega)
  by_cases h29 : j < 774
  · exact kwxstaticRange_744.get (by omega) (by omega)
  by_cases h30 : j < 804
  · exact kwxstaticRange_774.get (by omega) (by omega)
  by_cases h31 : j < 834
  · exact kwxstaticRange_804.get (by omega) (by omega)
  by_cases h32 : j < 864
  · exact kwxstaticRange_834.get (by omega) (by omega)
  by_cases h33 : j < 894
  · exact kwxstaticRange_864.get (by omega) (by omega)
  by_cases h34 : j < 924
  · exact kwxstaticRange_894.get (by omega) (by omega)
  exact kwxstaticRange_924.get (by omega) (by omega)

end
end LeanVM.Guest
