/-
  LeanVM.Guest.Memory.GuestCntM.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntM.Part00
public import LeanVM.Guest.Memory.GuestCntM.Part01
public import LeanVM.Guest.Memory.GuestCntM.Part02
public import LeanVM.Guest.Memory.GuestCntM.Part03
public import LeanVM.Guest.Memory.GuestCntM.Part04
public import LeanVM.Guest.Memory.GuestCntM.Part05
public import LeanVM.Guest.Memory.GuestCntM.Part06

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwmchkIdx_19 : kwmchkIdx 19 = true := by
  have hb : blockB (kwmlookJ 19) (kwmomLookJ 19) false [] Data.core19.params Data.core19.name ([], []) Data.core19.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core19.body)]
    rw [blockB_dropE _ _ _ 0 558 558 kwmsplit_19_0.1 rfl kwmsplit_19_0.2.2,
      ← blockR_eq ((Data.core19.body.drop 0).take 558), kwmsplit_19_0.2.1]
    rw [← blockR_eq (Data.core19.body.drop 558), kwmsplit_19_558]
    rfl
  exact kwmchkIdx_of_split (fn := Data.core19) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kwmchkIdx_20 : kwmchkIdx 20 = true := by
  have hb : blockB (kwmlookJ 20) (kwmomLookJ 20) false [] Data.core20.params Data.core20.name ([], []) Data.core20.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core20.body)]
    rw [blockB_dropE _ _ _ 0 94 94 kwmsplit_20_0.1 rfl kwmsplit_20_0.2.2,
      ← blockR_eq ((Data.core20.body.drop 0).take 94), kwmsplit_20_0.2.1]
    rw [← blockR_eq (Data.core20.body.drop 94), kwmsplit_20_94]
    rfl
  exact kwmchkIdx_of_split (fn := Data.core20) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kwmchkIdx_all : ∀ j < 947, kwmchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 19
  · subst h1000; exact kwmchkIdx_19
  by_cases h1001 : j = 20
  · subst h1001; exact kwmchkIdx_20
  by_cases h0 : j < 11
  · exact kwmstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kwmstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 19
  · exact kwmstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 51
  · exact kwmstaticRange_21.get (by omega) (by omega)
  by_cases h4 : j < 81
  · exact kwmstaticRange_51.get (by omega) (by omega)
  by_cases h5 : j < 111
  · exact kwmstaticRange_81.get (by omega) (by omega)
  by_cases h6 : j < 141
  · exact kwmstaticRange_111.get (by omega) (by omega)
  by_cases h7 : j < 171
  · exact kwmstaticRange_141.get (by omega) (by omega)
  by_cases h8 : j < 201
  · exact kwmstaticRange_171.get (by omega) (by omega)
  by_cases h9 : j < 231
  · exact kwmstaticRange_201.get (by omega) (by omega)
  by_cases h10 : j < 261
  · exact kwmstaticRange_231.get (by omega) (by omega)
  by_cases h11 : j < 291
  · exact kwmstaticRange_261.get (by omega) (by omega)
  by_cases h12 : j < 310
  · exact kwmstaticRange_291.get (by omega) (by omega)
  by_cases h13 : j < 317
  · exact kwmstaticRange_310.get (by omega) (by omega)
  by_cases h14 : j < 324
  · exact kwmstaticRange_317.get (by omega) (by omega)
  by_cases h15 : j < 354
  · exact kwmstaticRange_324.get (by omega) (by omega)
  by_cases h16 : j < 384
  · exact kwmstaticRange_354.get (by omega) (by omega)
  by_cases h17 : j < 414
  · exact kwmstaticRange_384.get (by omega) (by omega)
  by_cases h18 : j < 444
  · exact kwmstaticRange_414.get (by omega) (by omega)
  by_cases h19 : j < 474
  · exact kwmstaticRange_444.get (by omega) (by omega)
  by_cases h20 : j < 504
  · exact kwmstaticRange_474.get (by omega) (by omega)
  by_cases h21 : j < 534
  · exact kwmstaticRange_504.get (by omega) (by omega)
  by_cases h22 : j < 564
  · exact kwmstaticRange_534.get (by omega) (by omega)
  by_cases h23 : j < 594
  · exact kwmstaticRange_564.get (by omega) (by omega)
  by_cases h24 : j < 624
  · exact kwmstaticRange_594.get (by omega) (by omega)
  by_cases h25 : j < 654
  · exact kwmstaticRange_624.get (by omega) (by omega)
  by_cases h26 : j < 684
  · exact kwmstaticRange_654.get (by omega) (by omega)
  by_cases h27 : j < 714
  · exact kwmstaticRange_684.get (by omega) (by omega)
  by_cases h28 : j < 744
  · exact kwmstaticRange_714.get (by omega) (by omega)
  by_cases h29 : j < 774
  · exact kwmstaticRange_744.get (by omega) (by omega)
  by_cases h30 : j < 804
  · exact kwmstaticRange_774.get (by omega) (by omega)
  by_cases h31 : j < 834
  · exact kwmstaticRange_804.get (by omega) (by omega)
  by_cases h32 : j < 864
  · exact kwmstaticRange_834.get (by omega) (by omega)
  by_cases h33 : j < 894
  · exact kwmstaticRange_864.get (by omega) (by omega)
  by_cases h34 : j < 924
  · exact kwmstaticRange_894.get (by omega) (by omega)
  exact kwmstaticRange_924.get (by omega) (by omega)

end
end LeanVM.Guest
