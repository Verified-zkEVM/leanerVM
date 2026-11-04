/-
  LeanVM.Guest.Memory.GuestCntS.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntS.Part00
public import LeanVM.Guest.Memory.GuestCntS.Part01
public import LeanVM.Guest.Memory.GuestCntS.Part02
public import LeanVM.Guest.Memory.GuestCntS.Part03
public import LeanVM.Guest.Memory.GuestCntS.Part04
public import LeanVM.Guest.Memory.GuestCntS.Part05
public import LeanVM.Guest.Memory.GuestCntS.Part06

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwschkIdx_19 : kwschkIdx 19 = true := by
  have hb : blockB (kwslookJ 19) (kwsomLookJ 19) false [] Data.core19.params Data.core19.name ([], []) Data.core19.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core19.body)]
    rw [blockB_dropE _ _ _ 0 558 558 kwssplit_19_0.1 rfl kwssplit_19_0.2.2,
      ← blockR_eq ((Data.core19.body.drop 0).take 558), kwssplit_19_0.2.1]
    rw [← blockR_eq (Data.core19.body.drop 558), kwssplit_19_558]
    rfl
  exact kwschkIdx_of_split (fn := Data.core19) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kwschkIdx_20 : kwschkIdx 20 = true := by
  have hb : blockB (kwslookJ 20) (kwsomLookJ 20) false [] Data.core20.params Data.core20.name ([], []) Data.core20.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core20.body)]
    rw [blockB_dropE _ _ _ 0 94 94 kwssplit_20_0.1 rfl kwssplit_20_0.2.2,
      ← blockR_eq ((Data.core20.body.drop 0).take 94), kwssplit_20_0.2.1]
    rw [← blockR_eq (Data.core20.body.drop 94), kwssplit_20_94]
    rfl
  exact kwschkIdx_of_split (fn := Data.core20) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kwschkIdx_all : ∀ j < 947, kwschkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 19
  · subst h1000; exact kwschkIdx_19
  by_cases h1001 : j = 20
  · subst h1001; exact kwschkIdx_20
  by_cases h0 : j < 11
  · exact kwsstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kwsstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 19
  · exact kwsstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 51
  · exact kwsstaticRange_21.get (by omega) (by omega)
  by_cases h4 : j < 81
  · exact kwsstaticRange_51.get (by omega) (by omega)
  by_cases h5 : j < 111
  · exact kwsstaticRange_81.get (by omega) (by omega)
  by_cases h6 : j < 141
  · exact kwsstaticRange_111.get (by omega) (by omega)
  by_cases h7 : j < 171
  · exact kwsstaticRange_141.get (by omega) (by omega)
  by_cases h8 : j < 201
  · exact kwsstaticRange_171.get (by omega) (by omega)
  by_cases h9 : j < 231
  · exact kwsstaticRange_201.get (by omega) (by omega)
  by_cases h10 : j < 261
  · exact kwsstaticRange_231.get (by omega) (by omega)
  by_cases h11 : j < 291
  · exact kwsstaticRange_261.get (by omega) (by omega)
  by_cases h12 : j < 310
  · exact kwsstaticRange_291.get (by omega) (by omega)
  by_cases h13 : j < 317
  · exact kwsstaticRange_310.get (by omega) (by omega)
  by_cases h14 : j < 324
  · exact kwsstaticRange_317.get (by omega) (by omega)
  by_cases h15 : j < 354
  · exact kwsstaticRange_324.get (by omega) (by omega)
  by_cases h16 : j < 384
  · exact kwsstaticRange_354.get (by omega) (by omega)
  by_cases h17 : j < 414
  · exact kwsstaticRange_384.get (by omega) (by omega)
  by_cases h18 : j < 444
  · exact kwsstaticRange_414.get (by omega) (by omega)
  by_cases h19 : j < 474
  · exact kwsstaticRange_444.get (by omega) (by omega)
  by_cases h20 : j < 504
  · exact kwsstaticRange_474.get (by omega) (by omega)
  by_cases h21 : j < 534
  · exact kwsstaticRange_504.get (by omega) (by omega)
  by_cases h22 : j < 564
  · exact kwsstaticRange_534.get (by omega) (by omega)
  by_cases h23 : j < 594
  · exact kwsstaticRange_564.get (by omega) (by omega)
  by_cases h24 : j < 624
  · exact kwsstaticRange_594.get (by omega) (by omega)
  by_cases h25 : j < 654
  · exact kwsstaticRange_624.get (by omega) (by omega)
  by_cases h26 : j < 684
  · exact kwsstaticRange_654.get (by omega) (by omega)
  by_cases h27 : j < 714
  · exact kwsstaticRange_684.get (by omega) (by omega)
  by_cases h28 : j < 744
  · exact kwsstaticRange_714.get (by omega) (by omega)
  by_cases h29 : j < 774
  · exact kwsstaticRange_744.get (by omega) (by omega)
  by_cases h30 : j < 804
  · exact kwsstaticRange_774.get (by omega) (by omega)
  by_cases h31 : j < 834
  · exact kwsstaticRange_804.get (by omega) (by omega)
  by_cases h32 : j < 864
  · exact kwsstaticRange_834.get (by omega) (by omega)
  by_cases h33 : j < 894
  · exact kwsstaticRange_864.get (by omega) (by omega)
  by_cases h34 : j < 924
  · exact kwsstaticRange_894.get (by omega) (by omega)
  exact kwsstaticRange_924.get (by omega) (by omega)

end
end LeanVM.Guest
