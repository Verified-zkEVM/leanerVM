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

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwdchkIdx_19 : kwdchkIdx 19 = true := by
  have hb : blockB (kwdlookJ 19) (kwdomLookJ 19) false [] Data.core19.params Data.core19.name ([], []) Data.core19.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core19.body)]
    rw [blockB_dropE _ _ _ 0 558 558 kwdsplit_19_0.1 rfl kwdsplit_19_0.2.2,
      ← blockR_eq ((Data.core19.body.drop 0).take 558), kwdsplit_19_0.2.1]
    rw [← blockR_eq (Data.core19.body.drop 558), kwdsplit_19_558]
    rfl
  exact kwdchkIdx_of_split (fn := Data.core19) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kwdchkIdx_20 : kwdchkIdx 20 = true := by
  have hb : blockB (kwdlookJ 20) (kwdomLookJ 20) false [] Data.core20.params Data.core20.name ([], []) Data.core20.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core20.body)]
    rw [blockB_dropE _ _ _ 0 94 94 kwdsplit_20_0.1 rfl kwdsplit_20_0.2.2,
      ← blockR_eq ((Data.core20.body.drop 0).take 94), kwdsplit_20_0.2.1]
    rw [← blockR_eq (Data.core20.body.drop 94), kwdsplit_20_94]
    rfl
  exact kwdchkIdx_of_split (fn := Data.core20) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kwdchkIdx_all : ∀ j < 947, kwdchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 19
  · subst h1000; exact kwdchkIdx_19
  by_cases h1001 : j = 20
  · subst h1001; exact kwdchkIdx_20
  by_cases h0 : j < 11
  · exact kwdstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kwdstaticRange_11.get (by omega) (by omega)
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
  by_cases h12 : j < 310
  · exact kwdstaticRange_291.get (by omega) (by omega)
  by_cases h13 : j < 317
  · exact kwdstaticRange_310.get (by omega) (by omega)
  by_cases h14 : j < 324
  · exact kwdstaticRange_317.get (by omega) (by omega)
  by_cases h15 : j < 354
  · exact kwdstaticRange_324.get (by omega) (by omega)
  by_cases h16 : j < 384
  · exact kwdstaticRange_354.get (by omega) (by omega)
  by_cases h17 : j < 414
  · exact kwdstaticRange_384.get (by omega) (by omega)
  by_cases h18 : j < 444
  · exact kwdstaticRange_414.get (by omega) (by omega)
  by_cases h19 : j < 474
  · exact kwdstaticRange_444.get (by omega) (by omega)
  by_cases h20 : j < 504
  · exact kwdstaticRange_474.get (by omega) (by omega)
  by_cases h21 : j < 534
  · exact kwdstaticRange_504.get (by omega) (by omega)
  by_cases h22 : j < 564
  · exact kwdstaticRange_534.get (by omega) (by omega)
  by_cases h23 : j < 594
  · exact kwdstaticRange_564.get (by omega) (by omega)
  by_cases h24 : j < 624
  · exact kwdstaticRange_594.get (by omega) (by omega)
  by_cases h25 : j < 654
  · exact kwdstaticRange_624.get (by omega) (by omega)
  by_cases h26 : j < 684
  · exact kwdstaticRange_654.get (by omega) (by omega)
  by_cases h27 : j < 714
  · exact kwdstaticRange_684.get (by omega) (by omega)
  by_cases h28 : j < 744
  · exact kwdstaticRange_714.get (by omega) (by omega)
  by_cases h29 : j < 774
  · exact kwdstaticRange_744.get (by omega) (by omega)
  by_cases h30 : j < 804
  · exact kwdstaticRange_774.get (by omega) (by omega)
  by_cases h31 : j < 834
  · exact kwdstaticRange_804.get (by omega) (by omega)
  by_cases h32 : j < 864
  · exact kwdstaticRange_834.get (by omega) (by omega)
  by_cases h33 : j < 894
  · exact kwdstaticRange_864.get (by omega) (by omega)
  by_cases h34 : j < 924
  · exact kwdstaticRange_894.get (by omega) (by omega)
  exact kwdstaticRange_924.get (by omega) (by omega)

end
end LeanVM.Guest
