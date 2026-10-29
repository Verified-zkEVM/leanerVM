/-
  LeanVM.Guest.Memory.GuestCntJ.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntJ.Part00
public import LeanVM.Guest.Memory.GuestCntJ.Part01
public import LeanVM.Guest.Memory.GuestCntJ.Part02
public import LeanVM.Guest.Memory.GuestCntJ.Part03
public import LeanVM.Guest.Memory.GuestCntJ.Part04
public import LeanVM.Guest.Memory.GuestCntJ.Part05
public import LeanVM.Guest.Memory.GuestCntJ.Part06
public import LeanVM.Guest.Memory.GuestCntJ.Part07

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwjchkIdx_19 : kwjchkIdx 19 = true := by
  have hb : blockB (kwjlookJ 19) (kwjomLookJ 19) false [] Data.core19.params Data.core19.name ([], []) Data.core19.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core19.body)]
    rw [blockB_dropE _ _ _ 0 533 533 kwjsplit_19_0.1 rfl kwjsplit_19_0.2.2,
      ← blockR_eq ((Data.core19.body.drop 0).take 533), kwjsplit_19_0.2.1]
    rw [← blockR_eq (Data.core19.body.drop 533), kwjsplit_19_533]
    rfl
  exact kwjchkIdx_of_split (fn := Data.core19) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kwjchkIdx_20 : kwjchkIdx 20 = true := by
  have hb : blockB (kwjlookJ 20) (kwjomLookJ 20) false [] Data.core20.params Data.core20.name ([], []) Data.core20.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core20.body)]
    rw [blockB_dropE _ _ _ 0 246 246 kwjsplit_20_0.1 rfl kwjsplit_20_0.2.2,
      ← blockR_eq ((Data.core20.body.drop 0).take 246), kwjsplit_20_0.2.1]
    rw [blockB_dropE _ _ _ 246 63 309 kwjsplit_20_246.1 rfl kwjsplit_20_246.2.2,
      ← blockR_eq ((Data.core20.body.drop 246).take 63), kwjsplit_20_246.2.1]
    rw [blockB_dropE _ _ _ 309 48 357 kwjsplit_20_309.1 rfl kwjsplit_20_309.2.2,
      ← blockR_eq ((Data.core20.body.drop 309).take 48), kwjsplit_20_309.2.1]
    rw [blockB_dropE _ _ _ 357 63 420 kwjsplit_20_357.1 rfl kwjsplit_20_357.2.2,
      ← blockR_eq ((Data.core20.body.drop 357).take 63), kwjsplit_20_357.2.1]
    rw [blockB_dropE _ _ _ 420 48 468 kwjsplit_20_420.1 rfl kwjsplit_20_420.2.2,
      ← blockR_eq ((Data.core20.body.drop 420).take 48), kwjsplit_20_420.2.1]
    rw [blockB_dropE _ _ _ 468 110 578 kwjsplit_20_468.1 rfl kwjsplit_20_468.2.2,
      ← blockR_eq ((Data.core20.body.drop 468).take 110), kwjsplit_20_468.2.1]
    rw [← blockR_eq (Data.core20.body.drop 578), kwjsplit_20_578]
    rfl
  exact kwjchkIdx_of_split (fn := Data.core20) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kwjchkIdx_all : ∀ j < 878, kwjchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 19
  · subst h1000; exact kwjchkIdx_19
  by_cases h1001 : j = 20
  · subst h1001; exact kwjchkIdx_20
  by_cases h0 : j < 10
  · exact kwjstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kwjstaticRange_10.get (by omega) (by omega)
  by_cases h2 : j < 19
  · exact kwjstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 51
  · exact kwjstaticRange_21.get (by omega) (by omega)
  by_cases h4 : j < 81
  · exact kwjstaticRange_51.get (by omega) (by omega)
  by_cases h5 : j < 111
  · exact kwjstaticRange_81.get (by omega) (by omega)
  by_cases h6 : j < 141
  · exact kwjstaticRange_111.get (by omega) (by omega)
  by_cases h7 : j < 171
  · exact kwjstaticRange_141.get (by omega) (by omega)
  by_cases h8 : j < 201
  · exact kwjstaticRange_171.get (by omega) (by omega)
  by_cases h9 : j < 231
  · exact kwjstaticRange_201.get (by omega) (by omega)
  by_cases h10 : j < 261
  · exact kwjstaticRange_231.get (by omega) (by omega)
  by_cases h11 : j < 291
  · exact kwjstaticRange_261.get (by omega) (by omega)
  by_cases h12 : j < 299
  · exact kwjstaticRange_291.get (by omega) (by omega)
  by_cases h13 : j < 306
  · exact kwjstaticRange_299.get (by omega) (by omega)
  by_cases h14 : j < 313
  · exact kwjstaticRange_306.get (by omega) (by omega)
  by_cases h15 : j < 343
  · exact kwjstaticRange_313.get (by omega) (by omega)
  by_cases h16 : j < 373
  · exact kwjstaticRange_343.get (by omega) (by omega)
  by_cases h17 : j < 403
  · exact kwjstaticRange_373.get (by omega) (by omega)
  by_cases h18 : j < 433
  · exact kwjstaticRange_403.get (by omega) (by omega)
  by_cases h19 : j < 463
  · exact kwjstaticRange_433.get (by omega) (by omega)
  by_cases h20 : j < 493
  · exact kwjstaticRange_463.get (by omega) (by omega)
  by_cases h21 : j < 523
  · exact kwjstaticRange_493.get (by omega) (by omega)
  by_cases h22 : j < 553
  · exact kwjstaticRange_523.get (by omega) (by omega)
  by_cases h23 : j < 583
  · exact kwjstaticRange_553.get (by omega) (by omega)
  by_cases h24 : j < 613
  · exact kwjstaticRange_583.get (by omega) (by omega)
  by_cases h25 : j < 643
  · exact kwjstaticRange_613.get (by omega) (by omega)
  by_cases h26 : j < 673
  · exact kwjstaticRange_643.get (by omega) (by omega)
  by_cases h27 : j < 703
  · exact kwjstaticRange_673.get (by omega) (by omega)
  by_cases h28 : j < 733
  · exact kwjstaticRange_703.get (by omega) (by omega)
  by_cases h29 : j < 763
  · exact kwjstaticRange_733.get (by omega) (by omega)
  by_cases h30 : j < 793
  · exact kwjstaticRange_763.get (by omega) (by omega)
  by_cases h31 : j < 823
  · exact kwjstaticRange_793.get (by omega) (by omega)
  by_cases h32 : j < 853
  · exact kwjstaticRange_823.get (by omega) (by omega)
  exact kwjstaticRange_853.get (by omega) (by omega)

end
end LeanVM.Guest
