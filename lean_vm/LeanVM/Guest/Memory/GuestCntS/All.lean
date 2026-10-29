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
public import LeanVM.Guest.Memory.GuestCntS.Part07

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwschkIdx_19 : kwschkIdx 19 = true := by
  have hb : blockB (kwslookJ 19) (kwsomLookJ 19) false [] Data.core19.params Data.core19.name ([], []) Data.core19.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core19.body)]
    rw [blockB_dropE _ _ _ 0 533 533 kwssplit_19_0.1 rfl kwssplit_19_0.2.2,
      ← blockR_eq ((Data.core19.body.drop 0).take 533), kwssplit_19_0.2.1]
    rw [← blockR_eq (Data.core19.body.drop 533), kwssplit_19_533]
    rfl
  exact kwschkIdx_of_split (fn := Data.core19) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kwschkIdx_20 : kwschkIdx 20 = true := by
  have hb : blockB (kwslookJ 20) (kwsomLookJ 20) false [] Data.core20.params Data.core20.name ([], []) Data.core20.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core20.body)]
    rw [blockB_dropE _ _ _ 0 246 246 kwssplit_20_0.1 rfl kwssplit_20_0.2.2,
      ← blockR_eq ((Data.core20.body.drop 0).take 246), kwssplit_20_0.2.1]
    rw [blockB_dropE _ _ _ 246 63 309 kwssplit_20_246.1 rfl kwssplit_20_246.2.2,
      ← blockR_eq ((Data.core20.body.drop 246).take 63), kwssplit_20_246.2.1]
    rw [blockB_dropE _ _ _ 309 48 357 kwssplit_20_309.1 rfl kwssplit_20_309.2.2,
      ← blockR_eq ((Data.core20.body.drop 309).take 48), kwssplit_20_309.2.1]
    rw [blockB_dropE _ _ _ 357 63 420 kwssplit_20_357.1 rfl kwssplit_20_357.2.2,
      ← blockR_eq ((Data.core20.body.drop 357).take 63), kwssplit_20_357.2.1]
    rw [blockB_dropE _ _ _ 420 48 468 kwssplit_20_420.1 rfl kwssplit_20_420.2.2,
      ← blockR_eq ((Data.core20.body.drop 420).take 48), kwssplit_20_420.2.1]
    rw [blockB_dropE _ _ _ 468 110 578 kwssplit_20_468.1 rfl kwssplit_20_468.2.2,
      ← blockR_eq ((Data.core20.body.drop 468).take 110), kwssplit_20_468.2.1]
    rw [← blockR_eq (Data.core20.body.drop 578), kwssplit_20_578]
    rfl
  exact kwschkIdx_of_split (fn := Data.core20) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kwschkIdx_all : ∀ j < 878, kwschkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 19
  · subst h1000; exact kwschkIdx_19
  by_cases h1001 : j = 20
  · subst h1001; exact kwschkIdx_20
  by_cases h0 : j < 10
  · exact kwsstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kwsstaticRange_10.get (by omega) (by omega)
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
  by_cases h12 : j < 299
  · exact kwsstaticRange_291.get (by omega) (by omega)
  by_cases h13 : j < 306
  · exact kwsstaticRange_299.get (by omega) (by omega)
  by_cases h14 : j < 313
  · exact kwsstaticRange_306.get (by omega) (by omega)
  by_cases h15 : j < 343
  · exact kwsstaticRange_313.get (by omega) (by omega)
  by_cases h16 : j < 373
  · exact kwsstaticRange_343.get (by omega) (by omega)
  by_cases h17 : j < 403
  · exact kwsstaticRange_373.get (by omega) (by omega)
  by_cases h18 : j < 433
  · exact kwsstaticRange_403.get (by omega) (by omega)
  by_cases h19 : j < 463
  · exact kwsstaticRange_433.get (by omega) (by omega)
  by_cases h20 : j < 493
  · exact kwsstaticRange_463.get (by omega) (by omega)
  by_cases h21 : j < 523
  · exact kwsstaticRange_493.get (by omega) (by omega)
  by_cases h22 : j < 553
  · exact kwsstaticRange_523.get (by omega) (by omega)
  by_cases h23 : j < 583
  · exact kwsstaticRange_553.get (by omega) (by omega)
  by_cases h24 : j < 613
  · exact kwsstaticRange_583.get (by omega) (by omega)
  by_cases h25 : j < 643
  · exact kwsstaticRange_613.get (by omega) (by omega)
  by_cases h26 : j < 673
  · exact kwsstaticRange_643.get (by omega) (by omega)
  by_cases h27 : j < 703
  · exact kwsstaticRange_673.get (by omega) (by omega)
  by_cases h28 : j < 733
  · exact kwsstaticRange_703.get (by omega) (by omega)
  by_cases h29 : j < 763
  · exact kwsstaticRange_733.get (by omega) (by omega)
  by_cases h30 : j < 793
  · exact kwsstaticRange_763.get (by omega) (by omega)
  by_cases h31 : j < 823
  · exact kwsstaticRange_793.get (by omega) (by omega)
  by_cases h32 : j < 853
  · exact kwsstaticRange_823.get (by omega) (by omega)
  exact kwsstaticRange_853.get (by omega) (by omega)

end
end LeanVM.Guest
