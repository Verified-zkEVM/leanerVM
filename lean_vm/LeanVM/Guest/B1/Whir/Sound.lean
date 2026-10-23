/-
  LeanVM.Guest.B1.Whir.Sound

  `open_stacked` is sound at every candidate.
-/

module

public import LeanVM.Guest.B1.Whir.FactsAll
public import LeanVM.Guest.B1.Whir.DataAll
public import LeanVM.Guest.B1.Whir.Names
public import LeanVM.Guest.B1.Bits.AssertCanonical
public import LeanVM.Guest.B1.Bits.Grind
public import LeanVM.Guest.B1.Bits.QueryBits
public import LeanVM.Guest.B1.Merkle.CapAll
public import LeanVM.Guest.B1.Opening.Fold
public import LeanVM.Guest.B1.Opening.OodPoint
public import LeanVM.Guest.B1.Opening.FinalMessage
public import LeanVM.Guest.B1.Opening.RowWeights
public import LeanVM.Guest.B1.Opening.QueriesAll
public import LeanVM.Guest.B1.Eq.FoldFinal

/-!
# `open_stacked`, soundly (TRIAGE G #42)

`open_stacked_sound_holds : open_stacked_sound_Spec`: for every stack log `22 ≤ μ ≤ 28` and rate
`1 ≤ r ≤ 4`, a call of `open_stacked__L{candidate μ r}` establishes `OpenOut`: the words it reads
and the openings run the Spec's `whirOpen μ r target` (the stacked WHIR opening up to its
terminal check, `verifyWhir_split`), and it returns the terminal's claim, point, glued weight
and residual. From the candidate's core IR (`osData_all`), its facts (`candB_all`), B1-a's
callees (`*_holds`) and `open_generic`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier

@[expose] public section

/-- **A level's callees**, from B1-a's theorems and the names' facts. -/
theorem lvCallees_of {rd : Reader} {c : OsCfg} {lvl : ℕ} {lv : OsLv}
    (hsq : FnIs (c.sqLoop lvl) (osParams 5) (sqLoopBody lv (c.sqLoop lvl)))
    (hn : NamesOk c lvl lv) : LvCallees rd c lvl lv := by
  obtain ⟨hood, hfm, hgr, hdec, hcap, hq, hrw, hfo⟩ := hn
  refine ⟨fun a r h ↦ (opening_fold_holds rd a r).mp h,
    fun a r h ↦ (assert_canonical_holds rd a r).mp h,
    fun hnf a r h ↦ (opening_ood_point_holds _ (hood hnf) rd a r).mp h,
    fun a r h ↦ (opening_final_message_holds _ hfm rd a r).mp h,
    fun a r h ↦ by rw [hgr] at h; exact (grind_check_holds rd a r).mp h, hsq,
    fun a r h ↦ (decode_query_bits_all_holds _ hdec rd a r).mp h, fun a r h ↦ ?_,
    fun a r h ↦ (verify_merkle_cap_holds _ hcap rd a r).mp h,
    opening_queries_all_holds _ hq⟩
  rw [hrw] at h
  by_cases h0 : lvl = 0
  · simp only [h0, ↓reduceIte] at h hfo ⊢
    rw [hfo]; exact opening_row_weights_holds.1 rd a r |>.mp h
  · simp only [h0, ↓reduceIte] at h hfo ⊢
    rw [hfo]; exact opening_row_weights_holds.2 rd a r |>.mp h

theorem calleesOk_of {rd : Reader} {c : OsCfg} : ∀ (lvs : List OsLv) (lvl : ℕ),
    (∀ i (hi : i < lvs.length), LvCallees rd c (lvl + i) lvs[i]) → CalleesOk rd c lvl lvs
  | [], _, _ => trivial
  | lv :: rest, lvl, h => ⟨h 0 (by simp), calleesOk_of rest (lvl + 1) fun i hi ↦ by
      have := h (i + 1) (by simp; omega)
      rwa [show lvl + (i + 1) = lvl + 1 + i by ring] at this⟩

theorem openName_eq (μ r : ℕ) (h : candidate μ r < 28) :
    openName μ r = "open_stacked__L" ++ natStr (candidate μ r) := by
  rw [openName, openNames, natStr_eq, List.getD_eq_getElem _ _ (by simpa using h)]
  simp

theorem osCfg_levels_getElem (m i : ℕ) (h : i < (osCfg m).levels.length) :
    (osCfg m).levels[i] = osLv m i := by
  simp [osCfg]

/-- **`open_stacked` is sound at every candidate.** -/
theorem open_stacked_sound_holds : open_stacked_sound_Spec := by
  intro rd μ r h1 h2 h3 h4 root fs target root0 root1 cur rets hfs hroot hrel
  have hm : candidate μ r < 28 := by unfold candidate; omega
  obtain ⟨cfg, hF, hnames, hffm⟩ := candB_sound (candB_all μ r h1 h2 h3 h4)
  have hdata := osData_all _ hm
  rw [openName_eq μ r hm] at hrel
  refine open_generic hdata.1 (fun lvl h ↦ ?_) hF ?_ (fun a r h ↦ (opening_fold_holds rd a r).mp h)
    (fun a r h ↦ (fold_final_msg_holds _ hffm rd a r).mp h) hfs hroot hrel
  · rw [osCfg_levels_getElem _ _ h]; exact (hdata.2 lvl h).2
  · refine calleesOk_of _ 0 fun i hi ↦ ?_
    rw [Nat.zero_add, osCfg_levels_getElem _ _ hi]
    have hn := hnames i hi
    rw [lv_getD hi, osCfg_levels_getElem _ _ hi] at hn
    exact lvCallees_of (hdata.2 i hi).1 hn

end
end LeanVM.Guest.B1.Whir
