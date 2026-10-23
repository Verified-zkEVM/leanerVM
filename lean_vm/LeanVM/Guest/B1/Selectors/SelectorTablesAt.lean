/-
  LeanVM.Guest.B1.Selectors.SelectorTablesAt

  `selector_tables` is complete in the uniform placed form (`CompleteAtD`): its two buffers at the
  bump allocator's positions, returned.
-/

module

public import LeanVM.Guest.B1.Selectors.SelectorTablesComplete
public import LeanVM.Guest.B1.Tables.FlatAt

/-!
# `selector_tables`, placed (TRIAGE G #69)

At frame pointer `fp` the buffers lie at `ese = fp + fs "selector_tables"` (`210` words) and
`esg = ese + 210` (`112`); the function returns their pointers, and its returned layout is
`stOwn` there (`stOut`). `selector_tables_completeAt`: `CompleteAtD` on the point's runs
`stLin`, by `completeAt_flatOutD` on the honest valuation `stVal` (`st_sholds`), every load in
the point's runs or the buffers. `st_out_tabs`: the returned buffers hold the opening point's
tables when they lie apart from the point's runs.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- What `selector_tables` returns: its buffers' pointers, and the buffers holding `stOwn`. -/
def stOut (ept ept1 : ℕ) (p p1 : List E) : List E → Layout → Prop := fun rets L =>
  ∃ ese esg : ℕ, rets = [ofK (gpow ese), ofK (gpow esg)] ∧ L = stOwn ept ept1 ese esg p p1

theorem stVal_param (ept ept1 ese esg : ℕ) (p p1 : List E) :
    stVal ept ept1 ese esg p p1 (.n 0) = ofK (gpow ept) ∧
      stVal ept ept1 ese esg p p1 (.n 1) = ofK (gpow ept1) :=
  ⟨ev_params _ _ (l := [ofK (gpow ept), ofK (gpow ept1)]) st_chk (by norm_num),
    ev_params _ _ (l := [ofK (gpow ept), ofK (gpow ept1)]) st_chk (by norm_num)⟩

theorem stVal_bufs (ept ept1 ese esg : ℕ) (p p1 : List E) :
    stVal ept ept1 ese esg p p1 (.n 2) = ofK (gpow ese) ∧
      stVal ept ept1 ese esg p p1 (.n 3) = ofK (gpow esg) ∧
      stVal ept ept1 ese esg p p1 (.n 368) = ofK (gpow ese) ∧
      stVal ept ept1 ese esg p p1 (.n 369) = ofK (gpow esg) := by
  have hg : ∀ s ∈ stPre, GoodS (layRd (stLin ept ept1 p p1)) (storesOf 2 stPre) (stW ese esg)
      (stVal ept ept1 ese esg p p1) s :=
    (ev_spec (layRd (stLin ept ept1 p p1)) (stW ese esg) stPre
      [ofK (gpow ept), ofK (gpow ept1)] st_chk).2.2
  have e2 : stVal ept ept1 ese esg p p1 (.n 2) = ofK (gpow ese) := by
    simpa [GoodS, Good, stW] using hg _ st_alloc_mem.1
  have e3 : stVal ept ept1 ese esg p p1 (.n 3) = ofK (gpow esg) := by
    simpa [GoodS, Good, stW] using hg _ st_alloc_mem.2
  have c1 := hg _ (show Stmt.atom (.copy (.n 368) (.n 2)) ∈ stPre by simp [stPre])
  have c2 := hg _ (show Stmt.atom (.copy (.n 369) (.n 3)) ∈ stPre by simp [stPre])
  simp only [GoodS, Good] at c1 c2
  exact ⟨e2, e3, by rw [c1, e2], by rw [c2, e3]⟩

theorem st_flat : stPre.all Stmt.flat = true := by decide +kernel

theorem st_addrs : stPre.filterMap Main.Stmt.addrS = [] := by decide +kernel

theorem st_allocs : stPre.filterMap Main.Stmt.allocSz = [(.n 2, .inl 210), (.n 3, .inl 112)] := by
  decide +kernel

theorem st_not_loop : coreProgram.loop "selector_tables" = false := by decide +kernel

set_option maxRecDepth 10000 in
/-- **`selector_tables` is complete, placed**: on the point's runs, at every frame pointer, its
buffers at the bump allocator's positions, returned. -/
theorem selector_tables_completeAt (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (ept ept1 : ℕ) (p p1 : List E) (hl : p.length = 28) (hl1 : p1.length = 28) :
    CompleteAtD fs cert k "selector_tables" (stLin ept ept1 p p1) [ofK (gpow ept), ofK (gpow ept1)]
      (stOut ept ept1 p p1) := by
  obtain ⟨fn, hf, hp, hb⟩ := stFound
  set f := "selector_tables"
  have hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s)
      [stEqWords (stVal ept ept1 (fp + fs f) (fp + fs f + 210) p p1), stGWords] [210, 112] := by
    intro fp; simp [stEqWords, stGWords]
  have hbuf : ∀ fp, bufL (fp + fs f) [210, 112]
      [stEqWords (stVal ept ept1 (fp + fs f) (fp + fs f + 210) p p1), stGWords] =
        stOwn ept ept1 (fp + fs f) (fp + fs f + 210) p p1 := by
    intro fp; simp [bufL, bases, stOwn]
  refine completeAt_flatOutD (fs := fs) (cert := cert) hf st_not_loop k (stLin ept ept1 p p1) _
    (fun fp ↦ [ofK (gpow (fp + fs f)), ofK (gpow (fp + fs f + 210))]) _ hb st_flat st_addrs
    [210, 112] (fun fp ↦ [stEqWords (stVal ept ept1 (fp + fs f) (fp + fs f + 210) p p1), stGWords])
    hown (fun fp ↦ ⟨_, _, rfl, hbuf fp⟩) (fun _ ↦ []) (fun _ _ h ↦ absurd h (by simp))
    (fun _ _ h ↦ absurd h (by simp)) (fun _ _ _ _ _ h ↦ absurd h (by simp)) ?_
  intro fp outs ho rd _ hB hLin
  obtain ⟨e0, e1⟩ := stVal_param ept ept1 (fp + fs f) (fp + fs f + 210) p p1
  obtain ⟨e2, e3, e368, e369⟩ := stVal_bufs ept ept1 (fp + fs f) (fp + fs f + 210) p p1
  rw [hbuf fp] at hB
  have hm : MemLay rd (stOwn ept ept1 (fp + fs f) (fp + fs f + 210) p p1 ++ stLin ept ept1 p p1) :=
    memLay_append.mpr ⟨hB, hLin⟩
  have hat := st_sholds ept ept1 (fp + fs f) (fp + fs f + 210) p p1 hl hl1 rd hm
  have hkind : ∀ s ∈ stPre, stKind s = true := fun s hs ↦ List.all_eq_true.mp st_kinds s hs
  have hatom : ∀ s ∈ stPre, ∃ a, s = .atom a := by
    intro s hs
    rcases stKind_cases (hkind s hs) with ⟨_, h⟩ | ⟨_, _, h | h, _⟩ | ⟨_, h, _⟩ |
      ⟨_, h, _⟩ | ⟨_, h, _⟩ <;> exact ⟨_, h⟩
  refine ⟨stVal ept ept1 (fp + fs f) (fp + fs f + 210) p p1, by rw [hp]; simp only [List.map_cons,
    List.map_nil, e0, e1], fun s hs ↦ ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := hatom s hs
    exact True.intro
  · rw [hb]
    refine holdsList_straight stPre _ _ _ hat ?_
    simp [e368, e369]
  · rw [st_allocs]; rfl
  · rw [st_allocs]; simp [bases, e2, e3]
  · have : stPre.filterMap (Stmt.callSF (stVal ept ept1 (fp + fs f) (fp + fs f + 210) p p1)) = [] := by
      rw [List.filterMap_eq_nil_iff]
      intro s hs
      obtain ⟨a, rfl⟩ := hatom s hs
      rfl
    rw [this]
    match outs, ho with
    | [], _ => exact True.intro
  · rw [flatMap_loadsEv _ stPre (by decide +kernel)]
    intro q hq
    obtain ⟨s, hs, hq⟩ := List.mem_filterMap.mp hq
    rcases stKind_cases (hkind s hs) with ⟨_, rfl⟩ | ⟨d, o, h | h, ho⟩ | ⟨o, rfl, ho⟩ |
      ⟨o, rfl, ho⟩ | ⟨a, rfl, ha⟩
    · simp [Stmt.loadS] at hq
    · subst h; simp only [Stmt.loadS, Option.some.injEq] at hq; subst hq
      exact ⟨ept + o, by rw [e0, tb_addr_ofK], Or.inl ⟨(ept, p), by simp [stLin], by omega,
        by simp [hl]; omega⟩⟩
    · subst h; simp only [Stmt.loadS, Option.some.injEq] at hq; subst hq
      exact ⟨ept1 + o, by rw [e1, tb_addr_ofK], Or.inl ⟨(ept1, p1), by simp [stLin], by omega,
        by simp [hl1]; omega⟩⟩
    · simp only [Stmt.loadS, Option.some.injEq] at hq; subst hq
      refine ⟨fp + fs f + o, by rw [e2, tb_addr_ofK], Or.inr ?_⟩
      rw [hbuf fp]
      exact ⟨_, List.mem_cons_self, by omega, by simp [stEqWords]; omega⟩
    · simp only [Stmt.loadS, Option.some.injEq] at hq; subst hq
      refine ⟨fp + fs f + 210 + o, by rw [e3, tb_addr_ofK], Or.inr ?_⟩
      rw [hbuf fp]
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by omega, by simp [stGWords]; omega⟩
    · cases a <;> simp [Stmt.loadS, pureB] at hq ha

/-- **The returned buffers hold the opening point's tables**, on any memory holding them, when
they and the point's runs lie apart below the order of `g`. -/
theorem st_out_tabs {ept ept1 : ℕ} {p p1 : List E} (hl : p.length = 28) (hl1 : p1.length = 28)
    {rets : List E} {L : Layout} (h : stOut ept ept1 p p1 rets L)
    (hd : DisjLay (L ++ stLin ept ept1 p p1)) (hlo : LowLay (L ++ stLin ept ept1 p p1))
    {rd : Reader} (hm : MemL rd L) :
    SelTabsAt rd (rets.getD 0 0) (rets.getD 1 0) p p1 := by
  obtain ⟨ese, esg, rfl, rfl⟩ := h
  exact st_tabs ept ept1 ese esg p p1 hl hl1 hd hlo rd hm

end
end LeanVM.Guest.B1.Tables
