/-
  LeanVM.Guest.B1.Selectors.SelectorTablesComplete

  `selector_tables`, completely: on the honest valuation (the body evaluated on the point's
  words, its two buffers at any bases), every statement holds on a memory holding the point and
  the buffers' words, and the buffers hold the opening point's tables.
-/

module

public import LeanVM.Guest.B1.Selectors.SelectorTables
public import LeanVM.Guest.B1.Selectors.LayoutBasic

/-!
# `selector_tables`, completely (TRIAGE G #69)

The point and its complements are the runs `(ept, p)`, `(ept1, p1)` (`stLin`); the buffers'
bases are `ese` (`210` words) and `esg` (`112`). The honest valuation `stVal` is the body
evaluated on `layRd` of the point (`Fwd.ev`, the two allocations answered by the bases). Its
buffers' words (`stOwn`): the eq buffer's are the stored values, the `g` buffer's the baked shares.

`st_holds`: on every memory holding `stOwn ++ stLin`, the relation holds with the buffers'
pointers as returns; `st_tabs`: the buffers then hold the opening point's tables (by soundness).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The point's runs. -/
def stLin (ept ept1 : ℕ) (p p1 : List E) : TLay := [(ept, p), (ept1, p1)]

/-- The allocations' answers: the eq buffer at `ese`, the `g` buffer at `esg`. -/
def stW (ese esg : ℕ) : ℕ → E := fun i => if i = 2 then ofK (gpow ese) else ofK (gpow esg)

/-- **The honest valuation.** -/
noncomputable def stVal (ept ept1 ese esg : ℕ) (p p1 : List E) : Val :=
  B1.Val.ofArgs (ev (layRd (stLin ept ept1 p p1)) (stW ese esg) [ofK (gpow ept), ofK (gpow ept1)] stPre)

/-- The eq buffer's words: the stored values. -/
def stEqWords (σ : Val) : List E := (List.range 210).map fun k => σ (.n (stEq (k / 30) (k % 30)))

/-- The `g` buffer's words: the baked shares. -/
def stGWords : List E := (List.range 112).map fun k => word (stShare (k / 16) (k % 16)) 0 0

/-- The buffers' runs. -/
noncomputable def stOwn (ept ept1 ese esg : ℕ) (p p1 : List E) : TLay :=
  [(ese, stEqWords (stVal ept ept1 ese esg p p1)), (esg, stGWords)]

theorem st_chk : chk 2 stPre = some 370 := by decide +kernel

/-- What a statement of the body is: a pure atom, a hint, a load of the point, or a store. -/
def stKind : Stmt → Bool
  | .atom (.hint _) => true
  | .atom (.load (.n _) (.n 0) o) | .atom (.load (.n _) (.n 1) o) => decide (o < 28)
  | .atom (.load (.n d) (.n 2) o) => decide (o < 210) && decide (d = stEq (o / 30) (o % 30))
  | .atom (.load (.n d) (.n 3) o) => decide (o < 112) && decide (d = stB (o / 16) + 36 + o % 16)
  | .atom a => pureB a
  | _ => false

theorem st_kinds : stPre.all stKind = true := by decide +kernel

/-- The stores of the body are the buffers' loads. -/
def stStoreOk : Atom → Bool
  | .load (.n _) (.n 2) _ | .load (.n _) (.n 3) _ => true
  | _ => false

theorem st_stores : (storesOf 2 stPre).all stStoreOk = true := by decide +kernel

theorem st_const_mem {j u : ℕ} (hj : j < 7) (hu : u < 16) :
    Stmt.atom (.const (.n (stB j + 36 + u)) (word (stShare j u) 0 0)) ∈ stPre := by
  unfold stPre
  apply List.mem_append_left
  apply List.mem_append_right
  rw [List.mem_flatten]
  refine ⟨stNib j, List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩, ?_⟩
  unfold stNib
  apply List.mem_append_right
  rw [List.mem_flatten]
  exact ⟨_, List.mem_map.mpr ⟨u, List.mem_range.mpr hu, rfl⟩, by simp⟩

theorem st_alloc_mem : Stmt.atom (.hint (.alloc (.n 2) 210)) ∈ stPre ∧
    Stmt.atom (.hint (.alloc (.n 3) 112)) ∈ stPre := by
  unfold stPre; simp

/-- The kinds of the body's statements. -/
theorem stKind_cases {s : Stmt} (h : stKind s = true) :
    (∃ hn, s = .atom (.hint hn)) ∨
    (∃ d o, (s = .atom (.load (.n d) (.n 0) o) ∨ s = .atom (.load (.n d) (.n 1) o)) ∧ o < 28) ∨
    (∃ o, s = .atom (.load (.n (stEq (o / 30) (o % 30))) (.n 2) o) ∧ o < 210) ∨
    (∃ o, s = .atom (.load (.n (stB (o / 16) + 36 + o % 16)) (.n 3) o) ∧ o < 112) ∨
    (∃ a, s = .atom a ∧ pureB a = true) := by
  unfold stKind at h
  split at h
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr (Or.inl ⟨_, _, Or.inl rfl, by simpa using h⟩)
  · exact Or.inr (Or.inl ⟨_, _, Or.inr rfl, by simpa using h⟩)
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, rfl⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨_, rfl, h1⟩))
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, rfl⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, h1⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, rfl, h⟩)))
  · exact absurd h (by simp)

theorem pure_holds_rd {a : Atom} (ha : pureB a = true) {rd rd' : Reader} {σ : Val}
    (h : a.Holds rd σ) : a.Holds rd' σ := by
  cases a <;> simp_all [pureB, Atom.Holds]

theorem st_rdAt {rd : Reader} {L : TLay} (hm : MemLay rd L) {q : ℕ × List E} (hq : q ∈ L)
    {o : ℕ} (ho : o < q.2.length) :
    rdAt (layRd L) (ofK (gpow q.1)) o = q.2.getD o 0 ∧
      LoadHolds rd (ofK (gpow q.1)) o (q.2.getD o 0) := by
  have hr := memLay_read hm hq ho
  refine ⟨?_, tb_isInK_ofK _, by rw [tb_addr_ofK]; exact hr⟩
  rw [rdAt, tb_addr_ofK, layRd_agree hm ⟨q, hq, o, ho, rfl⟩, hr]
  rfl

set_option maxRecDepth 10000 in
/-- **Every statement holds** on a memory holding the buffers and the point. -/
theorem st_holds (ept ept1 ese esg : ℕ) (p p1 : List E) (hl : p.length = 28)
    (hl1 : p1.length = 28) (rd : Reader)
    (hm : MemLay rd (stOwn ept ept1 ese esg p p1 ++ stLin ept ept1 p p1)) :
    coreProgram.Rel rd "selector_tables" [ofK (gpow ept), ofK (gpow ept1)]
      [ofK (gpow ese), ofK (gpow esg)] := by
  obtain ⟨fn, hf, hp, hb⟩ := stFound
  have hg : ∀ s ∈ stPre, GoodS (layRd (stLin ept ept1 p p1)) (storesOf 2 stPre) (stW ese esg)
      (stVal ept ept1 ese esg p p1) s :=
    (ev_spec (layRd (stLin ept ept1 p p1)) (stW ese esg) stPre
      [ofK (gpow ept), ofK (gpow ept1)] st_chk).2.2
  have e0 : stVal ept ept1 ese esg p p1 (.n 0) = ofK (gpow ept) :=
    ev_params _ _ (l := [ofK (gpow ept), ofK (gpow ept1)]) st_chk (by norm_num)
  have e1 : stVal ept ept1 ese esg p p1 (.n 1) = ofK (gpow ept1) :=
    ev_params _ _ (l := [ofK (gpow ept), ofK (gpow ept1)]) st_chk (by norm_num)
  set σ := stVal ept ept1 ese esg p p1 with hσ
  have e2 : σ (.n 2) = ofK (gpow ese) := by
    have := hg _ st_alloc_mem.1
    simpa [GoodS, Good, stW] using this
  have e3 : σ (.n 3) = ofK (gpow esg) := by
    have := hg _ st_alloc_mem.2
    simpa [GoodS, Good, stW] using this
  obtain ⟨hmo, hmi⟩ := memLay_append.mp hm
  have hS : ∀ a ∈ storesOf 2 stPre, stStoreOk a = true := fun a ha =>
    List.all_eq_true.mp st_stores a ha
  have hat : ∀ s ∈ stPre, SHolds (coreProgram.Rel rd) rd σ s := by
    intro s hs
    have hgs := hg s hs
    rcases stKind_cases (List.all_eq_true.mp st_kinds s hs) with
      ⟨hn, rfl⟩ | ⟨d, o, hld, ho⟩ | ⟨o, rfl, ho⟩ | ⟨o, rfl, ho⟩ | ⟨a, rfl, ha⟩
    · trivial
    · rcases hld with rfl | rfl
      · simp only [GoodS, Good] at hgs
        rcases hgs with hgs | hgs
        · exact absurd (hS _ hgs) (by simp [stStoreOk])
        · have := st_rdAt hmi (q := (ept, p)) (by simp [stLin]) (o := o) (by simp [hl, ho])
          show LoadHolds rd (σ (.n 0)) o (σ (.n d))
          rw [hgs, e0, this.1]; exact this.2
      · simp only [GoodS, Good] at hgs
        rcases hgs with hgs | hgs
        · exact absurd (hS _ hgs) (by simp [stStoreOk])
        · have := st_rdAt hmi (q := (ept1, p1)) (by simp [stLin]) (o := o) (by simp [hl1, ho])
          show LoadHolds rd (σ (.n 1)) o (σ (.n d))
          rw [hgs, e1, this.1]; exact this.2
    · show LoadHolds rd (σ (.n 2)) o (σ (.n (stEq (o / 30) (o % 30))))
      have h := hmo (ese, stEqWords σ) (by unfold stOwn; exact List.mem_cons_self) o (by simp [stEqWords, ho])
      rw [e2]
      simpa [stEqWords] using h
    · show LoadHolds rd (σ (.n 3)) o (σ (.n (stB (o / 16) + 36 + o % 16)))
      have hc := hg _ (st_const_mem (j := o / 16) (u := o % 16) (by omega) (by omega))
      simp only [GoodS, Good] at hc
      have h := hmo (esg, stGWords) (by unfold stOwn; exact List.mem_cons_of_mem _ List.mem_cons_self) o (by simp [stGWords, ho])
      rw [e3, hc]
      simpa [stGWords] using h
    · exact pure_holds_rd ha (holds_of_pure ha (by simpa only [GoodS] using hgs))
  refine (tb_rel_iff_sem hf _ _).mpr ⟨σ, by rw [hp]; simp [e0, e1], ?_⟩
  rw [hb]
  refine holdsList_straight stPre _ _ _ hat ?_
  have c1 := hg _ (show Stmt.atom (.copy (.n 368) (.n 2)) ∈ stPre by simp [stPre])
  have c2 := hg _ (show Stmt.atom (.copy (.n 369) (.n 3)) ∈ stPre by simp [stPre])
  simp only [GoodS, Good] at c1 c2
  simp [c1, c2, e2, e3]

theorem memLay_mem {rd : Reader} {L : TLay} (hm : MemLay rd L) {q : ℕ × List E} (hq : q ∈ L) :
    TbReadsAt rd (ofK (gpow q.1)) q.2 := hm q hq

set_option maxRecDepth 10000 in
/-- **The buffers hold the opening point's tables**, on any memory holding them, when the runs
lie apart below the order of `g`. -/
theorem st_tabs (ept ept1 ese esg : ℕ) (p p1 : List E) (hl : p.length = 28)
    (hl1 : p1.length = 28)
    (hd : DisjLay (stOwn ept ept1 ese esg p p1 ++ stLin ept ept1 p p1))
    (hlo : LowLay (stOwn ept ept1 ese esg p p1 ++ stLin ept ept1 p p1))
    (rd : Reader) (hm : MemLay rd (stOwn ept ept1 ese esg p p1)) :
    SelTabsAt rd (ofK (gpow ese)) (ofK (gpow esg)) p p1 := by
  set L := stOwn ept ept1 ese esg p p1 ++ stLin ept ept1 p p1 with hL
  have hm1 := memLay_layRd hd hlo
  have hrel := st_holds ept ept1 ese esg p p1 hl hl1 (layRd L) hm1
  have hout := selector_tables_sound hrel
  simp only [SelTablesOut] at hout
  obtain ⟨hmo1, hmi1⟩ := memLay_append.mp hm1
  have h3 := hout p p1 hl hl1 (hmi1 (ept, p) (by simp [stLin]))
    (hmi1 (ept1, p1) (by simp [stLin]))
  have hqe : (ese, stEqWords (stVal ept ept1 ese esg p p1)) ∈ stOwn ept ept1 ese esg p p1 := by
    unfold stOwn; exact List.mem_cons_self
  have hqg : (esg, stGWords) ∈ stOwn ept ept1 ese esg p p1 := by
    unfold stOwn; exact List.mem_cons_of_mem _ List.mem_cons_self
  refine ⟨fun j hj k hk => ?_, fun j hj k hk => ?_⟩
  · have hj7 : j < 7 := hj
    have h := h3.1 j hj k hk
    rw [tb_loadHolds_mul_gen_pow] at h ⊢
    have hk' : k < 30 := by
      have : (eqLevels (topNib p j) (topNib p1 j)).length = 30 := by
        rw [eqLevels_length (topNib_length hl hj) (topNib_length hl1 hj)]; rfl
      omega
    exact lay_transfer hmo1 hm hqe (by simp [stEqWords]; omega) h
  · have hj7 : j < 7 := hj
    have h := h3.2 j hj k hk
    rw [tb_loadHolds_mul_gen_pow] at h ⊢
    have hk' : k < 16 := by
      have : (gTable (topShares j)).length = 16 := by
        rw [gTable_length (n := 4) (by simp [topShares])]; rfl
      omega
    exact lay_transfer hmo1 hm hqg (by simp [stGWords]; omega) h

end
end LeanVM.Guest.B1.Tables
