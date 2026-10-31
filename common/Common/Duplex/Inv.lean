module

public import Common.Duplex.Table

@[expose] public section

/-!
# The simulator's invariant

Without collision, the simulator's records describe the challenge chains: every programmed answer
carries its challenge (`Inv`), and every next state of a chain is either answered with the next
challenge or would be programmed with it (`NextOK`). A fresh step without collision keeps this
(`inv_step`).
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec

namespace Common.Duplex

variable {Msg Dg St Root Z W Cp : Type} {n : ℕ}
  [DecidableEq Msg] [DecidableEq St] [DecidableEq Root] [DecidableEq Cp]
  (D : DuplexSpec Msg Dg St Root Z W Cp n)

/-! ## The records after a step -/

theorem answer_record (s : SimSt St Root n) (x y : St) (lbl : Option (Root × Fin n)) (x' : St) :
    (s.record D x y lbl).answer x' = if x' = x then some y else s.answer x' := by
  by_cases h : x' = x
  · subst h; simp [SimSt.answer, SimSt.record]
  · simp only [SimSt.answer, SimSt.record, h, ↓reduceIte]
    rw [List.find?_cons_of_neg (by simpa [eq_comm] using h)]

theorem log_record (s : SimSt St Root n) (x y : St) (lbl : Option (Root × Fin n)) :
    (s.record D x y lbl).log = (x, y, lbl) :: s.log := rfl

theorem x0_record (s : SimSt St Root n) (x y : St) (lbl : Option (Root × Fin n)) :
    (s.record D x y lbl).x0 = s.x0 := rfl

theorem y0_record (s : SimSt St Root n) (x y : St) (lbl : Option (Root × Fin n)) :
    (s.record D x y lbl).y0 = if s.x0 = some x then some y else s.y0 := rfl

theorem labOf_record_none (s : SimSt St Root n) (x y : St) (x' : St) :
    (s.record D x y none).labOf x' = s.labOf x' := rfl

theorem labOf_record_some (s : SimSt St Root n) (x y : St) (r : Root) (j : Fin n) (x' : St) :
    (s.record D x y (some (r, j))).labOf x' =
      if h : j.val + 1 < n then
        if s.labOf (D.next y) = none ∧ x' = D.next y then some (r, ⟨j.val + 1, h⟩)
        else s.labOf x'
      else s.labOf x' := by
  by_cases h1 : j.val + 1 < n
  · by_cases h2 : s.labOf (D.next y) = none
    · have e : (s.record D x y (some (r, j))).lab = (D.next y, (r, ⟨j.val + 1, h1⟩)) :: s.lab := by
        simp [SimSt.record, h1, h2]
      by_cases hx : x' = D.next y
      · subst hx
        simp only [h1, ↓reduceDIte, h2, and_self, ↓reduceIte]
        simp [SimSt.labOf, e]
      · simp only [h1, ↓reduceDIte, h2, hx, and_false, ↓reduceIte]
        simp only [SimSt.labOf, e]
        rw [List.find?_cons_of_neg (by simpa [eq_comm] using hx)]
    · have e : (s.record D x y (some (r, j))).lab = s.lab := by
        simp [SimSt.record, h1, h2]
      simp only [h1, ↓reduceDIte, h2, false_and, ↓reduceIte]
      simp only [SimSt.labOf, e]
  · have e : (s.record D x y (some (r, j))).lab = s.lab := by simp [SimSt.record, h1]
    simp only [h1, ↓reduceDIte]
    simp only [SimSt.labOf, e]

theorem mem_forb_of_key {s : SimSt St Root n} {e} (he : e ∈ s.log) :
    D.cap e.1 ∈ forb D s := by
  simp only [forb, List.mem_toFinset, List.mem_append, List.mem_map]
  exact Or.inl (Or.inl ⟨e, he, rfl⟩)

theorem mem_forb_of_val {s : SimSt St Root n} {e} (he : e ∈ s.log) :
    D.cap e.2.1 ∈ forb D s := by
  simp only [forb, List.mem_toFinset, List.mem_append, List.mem_map]
  exact Or.inl (Or.inr ⟨e, he, rfl⟩)

theorem mem_forb_of_x0 {s : SimSt St Root n} {x0} (h : s.x0 = some x0) :
    D.cap x0 ∈ forb D s := by
  simp [forb, h]

theorem answer_eq_some {s : SimSt St Root n} {x y : St} (h : s.answer x = some y) :
    ∃ e ∈ s.log, e.1 = x ∧ e.2.1 = y := by
  simp only [SimSt.answer, Option.map_eq_some_iff] at h
  obtain ⟨e, he, rfl⟩ := h
  exact ⟨e, List.mem_of_find?_eq_some he, by simpa using List.find?_some he, rfl⟩

theorem answer_eq_none {s : SimSt St Root n} {x : St} (h : s.answer x = none) :
    ∀ e ∈ s.log, e.1 ≠ x := by
  simp only [SimSt.answer, Option.map_eq_none_iff, List.find?_eq_none] at h
  exact fun e he hx ↦ h e he (by simpa using hx)

theorem cap_first' (r : Root) (y : St) : D.cap (D.first r y) = D.cap y := D.cap_first r y

theorem cap_next' (y : St) : D.cap (D.next y) = D.cap y := D.cap_next y

theorem out_build (z : Z) (w : W) : D.out (D.build (z, w)) = z := by
  simp [DuplexSpec.out]

/-! ## The invariant -/

/-- A next state of a chain is answered with its challenge, or would be programmed with it. -/
def NextOK (s : SimSt St Root n) (x : St) (L : Root × Fin n) : Prop :=
  (s.answer x = none → efflab D s x = some L) ∧ ∀ e ∈ s.log, e.1 = x → e.2.2 = some L

/-- **The simulator's invariant** for the label's hash `iv` and the table `g`. -/
structure Inv (g : Tab Root Z n) (iv : Dg) (s : SimSt St Root n) : Prop where
  x0 : s.x0 = some (D.init iv)
  nodup : (s.log.map (·.1)).Nodup
  y0 : s.y0 = s.answer (D.init iv)
  out : ∀ e ∈ s.log, ∀ r j, e.2.2 = some (r, j) → D.out e.2.1 = g.at r j
  place : ∀ e ∈ s.log, ∀ r (j : Fin n), e.2.2 = some (r, j) →
    (j.val = 0 → ∃ v, s.y0 = some v ∧ e.1 = D.first r v) ∧
    (∀ j' : Fin n, j.val = j'.val + 1 → ∃ e' ∈ s.log, e'.2.2 = some (r, j') ∧ e.1 = D.next e'.2.1)
  lab : ∀ p ∈ s.lab, ∃ j' : Fin n, p.2.2.val = j'.val + 1 ∧
    ∃ e' ∈ s.log, e'.2.2 = some (p.2.1, j') ∧ p.1 = D.next e'.2.1
  nxt : ∀ e ∈ s.log, ∀ r (j : Fin n) (h : j.val + 1 < n), e.2.2 = some (r, j) →
    NextOK D s (D.next e.2.1) (r, ⟨j.val + 1, h⟩)
  fst : ∀ v, s.y0 = some v → ∀ r, NextOK D s (D.first r v) (r, ⟨0, D.n_pos⟩)
  uniq : ∀ e ∈ s.log, ∀ e' ∈ s.log, e.2.2 = e'.2.2 → e.2.2 ≠ none → e = e'

variable {D}

theorem answer_ne_none_of_mem {s : SimSt St Root n} {e} (he : e ∈ s.log) :
    s.answer e.1 ≠ none := fun h ↦ answer_eq_none h e he rfl

theorem mem_used_iff {s : SimSt St Root n} {L : Root × Fin n} :
    L ∈ s.used ↔ ∃ e ∈ s.log, e.2.2 = some L := by
  simp [SimSt.used, List.mem_filterMap]

/-- A used first challenge: its state is answered. -/
theorem Inv.used_zero {g : Tab Root Z n} {iv : Dg} {s : SimSt St Root n} (hI : Inv D g iv s)
    {v : St} (hv : s.y0 = some v) (r : Root) (hu : (r, ⟨0, D.n_pos⟩) ∈ s.used) :
    s.answer (D.first r v) ≠ none := by
  obtain ⟨e, he, hl⟩ := mem_used_iff.mp hu
  obtain ⟨v', hv', hx⟩ := (hI.place e he r _ hl).1 rfl
  rw [hv] at hv'
  cases hv'
  rw [← hx]
  exact answer_ne_none_of_mem he

/-- A used next challenge: its state is answered. -/
theorem Inv.used_succ {g : Tab Root Z n} {iv : Dg} {s : SimSt St Root n} (hI : Inv D g iv s)
    {e} (he : e ∈ s.log) {r : Root} {j : Fin n} (hl : e.2.2 = some (r, j)) (h : j.val + 1 < n)
    (hu : (r, (⟨j.val + 1, h⟩ : Fin n)) ∈ s.used) : s.answer (D.next e.2.1) ≠ none := by
  obtain ⟨e'', he'', hl''⟩ := mem_used_iff.mp hu
  obtain ⟨e', he', hl', hx⟩ := (hI.place e'' he'' r _ hl'').2 j rfl
  have : e' = e := hI.uniq e' he' e he (by rw [hl', hl]) (by simp [hl'])
  subst this
  rw [← hx]
  exact answer_ne_none_of_mem he''

theorem progLbl_of {s : SimSt St Root n} {x : St} {L : Root × Fin n}
    (h : efflab D s x = some L) (hu : L ∉ s.used) : progLbl D s x = some L := by
  simp [progLbl, h, hu]

/-! ## A fresh step without collision keeps the invariant -/

section Step

variable {g : Tab Root Z n} {iv : Dg} {s : SimSt St Root n} {x y : St}

theorem not_mem_insert_forb (hcol : D.cap y ∉ insert (D.cap x) (forb D s)) :
    D.cap y ≠ D.cap x ∧ (∀ e ∈ s.log, D.cap y ≠ D.cap e.1) ∧
      (∀ e ∈ s.log, D.cap y ≠ D.cap e.2.1) ∧ (∀ x0, s.x0 = some x0 → D.cap y ≠ D.cap x0) := by
  simp only [Finset.mem_insert, not_or] at hcol
  refine ⟨hcol.1, fun e he h ↦ hcol.2 (h ▸ mem_forb_of_key D he),
    fun e he h ↦ hcol.2 (h ▸ mem_forb_of_val D he), fun x0 h0 h ↦ hcol.2 (h ▸ mem_forb_of_x0 D h0)⟩

/-- A state whose capacity is that of the fresh answer is not answered. -/
theorem answer_of_cap (hk : ∀ e ∈ s.log, D.cap y ≠ D.cap e.1) {x' : St}
    (hx' : D.cap x' = D.cap y) : s.answer x' = none := by
  simp only [SimSt.answer, Option.map_eq_none_iff, List.find?_eq_none, decide_eq_true_eq]
  intro e he hex
  exact hk e he (hex ▸ hx').symm

/-- A state whose capacity is that of the fresh answer has no registered challenge. -/
theorem labOf_of_cap (hI : Inv D g iv s) (hv : ∀ e ∈ s.log, D.cap y ≠ D.cap e.2.1) {x' : St}
    (hx' : D.cap x' = D.cap y) : s.labOf x' = none := by
  simp only [SimSt.labOf, Option.map_eq_none_iff, List.find?_eq_none, decide_eq_true_eq]
  intro p hp hpx
  obtain ⟨j', -, e', he', -, hpe⟩ := hI.lab p hp
  apply hv e' he'
  rw [← hx', ← hpx, hpe, cap_next']

/-- The answer at the initial state, once known, is recorded. -/
theorem Inv.y0_mem (hI : Inv D g iv s) {v : St} (hv : s.y0 = some v) :
    ∃ e ∈ s.log, e.2.1 = v := by
  rw [hI.y0] at hv
  obtain ⟨e, he, -, hev⟩ := answer_eq_some hv
  exact ⟨e, he, hev⟩

theorem labOf_record_ne (P : Option (Root × Fin n)) {x' : St} (hne : x' ≠ D.next y) :
    (s.record D x y P).labOf x' = s.labOf x' := by
  rcases P with _ | ⟨r, j⟩
  · rfl
  · rw [labOf_record_some]
    split_ifs with h1 h2
    · exact absurd h2.2 hne
    · rfl
    · rfl

theorem efflab_record_of (P : Option (Root × Fin n)) {x' : St} (hx0 : s.x0 ≠ some x)
    (hl : (s.record D x y P).labOf x' = s.labOf x') :
    efflab D (s.record D x y P) x' = efflab D s x' := by
  simp only [efflab, x0_record, y0_record, hx0, ↓reduceIte, hl]

theorem efflab_record_x0 {x' : St} (hx0 : s.x0 = some x) :
    efflab D (s.record D x y none) x' =
      if s.x0 = some x' then none else
        match D.dec y x' with
        | some r => some (r, ⟨0, D.n_pos⟩)
        | none => s.labOf x' := by
  simp only [efflab, x0_record, y0_record, hx0, ↓reduceIte, labOf_record_none]
  split_ifs
  · rfl
  · rcases D.dec y x' <;> rfl

theorem progLbl_x0 (hx0 : s.x0 = some x) : progLbl D s x = none := by
  simp [progLbl, efflab, hx0]

/-- **The step at the initial state** keeps the invariant. -/
theorem inv_record_x0 (hI : Inv D g iv s) (hx : s.answer x = none) (hx0 : x = D.init iv)
    (hcol : D.cap y ∉ insert (D.cap x) (forb D s)) : Inv D g iv (s.record D x y none) := by
  subst hx0
  obtain ⟨hcx, hck, hcv, hc0⟩ := not_mem_insert_forb hcol
  have hsx0 := hI.x0
  have hy0 : s.y0 = none := by rw [hI.y0, hx]
  -- states with the capacity of `y` are fresh
  have hfresh : ∀ x', D.cap x' = D.cap y →
      (s.record D (D.init iv) y none).answer x' = none := by
    intro x' hx'
    rw [answer_record]
    rw [ite_neg' (fun h ↦ hcx (h ▸ hx').symm)]
    exact answer_of_cap hck hx'
  constructor
  · exact hsx0
  · simp only [log_record, List.map_cons, List.nodup_cons]
    exact ⟨fun h ↦ by
      obtain ⟨e, he, hex⟩ := List.mem_map.mp h
      exact answer_eq_none hx e he hex, hI.nodup⟩
  · simp [y0_record, hsx0, answer_record]
  · intro e he r j hl
    rcases List.mem_cons.mp he with rfl | he
    · simp at hl
    · exact hI.out e he r j hl
  · intro e he r j hl
    rcases List.mem_cons.mp he with rfl | he
    · simp at hl
    · obtain ⟨h1, h2⟩ := hI.place e he r j hl
      refine ⟨fun hj ↦ ?_, fun j' hj' ↦ ?_⟩
      · obtain ⟨v, hv, -⟩ := h1 hj
        rw [hy0] at hv; cases hv
      · obtain ⟨e', he', hl', hx'⟩ := h2 j' hj'
        exact ⟨e', List.mem_cons_of_mem _ he', hl', hx'⟩
  · intro p hp
    obtain ⟨j', hj', e', he', hl', hx'⟩ := hI.lab p hp
    exact ⟨j', hj', e', List.mem_cons_of_mem _ he', hl', hx'⟩
  · intro e he r j h hl
    rcases List.mem_cons.mp he with rfl | he
    · simp at hl
    obtain ⟨h1, h2⟩ := hI.nxt e he r j h hl
    have hne : D.next e.2.1 ≠ D.init iv := by
      intro heq
      have := h1 (heq ▸ hx)
      rw [heq] at this
      simp [efflab, hsx0] at this
    refine ⟨fun ha ↦ ?_, fun e2 he2 hk ↦ ?_⟩
    · rw [answer_record, ite_neg' hne] at ha
      rw [efflab_record_x0 hsx0, ite_neg' (by rw [hsx0]; exact fun h ↦ hne (Option.some.inj h).symm)]
      have hd : D.dec y (D.next e.2.1) = none := by
        rcases hdd : D.dec y (D.next e.2.1) with _ | r'
        · rfl
        · have := (D.dec_iff _ _ _).mp hdd
          exact absurd (by rw [← cap_first' D r' y, this, cap_next']) (hcv e he)
      simp only [hd]
      have := h1 ha
      simpa [efflab, hsx0, hy0, Ne.symm (fun h ↦ hne (Option.some.inj h)),
        show ¬ (some (D.init iv) = some (D.next e.2.1)) from
          fun h ↦ hne (Option.some.inj h).symm] using this
    · rcases List.mem_cons.mp he2 with rfl | he2
      · exact absurd hk.symm hne
      · exact h2 e2 he2 hk
  · intro v hv r
    simp only [y0_record, hsx0, ↓reduceIte, Option.some.injEq] at hv
    subst hv
    have hfc : D.cap (D.first r y) = D.cap y := cap_first' D r y
    refine ⟨fun _ ↦ ?_, fun e he hk ↦ ?_⟩
    · rw [efflab_record_x0 hsx0]
      have hne : ¬ s.x0 = some (D.first r y) := by
        rw [hsx0]; intro h
        exact hcx (by rw [← hfc, ← Option.some.inj h])
      rw [ite_neg' hne, (D.dec_iff y _ r).mpr rfl]
    · exfalso
      have := hfresh _ hfc
      rw [← hk] at this
      exact answer_ne_none_of_mem he this
  · intro e he e' he' hll hn
    rcases List.mem_cons.mp he with rfl | he
    · exact absurd rfl hn
    rcases List.mem_cons.mp he' with rfl | he'
    · exact absurd hll.symm (fun h ↦ by simp at h; exact hn h.symm)
    exact hI.uniq e he e' he' hll hn

theorem efflab_spec {r : Root} {j : Fin n} (hx0 : s.x0 ≠ some x)
    (h : efflab D s x = some (r, j)) :
    (∃ v, s.y0 = some v ∧ D.first r v = x ∧ j.val = 0) ∨
      (∃ p ∈ s.lab, p.1 = x ∧ p.2 = (r, j)) := by
  unfold efflab at h
  rw [ite_neg' hx0] at h
  have hlab : s.labOf x = some (r, j) → ∃ p ∈ s.lab, p.1 = x ∧ p.2 = (r, j) := fun hl ↦ by
    simp only [SimSt.labOf, Option.map_eq_some_iff] at hl
    obtain ⟨p, hp, hpe⟩ := hl
    exact ⟨p, List.mem_of_find?_eq_some hp, by simpa using List.find?_some hp, hpe⟩
  rcases hy0 : s.y0 with _ | v
  · simp only [hy0] at h
    exact Or.inr (hlab h)
  · simp only [hy0] at h
    rcases hd : D.dec v x with _ | r'
    · simp only [hd] at h
      exact Or.inr (hlab h)
    · simp only [hd, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inl ⟨v, rfl, (D.dec_iff v x r').mp hd, rfl⟩

theorem progLbl_not_used {L : Root × Fin n} (h : progLbl D s x = some L) : L ∉ s.used := by
  unfold progLbl at h
  split at h
  · split_ifs at h with hu
    cases h; exact hu
  · cases h

theorem progLbl_efflab {L : Root × Fin n} (h : progLbl D s x = some L) :
    efflab D s x = some L := by
  unfold progLbl at h
  split at h
  · next L' hL' => split_ifs at h; cases h; exact hL'
  · cases h

/-- The next states of the chains stay described after a step elsewhere. -/
theorem nextOK_record (hx : s.answer x = none) (hx0 : s.x0 ≠ some x)
    (hcv : ∀ e ∈ s.log, D.cap y ≠ D.cap e.2.1) {x' : St} {L : Root × Fin n}
    (hok : NextOK D s x' L) (hcx' : ∃ e ∈ s.log, D.cap x' = D.cap e.2.1)
    (hprog : x' = x → progLbl D s x = some L) :
    NextOK D (s.record D x y (progLbl D s x)) x' L := by
  have hne : x' ≠ D.next y := by
    obtain ⟨e, he, hce⟩ := hcx'
    intro h
    exact hcv e he (by rw [← cap_next' D y, ← h, hce])
  by_cases hxx : x' = x
  · subst hxx
    refine ⟨fun h ↦ by simp [answer_record] at h, fun e he hk ↦ ?_⟩
    rcases List.mem_cons.mp he with rfl | he
    · exact hprog rfl
    · exact absurd hk (answer_eq_none hx e he)
  · refine ⟨fun ha ↦ ?_, fun e he hk ↦ ?_⟩
    · rw [answer_record, ite_neg' hxx] at ha
      rw [efflab_record_of _ hx0 (labOf_record_ne _ hne)]
      exact hok.1 ha
    · rcases List.mem_cons.mp he with rfl | he
      · exact absurd hk.symm hxx
      · exact hok.2 e he hk

/-- **A step away from the initial state** keeps the invariant. -/
theorem inv_record_other (hI : Inv D g iv s) (hx : s.answer x = none) (hx0 : x ≠ D.init iv)
    (hy : ∀ r j, progLbl D s x = some (r, j) → D.out y = g.at r j)
    (hcol : D.cap y ∉ insert (D.cap x) (forb D s)) :
    Inv D g iv (s.record D x y (progLbl D s x)) := by
  obtain ⟨hcx, hck, hcv, hc0⟩ := not_mem_insert_forb hcol
  have hsx0 := hI.x0
  have hx0' : s.x0 ≠ some x := by rw [hsx0]; exact fun h ↦ hx0 (Option.some.inj h).symm
  have hy0' : (s.record D x y (progLbl D s x)).y0 = s.y0 := by
    simp [y0_record, hx0']
  constructor
  · exact hsx0
  · simp only [log_record, List.map_cons, List.nodup_cons]
    exact ⟨fun h ↦ by
      obtain ⟨e, he, hex⟩ := List.mem_map.mp h
      exact answer_eq_none hx e he hex, hI.nodup⟩
  · rw [hy0', hI.y0, answer_record, ite_neg' (Ne.symm hx0)]
  · intro e he r j hl
    rcases List.mem_cons.mp he with rfl | he
    · exact hy r j hl
    · exact hI.out e he r j hl
  · intro e he r j hl
    rw [hy0']
    rcases List.mem_cons.mp he with rfl | he
    · -- the new entry: its challenge came from `efflab`
      simp only at hl
      have hL : efflab D s x = some (r, j) := by
        unfold progLbl at hl
        split at hl
        · next L hL => split_ifs at hl; cases hl; exact hL
        · cases hl
      rcases efflab_spec hx0' hL with ⟨v, hv, hfv, hj⟩ | ⟨p, hp, hpx, hpl⟩
      · exact ⟨fun _ ↦ ⟨v, hv, hfv.symm⟩, fun j' hj' ↦ by omega⟩
      · obtain ⟨j', hj', e', he', hl', hx'⟩ := hI.lab p hp
        rw [hpl] at hj' hl'
        refine ⟨fun hj ↦ by simp at hj'; omega, fun j'' hj'' ↦ ?_⟩
        have : j'' = j' := Fin.ext (by simp at hj'; omega)
        subst this
        exact ⟨e', List.mem_cons_of_mem _ he', hl', hpx ▸ hx'⟩
    · obtain ⟨h1, h2⟩ := hI.place e he r j hl
      exact ⟨h1, fun j' hj' ↦ by
        obtain ⟨e', he', hl', hx'⟩ := h2 j' hj'
        exact ⟨e', List.mem_cons_of_mem _ he', hl', hx'⟩⟩
  · intro p hp
    rcases hP : progLbl D s x with _ | ⟨r0, j0⟩
    · rw [hP] at hp
      obtain ⟨j', hj', e', he', hl', hx'⟩ := hI.lab p hp
      exact ⟨j', hj', e', List.mem_cons_of_mem _ he', hl', hx'⟩
    · rw [hP] at hp
      have hold : p ∈ s.lab → ∃ j' : Fin n, p.2.2.val = j'.val + 1 ∧
          ∃ e' ∈ (s.record D x y (some (r0, j0))).log, e'.2.2 = some (p.2.1, j') ∧
            p.1 = D.next e'.2.1 := fun hp ↦ by
        obtain ⟨j', hj', e', he', hl', hx'⟩ := hI.lab p hp
        exact ⟨j', hj', e', List.mem_cons_of_mem _ he', hl', hx'⟩
      by_cases h1 : j0.val + 1 < n
      · by_cases h2 : s.labOf (D.next y) = none
        · have he : (s.record D x y (some (r0, j0))).lab =
              (D.next y, (r0, ⟨j0.val + 1, h1⟩)) :: s.lab := by simp [SimSt.record, h1, h2]
          rw [he] at hp
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact ⟨j0, rfl, (x, y, some (r0, j0)), List.mem_cons_self, rfl, rfl⟩
          · exact hold hp'
        · have he : (s.record D x y (some (r0, j0))).lab = s.lab := by
            simp [SimSt.record, h1, h2]
          rw [he] at hp
          exact hold hp
      · have he : (s.record D x y (some (r0, j0))).lab = s.lab := by simp [SimSt.record, h1]
        rw [he] at hp
        exact hold hp
  · intro e he r j h hl
    rcases List.mem_cons.mp he with rfl | he
    · simp only at hl ⊢
      have hny : D.next y ≠ x := fun h' ↦ hcx (by rw [← cap_next' D y, h'])
      have hans : s.answer (D.next y) = none := answer_of_cap hck (cap_next' D y)
      have hans' : (s.record D x y (progLbl D s x)).answer (D.next y) = none := by
        rw [answer_record, ite_neg' hny, hans]
      refine ⟨fun _ ↦ ?_, fun e2 he2 hk ↦ absurd hans'
        (by rw [← hk]; exact answer_ne_none_of_mem he2)⟩
      have hlab0 : s.labOf (D.next y) = none := labOf_of_cap hI hcv (cap_next' D y)
      have hx0n : s.x0 ≠ some (D.next y) := by
        rw [hsx0]; exact fun h' ↦ hc0 _ hsx0 (by rw [← cap_next' D y, ← Option.some.inj h'])
      unfold efflab
      rw [ite_neg' (by rw [x0_record]; exact hx0n), hy0', hl, labOf_record_some]
      simp only [h, ↓reduceDIte, hlab0, true_and, ↓reduceIte]
      rcases hv : s.y0 with _ | v
      · rfl
      · have hd : D.dec v (D.next y) = none := by
          rcases hdd : D.dec v (D.next y) with _ | r'
          · rfl
          · obtain ⟨e0, he0, he0v⟩ := hI.y0_mem hv
            have := (D.dec_iff _ _ _).mp hdd
            exact absurd (by rw [← cap_next' D y, ← this, cap_first', he0v]) (hcv e0 he0)
        simp only [hd]
    · have hok := hI.nxt e he r j h hl
      have hus : (r, (⟨j.val + 1, h⟩ : Fin n)) ∈ s.used → s.answer (D.next e.2.1) ≠ none :=
        hI.used_succ he hl h
      exact nextOK_record hx hx0' hcv hok ⟨e, he, cap_next' D _⟩
        (fun hxx ↦ by
          subst hxx
          exact progLbl_of (hok.1 hx) (fun hu ↦ hus hu hx))
  · intro v hv r
    rw [hy0'] at hv
    obtain ⟨e0, he0, he0v⟩ := hI.y0_mem hv
    exact nextOK_record hx hx0' hcv (hI.fst v hv r)
      ⟨e0, he0, by rw [cap_first', he0v]⟩
      (fun hxx ↦ by
        subst hxx
        exact progLbl_of ((hI.fst v hv r).1 hx) (fun hu ↦ hI.used_zero hv r hu hx))
  · intro e he e' he' hll hn
    rcases List.mem_cons.mp he with rfl | he <;> rcases List.mem_cons.mp he' with rfl | he'
    · rfl
    · exfalso
      obtain ⟨L, hL⟩ := Option.ne_none_iff_exists'.mp hn
      exact progLbl_not_used (hL ▸ rfl : progLbl D s x = some L)
        (mem_used_iff.mpr ⟨e', he', hll ▸ hL⟩)
    · exfalso
      obtain ⟨L, hL⟩ := Option.ne_none_iff_exists'.mp hn
      exact progLbl_not_used (hll.symm.trans hL : progLbl D s x = some L)
        (mem_used_iff.mpr ⟨e, he, hL⟩)
    · exact hI.uniq e he e' he' hll hn

end Step

end Common.Duplex

namespace Common.Duplex

variable {Msg Dg St Root Z W Cp : Type} {n : ℕ}
  [DecidableEq Msg] [DecidableEq St] [DecidableEq Root] [DecidableEq Cp]
  [SampleableType Dg] [SampleableType St] [SampleableType Z] [SampleableType W]
  [Fintype St] [Fintype Z] [Fintype W] [Fintype Root] [Nonempty Z]
  {D : DuplexSpec Msg Dg St Root Z W Cp n}

/-! ## The steps of the table world -/

/-- The table world's state is good: the invariant, a cache without challenges, the label's
hash cached. -/
structure Good (D : DuplexSpec Msg Dg St Root Z W Cp n) (g : Tab Root Z n) (iv : Dg)
    (sc : SimSt St Root n × (GSpec Msg Dg Root Z n).QueryCache) : Prop where
  inv : Inv D g iv sc.1
  gfree : GFree sc.2
  label : sc.2 (.inl D.label) = some iv

theorem bad_record (s : SimSt St Root n) (x y : St) (lbl : Option (Root × Fin n)) :
    (s.record D x y lbl).bad = (s.bad || decide (D.cap y ∈ insert (D.cap x) (forb D s))) := rfl

theorem tab_bad_mono (g : Tab Root Z n) (t : (Rom2 Msg Dg St).Domain) (s : SimSt St Root n)
    (c : (GSpec Msg Dg Root Z n).QueryCache) (hc : GFree c) (hs : s.bad = true) {z}
    (hz : z ∈ support ((tabImpl D g t).run (s, c))) : z.2.1.bad = true := by
  rcases t with k | m | x
  · rw [tab_coin D g k s c hz]; exact hs
  · obtain ⟨-, h⟩ := tab_H D g m s c hz
    rw [h]; split_ifs <;> exact hs
  · rcases tab_F D g x s c hc hz with ⟨-, h⟩ | ⟨-, h, -⟩
    · rw [h]; exact hs
    · rw [h]; simp [bad_record, hs]

theorem record_x0_self (s : SimSt St Root n) {x0 : St} (h : s.x0 = some x0) :
    ({ s with x0 := some x0 } : SimSt St Root n) = s := by
  cases s; simp_all

/-- **A step without collision keeps the table world good.** -/
theorem good_step (g : Tab Root Z n) (iv : Dg) (t : (Rom2 Msg Dg St).Domain)
    (sc : SimSt St Root n × (GSpec Msg Dg Root Z n).QueryCache) (hG : Good D g iv sc)
    {z} (hz : z ∈ support ((tabImpl D g t).run sc)) (hb : z.2.1.bad = false) :
    Good D g iv z.2 := by
  obtain ⟨s, c⟩ := sc
  rcases t with k | m | x
  · rw [tab_coin D g k s c hz]; exact hG
  · obtain ⟨hv, h⟩ := tab_H D g m s c hz
    have hc : (z.1, z.2.2) ∈ support (roStep (hs := GSpec Msg Dg Root Z n) (.inl m) c) := hv
    have hz2 : z.2.2 = c ∨ ∃ u, z.2.2 = c.cacheQuery (.inl m) u ∧ c (.inl m) = none := by
      rcases hcm : c (.inl m) with _ | u
      · rw [roStep_of_none hcm] at hc
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hc
        obtain ⟨u, -, hu⟩ := hc
        exact Or.inr ⟨u, (Prod.mk.inj hu).2, rfl⟩
      · rw [roStep_of_some hcm] at hc
        simp only [support_pure, Set.mem_singleton_iff] at hc
        exact Or.inl (Prod.mk.inj hc).2
    have hs : z.2.1 = s := by
      rw [h]
      split_ifs with hm
      · subst hm
        rw [roStep_of_some hG.label] at hc
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hc
        rw [hc.1]
        exact record_x0_self s hG.inv.x0
      · rfl
    refine ⟨hs ▸ hG.inv, ?_, ?_⟩
    · rcases hz2 with h2 | ⟨u, h2, -⟩
      · rw [h2]; exact hG.gfree
      · intro d; rw [h2, QueryCache.cacheQuery_of_ne _ _ (by simp)]; exact hG.gfree d
    · rcases hz2 with h2 | ⟨u, h2, hn⟩
      · rw [h2]; exact hG.label
      · rw [h2]
        by_cases hm : m = D.label
        · subst hm; rw [hG.label] at hn; cases hn
        · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa [eq_comm] using hm)]; exact hG.label
  · rcases tab_F D g x s c hG.gfree hz with ⟨-, h⟩ | ⟨hx, h, hy⟩
    · rw [h]; exact hG
    · rw [h] at hb ⊢
      have hcol : D.cap z.1 ∉ insert (D.cap x) (forb D s) := by
        intro hm
        simp [bad_record, hm] at hb
      refine ⟨?_, hG.gfree, hG.label⟩
      by_cases hx0 : x = D.init iv
      · have hp : progLbl D s x = none := progLbl_x0 (by rw [hG.inv.x0, hx0])
        simp only [hp]
        exact inv_record_x0 hG.inv hx hx0 hcol
      · refine inv_record_other hG.inv hx hx0 (fun r j hl ↦ ?_) hcol
        obtain ⟨w, hw⟩ := hy r j hl
        rw [hw, out_build]

end Common.Duplex
