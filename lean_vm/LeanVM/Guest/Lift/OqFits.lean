/-
  LeanVM.Guest.Lift.OqFits

  `opening_queries`' frame facts (`OqFits`) from two facts of the frame certificates: every frame
  run fits its frame (`Lift.RunsFit`), and two frame runs of a body meet only at a common value
  (`Lift.RunsApart`).
-/

module

public import LeanVM.Guest.Memory.LiftPure
public import LeanVM.Guest.B1.Opening.QueriesPlacedD2

/-!
# `opening_queries`' frames

`OqFits` (B1-b's `QueriesPlacedD*`) asks, of the frame certificate, that each query's path run
(the `4·pd` hinted children, at the certificate's cell of `.n ch`) lies in its function's frame,
and, at level 0, that the iteration's two queries' runs are apart. Each is a `frameAddr` of the
body (`oqQuery_frameAddr`), of the 80-cell run `oqRun s ch`, so:

* `oqRun_fit`: a run fits its frame (`RunsFit`), so its first `4·pd` cells do;
* `oqRun_apart`: two runs whose first `4·pd` values are distinct (`ch + 4·pd ≤ ch'`) hold them
  at disjoint cells (`RunsApart`: a cell of two runs holds one value).

`oqFits1_of`, `oqFits0_of` take the arguments of `oqCompleteD1`, `oqCompleteD0` (the bodies) and
give `OqFits`; `OqFitsS*` instantiate them at the 56 deployed specializations.
-/

namespace LeanVM.Guest.Lift

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- **Two frame runs of a body meet only at a common value**: where their cells coincide, their
values do. The certificates' fact, discharged for the deployed instance from the checker's
(`B2C.FnStatic.runsFun`). -/
def RunsApart (cert : String → V → ℕ) : Prop :=
  ∀ f fn, coreProgram.find? f = some fn → ∀ p r rs p' r' rs',
    Atom.frameAddr p (r :: rs) ∈ blockAtoms fn.body →
    Atom.frameAddr p' (r' :: rs') ∈ blockAtoms fn.body →
    ∀ (k : ℕ) (hk : k < (r :: rs).length) (k' : ℕ) (hk' : k' < (r' :: rs').length),
      cert f r + k = cert f r' + k' → (r :: rs)[k] = (r' :: rs')[k']

theorem mem_blockAtoms {a : Atom} : ∀ {ss : List Stmt}, Stmt.atom a ∈ ss → a ∈ blockAtoms ss
  | [], h => by cases h
  | s :: ss, h => by
    rw [blockAtoms, List.mem_append]
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inl (by simp [stmtAtoms])
    · exact Or.inr (mem_blockAtoms h)

end
end LeanVM.Guest.Lift

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

theorem oqRun_getElem? {s : Oq} {ch k : ℕ} (hk : k < 4 * s.pd) :
    (oqRun s ch)[k]? = some (.n (ch + k)) := by
  unfold oqRun
  rw [List.getElem?_append_left (by simpa using hk)]
  simp [hk]

theorem oqRun_cons (s : Oq) (ch : ℕ) (hpd : 4 * s.pd ≤ 80) (hpd1 : 1 ≤ s.pd) :
    ∃ rs, oqRun s ch = .n ch :: rs ∧ rs.length + 1 = 80 := by
  have hlen : (oqRun s ch).length = 80 := by simp [oqRun]; omega
  have h0 := oqRun_getElem? (s := s) (ch := ch) (k := 0) (by omega)
  cases hr : oqRun s ch with
  | nil => rw [hr] at hlen; cases hlen
  | cons r rs =>
    rw [hr] at h0 hlen
    simp only [List.getElem?_cons_zero, Nat.add_zero, Option.some.injEq] at h0
    exact ⟨rs, by rw [h0], by simpa using hlen⟩

theorem oqRun_getElem {s : Oq} {ch : ℕ} {rs : List V} (hrs : oqRun s ch = .n ch :: rs) {k : ℕ}
    (hk : k < 4 * s.pd) (hk' : k < (V.n ch :: rs).length) : (V.n ch :: rs)[k] = .n (ch + k) := by
  have h := oqRun_getElem? (s := s) (ch := ch) hk
  rw [hrs, List.getElem?_eq_some_iff] at h
  exact h.2

/-- **A query's path run fits its frame.** -/
theorem oqRun_fit (hfit : Lift.RunsFit fs cert) {f : String} {fn : Fn}
    (hf : coreProgram.find? f = some fn) {s : Oq} (hpd : 4 * s.pd ≤ 80) (hpd1 : 1 ≤ s.pd)
    {p : V} {ch : ℕ} (hm : Atom.frameAddr p (oqRun s ch) ∈ Lift.blockAtoms fn.body) :
    cert f (.n ch) + 4 * s.pd ≤ fs f := by
  obtain ⟨rs, hrs, hl⟩ := oqRun_cons s ch hpd hpd1
  rw [hrs] at hm
  have := hfit f fn hf p (.n ch) rs hm
  omega

/-- **Two queries' path runs are apart**, their first `4·pd` values distinct. -/
theorem oqRun_apart (hap : Lift.RunsApart cert) {f : String} {fn : Fn}
    (hf : coreProgram.find? f = some fn) {s : Oq} (hpd : 4 * s.pd ≤ 80) (hpd1 : 1 ≤ s.pd)
    {p p' : V} {ch ch' : ℕ} (hm : Atom.frameAddr p (oqRun s ch) ∈ Lift.blockAtoms fn.body)
    (hm' : Atom.frameAddr p' (oqRun s ch') ∈ Lift.blockAtoms fn.body) (hd : ch + 4 * s.pd ≤ ch') :
    cert f (.n ch) + 4 * s.pd ≤ cert f (.n ch') ∨ cert f (.n ch') + 4 * s.pd ≤ cert f (.n ch) := by
  obtain ⟨rs, hrs, hl⟩ := oqRun_cons s ch hpd hpd1
  obtain ⟨rs', hrs', hl'⟩ := oqRun_cons s ch' hpd hpd1
  rw [hrs] at hm
  rw [hrs'] at hm'
  have key : ∀ k < 4 * s.pd, ∀ k' < 4 * s.pd, cert f (.n ch) + k = cert f (.n ch') + k' →
      ch + k = ch' + k' := by
    intro k hk k' hk' he
    have h := hap f fn hf p (.n ch) rs p' (.n ch') rs' hm hm' k (by simp; omega) k'
      (by simp; omega) he
    have e := (oqRun_getElem hrs hk (by simp; omega)).symm.trans
      (h.trans (oqRun_getElem hrs' hk' (by simp; omega)))
    exact congrArg V.idx e
  by_contra hne
  rw [not_or, Nat.not_le, Nat.not_le] at hne
  rcases le_total (cert f (.n ch)) (cert f (.n ch')) with hle | hle
  · have := key (cert f (.n ch') - cert f (.n ch)) (by omega) 0 (by omega) (by omega)
    omega
  · have := key 0 (by omega) (cert f (.n ch) - cert f (.n ch')) (by omega) (by omega)
    omega

/-! ## The bodies' path runs -/

theorem loop1_run1 (s : Oq) (odd : ℕ) (loop : String) :
    Stmt.atom (.frameAddr (.n (oqCh s 11 true + 4 * s.pd)) (oqRun s (oqCh s 11 true))) ∈
      oqLoop1T s odd loop := by
  simp only [oqLoop1T, oqLoop1A, List.mem_append, oqQuery_frameAddr, true_or, or_true]

theorem loop1_run2 (s : Oq) (odd : ℕ) (loop : String) :
    Stmt.atom (.frameAddr (.n (oqCh s (oqE1 s + 1) false + 4 * s.pd))
      (oqRun s (oqCh s (oqE1 s + 1) false))) ∈ oqLoop1T s odd loop := by
  simp only [oqLoop1T, oqLoop1A, List.mem_append, oqQuery_frameAddr, true_or, or_true]

theorem loop0_run (s : Oq) (loop : String) :
    Stmt.atom (.frameAddr (.n (oqCh s 10 true + 4 * s.pd)) (oqRun s (oqCh s 10 true))) ∈
      oqLoop0T s loop := by
  simp only [oqLoop0T, oqLoop0A, List.mem_append, oqQuery_frameAddr, true_or, or_true]

theorem main_run (s : Oq) (loop : String) :
    Stmt.atom (.frameAddr (.n (oqCh s 13 true + 4 * s.pd)) (oqRun s (oqCh s 13 true))) ∈
      oqMainT s 1 loop := by
  simp only [oqMainT, oqMainA, List.mem_append, ↓reduceIte, oqQuery_frameAddr, true_or, or_true]

/-! ## `OqFits` -/

/-- **A level-0 specialization's frames fit its runs**, from its bodies (`oqCompleteD1`'s
arguments) and the certificates' `RunsFit`, `RunsApart`. -/
theorem oqFits1_of (hfit : Lift.RunsFit fs cert) (hap : Lift.RunsApart cert)
    {s : Oq} (_hs : s.RowShape) (hb1 : s.base = 1) (hpd : 4 * s.pd ≤ 80) (hpd1 : 1 ≤ s.pd)
    (_hcd : 2 ≤ s.cd) (_hcd8 : s.cd ≤ 8) {odd : ℕ} (_hodd : odd ≤ 1) {name loop : String}
    {fm fl : Fn} (hfm : coreProgram.find? name = some fm)
    (_hpm : fm.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6])
    (hbm : fm.body = oqMainT s odd loop)
    (hfl : coreProgram.find? loop = some fl) (_hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop1T s odd loop)
    (hd : oqCh s 11 true + 4 * s.pd ≤ oqCh s (oqE1 s + 1) false := by decide) :
    OqFits fs cert name loop s odd := by
  simp only [OqFits, hb1, ↓reduceIte]
  have m1 := Lift.mem_blockAtoms (loop1_run1 s odd loop)
  have m2 := Lift.mem_blockAtoms (loop1_run2 s odd loop)
  rw [← hbl] at m1 m2
  refine ⟨fun h => ?_, oqRun_fit hfit hfl hpd hpd1 m1, oqRun_fit hfit hfl hpd hpd1 m2,
    oqRun_apart hap hfl hpd hpd1 m1 m2 hd⟩
  subst h
  have m := Lift.mem_blockAtoms (main_run s loop)
  rw [← hbm] at m
  exact oqRun_fit hfit hfm hpd hpd1 m

/-- **A deeper specialization's frames fit its runs**, from its bodies (`oqCompleteD0`'s
arguments) and the certificates' `RunsFit`. -/
theorem oqFits0_of (hfit : Lift.RunsFit fs cert) (_hap : Lift.RunsApart cert)
    {s : Oq} (_hs : s.RowShape) (hb0 : s.base = 0) (hpd : 4 * s.pd ≤ 80) (hpd1 : 1 ≤ s.pd)
    (_hcd : 2 ≤ s.cd) (_hcd8 : s.cd ≤ 8) {name loop : String} {fm fl : Fn}
    (_hfm : coreProgram.find? name = some fm)
    (_hpm : fm.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6])
    (_hbm : fm.body = oqMainT s 0 loop)
    (hfl : coreProgram.find? loop = some fl) (_hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop0T s loop) : OqFits fs cert name loop s 0 := by
  simp only [OqFits, hb0, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte]
  have m := Lift.mem_blockAtoms (loop0_run s loop)
  rw [← hbl] at m
  exact oqRun_fit hfit hfl hpd hpd1 m

end
end LeanVM.Guest.B1
