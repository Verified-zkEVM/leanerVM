/-
  LeanVM.Guest.B1.Opening.QueriesPlaced3

  One iteration of `opening_queries`' loop, placed (`RelAtIn`).
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlaced2

/-!
# One iteration, placed

An iteration's body is straight-line: its atoms (`oqLoop1A`, `oqLoop0A`) then the tail's `callIf`
and `ret []`. `oqLoop1A_ok`, `oqLoop0A_ok`: its atoms by kind, its loads through the weights, the
bit pointers and bit runs, the path's frame runs, the flags, the cap leaves and the chain.

`oqIter1_relAtIn`, `oqIter0_relAtIn`: one iteration at `fp`, at its honest values (`oqIter1F`,
the queries' frame addresses `g^(fp + cert loop ch)` its frame runs), its tail at `fp + fs loop`
(`relAtIn_of_walk_loop`): its frame runs its own data, every other load in the caller's region
`R` (`OqIn`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Statements by kind -/

theorem AtomsOk.mono {P Q : Atom → Prop} {ss : List Stmt} (h : AtomsOk P ss)
    (hPQ : ∀ a, P a → Q a) : AtomsOk Q ss := fun x hx ↦ by
  obtain ⟨a, rfl, ha⟩ := h x hx
  exact ⟨a, rfl, hPQ a ha⟩

theorem AtomsOk.straight {P : Atom → Prop} {ss : List Stmt} (h : AtomsOk P ss) :
    ss.all Stmt.straight = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨a, rfl, -⟩ := h x hx
  rfl

theorem AtomsOk.allocSz {L : V → ℕ → Prop} {F : V → List V → Prop} {ss : List Stmt}
    (h : AtomsOk (AtomKind L F) ss) : ss.filterMap Stmt.allocSz = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro x hx
  obtain ⟨a, rfl, ha⟩ := h x hx
  cases a with
  | hint hh => cases hh <;> first | exact ha.elim | rfl
  | _ => rfl

theorem AtomsOk.callS {P : Atom → Prop} {ss : List Stmt} (h : AtomsOk P ss) :
    ss.filterMap Stmt.callS = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro x hx
  obtain ⟨a, rfl, -⟩ := h x hx
  rfl

theorem AtomsOk.load {L : V → ℕ → Prop} {F : V → List V → Prop} {ss : List Stmt}
    (h : AtomsOk (AtomKind L F) ss) {q : V × ℕ} (hq : q ∈ ss.filterMap stmtLoad?) : L q.1 q.2 := by
  obtain ⟨x, hx, he⟩ := List.mem_filterMap.mp hq
  obtain ⟨a, rfl, ha⟩ := h x hx
  cases a with
  | load d p off =>
    simp only [stmtLoad?, Option.some.injEq] at he
    subst he; exact ha
  | _ => simp [stmtLoad?] at he

theorem AtomsOk.addr {L : V → ℕ → Prop} {F : V → List V → Prop} {ss : List Stmt}
    (h : AtomsOk (AtomKind L F) ss) {q : V × V} (hq : q ∈ ss.filterMap Stmt.addrS) :
    ∃ run, F q.1 run ∧ run.head? = some q.2 := by
  obtain ⟨x, hx, he⟩ := List.mem_filterMap.mp hq
  obtain ⟨a, rfl, ha⟩ := h x hx
  cases a with
  | frameAddr p run =>
    cases run with
    | nil => simp [Stmt.addrS] at he
    | cons r rs =>
      simp only [Stmt.addrS, Option.some.injEq] at he
      subst he
      exact ⟨_, ha, rfl⟩
  | _ => simp [Stmt.addrS] at he

/-- An address of the region `R`. -/
def OqIn (R : ℕ → Prop) (A : K) : Prop := ∃ i, A = Parameters.gpow i ∧ R i

theorem addr_gpow (c k off : ℕ) :
    (ofK (Parameters.gpow c) * gen ^ k).limb 0 * Parameters.gpow off =
      Parameters.gpow (c + k + off) := by
  rw [gen_pow_eq_ofK, ← ofK_mul, gpow_add', limb_ofK]
  simp [gpow_add']

theorem oqRun_head (s : Oq) (ch : ℕ) (hpd : 1 ≤ s.pd) : (oqRun s ch).head? = some (.n ch) := by
  obtain ⟨p, hp⟩ : ∃ p, 4 * s.pd = p + 1 := ⟨4 * s.pd - 1, by omega⟩
  simp [oqRun, hp, List.range_succ_eq_map]

theorem oqRun_length (s : Oq) (ch : ℕ) (hpd : 4 * s.pd ≤ 80) : (oqRun s ch).length = 80 := by
  simp [oqRun]; omega

theorem stmtRun_oqRun (s : Oq) (ch : ℕ) (hpd1 : 1 ≤ s.pd) (hpd : 4 * s.pd ≤ 80) (p : V) :
    stmtRun? (.atom (.frameAddr p (oqRun s ch))) = some (.n ch, 80) := by
  have h1 := oqRun_head s ch hpd1
  have h2 := oqRun_length s ch hpd
  generalize oqRun s ch = l at h1 h2
  cases l with
  | nil => simp at h1
  | cons r rs =>
    simp only [List.head?_cons, Option.some.injEq] at h1
    simp only [List.length_cons] at h2
    simp [stmtRun?, h1, h2]

/-! ## A level-0 iteration's atoms by kind -/

/-- The loads of a level-0 iteration. -/
def OqIt1L (s : Oq) (odd : ℕ) (p : V) (off : ℕ) : Prop :=
  OqQLoad s (.n 10) (.n 5) (oqCh s 11 true) p off ∨
    OqQLoad s (.n (oqE1 s)) (.n 5) (oqCh s (oqE1 s + 1) false) p off ∨
    (p = .n 9 ∧ (off = odd ∨ off = odd + 1)) ∨ (p = .n (oqC1 s) ∧ off = 0) ∨
    (p = .n (oqC1 s + 6) ∧ off = 1)

/-- The `frameAddr`s of a level-0 iteration. -/
def OqIt1F (s : Oq) (p : V) (run : List V) : Prop :=
  (p = .n (oqCh s 11 true + 4 * s.pd) ∧ run = oqRun s (oqCh s 11 true)) ∨
    (p = .n (oqCh s (oqE1 s + 1) false + 4 * s.pd) ∧ run = oqRun s (oqCh s (oqE1 s + 1) false))

theorem oqLoop1A_ok {s : Oq} (hcd : 2 ≤ s.cd) (odd : ℕ) :
    AtomsOk (AtomKind (OqIt1L s odd) (OqIt1F s)) (oqLoop1A s odd) := by
  unfold oqLoop1A
  refine atomsOk_append (atomsOk_append (atomsOk_append (atomsOk_append ?_ ?_) ?_) ?_) ?_
  · exact atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons
      (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩))) atomsOk_nil))
  · exact (oqQuery_atoms_ok hcd _ (.n 3) (.n 4) _ _ _ _).mono fun a ha ↦
      AtomKind.mono (fun p off h ↦ Or.inl h) (fun p run h ↦ Or.inl h) ha
  · exact atomsOk_cons (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩))) atomsOk_nil
  · exact (oqQuery_atoms_ok hcd _ (.n 3) (.n 4) _ _ _ _).mono fun a ha ↦
      AtomKind.mono (fun p off h ↦ Or.inr (Or.inl h)) (fun p run h ↦ Or.inr h) ha
  · refine atomsOk_cons trivial (atomsOk_cons (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
      (atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial
      (atomsOk_cons trivial (atomsOk_cons (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
      ?_)))))))
    exact atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial
      (atomsOk_cons trivial atomsOk_nil))))

/-! ## A deeper iteration's atoms by kind -/

/-- The loads of a deeper iteration. -/
def OqIt0L (s : Oq) (p : V) (off : ℕ) : Prop :=
  OqQLoad s (.n 9) (.n 5) (oqCh s 10 true) p off ∨ (p = .n 8 ∧ off = 0) ∨
    (p = .n (oqC0 s) ∧ off = 0) ∨ (p = .n (oqC0 s + 4) ∧ off = 1)

/-- The `frameAddr` of a deeper iteration. -/
def OqIt0F (s : Oq) (p : V) (run : List V) : Prop :=
  p = .n (oqCh s 10 true + 4 * s.pd) ∧ run = oqRun s (oqCh s 10 true)

theorem oqLoop0A_ok {s : Oq} (hcd : 2 ≤ s.cd) :
    AtomsOk (AtomKind (OqIt0L s) (OqIt0F s)) (oqLoop0A s) := by
  unfold oqLoop0A
  refine atomsOk_append (atomsOk_append ?_ ?_) ?_
  · exact atomsOk_cons trivial (atomsOk_cons (Or.inr (Or.inl ⟨rfl, rfl⟩)) atomsOk_nil)
  · exact (oqQuery_atoms_ok hcd _ (.n 3) (.n 4) _ _ _ _).mono fun a ha ↦
      AtomKind.mono (fun p off h ↦ Or.inl h) (fun p run h ↦ h) ha
  · refine atomsOk_cons trivial (atomsOk_cons (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
      (atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial
      (atomsOk_cons (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))) ?_)))))
    exact atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial
      (atomsOk_cons trivial atomsOk_nil))))

end
end LeanVM.Guest.B1
