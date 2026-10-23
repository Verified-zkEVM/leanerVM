/-
  LeanVM.Guest.B1.Opening.QueriesPlaced1

  The statements of `opening_queries`' templates, by kind: their loads and where they read, their
  frame run, no `HeapBuf` in a query.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesMain
public import LeanVM.Guest.Memory.Straight

/-!
# The statements of `opening_queries`, by kind

The placed form (`RelAtIn`) needs, of a body, its `HeapBuf`s, its `frameAddr`s and runs, its
calls and where its loads read. `OqAtomOk`: an atom of a query is a load reading the weights
(`wp`, below `lo + I/lo`), its bit run (`bp`, below `pd + cd`), the path's frame run
(`.n (L_l + 2)` at `4l`, `4l + 1`), the flag (`.n z` at `2^(cd-1)`) or the cap leaf (`.n (z + 10)`
at `2^(cd+1)`, `+ 1`); or the path's `frameAddr` (pointer `.n (ch + 4pd)`, its run of 80 cells
from `.n ch`); or neither a load, a `frameAddr` nor a `HeapBuf`. `oqQuery_atoms_ok`: every
statement of a query is such an atom.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- A load of a query: its pointer and offset. -/
def OqQLoad (s : Oq) (bp wp : V) (ch : ℕ) (p : V) (off : ℕ) : Prop :=
  (p = wp ∧ off < s.lo + s.I / s.lo) ∨ (p = bp ∧ off < s.pd + s.cd) ∨
    (∃ l < s.pd, p = .n (oqL0 ch + 17 * l + 2) ∧ (off = 4 * l ∨ off = 4 * l + 1)) ∨
    (p = .n (oqCq s ch + 5 + 6 * (s.cd - 2)) ∧ off = 2 ^ (s.cd - 1)) ∨
    (p = .n (oqCq s ch + 5 + 6 * (s.cd - 2) + 10) ∧
      (off = 2 ^ (s.cd + 1) ∨ off = 2 ^ (s.cd + 1) + 1))

/-- The path's frame run: the `4·pd` children, then the spare cells after the frame address. -/
def oqRun (s : Oq) (ch : ℕ) : List V :=
  ((List.range (4 * s.pd)).map fun j ↦ .n (ch + j)) ++
    ((List.range (80 - 4 * s.pd)).map fun j ↦ .n (ch + 4 * s.pd + 1 + j))

/-- **An atom of a query, by kind**: a load as `OqQLoad`, the path's `frameAddr`, or neither nor a
`HeapBuf`. -/
def OqAtomOk (s : Oq) (bp wp : V) (ch : ℕ) : Atom → Prop
  | .load _ p off => OqQLoad s bp wp ch p off
  | .frameAddr p run => p = .n (ch + 4 * s.pd) ∧ run = oqRun s ch
  | .hint (.alloc ..) => False
  | .hint (.allocDyn ..) => False
  | _ => True

/-- Every statement is an atom of the kind `P`. -/
def AtomsOk (P : Atom → Prop) (ss : List Stmt) : Prop := ∀ x ∈ ss, ∃ a, x = .atom a ∧ P a

theorem atomsOk_append {P : Atom → Prop} {ss ts : List Stmt} (h1 : AtomsOk P ss) (h2 : AtomsOk P ts) :
    AtomsOk P (ss ++ ts) :=
  fun x h ↦ (List.mem_append.mp h).elim (h1 x) (h2 x)

theorem atomsOk_flatten {P : Atom → Prop} {bs : List (List Stmt)} (h : ∀ b ∈ bs, AtomsOk P b) :
    AtomsOk P bs.flatten := fun x hm ↦ by
  obtain ⟨b, hb, hm⟩ := List.mem_flatten.mp hm
  exact h b hb x hm

theorem atomsOk_nil {P : Atom → Prop} : AtomsOk P [] := fun _ h ↦ absurd h (by simp)

/-- A singleton list of statements. -/
theorem atomsOk_cons {P : Atom → Prop} {a : Atom} {ss : List Stmt} (ha : P a) (h : AtomsOk P ss) :
    AtomsOk P (.atom a :: ss) := fun x hx ↦ by
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ⟨a, rfl, ha⟩
  · exact h x hx

section
variable (s : Oq) (bp wp : V) (ch : ℕ)

theorem ok_rowT (b R : ℕ) : AtomsOk (OqAtomOk s bp wp ch) (oqRowT b R) :=
  atomsOk_cons trivial atomsOk_nil

theorem ok_packsT (b R : ℕ) : AtomsOk (OqAtomOk s bp wp ch) (oqPacksT b R) := by
  refine atomsOk_flatten fun x hx ↦ ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
  exact atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial
    atomsOk_nil)))

theorem ok_padT (pr : ℕ) : AtomsOk (OqAtomOk s bp wp ch) (oqPadT pr) :=
  atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial
    (atomsOk_cons trivial atomsOk_nil))))

theorem ok_wordT (b jw t : ℕ) : AtomsOk (OqAtomOk s bp wp ch) (oqWordT s b jw t) := by
  unfold oqWordT
  split_ifs
  · exact atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial atomsOk_nil))
  · exact atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial atomsOk_nil))

theorem ok_leafT (b pr kL : ℕ) : AtomsOk (OqAtomOk s bp wp ch) (oqLeafT s b pr kL) := by
  refine atomsOk_flatten fun x hx ↦ ?_
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
  unfold oqBlockT
  split_ifs
  · exact atomsOk_cons trivial atomsOk_nil
  · refine atomsOk_append (atomsOk_flatten fun y hy ↦ ?_) (atomsOk_cons trivial atomsOk_nil)
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hy
    unfold oqXorT
    dsimp only
    split_ifs
    · exact atomsOk_cons trivial atomsOk_nil
    · exact atomsOk_cons trivial atomsOk_nil
    · exact atomsOk_cons trivial (atomsOk_cons trivial atomsOk_nil)

theorem ok_dotT (b : ℕ) : AtomsOk (OqAtomOk s bp wp ch) (oqDotT s wp b) := by
  refine atomsOk_flatten fun x hx ↦ ?_
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hx
  rw [List.mem_range] at hh
  unfold oqGroupT
  refine atomsOk_append (atomsOk_append (atomsOk_flatten fun y hy ↦ ?_)
    (atomsOk_cons (Or.inl ⟨rfl, by omega⟩) (atomsOk_cons trivial atomsOk_nil))) ?_
  · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hy
    rw [List.mem_range] at hl
    unfold oqTermT
    refine atomsOk_append (atomsOk_append ?_ (atomsOk_cons
      (Or.inl ⟨rfl, Nat.lt_of_lt_of_le hl (Nat.le_add_right _ _)⟩)
      (atomsOk_cons trivial atomsOk_nil))) ?_
    · split_ifs
      · exact atomsOk_nil
      · exact ok_wordT s bp wp ch _ _ _
    · split_ifs
      · exact atomsOk_nil
      · exact atomsOk_cons trivial atomsOk_nil
  · split_ifs
    · exact atomsOk_nil
    · exact atomsOk_cons trivial atomsOk_nil

theorem ok_pathT (pr kL : ℕ) : AtomsOk (OqAtomOk s bp wp ch) (oqPathT s bp pr kL ch) := by
  unfold oqPathT
  refine atomsOk_cons trivial (atomsOk_cons ⟨rfl, rfl⟩ (atomsOk_cons trivial (atomsOk_cons trivial
    (atomsOk_flatten fun y hy ↦ ?_))))
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hy
  rw [List.mem_range] at hl
  exact atomsOk_cons (Or.inr (Or.inl ⟨rfl, by omega⟩)) (atomsOk_cons trivial (atomsOk_cons trivial
    (atomsOk_cons (Or.inr (Or.inr (Or.inl ⟨l, hl, rfl, Or.inl rfl⟩)))
    (atomsOk_cons (Or.inr (Or.inr (Or.inl ⟨l, hl, rfl, Or.inr rfl⟩)))
    (atomsOk_cons trivial (atomsOk_cons trivial atomsOk_nil))))))

theorem ok_capT (hcd : 2 ≤ s.cd) (cap flags : V) (kL : ℕ) :
    AtomsOk (OqAtomOk s bp wp ch) (oqCapT s bp cap flags kL ch) := by
  unfold oqCapT
  refine atomsOk_append (atomsOk_append ?_ (atomsOk_flatten fun y hy ↦ ?_)) ?_
  · exact atomsOk_cons trivial (atomsOk_cons (Or.inr (Or.inl ⟨rfl, by omega⟩)) (atomsOk_cons trivial
      (atomsOk_cons trivial (atomsOk_cons trivial atomsOk_nil))))
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy
    rw [List.mem_range] at hj
    exact atomsOk_cons trivial (atomsOk_cons (Or.inr (Or.inl ⟨rfl, by omega⟩))
      (atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial
      (atomsOk_cons trivial atomsOk_nil)))))
  · refine atomsOk_cons trivial (atomsOk_cons trivial
      (atomsOk_cons (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))) ?_))
    refine atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial
      (atomsOk_cons (Or.inr (Or.inl ⟨rfl, by omega⟩)) ?_))))
    exact atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial
      (atomsOk_cons (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inl rfl⟩))))
      (atomsOk_cons (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr rfl⟩)))) atomsOk_nil)))))

end

/-- **Every statement of a query is an atom of its kind.** -/
theorem oqQuery_atoms_ok {s : Oq} (hcd : 2 ≤ s.cd) (bp cap flags wp : V) (b : ℕ) (emit : Bool)
    (pr : ℕ) : AtomsOk (OqAtomOk s bp wp (oqCh s b emit)) (oqQueryT s bp cap flags wp b emit pr) := by
  unfold oqQueryT
  refine atomsOk_append (atomsOk_append (atomsOk_append (atomsOk_append (atomsOk_append
    (atomsOk_append (ok_rowT _ _ _ _ _ _) (ok_packsT _ _ _ _ _ _)) (ok_dotT _ _ _ _ _)) ?_)
    (ok_leafT _ _ _ _ _ _ _)) (ok_pathT _ _ _ _ _ _)) (ok_capT _ _ _ _ hcd _ _ _)
  split_ifs
  · exact ok_padT _ _ _ _ _
  · exact atomsOk_nil

/-- The path's `frameAddr` is a statement of the query. -/
theorem oqQuery_frameAddr (s : Oq) (bp cap flags wp : V) (b : ℕ) (emit : Bool) (pr : ℕ) :
    Stmt.atom (.frameAddr (.n (oqCh s b emit + 4 * s.pd)) (oqRun s (oqCh s b emit))) ∈
      oqQueryT s bp cap flags wp b emit pr := by
  simp [oqQueryT, oqPathT, oqRun]

end
end LeanVM.Guest.B1
