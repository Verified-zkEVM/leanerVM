/-
  LeanVM.Guest.B1.Opening.QueriesPlaced1

  The statements of `opening_queries`' templates, by kind: their loads and where they read, no
  `frameAddr` and no `HeapBuf` in a query.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesMain
public import LeanVM.Guest.Memory.Straight
public import LeanVM.Guest.B1.Opening.WalkMatch

/-!
# The statements of `opening_queries`, by kind

The placed form (`RelAtIn`) needs, of a body, its `HeapBuf`s, its `frameAddr`s (a query has
none), its calls and where its loads read. `OqAtomOk`: an atom of a query is a load reading the weights
(`wp`, below `lo + I/lo`), its windows (`bp`, below `npw + 2`: the path's and the cap's two), the
flag (`.n (Cq + 2)` at `2^(cd-1)`) or the cap leaf (`.n (Cq + 8)` at `2^(cd+1)`, `+ 1`), or
neither a load, a `frameAddr` nor a `HeapBuf`. `AtomsOk`: every statement is such an atom or a
`match` of quiet arms (`walk_window`: keccaks, constants, copies). `oqQuery_atoms_ok`: every
statement of a query is.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- A load of a query: its pointer and offset: the weights, the windows (the path's and the cap's
two), the flag, the cap leaf. -/
def OqQLoad (s : Oq) (bp wp : V) (ch : ℕ) (p : V) (off : ℕ) : Prop :=
  (p = wp ∧ off < s.lo + s.I / s.lo) ∨ (p = bp ∧ off < oqNpw s + 2) ∨
    (p = .n (oqCq s ch + 2) ∧ off = 2 ^ (s.cd - 1)) ∨
    (p = .n (oqCq s ch + 8) ∧ (off = 2 ^ (s.cd + 1) ∨ off = 2 ^ (s.cd + 1) + 1))

/-- **An atom by kind**: a load whose pointer and offset satisfy `L`, a `frameAddr` whose pointer
and run satisfy `F`, or neither a load, a `frameAddr` nor a `HeapBuf`. -/
def AtomKind (L : V → ℕ → Prop) (F : V → List V → Prop) : Atom → Prop
  | .load _ p off => L p off
  | .frameAddr p run => F p run
  | .hint (.alloc ..) => False
  | .hint (.allocDyn ..) => False
  | _ => True

theorem AtomKind.mono {L L' : V → ℕ → Prop} {F F' : V → List V → Prop}
    (hL : ∀ p off, L p off → L' p off) (hF : ∀ p run, F p run → F' p run) {a : Atom}
    (h : AtomKind L F a) : AtomKind L' F' a := by
  cases a with
  | load _ p off => exact hL p off h
  | frameAddr p run => exact hF p run h
  | hint hh => cases hh <;> exact h
  | _ => exact h

/-- **An atom of a query, by kind**: a load as `OqQLoad`, or neither a load, a `frameAddr` nor a
`HeapBuf`. -/
abbrev OqAtomOk (s : Oq) (bp wp : V) (ch : ℕ) : Atom → Prop :=
  AtomKind (OqQLoad s bp wp ch) (fun _ _ ↦ False)

/-- Every statement is an atom of the kind `P`, or a `match` of quiet atom arms (fewer than
`2^64`). -/
def AtomsOk (P : Atom → Prop) (ss : List Stmt) : Prop :=
  ∀ x ∈ ss, (∃ a, x = .atom a ∧ P a) ∨
    ∃ y arms, x = .match_ y arms ∧ Stmt.flatM (.match_ y arms) = true ∧ arms.length ≤ 2 ^ 64 - 1

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
  · exact Or.inl ⟨a, rfl, ha⟩
  · exact h x hx

theorem atomsOk_match {P : Atom → Prop} {y : V} {arms : List (List Stmt)} {ss : List Stmt}
    (ha : Stmt.flatM (.match_ y arms) = true) (hl : arms.length ≤ 2 ^ 64 - 1) (h : AtomsOk P ss) :
    AtomsOk P (.match_ y arms :: ss) := fun x hx ↦ by
  rcases List.mem_cons.mp hx with rfl | hx
  · exact Or.inr ⟨y, arms, rfl, ha, hl⟩
  · exact h x hx

theorem AtomsOk.flatM {P : Atom → Prop} {ss : List Stmt} (h : AtomsOk P ss) :
    ss.all Stmt.flatM = true := by
  rw [List.all_eq_true]
  intro x hx
  rcases h x hx with ⟨a, rfl, -⟩ | ⟨y, arms, rfl, hm, -⟩
  · rfl
  · exact hm

theorem oqStepT_quiet (pr ch l K n0 n1 : ℕ) (bit : Bool) :
    (oqStepT pr ch l K n0 n1 bit).all Stmt.quietS = true := by
  cases bit <;> rfl

theorem oqArmT_quiet (s : Oq) (pr kL ch i a : ℕ) : (oqArmT s pr kL ch i a).all Stmt.quietS = true := by
  rw [List.all_eq_true]
  intro x hx
  simp only [oqArmT, List.mem_append, List.mem_flatten, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with ⟨_, ⟨r, -, rfl⟩, hx⟩ | rfl | rfl
  · exact List.all_eq_true.mp (oqStepT_quiet ..) x hx
  · rfl
  · rfl

theorem oqWin_match_flatM (s : Oq) (pr kL ch i : ℕ) :
    Stmt.flatM (.match_ (.n (oqWk s ch i)) ((List.range (2 ^ oqWw s i)).map (oqArmT s pr kL ch i))) =
      true := by
  simp only [Stmt.flatM, List.all_eq_true, List.mem_map, List.mem_range]
  rintro _ ⟨a, -, rfl⟩
  exact List.all_eq_true.mp (oqArmT_quiet s pr kL ch i a)

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
  refine atomsOk_cons trivial (atomsOk_flatten fun y hy ↦ ?_)
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
  rw [List.mem_range] at hi
  exact atomsOk_cons (Or.inr (Or.inl ⟨rfl, by omega⟩)) (atomsOk_cons trivial
    (atomsOk_match (oqWin_match_flatM s pr kL ch i) (by
      rw [List.length_map, List.length_range]
      exact le_trans (Nat.pow_le_pow_right (by norm_num) (oqWw_le s i)) (by norm_num))
      atomsOk_nil))

theorem ok_capT (cap flags : V) (kL : ℕ) :
    AtomsOk (OqAtomOk s bp wp ch) (oqCapT s bp cap flags kL ch) := by
  unfold oqCapT
  exact atomsOk_cons (Or.inr (Or.inl ⟨rfl, by omega⟩)) (atomsOk_cons (Or.inr (Or.inl ⟨rfl, by omega⟩))
    (atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    (atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial
    (atomsOk_cons trivial (atomsOk_cons (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inl rfl⟩)))
    (atomsOk_cons (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr rfl⟩))) atomsOk_nil)))))))))))

end

/-- **Every statement of a query is an atom of its kind.** -/
theorem oqQuery_atoms_ok {s : Oq} (bp cap flags wp : V) (b : ℕ) (emit : Bool)
    (pr : ℕ) : AtomsOk (OqAtomOk s bp wp (oqCh s b emit)) (oqQueryT s bp cap flags wp b emit pr) := by
  unfold oqQueryT
  refine atomsOk_append (atomsOk_append (atomsOk_append (atomsOk_append (atomsOk_append
    (atomsOk_append (ok_rowT _ _ _ _ _ _) (ok_packsT _ _ _ _ _ _)) (ok_dotT _ _ _ _ _)) ?_)
    (ok_leafT _ _ _ _ _ _ _)) (ok_pathT _ _ _ _ _ _)) (ok_capT _ _ _ _ _ _ _)
  split_ifs
  · exact ok_padT _ _ _ _ _
  · exact atomsOk_nil

end
end LeanVM.Guest.B1
