/-
  LeanVM.Guest.B1.Sig.SpWotsPadComplete

  A block written with its padding run at `b`, below its own values, completes moved where the
  compiler allocates the run: renamed (the run to `P`, every value from `P` on five up) and the run's
  five constants inserted.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsLayout
public import LeanVM.Guest.B1.Sig.CompleteBasic

/-!
# The padding run, moved

`sp_wots`'s template writes each arm with its padding run virtual (`withPad`). For completeness the
arm is evaluated with the run at the group's own digit cells `b ..< b + 5` (unused by its arms,
below their values), where the shared WOTS+C lemmas apply; then moved:

* `padC`, `padRen b P`: the run's constants; the renaming moving the run at `b` to `P` and every
  value from `P` on five up;
* `padVal σ σ1 b P lo hi`: the valuation the moved block holds of: `σ1` read through the renaming
  on `lo ..< hi`, `σ` elsewhere;
* `padMove_completes`: the moved block, the run inserted anywhere, completes on `lo ..< hi` from
  `σ`, when the block's atoms hold of `σ1` (its run's constants at `b`, `σ` below `lo` elsewhere).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- The padding run's constant `j`: `0x01`, then zeros. -/
def padC (j : Nat) : E := word (if j = 0 then 1 else 0) 0 0

/-- The renaming moving a run at `b` to `P` and every value from `P` on five up. -/
def padRen (b P : Nat) (v : V) : V :=
  if v.path = [] ∧ v.tag = 0 then
    .n (if b ≤ v.idx ∧ v.idx < b + 5 then P + (v.idx - b) else if P ≤ v.idx then v.idx + 5 else v.idx)
  else v

theorem padRen_n (b P k : Nat) : padRen b P (.n k) =
    .n (if b ≤ k ∧ k < b + 5 then P + (k - b) else if P ≤ k then k + 5 else k) := by
  simp [padRen]

/-- The valuation the moved block holds of. -/
def padVal (σ σ1 : Val) (b P lo hi : Nat) : Val := fun v =>
  if v.path = [] ∧ v.tag = 0 ∧ lo ≤ v.idx ∧ v.idx < hi then
    (if v.idx < P then σ1 (.n v.idx) else if v.idx < P + 5 then σ1 (.n (b + (v.idx - P)))
      else σ1 (.n (v.idx - 5)))
  else σ v

theorem padVal_n (σ σ1 : Val) (b P lo hi k : Nat) : padVal σ σ1 b P lo hi (.n k) =
    if lo ≤ k ∧ k < hi then
      (if k < P then σ1 (.n k) else if k < P + 5 then σ1 (.n (b + (k - P))) else σ1 (.n (k - 5)))
    else σ (.n k) := by
  simp [padVal]

theorem padVal_ext (σ σ1 : Val) (b P lo hi : Nat) : Ext lo hi σ (padVal σ σ1 b P lo hi) := by
  intro v hv
  have h : ¬ (v.path = [] ∧ v.tag = 0 ∧ lo ≤ v.idx ∧ v.idx < hi) := fun ⟨h1, h2, h3, h4⟩ =>
    hv v.idx h3 h4 (by cases v; simp_all)
  simp only [padVal, h, ↓reduceIte]

theorem padRun_atoms (P : Nat) : atomsOnly (padRun P) = true := by
  simp [padRun, List.range_succ, cst, atomsOnly]

theorem atomsOnly_append' {xs ys : List Stmt} (hx : atomsOnly xs = true) (hy : atomsOnly ys = true) :
    atomsOnly (xs ++ ys) = true := by
  induction xs with
  | nil => exact hy
  | cons x xs ih =>
      cases x <;> simp_all [atomsOnly]

theorem atomsOnly_renameList (r : V → V) : ∀ {ss : List Stmt}, atomsOnly ss = true →
    atomsOnly (Stmt.renameList r ss) = true
  | [], _ => rfl
  | .atom _ :: ss, h => by
      simp only [Stmt.renameList, Stmt.rename, atomsOnly] at h ⊢
      exact atomsOnly_renameList r h
  | .ite .. :: _, h | .match_ .. :: _, h | .call .. :: _, h | .callIf .. :: _, h
  | .dispatch .. :: _, h | .ret _ :: _, h => by simp [atomsOnly] at h

theorem atomsOnly_take {ss : List Stmt} (h : atomsOnly ss = true) (i : Nat) :
    atomsOnly (ss.take i) = true := by
  induction ss generalizing i with
  | nil => simp [atomsOnly]
  | cons s ss ih =>
      cases i with
      | zero => rfl
      | succ i => cases s <;> simp_all [atomsOnly]

theorem atomsOnly_drop {ss : List Stmt} (h : atomsOnly ss = true) (i : Nat) :
    atomsOnly (ss.drop i) = true := by
  induction ss generalizing i with
  | nil => simp [atomsOnly]
  | cons s ss ih =>
      cases i with
      | zero => exact h
      | succ i => cases s <;> simp_all [atomsOnly]

theorem mem_renameList_atom {r : V → V} : ∀ {ss : List Stmt} {a : Atom}, atomsOnly ss = true →
    Stmt.atom a ∈ Stmt.renameList r ss → ∃ a0, Stmt.atom a0 ∈ ss ∧ a = a0.rename r
  | [], _, _, h => absurd h (by simp [Stmt.renameList])
  | .atom b :: ss, a, hs, h => by
      simp only [Stmt.renameList, Stmt.rename, List.mem_cons, Stmt.atom.injEq] at h
      rcases h with rfl | h
      · exact ⟨b, List.mem_cons_self .., rfl⟩
      · obtain ⟨a0, h0, e⟩ := mem_renameList_atom (r := r) (by simpa [atomsOnly] using hs) h
        exact ⟨a0, List.mem_cons_of_mem _ h0, e⟩
  | .ite .. :: _, _, h, _ | .match_ .. :: _, _, h, _ | .call .. :: _, _, h, _
  | .callIf .. :: _, _, h, _ | .dispatch .. :: _, _, h, _ | .ret _ :: _, _, h, _ => by
      simp [atomsOnly] at h

/-- The moved valuation, read through the renaming, is `σ1` on the block's values. -/
theorem padVal_ren {σ σ1 : Val} {b P lo E hi : Nat} (hP : lo ≤ P) (hPE : P ≤ E)
    (hhi : E + 5 ≤ hi) (hag : ∀ j < lo, (j < b ∨ b + 5 ≤ j) → σ1 (.n j) = σ (.n j)) {j : Nat}
    (hj : j < E) : padVal σ σ1 b P lo hi (padRen b P (.n j)) = σ1 (.n j) := by
  rw [padRen_n]
  by_cases h1 : b ≤ j ∧ j < b + 5
  · have e1 : lo ≤ P + (j - b) ∧ P + (j - b) < hi := by omega
    have e2 : ¬ P + (j - b) < P := by omega
    have e3 : P + (j - b) < P + 5 := by omega
    simp only [h1, and_self, ↓reduceIte, padVal_n, e1, e2, e3]
    congr 2; omega
  · by_cases h2 : P ≤ j
    · have e1 : lo ≤ j + 5 ∧ j + 5 < hi := by omega
      have e2 : ¬ j + 5 < P := by omega
      have e3 : ¬ j + 5 < P + 5 := by omega
      simp only [h1, h2, ↓reduceIte, padVal_n, e1, e2, e3, Nat.add_sub_cancel, and_self]
    · by_cases h3 : lo ≤ j
      · have e1 : lo ≤ j ∧ j < hi := by omega
        have e2 : j < P := by omega
        simp only [h1, h2, ↓reduceIte, padVal_n, e1, e2, and_self]
      · have e1 : ¬ (lo ≤ j ∧ j < hi) := by omega
        simp only [h1, h2, ↓reduceIte, padVal_n, e1]
        exact (hag j (by omega) (by omega)).symm

theorem padVal_run {σ σ1 : Val} {b P lo E hi : Nat} (hP : lo ≤ P) (hPE : P ≤ E) (hhi : E + 5 ≤ hi)
    {j : Nat} (hj : j < 5) : padVal σ σ1 b P lo hi (.n (P + j)) = σ1 (.n (b + j)) := by
  have e1 : lo ≤ P + j ∧ P + j < hi := by omega
  have e2 : ¬ P + j < P := by omega
  have e3 : P + j < P + 5 := by omega
  simp only [padVal_n, e1, e2, e3, and_self, ↓reduceIte, Nat.add_sub_cancel_left]

/-- **The moved block completes**: a block of atoms with its run at `b`, holding of `σ1` (the run's
constants at `b`, `σ` below `lo` elsewhere), renamed by `padRen b P` and the run inserted anywhere,
completes on `lo ..< hi` from `σ`, its valuation `σ1` read through the renaming. -/
theorem padMove_completes {L : List Stmt} (hat : atomsOnly L = true) {b P lo E hi : Nat}
    (hP : lo ≤ P) (hPE : P ≤ E) (hhi : E + 5 ≤ hi)
    (hv : ∀ v ∈ Stmt.valsList L, ∃ j, v = .n j ∧ j < E) {σ σ1 : Val}
    (hpad : ∀ j < 5, σ1 (.n (b + j)) = padC j)
    (hag : ∀ j < lo, (j < b ∨ b + 5 ≤ j) → σ1 (.n j) = σ (.n j)) (hh : AtomsHold rd σ1 L)
    (i : Nat) :
    Completes C rd lo hi ((Stmt.renameList (padRen b P) L).take i ++ padRun P ++
        (Stmt.renameList (padRen b P) L).drop i) σ
      (fun σ' => σ' = padVal σ σ1 b P lo hi) := by
  have hren : atomsOnly (Stmt.renameList (padRen b P) L) = true := atomsOnly_renameList _ hat
  refine completes_atoms (atomsOnly_append' (atomsOnly_append' (atomsOnly_take hren i)
    (padRun_atoms P)) (atomsOnly_drop hren i)) (padVal_ext σ σ1 b P lo hi) rfl (fun a ha => ?_)
  have hmain : ∀ a, Stmt.atom a ∈ Stmt.renameList (padRen b P) L →
      a.Holds rd (padVal σ σ1 b P lo hi) := by
    intro a ha
    obtain ⟨a0, h0, rfl⟩ := mem_renameList_atom hat ha
    rw [Atom.holds_rename]
    refine (atom_congr a0 fun v hva => ?_).mpr (hh a0 h0)
    obtain ⟨j, rfl, hj⟩ := hv v (mem_valsList_of_mem h0 hva)
    exact padVal_ren hP hPE hhi hag hj
  simp only [List.mem_append] at ha
  rcases ha with (ha | ha) | ha
  · exact hmain a (List.mem_of_mem_take ha)
  · simp only [padRun, List.mem_map, List.mem_range, cst, Stmt.atom.injEq] at ha
    obtain ⟨k, hk, rfl⟩ := ha
    show padVal σ σ1 b P lo hi (.n (P + k)) = _
    rw [padVal_run hP hPE hhi hk, hpad k hk]
    rfl
  · exact hmain a (List.mem_of_mem_drop ha)

end
end LeanVM.Guest.B1.Sig
