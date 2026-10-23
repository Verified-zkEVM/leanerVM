/-
  LeanVM.Guest.B1.Opening.QueriesMain

  `opening_queries`: the soundness direction of its meaning, from its body and its loop's.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesLoop

/-!
# `opening_queries` is sound (G:1246-1269, TRIAGE #40)

`oqLoop_step`: the loop helper satisfies `loop_iff`'s step with its body of atoms
(`loop_step_atoms`). `oqMain1_sound`, `oqMain0_sound`: the function's relation, its loop's
iterations (`oqIter1_sound`, `oqIter0_sound`) and its start give `MeaningOpeningQueries`, the
bit pointers pointing to bits.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

/-- The loop's parameters. -/
def oqLoopParams : List V := [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7]

/-- A list literal of atoms. -/
macro "atoms_lit" : tactic => `(tactic| (repeat' apply allAtoms_cons) <;> exact allAtoms_nil)

/-- A list literal of atoms. -/
theorem allAtoms_of_forall {ss : List Stmt} (h : ∀ s ∈ ss, ∃ a, s = .atom a) : AllAtoms ss := h

theorem oqPadT_atoms (pr : ℕ) : AllAtoms (oqPadT pr) :=
  allAtoms_of_forall fun x hx => by simp [oqPadT] at hx; rcases hx with h | h | h | h | h <;> exact ⟨_, h⟩

theorem oqXorT_atoms (s : Oq) (b pr kL k c : ℕ) : AllAtoms (oqXorT s b pr kL k c) := by
  unfold oqXorT
  dsimp only
  split
  · exact allAtoms_cons allAtoms_nil
  · split
    · exact allAtoms_cons allAtoms_nil
    · exact allAtoms_cons (allAtoms_cons allAtoms_nil)

theorem oqBlockT_atoms (s : Oq) (b pr kL k : ℕ) : AllAtoms (oqBlockT s b pr kL k) := by
  unfold oqBlockT
  split
  · exact allAtoms_cons allAtoms_nil
  · exact allAtoms_append (allAtoms_map_flatten fun _ _ => oqXorT_atoms _ _ _ _ _ _)
      (allAtoms_cons allAtoms_nil)

theorem oqLeafT_atoms (s : Oq) (b pr kL : ℕ) : AllAtoms (oqLeafT s b pr kL) :=
  allAtoms_map_flatten fun _ _ => oqBlockT_atoms _ _ _ _ _

theorem oqLevelT_atoms (s : Oq) (bp : V) (pr kL ch l : ℕ) : AllAtoms (oqLevelT s bp pr kL ch l) :=
  allAtoms_of_forall fun x hx => by
    simp only [oqLevelT, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h | h | h | h | h <;> exact ⟨_, h⟩

theorem oqPathT_atoms (s : Oq) (bp : V) (pr kL ch : ℕ) : AllAtoms (oqPathT s bp pr kL ch) :=
  allAtoms_append (allAtoms_cons (allAtoms_cons (allAtoms_cons (allAtoms_cons allAtoms_nil))))
    (allAtoms_map_flatten fun _ _ => oqLevelT_atoms _ _ _ _ _ _)

theorem oqCapBitT_atoms (s : Oq) (bp : V) (ch j : ℕ) : AllAtoms (oqCapBitT s bp ch j) :=
  allAtoms_of_forall fun x hx => by
    simp only [oqCapBitT, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h | h | h | h <;> exact ⟨_, h⟩

theorem oqCapT_atoms (s : Oq) (bp cap flags : V) (kL ch : ℕ) : AllAtoms (oqCapT s bp cap flags kL ch) := by
  unfold oqCapT
  refine allAtoms_append (allAtoms_append ?_ (allAtoms_map_flatten fun _ _ => oqCapBitT_atoms _ _ _ _)) ?_
  all_goals atoms_lit

theorem oqQueryT_atoms (s : Oq) (bp cap flags wp : V) (b : ℕ) (emit : Bool) (pr : ℕ) :
    AllAtoms (oqQueryT s bp cap flags wp b emit pr) := by
  unfold oqQueryT
  refine allAtoms_append (allAtoms_append (allAtoms_append (allAtoms_append (allAtoms_append
    (allAtoms_append (oqRowT_atoms _ _) (oqPacksT_atoms _ _)) (oqDotT_atoms _ _ _)) ?_)
    (oqLeafT_atoms _ _ _ _)) (oqPathT_atoms _ _ _ _ _)) (oqCapT_atoms _ _ _ _ _ _)
  split
  · exact oqPadT_atoms _
  · exact allAtoms_nil

theorem atoms_list {ss : List Stmt} (h : ∀ s ∈ ss, ∃ a, s = .atom a) : AllAtoms ss := h

theorem oqLoop1A_atoms (s : Oq) (odd : ℕ) : AllAtoms (oqLoop1A s odd) := by
  unfold oqLoop1A
  dsimp only
  refine allAtoms_append (allAtoms_append (allAtoms_append (allAtoms_append ?_ (oqQueryT_atoms _ _ _ _ _ _ _ _))
    ?_) (oqQueryT_atoms _ _ _ _ _ _ _ _)) ?_
  all_goals atoms_lit

theorem oqLoop0A_atoms (s : Oq) : AllAtoms (oqLoop0A s) := by
  unfold oqLoop0A
  dsimp only
  refine allAtoms_append (allAtoms_append ?_ (oqQueryT_atoms _ _ _ _ _ _ _ _)) ?_
  all_goals atoms_lit

theorem oqMainA_atoms (s : Oq) (odd : ℕ) : AllAtoms (oqMainA s odd) := by
  unfold oqMainA
  dsimp only
  refine allAtoms_append (allAtoms_append ?_ ?_) ?_
  · atoms_lit
  · split
    · exact allAtoms_append (allAtoms_append (allAtoms_cons allAtoms_nil) (oqQueryT_atoms _ _ _ _ _ _ _ _))
        (allAtoms_cons (allAtoms_cons allAtoms_nil))
    · exact allAtoms_cons (allAtoms_cons allAtoms_nil)
  · exact allAtoms_cons (allAtoms_cons (allAtoms_cons allAtoms_nil))

/-! ## The loop's step -/

theorem oqLoop1_step {s : Oq} {odd : ℕ} {loop : String} {fl : Fn}
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop1T s odd loop) (ps : List E) (hps : ps.length = 7) :
    ∀ d x, coreProgram.relN rd (d + 1) loop (x :: ps) [] ↔
      AtomsBody rd fl.params (oqLoop1A s odd) (x :: ps) ∧ IsInK (x * gen + ps.headD 0) ∧
        (x * gen + ps.headD 0 ≠ 0 → coreProgram.relN rd d loop (x * gen :: ps) []) := by
  intro d x
  obtain ⟨N, rest, rfl⟩ : ∃ N rest, ps = N :: rest := by
    match ps, hps with
    | N :: rest, _ => exact ⟨N, rest, rfl⟩
  refine loop_step_atoms hfl hbl (oqLoop1A_atoms s odd) (fun σ hp hA => ?_) d
  rw [hpl] at hp
  simp only [oqLoopParams, List.map_cons, List.map_nil] at hp
  set c := oqC1 s with hc
  have a7 := hA _ (by simp [oqLoop1A, ← hc] : Stmt.atom (.const (.n (c + 7)) (word 2 0 0)) ∈ _)
  have a8 := hA _ (by simp [oqLoop1A, ← hc] : Stmt.atom (.mul (.n (c + 8)) (.n 0) (.n (c + 7))) ∈ _)
  have a9 := hA _ (by simp [oqLoop1A, ← hc] : Stmt.atom (.add (.n (c + 9)) (.n (c + 8)) (.n 1)) ∈ _)
  have a10 := hA _ (by simp [oqLoop1A, ← hc] : Stmt.atom (.const (.n (c + 10)) (word 2 0 0)) ∈ _)
  have a11 := hA _ (by simp [oqLoop1A, ← hc] :
    Stmt.atom (.mul (.n (c + 11)) (.n 0) (.n (c + 10))) ∈ _)
  simp only [Atom.Holds] at a7 a8 a9 a10 a11
  simp only [List.cons.injEq] at hp
  obtain ⟨h0, h1, hr⟩ := hp
  subst hr
  refine ⟨by rw [a9, a8, a7, word_gen, h0, h1], ?_⟩
  simp [a11, a10, word_gen, h0, h1]

theorem oqLoop0_step {s : Oq} {loop : String} {fl : Fn}
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop0T s loop) (ps : List E) (hps : ps.length = 7) :
    ∀ d x, coreProgram.relN rd (d + 1) loop (x :: ps) [] ↔
      AtomsBody rd fl.params (oqLoop0A s) (x :: ps) ∧ IsInK (x * gen + ps.headD 0) ∧
        (x * gen + ps.headD 0 ≠ 0 → coreProgram.relN rd d loop (x * gen :: ps) []) := by
  intro d x
  obtain ⟨N, rest, rfl⟩ : ∃ N rest, ps = N :: rest := by
    match ps, hps with
    | N :: rest, _ => exact ⟨N, rest, rfl⟩
  refine loop_step_atoms hfl hbl (oqLoop0A_atoms s) (fun σ hp hA => ?_) d
  rw [hpl] at hp
  simp only [oqLoopParams, List.map_cons, List.map_nil] at hp
  set c := oqC0 s with hc
  have a5 := hA _ (by simp [oqLoop0A, ← hc] : Stmt.atom (.const (.n (c + 5)) (word 2 0 0)) ∈ _)
  have a6 := hA _ (by simp [oqLoop0A, ← hc] : Stmt.atom (.mul (.n (c + 6)) (.n 0) (.n (c + 5))) ∈ _)
  have a7 := hA _ (by simp [oqLoop0A, ← hc] : Stmt.atom (.add (.n (c + 7)) (.n (c + 6)) (.n 1)) ∈ _)
  have a8 := hA _ (by simp [oqLoop0A, ← hc] : Stmt.atom (.const (.n (c + 8)) (word 2 0 0)) ∈ _)
  have a9 := hA _ (by simp [oqLoop0A, ← hc] :
    Stmt.atom (.mul (.n (c + 9)) (.n 0) (.n (c + 8))) ∈ _)
  simp only [Atom.Holds] at a5 a6 a7 a8 a9
  simp only [List.cons.injEq] at hp
  obtain ⟨h0, h1, hr⟩ := hp
  subst hr
  refine ⟨by rw [a7, a6, a5, word_gen, h0, h1], ?_⟩
  simp [a9, a8, word_gen, h0, h1]

end
end LeanVM.Guest.B1
