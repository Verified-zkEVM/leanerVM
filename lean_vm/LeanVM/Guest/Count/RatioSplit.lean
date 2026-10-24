/-
  LeanVM.Guest.Count.RatioSplit

  A ratio subtree's closure check of one large function, in pieces of its body: each piece's
  callees by index, checked on its own, the pieces appended.
-/

module

public import LeanVM.Guest.Count.RatioBase

namespace LeanVM.Guest.Count

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B2C

@[expose] public section

/-- Function `i`'s body. -/
noncomputable def krBody (i : ℕ) : List Stmt := ((coreProgram[i]?).getD default).body

/-- **The statements `[a, a + n)` of function `i`'s body call the functions of indices `L`**, all
in `J`. -/
noncomputable def krPiece (J : List ℕ) (i a n : ℕ) (L : List ℕ) : Bool :=
  (Stmt.blockCallees (((krBody i).drop a).take n) == L.map krName) &&
    L.all fun k => decide (k ∈ J) && Nat.blt k 899

theorem blockCallees_append : ∀ a b : List Stmt,
    Stmt.blockCallees (a ++ b) = Stmt.blockCallees a ++ Stmt.blockCallees b
  | [], _ => rfl
  | s :: a, b => by
    rw [List.cons_append, Stmt.blockCallees, Stmt.blockCallees, blockCallees_append a b,
      List.append_assoc]

theorem krPiece_append {J : List ℕ} {i a n m : ℕ} {L1 L2 : List ℕ} (h1 : krPiece J i a n L1 = true)
    (h2 : krPiece J i (a + n) m L2 = true) : krPiece J i a (n + m) (L1 ++ L2) = true := by
  simp only [krPiece, Bool.and_eq_true, beq_iff_eq] at h1 h2 ⊢
  refine ⟨?_, by rw [List.all_append, h1.2, h2.2]; rfl⟩
  rw [List.take_add, List.drop_drop, blockCallees_append, h1.1, h2.1, List.map_append]

theorem krClosedAt_of_piece {J : List ℕ} {C : ℕ → List ℕ} {i n : ℕ}
    (h : krPiece J i 0 n (C i) = true) (hn : (krBody i).length ≤ n) : krClosedAt J C i = true := by
  simp only [krPiece, List.drop_zero, List.take_of_length_le hn] at h
  exact h

end
end LeanVM.Guest.Count
