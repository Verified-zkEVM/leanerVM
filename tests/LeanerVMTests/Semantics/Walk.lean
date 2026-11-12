import LeanerVM.Semantics.Walk

/-!
# Tests: walks in a balanced functional graph

`exists_walksIn` on a small graph over `Fin 4`: a path `0 → 1 → 2` and a loop `3 → 3`, with
no edge out of `2`. The edges are those of `[0, 1, 3]`, the start `0` and the end `2`. The lemma
finds a walk; every walk from `0` to `2` takes the path's two steps, and the loop, a closed
walk, is off it. Without the edge out of `1` the graph is not balanced, so the lemma does not
apply.
-/

namespace LeanerVMTests.Semantics.Walk

open LeanerVM.Semantics

/-- The path `0 → 1 → 2` and the loop `3 → 3`; `2` has no successor. -/
def f : Fin 4 → Option (Fin 4)
  | 0 => some 1
  | 1 => some 2
  | 2 => none
  | 3 => some 3

/-- The graph is balanced from `0` to `2`. -/
theorem balanced : ((0 : Fin 4) :: [0, 1, 3].filterMap f).Perm (2 :: [0, 1, 3]) := by decide

/-- The lemma finds a walk of at most three steps. -/
example : ∃ n ≤ 3, WalksIn f [0, 1, 3] n 0 2 := exists_walksIn balanced

/-- The path is such a walk. -/
example : WalksIn f [0, 1, 3] 2 0 2 := ⟨by decide, 1, rfl, by decide, 2, rfl, rfl⟩

/-- Every walk from `0` to `2` takes exactly the path's two steps: the loop is not on it. -/
example (n : ℕ) (h : WalksIn f [0, 1, 3] n 0 2) : n = 2 := by
  rcases n with _ | _ | _ | n
  · exact absurd h (show (0 : Fin 4) ≠ 2 by decide)
  · obtain ⟨-, s, hs, h⟩ := h
    cases hs
    exact absurd h (show (1 : Fin 4) ≠ 2 by decide)
  · rfl
  · obtain ⟨-, s, hs, -, s', hs', -, s'', hs'', -⟩ := h
    cases hs
    cases hs'
    cases hs''

/-- Without the edge out of `1` the graph is not balanced. -/
example : ¬ ((0 : Fin 4) :: [0, 3].filterMap f).Perm (2 :: [0, 3]) := by decide

end LeanerVMTests.Semantics.Walk
