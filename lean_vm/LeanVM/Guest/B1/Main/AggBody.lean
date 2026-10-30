/-
  LeanVM.Guest.B1.Main.AggBody

  `aggregate_claims`' body (core function `31`), checked by kernel evaluation, and its baked seed.
-/

module

public import LeanVM.Guest.B1.Main.AggSqueeze
public import LeanVM.Guest.Value.KeccakConst
public import LeanVM.Guest.B1.Main.Body
public import LeanVM.Guest.Batch.Def

/-!
# `aggregate_claims`' body

`aggregate_claims(n_children_g, child_pi, child_fresh, child_carried, defer_stmt)` (G:4229-4328):
its body is its block `aggP`, then `ret []` (`agg_shape`). `aggOk` checks the block: the batching
seed's capacity cells `AGG_SEED_*` and the packed count `n_children_g` with three zeros in row
`0` of `absorb` (`.n 60`), the guarded loop `__loop24` and its tables (`lf = .n 7`,
`lc = .n 8`), the permutation of the last absorbing row (`.n 69`, `aggKi`, `aggKo`) and the
challenge `λ` from it (`.n 106`, `challA`) with `λ²` (`.n 107`), record `0` of `bc_chain`
(`.n 111`: power `1`, claim `0`), the guarded loops `__loop25` and `__loop26` (weights
`w = .n 129`), `batch_sumcheck__L23` on the permutation's capacity with the rounds at `.n 5`, the
last record's claim and the point at `.n 120`, the check that its final claim is
`bc_star_hint (.n 6)` times the weight, and the claim written at `defer_stmt`.
`seed_cells`: the five constants are the capacity cells of `Node.batchSeed` (G3's
`aggSeed_cells`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

/-- `aggregate_claims`' block: its body without the final `ret []`. -/
noncomputable def aggP : List Stmt := (Fn.body Data.core29).dropLast

set_option maxRecDepth 100000 in
theorem agg_shape : Fn.body Data.core29 = aggP ++ [Stmt.ret []] :=
  stmtsEqb_sound (by decide +kernel)

/-- The seed's constants `(lo, hi)`. -/
def seedLo : List (ℕ × ℕ) :=
  [(1562680967124014521, 0), (7666384441264927334, 11925545048015809408),
    (14528471851986820829, 15194020773630548750), (6704907289165917069, 10885225211858021658),
    (10587785389206534793, 159208925504336485)]

/-- The permutation of the last absorbing row (`fs_perm_pending`): its rate cells (four copied),
then its capacity. -/
def aggKi : List V := [.n 75, .n 76, .n 77, .n 78, .n 83, .n 84, .n 85, .n 86, .n 70, .n 71, .n 72,
  .n 73, .n 74]

/-- The permutation's outputs. -/
def aggKo : List V := (List.range 13).map fun i => .n (87 + i)

/-- **`aggregate_claims`' block, checked.** -/
noncomputable def aggOk : Bool :=
  let P := aggP
  let A := atomsIn P
  P.all Stmt.flat && decide (Data.core29.params = [.n 0, .n 1, .n 2, .n 3, .n 4]) &&
  (List.range 5).all (fun i => A.any (isConstAt (.n (9 + i)) (seedLo.getD i (0, 0)).1
    (seedLo.getD i (0, 0)).2) && A.any (isLoadAt (.n (9 + i)) (.n 60) i)) &&
  packIn A (.n 0) 14 && A.any (isConstAt (.n 23) 0 0) && packIn A (.n 23) 24 &&
  A.any (isConstAt (.n 33) 0 0) && packIn A (.n 33) 34 &&
  A.any (isConstAt (.n 43) 0 0) && packIn A (.n 43) 44 &&
  (List.range 4).all (fun j => A.any (isLoadAt (.n (20 + 10 * j)) (.n 60) (5 + 2 * j)) &&
    A.any (isLoadAt (.n (22 + 10 * j)) (.n 60) (6 + 2 * j))) &&
  guardOk P (.n 62) "__loop24" (.n 63) (.n 0) [.n 60, .n 2, .n 7, .n 3, .n 8, .n 1] &&
  monoIs A (.n 69) (.n 60) (.n 0) 13 &&
  A.any (isKeccakAt aggKi aggKo false false) && rowInOk A (.n 69) aggKi &&
  allIn A (challA (.n 87) (.n 88) 100) && isMul A (.n 107) (.n 106) (.n 106) &&
  A.any (isConstAt (.n 112) 1 0) && A.any (isLoadAt (.n 112) (.n 111) 0) &&
  A.any (isConstAt (.n 113) 0 0) && A.any (isLoadAt (.n 113) (.n 111) 1) &&
  guardOk P (.n 115) "__loop25" (.n 116) (.n 0) [.n 111, .n 7, .n 8, .n 107, .n 106] &&
  monoIs A (.n 118) (.n 111) (.n 0) 2 && A.any (isLoadAt (.n 119) (.n 118) 1) &&
  hasCall P "batch_sumcheck__L23" [.n 95, .n 96, .n 97, .n 98, .n 99, .n 5, .n 119, .n 120]
    [.n 121, .n 122, .n 123, .n 124, .n 125, .n 126] &&
  A.any (isConstAt (.n 130) 0 0) && A.any (isLoadAt (.n 130) (.n 129) 0) &&
  guardOk P (.n 132) "__loop26" (.n 133) (.n 0) [.n 7, .n 8, .n 120, .n 111, .n 129, .n 106] &&
  isMul A (.n 134) (.n 129) (.n 0) && A.any (isLoadAt (.n 135) (.n 134) 0) &&
  isMul A (.n 136) (.n 6) (.n 135) && A.any (isAssertEqAt (.n 126) (.n 136)) &&
  (List.range 23).all (fun k => A.any (isLoadAt (.n (137 + k)) (.n 120) k) &&
    A.any (isLoadAt (.n (137 + k)) (.n 4) k)) &&
  A.any (isLoadAt (.n 6) (.n 4) 23)

set_option maxRecDepth 100000 in
theorem agg_ok : aggOk = true := by decide +kernel

/-- **The seed's constants are the batching seed's capacity cells.** -/
theorem seed_cells : ∀ i < 5,
    word (seedLo.getD i (0, 0)).1 (seedLo.getD i (0, 0)).2 0 = (capOf batchSeed).getD i 0 := by
  intro i hi
  have e := fun c : Fin 5 => aggSeed_cells c
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl
  · exact (e 0).trans rfl
  · exact (e 1).trans rfl
  · exact (e 2).trans rfl
  · exact (e 3).trans rfl
  · exact (e 4).trans rfl

end
end LeanVM.Guest.B1.Main
