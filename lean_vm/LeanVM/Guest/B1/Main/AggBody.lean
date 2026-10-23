/-
  LeanVM.Guest.B1.Main.AggBody

  `aggregate_claims`' body (core function `31`), checked by kernel evaluation, and its baked seed.
-/

module

public import LeanVM.Guest.B1.Main.AggSqueeze
public import LeanVM.Guest.Value.KeccakConst
public import LeanVM.Guest.B1.Main.Body

/-!
# `aggregate_claims`' body

`aggregate_claims(n_children_g, child_pi, child_fresh, child_carried, defer_stmt)` (G:4295-4360):
its body is its block `aggP`, then `ret []` (`agg_shape`). `aggOk` checks the block: the batching
seed's capacity cells `AGG_SEED_*` and the packed count `n_children_g` with three zeros in row
`0` of `absorb` (`.n 60`), the guarded loops `__loop25`, `__loop26`, `__loop27` and their tables
(`lf = .n 7`, `lc = .n 8`, `lam = .n 71`, `sq = .n 79`, `w = .n 118`), the copy of the last
absorbing row into row `0` of `sq` (running claim `0`), `batch_sumcheck__L23` on the last
squeezing row with the rounds at `.n 5` and the point at `.n 104`, the check that its final claim
is `bc_star_hint (.n 6)` times the weight, and the claim written at `defer_stmt`.
`seed_cells`: the five constants are the capacity cells of `Node.batchSeed` (G3's
`aggSeed_cells`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

/-- `aggregate_claims`' block: its body without the final `ret []`. -/
noncomputable def aggP : List Stmt := (Fn.body Data.core31).dropLast

set_option maxRecDepth 100000 in
theorem agg_shape : Fn.body Data.core31 = aggP ++ [Stmt.ret []] :=
  stmtsEqb_sound (by decide +kernel)

/-- The seed's constants `(lo, hi)`. -/
def seedLo : List (ℕ × ℕ) :=
  [(1562680967124014521, 0), (7666384441264927334, 11925545048015809408),
    (14528471851986820829, 15194020773630548750), (6704907289165917069, 10885225211858021658),
    (10587785389206534793, 159208925504336485)]

/-- **`aggregate_claims`' block, checked.** -/
noncomputable def aggOk : Bool :=
  let P := aggP
  let A := atomsIn P
  P.all Stmt.flat && decide (Data.core31.params = [.n 0, .n 1, .n 2, .n 3, .n 4]) &&
  (List.range 5).all (fun i => A.any (isConstAt (.n (9 + i)) (seedLo.getD i (0, 0)).1
    (seedLo.getD i (0, 0)).2) && A.any (isLoadAt (.n (9 + i)) (.n 60) i)) &&
  packIn A (.n 0) 14 && A.any (isConstAt (.n 23) 0 0) && packIn A (.n 23) 24 &&
  A.any (isConstAt (.n 33) 0 0) && packIn A (.n 33) 34 &&
  A.any (isConstAt (.n 43) 0 0) && packIn A (.n 43) 44 &&
  (List.range 4).all (fun j => A.any (isLoadAt (.n (20 + 10 * j)) (.n 60) (5 + 2 * j)) &&
    A.any (isLoadAt (.n (22 + 10 * j)) (.n 60) (6 + 2 * j))) &&
  guardOk P (.n 62) "__loop25" (.n 63) (.n 0) [.n 60, .n 2, .n 7, .n 3, .n 8, .n 1] &&
  monoIs A (.n 69) (.n 60) (.n 0) 13 &&
  (List.range 13).all (fun k => A.any (isLoadAt (.n (80 + k)) (.n 69) k) &&
    A.any (isLoadAt (.n (80 + k)) (.n 79) k)) &&
  A.any (isConstAt (.n 93) 0 0) && A.any (isLoadAt (.n 93) (.n 79) 13) &&
  guardOk P (.n 95) "__loop26" (.n 96) (.n 0) [.n 79, .n 71, .n 7, .n 8] &&
  monoIs A (.n 102) (.n 79) (.n 0) 14 && A.any (isLoadAt (.n 103) (.n 102) 13) &&
  (List.range 5).all (fun i => A.any (isLoadAt (.n (105 + i)) (.n 102) i)) &&
  hasCall P "batch_sumcheck__L23" [.n 105, .n 106, .n 107, .n 108, .n 109, .n 5, .n 103, .n 104]
    [.n 110, .n 111, .n 112, .n 113, .n 114, .n 115] &&
  A.any (isConstAt (.n 119) 0 0) && A.any (isLoadAt (.n 119) (.n 118) 0) &&
  guardOk P (.n 121) "__loop27" (.n 122) (.n 0) [.n 7, .n 8, .n 104, .n 118, .n 71] &&
  isMul A (.n 123) (.n 118) (.n 0) && A.any (isLoadAt (.n 124) (.n 123) 0) &&
  isMul A (.n 125) (.n 6) (.n 124) && A.any (isAssertEqAt (.n 115) (.n 125)) &&
  (List.range 23).all (fun k => A.any (isLoadAt (.n (126 + k)) (.n 104) k) &&
    A.any (isLoadAt (.n (126 + k)) (.n 4) k)) &&
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
