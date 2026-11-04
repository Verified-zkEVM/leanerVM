/-
  LeanVM.Guest.B1.Main.Body

  `main`'s body (G:4375-4551): its shape and its facts checked by evaluation.
-/

module

public import LeanVM.Guest.B1.Main.Loops

/-!
# `main`'s body

`Data.core0`'s body is a flat block (`mPre`: the counts and their range checks, the exponent
tables, the claim list digests, the byte table, the raw signatures' loops, `da_digests`), the
direct DA check behind `n_direct_da == g` (`mDa`: `da_verify`, then its claim's digest stored at
`own_da`) or the zero digest stored there (`mDaZ`), a flat block (`mMid`: the children's loop, the
final count, `da_pick` and its two checks), the leaf's deferred claim or the batching behind
`n_children == 1` (`mLeaf`, `mAgg`), and a flat block (`mPost`: the statement's digest against
the public input) (`core0_shape`). `preOk`, `daOk`, `daZOk`, `midOk`, `leafOk`, `postOk` check
every fact the proof reads, by evaluation.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

/-! ## The shape -/

noncomputable def mPre : List Stmt := (Fn.body Data.core0).take 571
noncomputable def mDa : List Stmt := match (Fn.body Data.core0).getD 571 default with
  | .ite _ z _ => z
  | _ => []
noncomputable def mDaZ : List Stmt := match (Fn.body Data.core0).getD 571 default with
  | .ite _ _ n => n
  | _ => []
noncomputable def mMid : List Stmt := ((Fn.body Data.core0).drop 572).take 39
noncomputable def mLeaf : List Stmt := match (Fn.body Data.core0).getD 611 default with
  | .ite _ z _ => z
  | _ => []
noncomputable def mAgg : List Stmt := match (Fn.body Data.core0).getD 611 default with
  | .ite _ _ n => n
  | _ => []
noncomputable def mPost : List Stmt := ((Fn.body Data.core0).drop 612).take 11

set_option maxRecDepth 100000 in
theorem core0_shape : Fn.body Data.core0 =
    mPre ++ [.ite (.n 338) mDa mDaZ] ++ mMid ++ [.ite (.n 400) mLeaf mAgg] ++ mPost ++ [.ret []] :=
  stmtsEqb_sound (by decide +kernel)

/-! ## The facts, by evaluation -/

/-- `a == b` is asserted. -/
def isAssertEqAt (a b : V) : Atom → Bool
  | .assertEq x y => decide (x = a) && decide (y = b)
  | _ => false

theorem assertEq_sound {rd : Reader} {σ : Val} {atoms : List Atom} {a b : V}
    (h : atoms.any (isAssertEqAt a b) = true) (hat : ∀ x ∈ atoms, x.Holds rd σ) : σ a = σ b := by
  obtain ⟨x, hp, hx⟩ := any_holds h hat
  cases x <;> simp only [isAssertEqAt, Bool.false_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at hp
  obtain ⟨rfl, rfl⟩ := hp
  exact e_add_eq_zero_iff.mp hx

/-- `x` is range-checked against `b` itself (`assert log x < log (b · g)`, the bound built
directly). -/
theorem rcDir_sound {rd : Reader} (hm : MemOk rd) {σ : Val} {atoms : List Atom} {x b : V}
    (h : decide (rcOf atoms x = some b) = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    ∃ e, σ x = gen ^ e ∧ BelowLog (σ b * gen) e := by
  obtain ⟨y, t1, t2, h1, h2, h3⟩ := rcOf_sound (of_decide_eq_true h) hat
  obtain ⟨e, e', he, he', hx, hk⟩ := rc_sound hm ⟨h1, h2, h3⟩
  exact ⟨e, hx, he, e', he', by rw [hk, ← pow_succ]⟩

noncomputable def preOk : Bool :=
  let P := mPre
  let A := atomsIn mPre
  P.all Stmt.flat &&
  ((List.range 6).all fun v => rcConstOk A (.n v) 9272771591053052074) &&
  rcConstOk A (.n 6) 65536 && rcConstOk A (.n 7) 2 &&
  rcConstOk A (.n 42) 9272771591053052074 &&
  isMul A (.n 40) (.n 0) (.n 1) && isMul A (.n 41) (.n 3) (.n 4) &&
  isMul A (.n 42) (.n 40) (.n 41) &&
  hasCall P "exponent_tables" [] [.n 49] &&
  hasCall P "claim_list_digest" [.n 52, .n 0] [.n 56, .n 57] &&
  hasCall P "claim_list_digest" [.n 55, .n 3] [.n 58, .n 59] &&
  ((List.range 256).all fun v => A.any (isConstAt (.n (69 + v)) v 0) &&
    A.any (isLoadAt (.n (69 + v)) (.n 68) v)) &&
  isMul A (.n 67) (.n 66) (.n 40) &&
  guardOk P (.n 326) "__loop2" (.n 327) (.n 2) [.n 40, .n 66, .n 52] &&
  guardOk P (.n 329) "__loop3" (.n 330) (.n 5) [.n 41, .n 67, .n 2, .n 55, .n 68] &&
  isMul A (.n 335) (.n 6) (.n 6) && isMul A (.n 336) (.n 334) (.n 335) &&
  A.any (isAddAt (.n 338) (.n 7) (.n 337)) && A.any (isConstAt (.n 337) 2 0)

noncomputable def daOk : Bool :=
  let D := mDa
  D.all Stmt.flat &&
  hasCall D "da_verify" [.n 49] [.n 339, .n 340, .n 341, .n 342] &&
  pairHashOk (atomsIn D) (.n 339) (.n 340) (.n 341) (.n 342) (.n 336)

noncomputable def daZOk : Bool :=
  let A := atomsIn mDaZ
  mDaZ.all Stmt.flat &&
  A.any (isConstAt (.n 362) 0 0) && isLoad A (.n 362) (.n 336) 0 &&
  A.any (isConstAt (.n 363) 0 0) && isLoad A (.n 363) (.n 336) 1

noncomputable def midOk : Bool :=
  let M := mMid
  let A := atomsIn mMid
  M.all Stmt.flat &&
  isMul A (.n 381) (.n 2) (.n 5) && isLoad A (.n 381) (.n 380) 0 &&
  guardOk M (.n 383) "__loop4" (.n 384) (.n 6) [.n 380, .n 52, .n 66, .n 40, .n 55, .n 67,
    .n 41, .n 377, .n 334, .n 47, .n 48, .n 365, .n 49, .n 371] &&
  isMul A (.n 385) (.n 380) (.n 6) && isLoad A (.n 386) (.n 385) 0 &&
  A.any (isAssertEqAt (.n 386) (.n 42)) &&
  decide (rcOf A (.n 387) = some (.n 6)) &&
  A.any (isAddAt (.n 391) (.n 387) (.n 6)) && A.any (isAddAt (.n 393) (.n 7) (.n 392)) &&
  A.any (isConstAt (.n 392) 1 0) && isMul A (.n 394) (.n 391) (.n 393) &&
  A.any (isConstAt (.n 395) 0 0) && A.any (isAssertEqAt (.n 394) (.n 395)) &&
  isMul A (.n 396) (.n 387) (.n 387) && isMul A (.n 397) (.n 334) (.n 396) &&
  A.any (isAddAt (.n 400) (.n 6) (.n 399)) && A.any (isConstAt (.n 399) 1 0)

noncomputable def leafOk : Bool :=
  mLeaf.all Stmt.flat &&
  ((List.range 23).all fun k => (atomsIn mLeaf).any (isConstAt (.n (402 + k)) 0 0) &&
    isLoad (atomsIn mLeaf) (.n (402 + k)) (.n 398) k) &&
  isLoad (atomsIn mLeaf) (.n 401) (.n 398) 23 &&
  mAgg.all Stmt.flat &&
  hasCall mAgg "aggregate_claims" [.n 6, .n 365, .n 371, .n 377, .n 398] []

noncomputable def postOk : Bool :=
  let A := atomsIn mPost
  mPost.all Stmt.flat &&
  isLoad A (.n 425) (.n 397) 0 && isLoad A (.n 426) (.n 397) 1 &&
  hasCall mPost "statement_digest" [.n 47, .n 48, .n 56, .n 57, .n 58, .n 59, .n 425, .n 426, .n 398]
    [.n 427, .n 428] &&
  A.any (isConstAt (.n 429) 1 0) && isLoad A (.n 430) (.n 429) 0 &&
  A.any (isAssertEqAt (.n 430) (.n 427)) &&
  A.any (isConstAt (.n 431) 1 0) && A.any (isConstAt (.n 432) 2 0) &&
  isMul A (.n 433) (.n 431) (.n 432) && isLoad A (.n 434) (.n 433) 0 &&
  A.any (isAssertEqAt (.n 434) (.n 428))

set_option maxRecDepth 100000 in
theorem pre_ok : preOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem da_ok : daOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem daZ_ok : daZOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem mid_ok : midOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem leaf_ok : leafOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem post_ok : postOk = true := by decide +kernel

end
end LeanVM.Guest.B1.Main
