/-
  LeanVM.Guest.B1.Main.Body

  `main`'s body (G:4086-4282): its shape, its facts checked by evaluation, and what a run of it
  gives (`MainFacts`).
-/

module

public import LeanVM.Guest.B1.Main.Loops

/-!
# `main`'s body

`Data.core0`'s body is a flat block (`mPre`: the counts and their range checks, the exponent
tables, the DA list digest, the claim list digests, the signer set, the byte table, the raw
signatures' loops), the direct DA check behind `n_direct_da == g` (`mDa`), a flat block (`mMid`:
the children's loop and the final count), the leaf's deferred claim or the batching behind
`n_children == 1` (`mLeaf`, `mAgg`), and a flat block (`mPost`: the statement's digest against
the public input) (`core0_shape`). `mainOk` checks every fact the proof reads by evaluation;
`main_facts` gives them, as `MainFacts`, of a run of the body.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

/-! ## The shape -/

noncomputable def mPre : List Stmt := (Fn.body Data.core0).take 598
noncomputable def mDa : List Stmt := match (Fn.body Data.core0).getD 598 default with
  | .ite _ z _ => z
  | _ => []
noncomputable def mMid : List Stmt := ((Fn.body Data.core0).drop 599).take 30
noncomputable def mLeaf : List Stmt := match (Fn.body Data.core0).getD 629 default with
  | .ite _ z _ => z
  | _ => []
noncomputable def mAgg : List Stmt := match (Fn.body Data.core0).getD 629 default with
  | .ite _ _ n => n
  | _ => []
noncomputable def mPost : List Stmt := ((Fn.body Data.core0).drop 630).take 9

set_option maxRecDepth 100000 in
theorem core0_shape : Fn.body Data.core0 =
    mPre ++ [.ite (.n 383) mDa []] ++ mMid ++ [.ite (.n 419) mLeaf mAgg] ++ mPost ++ [.ret []] :=
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

noncomputable def preOk : Bool :=
  let P := mPre
  let A := atomsIn mPre
  P.all Stmt.flat &&
  ((List.range 6).all fun v => rcConstOk A (.n v) 9272771591053052074) &&
  rcConstOk A (.n 6) 65536 && rcConstOk A (.n 7) 2 && rcConstOk A (.n 40) 65536 &&
  rcConstOk A (.n 41) 139298 && rcConstOk A (.n 50) 139298 &&
  rcConstOk A (.n 58) 9272771591053052074 &&
  isMul A (.n 50) (.n 40) (.n 41) && isMul A (.n 55) (.n 0) (.n 1) &&
  isMul A (.n 56) (.n 3) (.n 4) && isMul A (.n 57) (.n 55) (.n 56) &&
  isMul A (.n 58) (.n 57) (.n 50) &&
  hasCall P "exponent_tables" [] [.n 65, .n 66] &&
  hasCall P "da_list_digest" [.n 69, .n 40] [.n 73, .n 74] &&
  hasCall P "claim_list_digest" [.n 77, .n 0] [.n 81, .n 82] &&
  hasCall P "claim_list_digest" [.n 80, .n 3] [.n 83, .n 84] &&
  pairHashOk A (.n 81) (.n 82) (.n 83) (.n 84) (.n 116) &&
  isMul A (.n 118) (.n 117) (.n 57) &&
  ((List.range 256).all fun v => A.any (isConstAt (.n (120 + v)) v 0) &&
    A.any (isLoadAt (.n (120 + v)) (.n 119) v)) &&
  guardOk P (.n 377) "__loop3" (.n 378) (.n 2) [.n 55, .n 117, .n 77] &&
  guardOk P (.n 380) "__loop4" (.n 381) (.n 5) [.n 56, .n 117, .n 55, .n 2, .n 80, .n 119] &&
  A.any (isAddAt (.n 383) (.n 7) (.n 382)) && A.any (isConstAt (.n 382) 2 0)

noncomputable def daOk : Bool :=
  let D := mDa
  let A := atomsIn mDa
  D.all Stmt.flat &&
  hasCall D "da_verify" [.n 66] [.n 384, .n 385, .n 386, .n 387] &&
  isMul A (.n 388) (.n 2) (.n 5) &&
  hasCall D "cover_da_root" [.n 69, .n 118, .n 50, .n 388] [.n 389, .n 390, .n 391, .n 392] &&
  A.any (isAssertEqAt (.n 384) (.n 389)) && A.any (isAssertEqAt (.n 385) (.n 390)) &&
  A.any (isAssertEqAt (.n 386) (.n 391)) && A.any (isAssertEqAt (.n 387) (.n 392))

noncomputable def midOk : Bool :=
  let M := mMid
  let A := atomsIn mMid
  M.all Stmt.flat &&
  isMul A (.n 410) (.n 2) (.n 5) && isMul A (.n 411) (.n 410) (.n 7) &&
  isLoad A (.n 411) (.n 409) 0 &&
  guardOk M (.n 413) "__loop5" (.n 414) (.n 6) [.n 409, .n 77, .n 117, .n 55, .n 80, .n 56,
    .n 406, .n 69, .n 118, .n 50, .n 63, .n 64, .n 394, .n 65, .n 66, .n 400] &&
  isMul A (.n 415) (.n 409) (.n 6) && isLoad A (.n 416) (.n 415) 0 &&
  A.any (isAssertEqAt (.n 416) (.n 58)) &&
  A.any (isAddAt (.n 419) (.n 6) (.n 418)) && A.any (isConstAt (.n 418) 1 0)

noncomputable def leafOk : Bool :=
  mLeaf.all Stmt.flat &&
  ((List.range 23).all fun k => (atomsIn mLeaf).any (isConstAt (.n (421 + k)) 0 0) &&
    isLoad (atomsIn mLeaf) (.n (421 + k)) (.n 417) k) &&
  isLoad (atomsIn mLeaf) (.n 420) (.n 417) 23 &&
  mAgg.all Stmt.flat &&
  hasCall mAgg "aggregate_claims" [.n 6, .n 394, .n 400, .n 406, .n 417] []

noncomputable def postOk : Bool :=
  let A := atomsIn mPost
  mPost.all Stmt.flat &&
  hasCall mPost "statement_digest" [.n 63, .n 64, .n 116, .n 73, .n 74, .n 417] [.n 444, .n 445] &&
  A.any (isConstAt (.n 446) 1 0) && isLoad A (.n 447) (.n 446) 0 &&
  A.any (isAssertEqAt (.n 447) (.n 444)) &&
  A.any (isConstAt (.n 448) 1 0) && A.any (isConstAt (.n 449) 2 0) &&
  isMul A (.n 450) (.n 448) (.n 449) && isLoad A (.n 451) (.n 450) 0 &&
  A.any (isAssertEqAt (.n 451) (.n 445))

set_option maxRecDepth 100000 in
theorem pre_ok : preOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem da_ok : daOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem mid_ok : midOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem leaf_ok : leafOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem post_ok : postOk = true := by decide +kernel

end
end LeanVM.Guest.B1.Main
