/-
  LeanVM.Guest.Lift.SpWotsLeaf

  `sp_wots`'s body is a leaf body that loads nothing: atoms, branches and arms, placing nothing,
  no load (kernel checks on ranges of its statements, those of its well-formedness check).
-/

module

public import LeanVM.Guest.Memory.LiftPure
public import LeanVM.Guest.B1.Sig.SphincsCompleteSpec

namespace LeanVM.Guest.Lift

open LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- An atom that is not a load. -/
def noLoad : Atom → Bool
  | .load .. => false
  | _ => true

set_option maxRecDepth 100000 in
theorem spWotsLeaf_0 : Stmt.leafOkList noLoad ((Data.core20.body.drop 0).take 45) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spWotsLeaf_45 : Stmt.leafOkList noLoad ((Data.core20.body.drop 45).take 32) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spWotsLeaf_77 : Stmt.leafOkList noLoad ((Data.core20.body.drop 77).take 109) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **`sp_wots`'s body is a leaf loading nothing.** -/
theorem spWots_leafOk : Stmt.leafOkList noLoad Data.core20.body = true := by
  have h186 : Stmt.leafOkList noLoad (Data.core20.body.drop 186) = true :=
    leafOk_end (l := Data.core20.body) (by decide +kernel)
  have h77 := leafOk_drop (l := Data.core20.body) (a := 77) (n := 109) spWotsLeaf_77 h186
  have h45 := leafOk_drop (l := Data.core20.body) (a := 45) (n := 32) spWotsLeaf_45 h77
  have h0 := leafOk_drop (l := Data.core20.body) (a := 0) (n := 45) spWotsLeaf_0 h45
  simpa using h0

end
end LeanVM.Guest.Lift
