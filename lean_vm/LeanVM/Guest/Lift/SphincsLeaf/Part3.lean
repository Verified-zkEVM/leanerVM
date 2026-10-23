/-
  LeanVM.Guest.Lift.SphincsLeaf.Part3

  Kernel checks that ranges of `verify_sig_lean_sphincs`'s statements are a leaf body.
-/

module

public import LeanVM.Guest.Memory.LiftPure
public import LeanVM.Guest.B1.Sig.Interface

namespace LeanVM.Guest.Lift

open LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

set_option maxRecDepth 100000 in
theorem sphincsLeaf_574 :
    Stmt.leafOkList anyAtom ((Data.core20.body.drop 574).take 36) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem sphincsLeaf_610 :
    Stmt.leafOkList anyAtom ((Data.core20.body.drop 610).take 150) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem sphincsLeaf_760 :
    Stmt.leafOkList anyAtom ((Data.core20.body.drop 760).take 150) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem sphincsLeaf_910 :
    Stmt.leafOkList anyAtom ((Data.core20.body.drop 910).take 4) = true := by
  decide +kernel

end
end LeanVM.Guest.Lift
