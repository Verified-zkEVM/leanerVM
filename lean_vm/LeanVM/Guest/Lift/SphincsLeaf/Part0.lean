/-
  LeanVM.Guest.Lift.SphincsLeaf.Part0

  Kernel checks that ranges of `verify_sig_lean_sphincs`'s statements are a leaf body.
-/

module

public import LeanVM.Guest.Memory.LiftPure
public import LeanVM.Guest.B1.Sig.Interface

namespace LeanVM.Guest.Lift

open LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

set_option maxRecDepth 100000 in
theorem sphincsLeaf_0 :
    Stmt.leafOkList anyAtom ((Data.core20.body.drop 0).take 150) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem sphincsLeaf_150 :
    Stmt.leafOkList anyAtom ((Data.core20.body.drop 150).take 85) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem sphincsLeaf_235 :
    Stmt.leafOkList anyAtom ((Data.core20.body.drop 235).take 37) = true := by
  decide +kernel

end
end LeanVM.Guest.Lift
