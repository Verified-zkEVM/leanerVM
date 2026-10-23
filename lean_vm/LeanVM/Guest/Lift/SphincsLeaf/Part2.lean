/-
  LeanVM.Guest.Lift.SphincsLeaf.Part2

  Kernel checks that ranges of `verify_sig_lean_sphincs`'s statements are a leaf body.
-/

module

public import LeanVM.Guest.Memory.LiftPure
public import LeanVM.Guest.B1.Sig.Interface

namespace LeanVM.Guest.Lift

open LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

set_option maxRecDepth 100000 in
theorem sphincsLeaf_420 :
    Stmt.leafOkList anyAtom ((Data.core20.body.drop 420).take 37) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem sphincsLeaf_457 :
    Stmt.leafOkList anyAtom ((Data.core20.body.drop 457).take 81) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem sphincsLeaf_538 :
    Stmt.leafOkList anyAtom ((Data.core20.body.drop 538).take 36) = true := by
  decide +kernel

end
end LeanVM.Guest.Lift
