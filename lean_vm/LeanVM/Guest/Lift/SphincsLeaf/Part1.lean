/-
  LeanVM.Guest.Lift.SphincsLeaf.Part1

  Kernel checks that ranges of `verify_sig_lean_sphincs`'s statements are a leaf body.
-/

module

public import LeanVM.Guest.Memory.LiftPure
public import LeanVM.Guest.B1.Sig.Interface

namespace LeanVM.Guest.Lift

open LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

set_option maxRecDepth 100000 in
theorem sphincsLeaf_272 :
    Stmt.leafOkList anyAtom ((Data.core20.body.drop 272).take 37) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem sphincsLeaf_309 :
    Stmt.leafOkList anyAtom ((Data.core20.body.drop 309).take 37) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem sphincsLeaf_346 :
    Stmt.leafOkList anyAtom ((Data.core20.body.drop 346).take 37) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem sphincsLeaf_383 :
    Stmt.leafOkList anyAtom ((Data.core20.body.drop 383).take 37) = true := by
  decide +kernel

end
end LeanVM.Guest.Lift
