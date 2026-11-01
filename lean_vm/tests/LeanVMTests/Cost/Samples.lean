import LeanVM.Cost.Samples.AddRaw

/-!
# Tests: the compiled samples run

The program of the samples' bodies (at the indices the compiler gave them) computes the samples'
values.
-/

namespace LeanVMTests.Cost

open LeanVM.Cost LeanVM.Cost.Library LeanVM.Cost.Samples LeanVM.Parameters

/-- The bodies, at the indices the compiler gave them. -/
def samplesProgram : Program :=
  #[.val (.nat 0), listZipWith.costBody, listFoldl.costBody, addRawK.costBody,
    addRawK.lam0.costBody]

def polyA : CompPoly.CPolynomial.Raw K := #[K.ofBits 3, K.ofBits 5, K.ofBits 7]
def polyB : CompPoly.CPolynomial.Raw K := #[K.ofBits 1, K.ofBits 6]

#guard (evalBody samplesProgram 100 3 [Enc.enc polyA, Enc.enc polyB]).map (·.1) ==
  some (Enc.enc (CompPoly.CPolynomial.Raw.addRaw polyA polyB))

end LeanVMTests.Cost
