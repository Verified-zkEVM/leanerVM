import LeanVMTests.Cost.Samples.AddRaw
import LeanVMTests.Cost.Samples.CommittedLeaves
import LeanVM.Cost.Extractor.MsReduce

/-!
# Tests: the compiled samples run

The program of the samples' bodies (at the indices the compiler gave them) computes the samples'
values.
-/

namespace LeanVMTests.Cost

open LeanVM.Cost LeanVM.Cost.Library LeanVMTests.Cost.Samples LeanVM.Parameters

def polyA : CompPoly.CPolynomial.Raw K := #[K.ofBits 3, K.ofBits 5, K.ofBits 7]
def polyB : CompPoly.CPolynomial.Raw K := #[K.ofBits 1, K.ofBits 6]

#guard (evalBody (Program.ofList addRawK.costDeps) 100 addRawK.costIdx
    [Enc.enc polyA, Enc.enc polyB]).map (·.1) ==
  some (Enc.enc (CompPoly.CPolynomial.Raw.addRaw polyA polyB))

/-! ## The committed leaves -/

section
open LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile
attribute [local instance] lexOrd

/-- A tree of height 1 and width 1: a root over two leaves of 8 bytes. -/
def leafL : Bytes := (List.range 8).map (·.toUInt8)
def leafR : Bytes := (List.range 8).map (· + 100 |>.toUInt8)
def digL : Digest := #v[1, 2, 3, 4]
def digR : Digest := #v[5, 6, 7, 8]
def rootD : Digest := #v[9, 9, 9, 9]
def nodeBytes : Bytes := digestBytes digL ++ digestBytes digR
def toyIndex : SortedMap (List UInt64 × ℕ) Hits :=
  preimageIndex [(leafL, digL), (leafR, digR), (nodeBytes, rootD)]

#guard committedLeavesFast toyIndex 1 1 rootD == #[bytesWords 1 leafL, bytesWords 1 leafR]
#guard (evalBody (Program.ofList committedLeavesC.costDeps) 1000 (committedLeavesC.costIdx)
    [Enc.enc toyIndex, Enc.enc (1 : ℕ), Enc.enc (1 : ℕ), Enc.enc rootD]).map (·.1) ==
  some (Enc.enc (committedLeavesFast toyIndex 1 1 rootD))

end

/-! ## One Mulders–Storjohann step

The extractor's own copy (`Cost/Extractor/MsReduce.lean`). -/

section
open CompPoly CompPoly.PolynomialMatrix

/-- The step as the extractor compiles it: its bodies and its index. -/
def msStepDeps : List (ℕ × Term) :=
  LeanVM.Cost.Auto.CompPoly.PolynomialMatrix.muldersStorjohannStepFast.c24.costDeps
def msStepIdx : ℕ := LeanVM.Cost.Auto.CompPoly.PolynomialMatrix.muldersStorjohannStepFast.c24.costIdx

def cpoly (l : List ℕ) : CPolynomial K := CPolynomial.ofArray (l.map K.ofBits).toArray

/-- Two rows of two entries, the same shifted leading position: the step cancels. -/
def msMatrix : PolynomialMatrix K := #[#[cpoly [1, 2, 3], cpoly [5]], #[cpoly [7, 1], cpoly [2]]]

#guard (muldersStorjohannStepFast msMatrix #[0, 0] 0 1).map (·.map (·.val)) !=
  msMatrix.map (·.map (·.val))
#guard (evalBody (Program.ofList msStepDeps) 100000 msStepIdx
    [Enc.enc msMatrix, Enc.enc #[(0 : ℕ), 0], Enc.enc (0 : ℕ), Enc.enc (1 : ℕ)]).map (·.1) ==
  some (Enc.enc (muldersStorjohannStepFast msMatrix #[0, 0] 0 1))

end

end LeanVMTests.Cost
