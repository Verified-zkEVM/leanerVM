import LeanVM.Protocol.Extraction.Fast.PMShape
import LeanVMTests.Extraction.Toy

/-!
# Tests: the lanes by the approximant-basis interpolation

`gsRunDistinctWith S` (the lane runner, its interpolation CompPoly's approximant-basis one on the
non-adaptive solver `S`, `Fast/LanePM.lean`) lists what `gsRunDistinctNF` (Mulders–Storjohann)
lists, on a word of a degree-`< 4` polynomial with errors:

* 16 points, multiplicity 1: on `pmSolver` (additive-FFT products, the ordered-weak-Popov PM-basis
  on evaluation-domain products) and on `pmSolverKaratsuba`.

At 32 points, multiplicity 3, the runners take minutes interpreted (the Mulders–Storjohann runner
a fraction of a second), so the larger shape is only checked to list `msg`.
-/

namespace LeanVMTests.Extraction.LanePM

open CompPoly CompPoly.GuruswamiSudan LeanVM.Parameters LeanVM.Extraction LeanVM.Extraction.Fast
open LeanVMTests.Extraction

/-- A message polynomial of degree `3`. -/
def msg : CPolynomial K := CPolynomial.ofArray #[K.ofBits 7, K.ofBits 123456, K.ofBits 99, K.ofBits 5]

/-- `msg` at `n` points, the points `v` with `v % e = 1` replaced. -/
def wordPoints (n e : ℕ) : Array (K × K) := Array.ofFn fun v : Fin n ↦
  (K.ofBits v.val, if v.val % e == 1 then K.ofBits (lcg v.val) else CPolynomial.eval (K.ofBits v.val) msg)

/-- The same polynomials, in any order. -/
def sameSet (a b : Array (CPolynomial K)) : Bool := a.all (b.contains ·) && b.all (a.contains ·)

-- 16 points, agreement 10 (multiplicity 1, `W = 9`), 4 errors.
#guard (gsParamsFor 4 16 10).interp.multiplicity == 1
#guard (gsRunDistinctNF (wordPoints 16 5) (gsParamsFor 4 16 10).interp 6).contains msg
#guard sameSet (gsRunDistinctWith pmSolver (wordPoints 16 5) (gsParamsFor 4 16 10).interp 6)
  (gsRunDistinctNF (wordPoints 16 5) (gsParamsFor 4 16 10).interp 6)
#guard sameSet (gsRunDistinctWith pmSolverKaratsuba (wordPoints 16 5) (gsParamsFor 4 16 10).interp 6)
  (gsRunDistinctNF (wordPoints 16 5) (gsParamsFor 4 16 10).interp 6)

-- 32 points, agreement 11 (multiplicity 3, `W = 32`), 11 errors.
#guard (gsParamsFor 4 32 11).interp.multiplicity == 3
#guard (gsRunDistinctNF (wordPoints 32 3) (gsParamsFor 4 32 11).interp 21).contains msg

end LeanVMTests.Extraction.LanePM
