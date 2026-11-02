import LeanVMTests.Cost.ProbePM
import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.ModularEquation.Basic
import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PMBasis

/-!
# Probe: CompPoly's certified windowed modular solve over `K`, compiled

`windowedSolutionBasisViaPMBasis` (CompPoly, `Approximant/ModularEquation/Basic.lean`;
github.com/Verified-zkEVM/CompPoly, Apache-2.0, "Copyright (c) 2026 CompPoly Contributors"; compiled,
not copied): the reduced exact-nullspace lift, one PM-basis call, the principal columns.
-/

namespace LeanVMTests.Cost.ProbeWin

open LeanVM.Cost LeanVM.Cost.Library LeanVM.Parameters LeanVM.Extraction.Fast CompPoly
open CompPoly.PolynomialMatrix.Approximant LeanVMTests.Cost.ProbeMul LeanVMTests.Cost.ProbeLeaf
open LeanVMTests.Cost.ProbePM

/-- The PM-basis context on the kernel leaf, Karatsuba's low products, cutoff 1. -/
abbrev pmCtxK : PMBasisContext K := kernelLeafPMBasisContextWithLow karatsubaMulContext lowK 1

cost_compile windowedK := windowedSolutionBasisViaPMBasis karatsubaModContext pmCtxK

/-- A monic polynomial of degree `d`. -/
def monic (s d : ℕ) : CPolynomial K := CPolynomial.ofArray ((poly s d).val.push 1)

/-- A modular equation: `r` coordinates, `c` columns, moduli of degree `d`, entries below. -/
def meq (s r c d : ℕ) : ModularEquation K :=
  { moduli := Array.ofFn fun j : Fin c ↦ monic (s + j.val) d, matrix := mat s r c d }

def winRun (E : ModularEquation K) (shift : Array ℕ) (bound : ℕ) : Bool × ℕ :=
  match run windowedK.costDeps windowedK.costIdx
      [MachineEncoding.encodeValue E, MachineEncoding.encodeValue shift, MachineEncoding.encodeValue bound] with
  | some (v, c) => (v == MachineEncoding.encodeValue (windowedSolutionBasisViaPMBasis karatsubaModContext pmCtxK E shift bound), c)
  | none => (false, 0)

#guard (winRun (meq 1 3 1 3) #[0, 0, 0] 2).1
#guard (winRun (meq 2 3 2 2) #[0, 1, 2] 3).1

-- Prices: `(r, c, d, bound, price)`.
/-- info: [(2, 1, 2, 2, 2470033), (3, 1, 3, 2, 3805105), (3, 2, 4, 4, 25019902), (4, 2, 4, 4, 27216303)] -/
#guard_msgs in
#eval [(2, 1, 2, 2), (3, 1, 3, 2), (3, 2, 4, 4), (4, 2, 4, 4)].map fun (r, c, d, b) ↦
  (r, c, d, b, (winRun (meq 1 r c d) (Array.replicate r 0) b).2)

/-- info: 201 -/
#guard_msgs in
#eval windowedK.costDeps.length
/-- info: true -/
#guard_msgs in
#eval windowedK.costDeps.map (·.1) |>.contains pmBasisK.costIdx

end LeanVMTests.Cost.ProbeWin
