import LeanVMTests.Cost.ProbeMul
import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PMBasis.KernelLeaf
import LeanVM.Cost.ProbeLib

/-!
# Probe: CompPoly's kernel leaf over `K`, compiled

`kernelLeafBasis` (CompPoly, `Approximant/PMBasis/KernelLeaf.lean`; github.com/Verified-zkEVM/CompPoly,
Apache-2.0, "Copyright (c) 2026 CompPoly Contributors"; compiled, not copied).
-/

namespace LeanVMTests.Cost.ProbeLeaf

open LeanVM.Cost LeanVM.Cost.Library LeanVM.Parameters LeanVM.Extraction.Fast CompPoly
open CompPoly.PolynomialMatrix.Approximant


cost_compile kernelLeafK := kernelLeafBasis (F := K)

open LeanVMTests.Cost.ProbeMul

/-- An X-adic problem: an `r × c` matrix of polynomials with `d` coefficients, orders `o`. -/
def prob (s r c d : ℕ) (o : Array ℕ) : XAdicProblem K := { orders := o, matrix := mat s r c d }

/-- The compiled leaf's value is the source's, and its price. -/
def leafRun (P : XAdicProblem K) (shift : Array ℕ) : Bool × ℕ :=
  match run kernelLeafK.costDeps kernelLeafK.costIdx
      [MachineEncoding.encodeValue P, MachineEncoding.encodeValue shift] with
  | some (v, c) => (v == MachineEncoding.encodeValue (kernelLeafBasis P shift), c)
  | none => (false, 0)

#guard (leafRun (prob 1 3 2 2 #[1, 1]) #[0, 0, 0]).1
#guard (leafRun (prob 2 3 1 3 #[2]) #[0, 1, 2]).1
#guard (leafRun (prob 3 4 2 3 #[1, 1]) #[5, 0, 2, 1]).1

-- Prices at order 1 (the report's leaf cutoff 1): `(r, c, price, r³)`.
/-- info: [(4, 1, 267874, 64), (8, 2, 1047672, 512), (16, 4, 4831528, 4096), (32, 8, 26108052, 32768)] -/
#guard_msgs in
#eval [(4, 1), (8, 2), (16, 4), (32, 8)].map fun (r, c) ↦
  (r, c, (leafRun (prob 1 r c 2 (Array.replicate c 1)) (Array.replicate r 0)).2, r ^ 3)

end LeanVMTests.Cost.ProbeLeaf
