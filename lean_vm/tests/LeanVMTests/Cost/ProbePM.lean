import LeanVMTests.Cost.ProbeLeaf
import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PMBasis.Recursion

/-!
# Probe: CompPoly's recursive PM-basis over `K`, compiled

`pmBasisWithFuelCore` and `pmBasis` (CompPoly, `Approximant/PMBasis/Recursion.lean`;
github.com/Verified-zkEVM/CompPoly, Apache-2.0, "Copyright (c) 2026 CompPoly Contributors"; compiled,
not copied) at the kernel-leaf runtime on Karatsuba's low products, leaf cutoff 1.
-/

namespace LeanVMTests.Cost.ProbePM

open LeanVM.Cost LeanVM.Cost.Library LeanVM.Parameters LeanVM.Extraction.Fast CompPoly
open CompPoly.PolynomialMatrix.Approximant LeanVMTests.Cost.ProbeMul LeanVMTests.Cost.ProbeLeaf

/-- The kernel-leaf runtime on Karatsuba's low products, leaf and composition cutoff 1. -/
abbrev runtimeK : PMBasisRuntime K := kernelLeafRuntimeWithLow karatsubaMulContext lowK 1

cost_compile pmCoreK := pmBasisWithFuelCore runtimeK

cost_compile pmBasisK := pmBasis runtimeK

def pmRun (P : XAdicProblem K) (shift : Array ℕ) : Bool × ℕ :=
  match run pmBasisK.costDeps pmBasisK.costIdx
      [MachineEncoding.encodeValue P, MachineEncoding.encodeValue shift] with
  | some (v, c) => (v == MachineEncoding.encodeValue (pmBasis runtimeK P shift), c)
  | none => (false, 0)

def coreRun (P : XAdicProblem K) (shift : Array ℕ) : Bool × ℕ :=
  match run pmCoreK.costDeps pmCoreK.costIdx
      [MachineEncoding.encodeValue (maxOrder P + 1), MachineEncoding.encodeValue P,
        MachineEncoding.encodeValue shift] with
  | some (v, c) => (v == MachineEncoding.encodeValue (pmBasisWithFuelCore runtimeK (maxOrder P + 1) P shift), c)
  | none => (false, 0)

#guard (pmRun (prob 1 3 2 4 #[3, 2]) #[0, 0, 0]).1
#guard (coreRun (prob 1 3 2 4 #[3, 2]) #[0, 0, 0]).1
#guard (pmRun (prob 2 4 1 5 #[6]) #[0, 2, 4, 6]).1

-- Prices: `(r, c, order, core price, pmBasis price)`, the matrix's entries of `order` coefficients.
#eval [(2, 1, 4), (4, 2, 4), (4, 2, 8), (4, 2, 16), (8, 4, 8)].map fun (r, c, o) ↦
  (r, c, o, (coreRun (prob 1 r c o (Array.replicate c o)) (Array.replicate r 0)).2,
    (pmRun (prob 1 r c o (Array.replicate c o)) (Array.replicate r 0)).2)

end LeanVMTests.Cost.ProbePM
