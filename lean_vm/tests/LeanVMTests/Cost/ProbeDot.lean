import LeanVMTests.Cost.ProbeFFT

/-!
# Probe: the evaluation-domain products' pointwise sums

`EvalMat.evalDot N s a B c` (lean_vm, `Fast/EvalMat/Product.lean`): at each of `N` points, a fold
over `List.range s` (the list rebuilt per point) of `a[k][v]·B[k][c][v]`. The PM-basis's dominant
term at the target (`r³·N` of them per level), so its price per multiply-add matters. Against it,
`evalDotRows` (same values, `evalDotRows_eq`): the fold over `k` outside, each step one array of
`N` fused multiply-adds.
-/

namespace LeanVMTests.Cost.ProbeDot

open LeanVM.Cost LeanVM.Cost.Library LeanVM.Parameters LeanVM.Extraction.Fast CompPoly
open LeanVM.Extraction.Fast.EvalMat LeanVMTests.Cost.ProbeFFT

/-- The pointwise sums, the fold over `k` outside. -/
def evalDotRows (N s : ℕ) (a : Array (Array K)) (B : Array (Array (Array K))) (c : ℕ) : Array K :=
  (List.range s).foldl (fun acc k ↦
    let x := a.getD k #[]
    let y := (B.getD k #[]).getD c #[]
    Array.ofFn fun v : Fin N ↦ acc.getD v.val 0 + x.getD v.val 0 * y.getD v.val 0)
    (Array.replicate N 0)

cost_compile evalDotC := evalDot (F := K)

cost_compile evalDotRowsC := evalDotRows

def vec (s N : ℕ) : Array K := Array.ofFn fun v : Fin N ↦ rnd (s * 7919 + v.val)

open MachineEncoding in
-- `(N, s, evalDot, evalDotRows, N·s)`.
#eval [(16, 8), (64, 8), (64, 32)].map fun (N, s) ↦
  let a := Array.ofFn fun k : Fin s ↦ vec k.val N
  let B := Array.ofFn fun k : Fin s ↦ #[vec (100 + k.val) N]
  let args := [encodeValue N, encodeValue s, encodeValue a, encodeValue B, encodeValue (0 : ℕ)]
  (N, s, check evalDotC.costDeps evalDotC.costIdx args (encodeValue (evalDot N s a B 0)),
    check evalDotRowsC.costDeps evalDotRowsC.costIdx args (encodeValue (evalDot N s a B 0)), N * s)

end LeanVMTests.Cost.ProbeDot
