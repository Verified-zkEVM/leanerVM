import LeanVM.Cost.Extractor.PMLane
import LeanVM.Protocol.Extraction.Fast.Karatsuba
import CompPoly.LinearAlgebra.PolynomialMatrix.Operations
import LeanVM.Cost.ProbeLib

/-!
# Probe: CompPoly's Strassen products of polynomial matrices over `K`, compiled

`mulStrassenWith` and `mulTruncColumnStrassenWith` (CompPoly, `PolynomialMatrix/Operations.lean`;
github.com/Verified-zkEVM/CompPoly, Apache-2.0, "Copyright (c) 2026 CompPoly Contributors"; compiled,
not copied) at the low-product context `MulLowContext.raw` on lean_vm's Karatsuba (the context the
report's fixed interpolation would use), the leaf cutoff a parameter.
-/

namespace LeanVMTests.Cost.ProbeMul

open LeanVM.Cost LeanVM.Cost.Library LeanVM.Parameters LeanVM.Extraction.Fast CompPoly

/-- Karatsuba's low products, as CompPoly's matrix low-product context. -/
abbrev lowK : PolynomialMatrix.MulLowContext K :=
  PolynomialMatrix.MulLowContext.raw karatsubaMulContext karatsubaMulLowContext

cost_compile strassenK := PolynomialMatrix.mulStrassenWith (F := K) lowK

cost_compile strassenTruncK := PolynomialMatrix.mulTruncColumnStrassenWith (F := K) lowK

cost_compile rawMulK := @CompPoly.CPolynomial.Raw.mul K _ _

cost_compile karatsubaK := @LeanVM.Extraction.Fast.karatsuba K _ _ _

end LeanVMTests.Cost.ProbeMul

namespace LeanVMTests.Cost.ProbeMul

open LeanVM.Cost LeanVM.Cost.Library LeanVM.Parameters LeanVM.Extraction.Fast CompPoly

def run (deps : List (ℕ × Term)) (i : ℕ) (args : List MachineValue) : Option (MachineValue × ℕ) :=
  evaluateFunctionBody (MachineProgram.ofList deps) 100000000 i args

/-- A pseudo-random element of `K`. -/
def rnd (s : ℕ) : K := K.ofBits ((s * 2654435761 + 12345) % 4294967291)

/-- A pseudo-random polynomial with `d` coefficients. -/
def poly (s d : ℕ) : CPolynomial K := CPolynomial.ofArray (Array.ofFn fun j : Fin d ↦ rnd (s * 1000 + j.val))

/-- An `r × c` matrix of polynomials with `d` coefficients. -/
def mat (s r c d : ℕ) : PolynomialMatrix K :=
  Array.ofFn fun i : Fin r ↦ Array.ofFn fun j : Fin c ↦ poly (s * 10000 + i.val * 100 + j.val) d

/-- The compiled Strassen product's value is the source's, and its price. -/
def strassenRun (cut : ℕ) (A B : PolynomialMatrix K) : Bool × ℕ :=
  match run strassenK.costDeps strassenK.costIdx
      [MachineEncoding.encodeValue cut, MachineEncoding.encodeValue A, MachineEncoding.encodeValue B] with
  | some (v, c) => (v == MachineEncoding.encodeValue (PolynomialMatrix.mulStrassenWith lowK cut A B), c)
  | none => (false, 0)

def truncRun (cut : ℕ) (orders : Array ℕ) (A B : PolynomialMatrix K) : Bool × ℕ :=
  match run strassenTruncK.costDeps strassenTruncK.costIdx
      [MachineEncoding.encodeValue cut, MachineEncoding.encodeValue orders, MachineEncoding.encodeValue A,
        MachineEncoding.encodeValue B] with
  | some (v, c) => (v == MachineEncoding.encodeValue (PolynomialMatrix.mulTruncColumnStrassenWith lowK cut orders A B), c)
  | none => (false, 0)

#guard (strassenRun 1 (mat 1 3 3 2) (mat 2 3 3 2)).1
#guard (strassenRun 2 (mat 1 4 4 3) (mat 2 4 4 3)).1
#guard (truncRun 1 #[2, 3, 1] (mat 1 3 3 2) (mat 2 3 3 2)).1
#guard (truncRun 2 #[4, 1, 3, 2] (mat 1 4 4 3) (mat 2 4 4 3)).1

-- Prices: `(n, d, cut, price, K-products of the schoolbook entry products n³d²)`.
/-- info: [(2, 4, 1, 55940, 128), (4, 4, 1, 420330, 1024), (4, 4, 4, 396823, 1024), (8, 4, 1, 3048892, 8192),
  (8, 4, 8, 3164523, 8192), (4, 16, 4, 5367319, 16384), (4, 64, 4, 63887255, 262144)] -/
#guard_msgs in
#eval [(2, 4, 1), (4, 4, 1), (4, 4, 4), (8, 4, 1), (8, 4, 8), (4, 16, 4), (4, 64, 4)].map fun (n, d, cut) ↦
  (n, d, cut, (strassenRun cut (mat 1 n n d) (mat 2 n n d)).2, n ^ 3 * d ^ 2)

/-- info: [(4, 4, 1, 407424, 1024), (8, 4, 1, 2961714, 8192), (4, 16, 4, 5313495, 16384)] -/
#guard_msgs in
#eval [(4, 4, 1), (8, 4, 1), (4, 16, 4)].map fun (n, d, cut) ↦
  (n, d, cut, (truncRun cut (Array.replicate n d) (mat 1 n n d) (mat 2 n n d)).2, n ^ 3 * d ^ 2)


-- Schoolbook `Raw.mul` and Karatsuba: `(d, price, price / d², price / (258·d²))`.
/-- info: [(4, 5448, 340, 131), (16, 82218, 321, 124), (32, 325922, 318, 123), (64, 1297938, 316, 122)] -/
#guard_msgs in
#eval [4, 16, 32, 64].map fun d ↦
  let c := ((run rawMulK.costDeps rawMulK.costIdx
    [MachineEncoding.encodeValue (poly 1 d).val, MachineEncoding.encodeValue (poly 2 d).val]).map (·.2)).getD 0
  (d, c, c / d ^ 2, c * 100 / (258 * d ^ 2))
/-- info: [(32, 325950), (64, 993044), (128, 3008886)] -/
#guard_msgs in
#eval [32, 64, 128].map fun d ↦
  let c := ((run karatsubaK.costDeps karatsubaK.costIdx
    [MachineEncoding.encodeValue (64 : ℕ), MachineEncoding.encodeValue (poly 1 d), MachineEncoding.encodeValue (poly 2 d)]).map (·.2)).getD 0
  (d, c)

end LeanVMTests.Cost.ProbeMul
