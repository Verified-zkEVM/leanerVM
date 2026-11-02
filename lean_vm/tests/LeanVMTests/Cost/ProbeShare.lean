import LeanVM.Cost.ProbeLib
import LeanVM.Protocol.Extraction.Fast.Karatsuba
import CompPoly.LinearAlgebra.PolynomialMatrix.Operations

/-!
# Probe: products and sums trimmed once (`rawMul_shared`, `rawAdd_shared`)

Off the chain: nothing compiled on the extractor's chain is imported, so CompPoly's `Raw.mul` and
`Raw.add` are compiled here through `ProbeLib`'s shared rewrites (the chain compiled them through
`trim_eq`, each computing its untrimmed result three times). The prices to compare with
`ProbeMul.lean`'s.
-/

namespace LeanVMTests.Cost.ProbeShare

open LeanVM.Cost LeanVM.Cost.Library LeanVM.Parameters LeanVM.Extraction.Fast CompPoly

def cmul (p q : CPolynomial K) : CPolynomial K := p * q

def cadd (p q : CPolynomial K) : CPolynomial K := p + q

abbrev lowK : PolynomialMatrix.MulLowContext K :=
  PolynomialMatrix.MulLowContext.raw karatsubaMulContext karatsubaMulLowContext

cost_compile cmulS := cmul

cost_compile caddS := cadd

cost_compile karatsubaS := @LeanVM.Extraction.Fast.karatsuba K _ _ _

cost_compile strassenS := PolynomialMatrix.mulStrassenWith (F := K) lowK

def run (deps : List (ℕ × Term)) (i : ℕ) (args : List MachineValue) : Option (MachineValue × ℕ) :=
  evaluateFunctionBody (MachineProgram.ofList deps) 100000000 i args

def rnd (s : ℕ) : K := K.ofBits ((s * 2654435761 + 12345) % 4294967291)

def poly (s d : ℕ) : CPolynomial K := CPolynomial.ofArray (Array.ofFn fun j : Fin d ↦ rnd (s * 1000 + j.val))

def mat (s r c d : ℕ) : PolynomialMatrix K :=
  Array.ofFn fun i : Fin r ↦ Array.ofFn fun j : Fin c ↦ poly (s * 10000 + i.val * 100 + j.val) d

#guard (run cmulS.costDeps cmulS.costIdx [MachineEncoding.encodeValue (poly 1 9),
  MachineEncoding.encodeValue (poly 2 7)]).map (·.1) == some (MachineEncoding.encodeValue (poly 1 9 * poly 2 7))
#guard (run caddS.costDeps caddS.costIdx [MachineEncoding.encodeValue (poly 1 9),
  MachineEncoding.encodeValue (poly 2 7)]).map (·.1) == some (MachineEncoding.encodeValue (poly 1 9 + poly 2 7))

-- `(d, price, price / d²)` of the schoolbook product.
#eval [4, 16, 32, 64].map fun d ↦
  let c := ((run cmulS.costDeps cmulS.costIdx
    [MachineEncoding.encodeValue (poly 1 d), MachineEncoding.encodeValue (poly 2 d)]).map (·.2)).getD 0
  (d, c, c / d ^ 2)
-- `(d, price, price / d)` of the sum.
#eval [4, 64].map fun d ↦
  let c := ((run caddS.costDeps caddS.costIdx
    [MachineEncoding.encodeValue (poly 1 d), MachineEncoding.encodeValue (poly 2 d)]).map (·.2)).getD 0
  (d, c, c / d)
#eval [32, 64, 128].map fun d ↦
  let c := ((run karatsubaS.costDeps karatsubaS.costIdx
    [MachineEncoding.encodeValue (64 : ℕ), MachineEncoding.encodeValue (poly 1 d), MachineEncoding.encodeValue (poly 2 d)]).map (·.2)).getD 0
  (d, c)
def strassenRun (cut : ℕ) (A B : PolynomialMatrix K) : Bool × ℕ :=
  match run strassenS.costDeps strassenS.costIdx
      [MachineEncoding.encodeValue cut, MachineEncoding.encodeValue A, MachineEncoding.encodeValue B] with
  | some (v, c) => (v == MachineEncoding.encodeValue (PolynomialMatrix.mulStrassenWith lowK cut A B), c)
  | none => (false, 0)

#guard (strassenRun 1 (mat 1 3 3 2) (mat 2 3 3 2)).1

#eval [(4, 4, 1), (8, 4, 1), (4, 64, 4)].map fun (n, d, cut) ↦
  (n, d, cut, (strassenRun cut (mat 1 n n d) (mat 2 n n d)).2)

end LeanVMTests.Cost.ProbeShare
