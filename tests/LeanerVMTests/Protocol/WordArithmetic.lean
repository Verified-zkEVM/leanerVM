import LeanerVM.Protocol.ProductSumWords
import LeanerVM.Protocol.ToCompPoly.EqBatch

/-!
# Differential tests of `E` on words and the batched equality kernels

`ExtWords.addW_eq`, `ExtWords.mulW_eq`, `ProductSum.roundOfBoundW_eq`,
`ProductSum.bindLowW_eq` and `eqBatch_getElem` prove the compiled paths equal to the
definitions; these `#guard`s check the compiled code.

* **Arithmetic.** `addW` and `mulW` against `E`'s sum and product on elements with every limb
  nonzero, on `0`, on `1` and on elements of `K`.
* **Rounds.** The round polynomial and the binding on words against the generic ones, on a table
  of `2 ^ 4` entries, at rounds `0` and `2`.
* **Kernels.** `eqBatch` against `Σ_j c_j · eq(z_j, ·)` built from the Lagrange bases, on points
  with Boolean coordinates (the terms then vanish off a block), with generic ones, with no term,
  and with two terms on the same block; a term dropped as a mutation.
-/

namespace LeanerVMTests.Protocol.WordArithmetic

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.ExtWords CompPoly CMlPolynomialEval

/-- A xorshift step. -/
private def xs (s : UInt64) : UInt64 :=
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  s ^^^ (s <<< 17)

/-- A `K` element from a seed. -/
private def kOf (s : UInt64) : K := BF64.ofBitVec (xs s).toBitVec

/-- An `E` element from a seed. -/
private def eOf (s : UInt64) : E := E.ofLimbs (kOf s) (kOf (s + 1)) (kOf (s + 2))

/-- Test elements: generic ones, `0`, `1`, elements of `K`. -/
private def elems : List E :=
  [eOf 3, eOf 5, eOf 7, 0, 1, E.ofLimbs (kOf 11) 0 0, E.ofLimbs 0 (kOf 13) 0]

/-! ## Arithmetic -/

#guard elems.all fun x ↦ elems.all fun y ↦ addW x y == x + y && mulW x y == x * y

/-! ## Rounds -/

/-- A table of `E` from a seed. -/
private def tabE (n : ℕ) (seed : UInt64) : CMlPolynomialEval E n :=
  Vector.ofFn fun i ↦ eOf (seed + 7 * i.val.toUInt64)

#guard ProductSum.roundOfBoundW (n := 4) (j := 0) (tabE 4 17) (tabE 4 19) ==
  ProductSum.roundOfBound (n := 4) (j := 0) (tabE 4 17) (tabE 4 19)
#guard ProductSum.roundOfBoundW (n := 4) (j := 2) (tabE 2 23) (tabE 2 29) ==
  ProductSum.roundOfBound (n := 4) (j := 2) (tabE 2 23) (tabE 2 29)
#guard ProductSum.bindLowW (tabE 4 31) (eOf 37) == bindLow (tabE 4 31) (eOf 37)

/-! ## Kernels -/

/-- `Σ_j c_j · eq(z_j, ·)` from the Lagrange bases. -/
private def eqDense {m : ℕ} (ts : List (E × Vector E m)) : CMlPolynomialEval E m :=
  Vector.ofFn fun x ↦ (ts.map fun t ↦ t.1 * (lagrangeBasis t.2)[x]).sum

/-- Terms on `2 ^ 3` entries: two on the block where the top coordinate is `0`, one with a
selector bit `1` in the middle, one generic. -/
private def terms : List (E × Vector E 3) :=
  [(eOf 41, #v[eOf 43, eOf 47, 0]), (eOf 53, #v[eOf 59, eOf 61, 0]),
    (eOf 67, #v[eOf 71, 1, eOf 73]), (eOf 79, #v[eOf 83, eOf 89, eOf 97])]

#guard eqBatch 3 terms == eqDense terms
#guard eqBatch 3 ([] : List (E × Vector E 3)) == eqDense []
#guard eqBatch 3 [(eOf 101, #v[1, 0, 1])] == eqDense [(eOf 101, #v[1, 0, 1])]
#guard !(eqBatch 3 terms.tail == eqDense terms)

end LeanerVMTests.Protocol.WordArithmetic
