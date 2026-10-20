import LeanerVM.Protocol.Whir.Glue

/-!
# WHIR sumcheck and glue tests

The plain sumcheck of two tables, binding the lowest variable first, on `n = 3` coordinates over
`E`; the round polynomial's check and value; its linearity in the weight (the glued claim's
polynomial is the glued polynomials); the committed word and the folded row. A plain file, so
`#guard` evaluates the compiled definitions; values of `E` are named as definitions.

* **The round polynomial is the honest one.** At every stage its values at `0` and `1` sum to the
  running claim, and its value at a challenge is the claim with that coordinate fixed.
* **A wrong polynomial is rejected.** The same polynomial with its linear coefficient changed
  fails the check on the unit-weight domain.
* **Linearity.** The round polynomial of the batch of two weights at `λ` is the batch of their
  round polynomials at `λ`, and the claim likewise.
* **The word.** The folded row at a position is the encoding of the folded table there.
-/

namespace LeanerVMTests.Protocol

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Whir CompPoly CMlPolynomialEval

/-- A table of eight entries. -/
def tA : CMlPolynomialEval E 3 :=
  Vector.ofFn fun i : Fin 8 ↦ algebraMap K E (K.ofBits (0x9e3779b97f4a7c15 * (i.val + 1) + 5))

/-- Another table. -/
def tB : CMlPolynomialEval E 3 :=
  Vector.ofFn fun i : Fin 8 ↦ algebraMap K E (K.ofBits (0x243f6a8885a308d3 * (i.val + 3) + 11))

/-- A third table, for the batch. -/
def tC : CMlPolynomialEval E 3 :=
  Vector.ofFn fun i : Fin 8 ↦ algebraMap K E (K.ofBits (0x13198a2e03707344 * (i.val + 7) + 2))

def e1 : E := algebraMap K E (K.ofBits 0x1d)
def e2 : E := algebraMap K E (K.ofBits 0x77)
def e3 : E := algebraMap K E (K.ofBits 0x5)
def lam : E := y + 1

/-! ## The honest polynomial -/

-- stage 0: the polynomial's values at 0 and 1 sum to the claim `Σ A·B`
#guard SumcheckRound.weightedSum 2 [((0 : E), (1 : E)), (1, 1)]
    (ProductSum.roundPoly tA tB 0 #v[]) = ProductSum.claim tA tB 0 #v[]
-- stage 1, after one challenge
#guard SumcheckRound.weightedSum 2 [((0 : E), (1 : E)), (1, 1)]
    (ProductSum.roundPoly tA tB 1 #v[e1]) = ProductSum.claim tA tB 1 #v[e1]
-- its value at the next challenge is the next claim
#guard SumcheckRound.evaluate 2 (ProductSum.roundPoly tA tB 1 #v[e1]) e2 =
  ProductSum.claim tA tB 2 #v[e1, e2]
-- the claim at stage 0 is the inner product, and with everything fixed it is the summand
#guard ProductSum.claim tA tB 0 #v[] = ∑ i : Fin 8, tA[i] * tB[i]
#guard ProductSum.claim tA tB 3 #v[e1, e2, e3] =
  evalMle tA #v[e1, e2, e3] * evalMle tB #v[e1, e2, e3]

/-! ## A wrong polynomial -/

/-- The honest polynomial with its linear coefficient changed. -/
def wrongPoly : SumcheckRound.Message E 2 :=
  #v[(ProductSum.roundPoly tA tB 1 #v[e1])[0], (ProductSum.roundPoly tA tB 1 #v[e1])[1] + 1,
    (ProductSum.roundPoly tA tB 1 #v[e1])[2]]

#guard SumcheckRound.weightedSum 2 [((0 : E), (1 : E)), (1, 1)] wrongPoly ≠
  ProductSum.claim tA tB 1 #v[e1]

/-! ## Linearity in the weight -/

/-- The batch of two weight tables. -/
def batchAC : CMlPolynomialEval E 3 := batchWeight ![tA, tC] lam

#guard ProductSum.roundPoly batchAC tB 1 #v[e1] =
  batchMessage ![ProductSum.roundPoly tA tB 1 #v[e1], ProductSum.roundPoly tC tB 1 #v[e1]] lam
#guard ProductSum.claim batchAC tB 1 #v[e1] =
  powerBatch ![ProductSum.claim tA tB 1 #v[e1], ProductSum.claim tC tB 1 #v[e1]] lam
-- a message batched with the wrong scalar is another message
#guard ProductSum.roundPoly batchAC tB 1 #v[e1] ≠
  batchMessage ![ProductSum.roundPoly tA tB 1 #v[e1], ProductSum.roundPoly tC tB 1 #v[e1]] (lam + 1)

/-! ## The word -/

/-- A table on `ℓ + κ = 2 + 2` coordinates. -/
def tw : CMlPolynomialEval E (2 + 2) :=
  Vector.ofFn fun i : Fin 16 ↦ algebraMap K E (K.ofBits (0x517cc1b727220a95 * (i.val + 1)))

def fr : Vector E 2 := #v[e1, e2]

-- the folded row at a position is the folded table's encoding there
#guard (List.range 8).all fun y ↦
  foldRow fr ((wordOf 2 2 1 3 tw).row ⟨y % 8, by omega⟩) =
    encode (algebraMap K E) 2 1 (foldTable tw fr) ⟨y % 8, by omega⟩

end LeanerVMTests.Protocol
