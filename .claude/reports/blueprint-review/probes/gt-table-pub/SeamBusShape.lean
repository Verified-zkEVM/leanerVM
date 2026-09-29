import LeanerVM.Protocol.Spine.Toy
import LeanerVM.Protocol.Spine.Seams
import LeanerVM.Protocol.Spine.Compose

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Toy CompPoly CPoly

namespace Probe

/-- Columns `[1, 1]`, `[1, 1]`, `[0, 0]`: an honest stack of the toy at statement `0`. -/
def q0 : Column 3 := ⟨#v[1, 1, 1, 1, 0, 0, 0, 0]⟩

#guard M3Holds toy (0 : K) q0

/-- The cubic term `X₂³` at the point `0`, weight one. -/
def cubicTerm : VirtualTerm toy :=
  ⟨1, 0, CMvPolynomial.X 2 * CMvPolynomial.X 2 * CMvPolynomial.X 2, #v[0]⟩

/-- The value of the cubic term on `q0`. -/
def cubicValue : E := cubicTerm.eval q0

-- The claim "the cubic term sums to 0" is true of `q0` ...
#guard cubicValue == 0

def cubicClaim : LinearClaim toy := ⟨[cubicTerm], 0⟩

def cubicSum : E := (cubicClaim.terms.map fun t ↦ t.eval q0).sum

#guard cubicSum == cubicClaim.value

-- ... the public line holds of `q0` at statement `0` (the toy's `aux` is `True`) ...
#guard toy.PublicLinesHold (0 : K) q0

-- ... and the statement is outside the bus seam all the same: only the degree clause fails.
example (o : ∀ i, TheOracle toy i) :
    ((((0 : K), (⟨[cubicClaim], []⟩ : BusOut toy)), o), ()) ∉ Seam.bus toy := fun h ↦
  absurd (h.2.1 _ (List.mem_singleton_self _) _ (List.mem_singleton_self _)) (by decide +kernel)

/-- The toy's constraint at the point `0`. -/
def termAt0 : VirtualTerm toy :=
  ⟨1, 0, CMvPolynomial.X 2 * CMvPolynomial.X 2 - CMvPolynomial.X 2, #v[0]⟩

/-- The same constraint at the point `1`: a different point for the same table. -/
def termAt1 : VirtualTerm toy :=
  ⟨1, 0, CMvPolynomial.X 2 * CMvPolynomial.X 2 - CMvPolynomial.X 2, #v[1]⟩

def v0 : E := termAt0.eval q0
def v1 : E := termAt1.eval q0

#guard v0 == 0
#guard v1 == 0

/-- One linear claim with two terms of the same table at two different points. -/
def twoPoints : LinearClaim toy := ⟨[termAt0, termAt1], 0⟩

def twoPointsSum : E := (twoPoints.terms.map fun t ↦ t.eval q0).sum

#guard twoPointsSum == twoPoints.value

-- The points differ: no single `ζ` has both as its prefix of length `τ = 1`.
#guard termAt0.point.toList ≠ termAt1.point.toList

/-- A thousand copies of a true claim: the seam puts no bound on the number of linear claims,
while the toy has one constraint and one flush. -/
def manyClaims : List (LinearClaim toy) := List.replicate 1000 ⟨[termAt0], 0⟩

#guard manyClaims.length = 1000
#guard (toy.constraints 0).length = 1
#guard (toy.flushes 0).length = 1

end Probe
