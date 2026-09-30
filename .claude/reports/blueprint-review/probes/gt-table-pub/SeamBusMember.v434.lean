import LeanerVM.Protocol.Spine.Toy
import LeanerVM.Protocol.Spine.Seams

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Toy CompPoly CPoly

namespace Probe

def q0 : Column 3 := ⟨#v[1, 1, 1, 1, 0, 0, 0, 0]⟩

def termAt0 : VirtualTerm toy :=
  ⟨1, 0, CMvPolynomial.X 2 * CMvPolynomial.X 2 - CMvPolynomial.X 2, #v[0]⟩
def termAt1 : VirtualTerm toy :=
  ⟨1, 0, CMvPolynomial.X 2 * CMvPolynomial.X 2 - CMvPolynomial.X 2, #v[1]⟩
def twoPoints : LinearClaim toy := ⟨[termAt0, termAt1], 0⟩

instance (q : Column toy.μ) (c : LinearClaim toy) : Decidable (c.Holds q) :=
  inferInstanceAs (Decidable (_ = _))

-- Every clause of the seam, evaluated.
#guard twoPoints.Holds q0
#guard ∀ t ∈ twoPoints.terms, t.poly.totalDegree ≤ toy.d
#guard toy.PublicLinesHold (0 : K) q0

end Probe
