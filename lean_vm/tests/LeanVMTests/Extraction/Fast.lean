import LeanVM.Protocol.Extraction.Fast.Extract
import LeanVMTests.Extraction.Toy

/-!
# Tests: the fast extractor's decoder

* Roth–Ruckenstein's substitution `Y := a + X·Y`: `substituteFast` (proved equal to CompPoly's
  `substituteYRootPlusXY`) agrees with it on pseudo-random polynomials over `K`;
* `decodeStacksAtFast` (proved equal to `decodeStacksAt`) decodes a toy word of `Toy.lean`.
-/

namespace LeanVMTests.Extraction

open CompPoly CompPoly.GuruswamiSudan LeanVM.Parameters LeanVM.Extraction LeanVM.Extraction.Fast

/-- A pseudo-random bivariate polynomial over `K` of `Y`-degree `< ny` and `X`-degree `< nx`. -/
def randomBivariate (seed nx ny : ℕ) : CBivariate K :=
  let r := randoms seed (nx * ny)
  CPolynomial.ofArray (Array.ofFn fun y : Fin ny ↦
    CPolynomial.ofArray (Array.ofFn fun x : Fin nx ↦ K.ofBits (r.getD (y.val * nx + x.val) 0)))

#guard (List.range 4).all fun s ↦
  let Q := randomBivariate s 12 9
  let a := K.ofBits (lcg (s + 77))
  substituteFast Q a == substituteYRootPlusXY Q a

-- A larger one, fast only (CompPoly's takes `|Q|²·ℓ/2` steps).
#guard (substituteFast (randomBivariate 9 200 40) (K.ofBits 5)).val.size = 40

/-- `decodes`, fast. -/
def decodesFast {μ : ℕ} (R A : ℕ) (q : Vector K (2 ^ μ)) (w : Array (List K)) : Bool × ℕ :=
  let l := decodeStacksAtFast μ R A fun v ↦ w.getD v []
  (l.any fun d ↦ d.toList == q.toList, l.length)

#guard decodesFast 1 3 (randomStack 1 7) (corrupt 1 [2] (wordOf 1 (randomStack 1 7))) = (true, 1)

end LeanVMTests.Extraction
