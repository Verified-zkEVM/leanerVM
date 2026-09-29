/-
  LeanerVM.Protocol.ClaimWeights

  A claim on one column of the stack is a weighted claim on the stack, the weight being the
  equality kernel at the claim's point lifted through the layout.
-/

module

public import LeanerVM.Protocol.Spine.Seams
public import LeanerVM.Protocol.ToCompPoly.BitProductTable

/-!
# Column claims as weighted claims

The opening argument works on one kind of claim, `⟨W, q⟩ = c` for a weight `W` on the stack. A
claim `P̃(z) = c` on a column joins that pool through the stacking identity: with `p` the point
`z` lifted through the layout, `P̃(z) = q̃(p) = Σ_w eq(p, w) q(w)` (specification §4.1,
`doc/leanvm/body/04-committing-the-witness.tex:12-18`). `eqWeight p` is that weight, with the
closed form of its extension the verifier evaluates, and `ColumnClaim.holds_iff_weighted` is the
step, for any instance and any committed column. It uses the reading law of the instance's
layout and nothing about how the layout was built.

Category A: written from the specification.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly CMlPolynomialEval

@[expose] public section

/-- The pairing of a weight with a column is the cube sum of their pointwise product. -/
theorem Weight.pair_eq_sumCube {μ : ℕ} (W : Weight μ) (q : Column μ) :
    W.pair q =
      sumCube (hadamard W.onCube (CMlPolynomialEval.map (algebraMap K E) q.values)) := by
  unfold Weight.pair sumCube
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hadamard_getElem]
  simp only [CMlPolynomialEval.map, Fin.getElem_fin, Vector.getElem_map, Vector.get_eq_getElem]
  rfl

/-- The equality kernel at a point, as a weight: its cube values are the Lagrange basis, and
its extension is the product of the coordinatewise factors. -/
def eqWeight {μ : ℕ} (p : Vector E μ) : Weight μ where
  onCube := lagrangeBasis p
  mle := fun r ↦ ∏ k : Fin μ, ((1 - r[k]) * (1 - p[k]) + r[k] * p[k])
  mle_eq := fun r ↦ (evalMle_lagrangeBasis p r).symm

/-- Pairing the equality kernel at `p` with a column evaluates the column at `p`. -/
theorem eqWeight_pair {μ : ℕ} (p : Vector E μ) (q : Column μ) :
    (eqWeight p).pair q = eval₂Mle q.values (algebraMap K E) p := by
  rw [Weight.pair_eq_sumCube, eval₂Mle, evalMle_eq_sumCube_hadamard]
  rfl

/-- A column claim is the weighted claim on the stack whose weight is the equality kernel at
the claim's point lifted through the layout. -/
theorem ColumnClaim.holds_iff_weighted {I : M3Instance} (q : Column I.μ) (c : ColumnClaim I) :
    c.Holds q ↔
      WeightedClaim.Holds q ⟨eqWeight (I.layout.extend c.col c.point), c.value⟩ := by
  unfold ColumnClaim.Holds WeightedClaim.Holds
  rw [eqWeight_pair, ← I.layout.read_eval]
  rfl

end
end LeanerVM.Protocol
