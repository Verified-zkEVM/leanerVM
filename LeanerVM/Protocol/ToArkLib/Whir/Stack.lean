/-
  LeanerVM.Protocol.ToArkLib.Whir.Stack

  The weight of the committed stack with its lanes first: the relayout of a weight, its
  extension at the rotated point, and the invariance of the weighted claim. Candidate for
  ArkLib.
-/

module

public import LeanerVM.Protocol.WhirFold
public import LeanerVM.Protocol.ToArkLib.InnerProduct

/-!
# The stack's weight, lanes first

The committed stack has its lanes on top (`relayout`, `LeanerVM.Protocol.WhirFold`); the opening
phase's weight is on the stack's coordinates. The opening reduces the claim on the stack to a claim
on the relayout of the stack, whose first coordinates are the lanes the first level folds, so the
weight has to be relayed out the same way: `relayoutWeight W` has the values of `W` with the same
two blocks of coordinates exchanged, and its extension at a point is the extension of `W` at the
point rotated, the high block first (`whir.rs`, `rotate_left(initial_k)`).

* `relayoutWeight`: the weight on the relayout;
* `pair_relayoutWeight`: the weighted claim of the relayout against the relayout is the stack's:
  relaying both out reorders the sum.
-/

namespace LeanerVM.Protocol

open CompPoly CMlPolynomialEval

@[expose] public section

variable {S : Type*} [CommRing S]

/-- The weight on the relayout of a stack: the values with the low `κ` and high `ℓ` coordinates
exchanged, the extension at a point the stack's weight at the point rotated. -/
def relayoutWeight {κ ℓ : ℕ} (W : Weight S (κ + ℓ)) : Weight S (ℓ + κ) where
  onCube := relayout W.onCube
  mle := fun p ↦ W.mle (highVec p ++ lowVec p)
  mle_eq := fun p ↦ by
    have h := evalMle_relayout W.onCube (lowVec p) (highVec p)
    rw [lowVec_append_highVec] at h
    rw [h, W.mle_eq]

/-- The weighted claim of the relayout against the relayout of a table is the weighted claim of
the stack: both sums run over the same pairs of entries, in another order. -/
theorem pair_relayoutWeight {R : Type*} [CommRing R] (φ : R →+* S) {κ ℓ : ℕ}
    (W : Weight S (κ + ℓ)) (q : CMlPolynomialEval R (κ + ℓ)) :
    (relayoutWeight W).pair φ (relayout q) = W.pair φ q := by
  unfold Weight.pair
  rw [sum_cube_split, sum_cube_split, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun u _ ↦ ?_
  simp only [relayoutWeight, relayout_getElem]

end

end LeanerVM.Protocol
