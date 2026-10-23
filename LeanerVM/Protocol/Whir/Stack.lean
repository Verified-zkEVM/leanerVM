/-
  LeanerVM.Protocol.Whir.Stack

  The weight of the committed stack with its lanes first: the relayout of a weight, its
  extension at the rotated point, and the invariance of the weighted claim.
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
  relaying both out reorders the sum;
* `relayout_relayout`: relaying out twice is the identity.
-/

namespace LeanerVM.Protocol

open CompPoly CMlPolynomialEval

@[expose] public section

variable {S : Type*} [CommRing S]

omit [CommRing S] in
/-- The relayout undone: exchanging the two blocks of coordinates twice. -/
theorem relayout_relayout {ℓ κ : ℕ} (t : CMlPolynomialEval S (ℓ + κ)) :
    relayout (κ := κ) (ℓ := ℓ) (relayout (κ := ℓ) (ℓ := κ) t) = t := by
  have key : ∀ j : Fin (2 ^ (ℓ + κ)),
      (relayout (κ := κ) (ℓ := ℓ) (relayout (κ := ℓ) (ℓ := κ) t))[j] = t[j] := fun j ↦ by
    obtain ⟨⟨u, x⟩, rfl⟩ := (cubeSplit ℓ κ).surjective j
    rw [cubeSplit_apply, relayout_getElem, relayout_getElem]
  exact Vector.ext fun i hi ↦ key ⟨i, hi⟩

/-- The weight on the relayout of a stack: the values with the low `κ` and high `ℓ` coordinates
exchanged, the extension at a point the stack's weight at the point rotated. As for `foldWeight`,
the verifier reads `mle` only, and the table is built only when `onCube` is read. -/
def relayoutWeight {κ ℓ : ℕ} (W : Weight S (κ + ℓ)) : Weight S (ℓ + κ) where
  cube := .mk fun _ ↦ relayout W.onCube
  mle := fun p ↦ W.mle (highVec p ++ lowVec p)
  mle_eq := fun p ↦ by
    have h := evalMle_relayout W.onCube (lowVec p) (highVec p)
    rw [lowVec_append_highVec] at h
    show _ = evalMle (relayout W.onCube) p
    rw [h, W.mle_eq]

/-- The relayout's values, as built. -/
theorem relayoutWeight_onCube {κ ℓ : ℕ} (W : Weight S (κ + ℓ)) :
    (relayoutWeight W).onCube = relayout W.onCube := rfl

/-- The weighted claim of the relayout against the relayout of a table is the weighted claim of
the stack: both sums run over the same pairs of entries, in another order. -/
theorem pair_relayoutWeight {R : Type*} [CommRing R] (φ : R →+* S) {κ ℓ : ℕ}
    (W : Weight S (κ + ℓ)) (q : CMlPolynomialEval R (κ + ℓ)) :
    (relayoutWeight W).pair φ (relayout q) = W.pair φ q := by
  unfold Weight.pair
  rw [sum_cube_split, sum_cube_split, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun u _ ↦ ?_
  simp only [relayoutWeight_onCube, relayout_getElem]

end

end LeanerVM.Protocol
