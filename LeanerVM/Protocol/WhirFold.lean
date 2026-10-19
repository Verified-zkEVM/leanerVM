/-
  LeanerVM.Protocol.WhirFold

  The fold of WHIR's interleaved word: folding the lanes of a table, the fold of the encoded
  lanes against the encoding of the folded table, the consistency claim a queried position
  yields, and the relayout of the stack that puts its lanes first (Annex B, `sec:protocol`).
-/

module

public import LeanerVM.Protocol.NovelBasis

/-!
# Folding the lanes

Protocol roadmap Layer 11 (`docs/roadmap/protocol-blueprint.md`), slice 2a of the WHIR opening
(issue #101). Annex B, Protocol 1 (`doc/leanvm/body/b-polynomial-commitment-scheme.tex`,
`fig:protocol`) and `fact:fold-decode`, at leanVM pin `a386121f84292f6fa663aaa3e570c15bc0240ea2`;
the conventions are those of `python-verifier/verifier.py` (`eq_kernel`, `multilinear_eval`,
`_induced_weight`: little-endian, a sum over a table binds coordinate `0` first) and of
`crates/pcs/src/whir.rs` (the comment above `rotate_left(initial_k)`). Nothing here is a
protocol: these are the identities about tables the completeness of one level rests on.

A level's table `t` has `ℓ + κ` coordinates, little-endian as everywhere here: the *low* `ℓ`
coordinates index a *lane* `u`, the high `κ` coordinates a position `x` of the lane's message, so
lane `u` is the message `sliceLow t u` (the entries whose low bits are `u`, one every `2 ^ ℓ`).
The word the prover commits holds, at the domain position `y` and the lane `u`, the symbol
`Enc(sliceLow t u)[y]` (`encode`). The `ℓ` fold challenges of the level, in round order, are the
point `r`: round `a` binds lane coordinate `a`, the lowest first.

* `foldTable t r` binds the lanes at `r`: `(foldTable t r)[x] = Σ_u eq(r,u) t[u,x]`
  (`foldTable_getElem`).
* `encode_foldTable` (`fact:fold-decode`): the fold of the encoded lanes is the encoding of
  the folded table, `Σ_u eq(r,u) Enc(sliceLow t u)[y] = Enc(foldTable t r)[y]`. It is the
  linearity of the encoder, and it is what makes the symbol the verifier reads and folds, `c_q`,
  a claim about the folded table.
* `pair_columnWeight_foldTable`: that claim is the weighted claim `<W_y, foldTable t r> = c_q`
  with the column weight `W_y` of position `y` (`encode_columnWeight`, `lem:colweight`), the
  consistency claim of step 3(d) of the protocol.
* `evalMle_foldTable`: binding the lanes then evaluating is evaluating at the point with the
  bound coordinates first, `MLE(foldTable t r)(z) = MLE(t)(r ++ z)`; iterated, the later levels'
  challenges follow the earlier ones.
* `relayout`: the committed stack has its lanes on *top* (lane `l` is the block `q[l·H ..)`);
  the level-0 table is `relayout q`, with the lanes first: `(relayout q)[u,x] = q[x,u]`.
  `evalMle_relayout` is the verifier's rotation of the terminal point:
  `MLE(relayout q)(r ++ z) = MLE(q)(z ++ r)`, the round challenges `r ++ z` read in witness
  order `z ++ r` (`rotate_left(initial_k)`).

## Wrong readings excluded

* The lanes of a level are its *low* coordinates and the fold binds them first; binding the high
  coordinates folds a different table (tested).
* The fold is by the Lagrange basis of `r`, not by the monomials `r_a ^ u_a`: the word is a
  multilinear extension in the lane axis.
* The level-0 point is not `r ++ z` for the stack: it is `z ++ r`. Evaluating the stack at the
  unrotated point is a different value (tested).
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly CMlPolynomialEval

@[expose] public section

variable {S : Type*} [CommRing S]

/-- Folding the lanes of a table at `r`: position `x` of the folded table is the multilinear
extension, at `r`, of the lane axis (the low coordinates) of `t` at `x`. -/
def foldTable {ℓ κ : ℕ} (t : CMlPolynomialEval S (ℓ + κ)) (r : Vector S ℓ) :
    CMlPolynomialEval S κ :=
  Vector.ofFn fun x ↦ evalMle (slice t x) r

/-- The folded table's entries: the lane entries at the position, weighted by the Lagrange basis
at `r`. -/
theorem foldTable_getElem {ℓ κ : ℕ} (t : CMlPolynomialEval S (ℓ + κ)) (r : Vector S ℓ)
    (x : Fin (2 ^ κ)) :
    (foldTable t r)[x] = ∑ u : Fin (2 ^ ℓ), t[cubeIndex u x] * (lagrangeBasis r)[u] := by
  simp only [foldTable, Fin.getElem_fin, Vector.getElem_ofFn, evalMle_eq_sum]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  simp [slice]

/-- `fact:fold-decode`: the fold of the encoded lanes is the encoding of the folded table. -/
theorem encode_foldTable (φ : K →+* S) {ℓ κ : ℕ} (R : ℕ)
    (t : CMlPolynomialEval S (ℓ + κ)) (r : Vector S ℓ) (y : Fin (2 ^ (κ + R))) :
    encode φ κ R (foldTable t r) y =
      ∑ u : Fin (2 ^ ℓ), (lagrangeBasis r)[u] * encode φ κ R (sliceLow t u) y := by
  simp only [encode_eq_sum, foldTable_getElem, Finset.mul_sum, sliceLow_getElem]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun x _ ↦ ?_
  ring

/-- The consistency claim of a queried position: the folded symbol is the weighted claim of the
position's column weight on the folded table. -/
theorem pair_columnWeight_foldTable (φ : K →+* S) {ℓ κ : ℕ} (R : ℕ)
    (t : CMlPolynomialEval S (ℓ + κ)) (r : Vector S ℓ) (y : Fin (2 ^ (κ + R))) :
    (columnWeight φ κ R y).pair (RingHom.id S) (foldTable t r) =
      ∑ u : Fin (2 ^ ℓ), (lagrangeBasis r)[u] * encode φ κ R (sliceLow t u) y :=
  encode_foldTable φ R t r y

/-- Binding the lanes at `r` then evaluating at `z` is evaluating at `r` followed by `z`. -/
theorem evalMle_foldTable {ℓ κ : ℕ} (t : CMlPolynomialEval S (ℓ + κ)) (r : Vector S ℓ)
    (z : Vector S κ) : evalMle (foldTable t r) z = evalMle t (r ++ z) := by
  rw [evalMle_eq_sum, evalMle_eq_sum, sum_cube_split]
  simp only [foldTable_getElem, Finset.sum_mul, lagrangeBasis_cubeIndex, lowVec_append,
    highVec_append]
  refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun u _ ↦ ?_
  ring

/-- The stack's lanes first: the table with the low `κ` and the high `ℓ` coordinates of `q`
exchanged, `(relayout q)[u,x] = q[x,u]` (`whir.rs`: the committed witness's top `initial_k`
variables are the lane, and the lane is the first axis of the level-0 table). -/
def relayout {κ ℓ : ℕ} (q : CMlPolynomialEval S (κ + ℓ)) : CMlPolynomialEval S (ℓ + κ) :=
  Vector.ofFn fun i ↦
    q[cubeIndex ((cubeSplit ℓ κ).symm i).2 ((cubeSplit ℓ κ).symm i).1]

omit [CommRing S] in
/-- The relayout's entries. -/
theorem relayout_getElem {κ ℓ : ℕ} (q : CMlPolynomialEval S (κ + ℓ)) (u : Fin (2 ^ ℓ))
    (x : Fin (2 ^ κ)) : (relayout q)[cubeIndex u x] = q[cubeIndex x u] := by
  simp [relayout, ← cubeSplit_apply]

/-- The verifier's rotation of the terminal point: the lane challenges `r` come first in round
order and last in witness order. -/
theorem evalMle_relayout {κ ℓ : ℕ} (q : CMlPolynomialEval S (κ + ℓ)) (r : Vector S ℓ)
    (z : Vector S κ) : evalMle (relayout q) (r ++ z) = evalMle q (z ++ r) := by
  rw [evalMle_eq_sum, evalMle_eq_sum, sum_cube_split, sum_cube_split]
  simp only [lagrangeBasis_cubeIndex, lowVec_append, highVec_append, relayout_getElem]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun u _ ↦ ?_
  ring

end

end LeanerVM.Protocol
