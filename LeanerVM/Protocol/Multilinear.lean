/-
  LeanerVM.Protocol.Multilinear

  Generic algebra of hypercube tables: sums over the cube, the equality kernel as a table,
  splitting a cube into a low block and a high block, slices at Boolean high coordinates, and
  back-loaded padding. Protocol roadmap Layer 1, generic half.
-/

module

public import CompPoly.Multilinear.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Hypercube tables

Protocol roadmap Layer 1 (`docs/roadmap/protocol-blueprint.md`), the generic half: everything
here is over an arbitrary commutative ring `R` and CompPoly's value tables
`CMlPolynomialEval R n` (a `Vector R (2 ^ n)`, bit `k` of the index being coordinate `k`, low bit
first). Category A: nothing here transcribes a source.

Derived from Verified-zkEVM/leanth `leanth-project` at 23929f8c, by Aristotle (Harmonic),
Stefano Rocca and Elias Judin, ported to CompPoly's tables and little-endian indexing
(`docs/roadmap/leanth-reuse.md`): the partition of unity `sumCube_eqTable`
(`Polynomial/Multilinear.lean:213`, `eqTilde_sum_cube`), the padding collapse `sumCube_padHigh`
and `sumCube_prodVars` (`ProofSystem/ZeroCheck.lean:836-886`, `sum_prod_cube_eq_one`,
`sum_prefix_collapse`), and the block-selection identity `evalMle_append_boolVec`
(`ProofSystem/Stacking.lean:603`, `eval_MLE_stack_block`; its little-endian restatement on the
explore branch, `Stacking/MLE.lean`, `eval_stackPoly_sel`). The proofs are new: they go through
`eval_mle_eq_eval`, the dot product with `lagrangeBasis`, and one lemma,
`lagrangeBasis_cubeIndex`, factoring the Lagrange basis across a split of the index.

## Conventions

* A point is a `Vector R n`; `z ++ s` puts `z` in the low coordinates.
* `cubeIndex i j = i + 2 ^ k * j` is the index whose low `k` bits are `i` and whose high `m`
  bits are `j`; `sum_cube_split` rewrites a sum over the cube as a double sum.
* `boolVec j` is the point of the cube with index `j`, as ring elements.
* `eqTable r` is CompPoly's `lagrangeBasis r`, the values of `eq(r, ·)` on the cube; in
  characteristic 2 the factor `r_k x_k + (1 - r_k)(1 - x_k)` is `1 + r_k + x_k`.

## Wrong readings excluded

* `evalMle_append_boolVec` reads the slice at the *high* index `j`; a version slicing on the
  low index is a different (strided) selection and is not what stacking uses.
* `padHigh` places the table where the high coordinates are all ones, so the pad sums to the
  table's own sum (`sumCube_padHigh`); padding by zero everywhere would multiply the sum by
  `2 ^ m` under an eq-weight, which is acceptance test 7 of the roadmap.
-/

namespace LeanerVM.Protocol

open CompPoly CMlPolynomialEval

@[expose] public section

variable {R : Type*} [CommRing R]

/-! ## Sums and products of tables -/

/-- The sum of a table over the cube. -/
def sumCube {n : ℕ} (t : CMlPolynomialEval R n) : R := ∑ i : Fin (2 ^ n), t[i]

/-- The pointwise product of two tables. -/
def hadamard {n : ℕ} (s t : CMlPolynomialEval R n) : CMlPolynomialEval R n :=
  Vector.ofFn fun i ↦ s[i] * t[i]

@[simp] theorem hadamard_getElem {n : ℕ} (s t : CMlPolynomialEval R n) (i : Fin (2 ^ n)) :
    (hadamard s t)[i] = s[i] * t[i] := by
  simp [hadamard]

/-- The equality kernel `eq(r, ·)` on the cube: CompPoly's Lagrange basis at `r`. -/
abbrev eqTable {n : ℕ} (r : Vector R n) : CMlPolynomialEval R n := lagrangeBasis r

/-- `lagrangeBasis_getElem` with a natural-number index. -/
theorem lagrangeBasis_getElem_nat {n : ℕ} (w : Vector R n) {a : ℕ} (ha : a < 2 ^ n) :
    (lagrangeBasis w)[a] = ∏ b : Fin n, if a.testBit b then w[b] else 1 - w[b] := by
  have h := lagrangeBasis_getElem (w := w) ⟨a, ha⟩
  simp only [Fin.getElem_fin, BitVec.getLsb_eq_getElem, BitVec.getElem_ofFin] at h
  exact h

/-- Multilinear evaluation is the dot product of the table with the Lagrange basis. -/
theorem evalMle_eq_sum {n : ℕ} (t : CMlPolynomialEval R n) (x : Vector R n) :
    evalMle t x = ∑ i : Fin (2 ^ n), t[i] * (lagrangeBasis x)[i] := by
  rw [eval_mle_eq_eval, CMlPolynomialEval.eval, Vector.dotProduct_eq_root_dotProduct]
  simp [dotProduct, Vector.get_eq_getElem]

/-- Evaluating at `r` is summing the table against the equality kernel at `r`. -/
theorem eval_eq_sum_eqTable {n : ℕ} (t : CMlPolynomialEval R n) (r : Vector R n) :
    evalMle t r = sumCube (hadamard (eqTable r) t) := by
  rw [evalMle_eq_sum, sumCube]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [hadamard_getElem, mul_comm]

/-- The all-ones table extends to the constant one. -/
theorem evalMle_replicate_one {n : ℕ} (x : Vector R n) :
    evalMle (Vector.replicate (2 ^ n) (1 : R)) x = 1 := by
  induction n with
  | zero => simp [evalMle_zero]
  | succ n ih =>
    rw [evalMle_succ]
    have h : evalMleLayer (Vector.replicate (2 ^ (n + 1)) (1 : R)) x.head =
        Vector.replicate (2 ^ n) 1 := by
      apply Vector.ext
      intro j hj
      rw [← Vector.get_eq_getElem _ ⟨j, hj⟩, evalMleLayer_get]
      simp only [Vector.get_replicate, Vector.getElem_replicate]
      ring
    rw [h, ih]

/-- The all-zeros table extends to the constant zero. -/
theorem evalMle_replicate_zero {n : ℕ} (x : Vector R n) :
    evalMle (Vector.replicate (2 ^ n) (0 : R)) x = 0 := by
  rw [evalMle_eq_sum]
  simp

/-- Evaluation is invariant under casting the number of variables. -/
theorem evalMle_cast {n n' : ℕ} (h : n = n') (h2 : 2 ^ n = 2 ^ n') (t : CMlPolynomialEval R n)
    (x : Vector R n) : evalMle (Vector.cast h2 t) (Vector.cast h x) = evalMle t x := by
  subst h
  simp

/-- The equality kernel sums to one over the cube: the partition of unity behind every
eq-weighted sum. -/
theorem sumCube_eqTable {n : ℕ} (r : Vector R n) : sumCube (eqTable r) = 1 := by
  have h := evalMle_replicate_one r
  rw [evalMle_eq_sum] at h
  simpa [sumCube, eqTable] using h

/-! ## Splitting the cube -/

/-- The index of the cube `{0,1}^(k+m)` whose low `k` bits are `i` and whose high `m` bits are
`j`. -/
def cubeIndex {k m : ℕ} (i : Fin (2 ^ k)) (j : Fin (2 ^ m)) : Fin (2 ^ (k + m)) :=
  ⟨i.val + 2 ^ k * j.val, by
    rw [pow_add]
    calc i.val + 2 ^ k * j.val < 2 ^ k + 2 ^ k * j.val := Nat.add_lt_add_right i.isLt _
      _ = 2 ^ k * (j.val + 1) := by ring
      _ ≤ 2 ^ k * 2 ^ m := Nat.mul_le_mul_left _ j.isLt⟩

@[simp] theorem cubeIndex_val {k m : ℕ} (i : Fin (2 ^ k)) (j : Fin (2 ^ m)) :
    (cubeIndex i j).val = i.val + 2 ^ k * j.val := rfl

theorem cubeIndex_div {k m : ℕ} (i : Fin (2 ^ k)) (j : Fin (2 ^ m)) :
    (cubeIndex i j).val / 2 ^ k = j.val := by
  rw [cubeIndex_val, Nat.add_mul_div_left _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt i.isLt,
    zero_add]

theorem cubeIndex_mod {k m : ℕ} (i : Fin (2 ^ k)) (j : Fin (2 ^ m)) :
    (cubeIndex i j).val % 2 ^ k = i.val := by
  rw [cubeIndex_val, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]

/-- Bit `a` of `cubeIndex i j` is bit `a` of `i` below `k` and bit `a - k` of `j` above. -/
theorem testBit_cubeIndex {k m : ℕ} (i : Fin (2 ^ k)) (j : Fin (2 ^ m)) (a : ℕ) :
    (cubeIndex i j).val.testBit a = if a < k then i.val.testBit a else j.val.testBit (a - k) := by
  rw [cubeIndex_val, add_comm]
  exact Nat.testBit_two_pow_mul_add j.val i.isLt a

/-- The split of the cube into low and high blocks, as an equivalence. -/
def cubeSplit (k m : ℕ) : Fin (2 ^ k) × Fin (2 ^ m) ≃ Fin (2 ^ (k + m)) :=
  (Equiv.prodComm _ _).trans (finProdFinEquiv.trans (finCongr (by rw [pow_add, mul_comm])))

@[simp] theorem cubeSplit_apply {k m : ℕ} (i : Fin (2 ^ k)) (j : Fin (2 ^ m)) :
    cubeSplit k m (i, j) = cubeIndex i j := by
  ext
  simp [cubeSplit, cubeIndex]

/-- A sum over the cube is a double sum over the high and the low block. -/
theorem sum_cube_split {M : Type*} [AddCommMonoid M] {k m : ℕ} (f : Fin (2 ^ (k + m)) → M) :
    ∑ x, f x = ∑ j : Fin (2 ^ m), ∑ i : Fin (2 ^ k), f (cubeIndex i j) := by
  rw [← (cubeSplit k m).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  simp

/-- The low `k` coordinates of a point. -/
def lowVec {k m : ℕ} (w : Vector R (k + m)) : Vector R k :=
  Vector.ofFn fun a ↦ w[a.val]'(by omega)

/-- The high `m` coordinates of a point. -/
def highVec {k m : ℕ} (w : Vector R (k + m)) : Vector R m :=
  Vector.ofFn fun b ↦ w[k + b.val]'(by omega)

omit [CommRing R] in
@[simp] theorem lowVec_append {k m : ℕ} (z : Vector R k) (s : Vector R m) :
    lowVec (z ++ s) = z := by
  apply Vector.ext
  intro a _
  simp [lowVec]

omit [CommRing R] in
@[simp] theorem highVec_append {k m : ℕ} (z : Vector R k) (s : Vector R m) :
    highVec (z ++ s) = s := by
  apply Vector.ext
  intro b hb
  simp [highVec, Vector.getElem_append_right]

/-- The Lagrange basis factors across the split of the index. -/
theorem lagrangeBasis_cubeIndex {k m : ℕ} (w : Vector R (k + m)) (i : Fin (2 ^ k))
    (j : Fin (2 ^ m)) :
    (lagrangeBasis w)[cubeIndex i j] =
      (lagrangeBasis (lowVec w))[i] * (lagrangeBasis (highVec w))[j] := by
  simp only [Fin.getElem_fin, lagrangeBasis_getElem_nat, testBit_cubeIndex]
  rw [Fin.prod_univ_add]
  congr 1
  · refine Finset.prod_congr rfl fun a _ ↦ ?_
    simp [lowVec, a.isLt]
  · refine Finset.prod_congr rfl fun b _ ↦ ?_
    simp [highVec]

/-! ## Boolean points and slices -/

/-- The point of the cube with index `j`, as ring elements. -/
def boolVec {m : ℕ} (j : Fin (2 ^ m)) : Vector R m :=
  Vector.ofFn fun b ↦ if j.val.testBit b then 1 else 0

/-- Two indices below `2 ^ m` agree iff their `m` low bits agree. -/
theorem fin_eq_iff_testBit {m : ℕ} (i j : Fin (2 ^ m)) :
    i = j ↔ ∀ b : Fin m, i.val.testBit b = j.val.testBit b := by
  refine ⟨fun h b ↦ by rw [h], fun h ↦ Fin.ext (Nat.eq_of_testBit_eq fun b ↦ ?_)⟩
  by_cases hb : b < m
  · exact h ⟨b, hb⟩
  · have hi : i.val < 2 ^ b :=
      lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hj : j.val < 2 ^ b :=
      lt_of_lt_of_le j.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_lt_two_pow hi, Nat.testBit_lt_two_pow hj]

/-- The Lagrange basis at a Boolean point is the indicator of that point. -/
theorem lagrangeBasis_boolVec {m : ℕ} (j i : Fin (2 ^ m)) :
    (lagrangeBasis (boolVec j : Vector R m))[i.val] = if i = j then 1 else 0 := by
  rw [lagrangeBasis_getElem_nat _ i.isLt]
  have h : ∀ b : Fin m,
      (if i.val.testBit b then (boolVec j : Vector R m)[b]
        else 1 - (boolVec j : Vector R m)[b]) =
      if i.val.testBit b = j.val.testBit b then 1 else 0 := by
    intro b
    simp only [boolVec, Fin.getElem_fin, Vector.getElem_ofFn]
    cases i.val.testBit b <;> cases j.val.testBit b <;> simp
  simp only [h, Fintype.prod_boole]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij, (fin_eq_iff_testBit i j).not.mp hij]

/-- Evaluating a table at a point of the cube reads the entry. -/
theorem evalMle_boolVec {m : ℕ} (t : CMlPolynomialEval R m) (j : Fin (2 ^ m)) :
    evalMle t (boolVec j) = t[j] := by
  rw [evalMle_eq_sum]
  simp only [Fin.getElem_fin, lagrangeBasis_boolVec, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The slice of a table at the high index `j`: the entries whose high `m` bits are `j`. -/
def slice {k m : ℕ} (t : CMlPolynomialEval R (k + m)) (j : Fin (2 ^ m)) :
    CMlPolynomialEval R k :=
  Vector.ofFn fun i ↦ t[cubeIndex i j]

omit [CommRing R] in
theorem slice_getElem {k m : ℕ} (t : CMlPolynomialEval R (k + m)) (j : Fin (2 ^ m))
    (i : Fin (2 ^ k)) : (slice t j)[i] = t[cubeIndex i j] := by
  simp [slice]

/-- The bound of `cubeIndex`, on natural numbers. -/
theorem cubeIndex_lt {k m : ℕ} {i : ℕ} (hi : i < 2 ^ k) (j : Fin (2 ^ m)) :
    i + 2 ^ k * j.val < 2 ^ (k + m) :=
  (cubeIndex ⟨i, hi⟩ j).isLt

omit [CommRing R] in
/-- `slice_getElem` with a natural-number index. -/
theorem slice_getElem_nat {k m : ℕ} (t : CMlPolynomialEval R (k + m)) (j : Fin (2 ^ m)) {i : ℕ}
    (hi : i < 2 ^ k) :
    (slice t j)[i] = t[i + 2 ^ k * j.val]'(cubeIndex_lt hi j) := by
  rw [slice, Vector.getElem_ofFn]
  rfl

/-- Evaluation at a split point is the eq-weighted sum of the slices' evaluations. -/
theorem evalMle_split {k m : ℕ} (t : CMlPolynomialEval R (k + m)) (z : Vector R k)
    (s : Vector R m) :
    evalMle t (z ++ s) = ∑ j : Fin (2 ^ m), (lagrangeBasis s)[j] * evalMle (slice t j) z := by
  rw [evalMle_eq_sum, sum_cube_split]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [evalMle_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [lagrangeBasis_cubeIndex, lowVec_append, highVec_append, slice_getElem]
  ring

/-- The selection identity: a Boolean high coordinate selects the slice at that index. -/
theorem evalMle_append_boolVec {k m : ℕ} (t : CMlPolynomialEval R (k + m)) (z : Vector R k)
    (j : Fin (2 ^ m)) :
    evalMle t (z ++ (boolVec j : Vector R m)) = evalMle (slice t j) z := by
  rw [evalMle_split]
  simp only [Fin.getElem_fin, lagrangeBasis_boolVec, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-! ## Back-loaded padding -/

/-- The index of the all-ones point of `{0,1}^m`. -/
def onesIndex (m : ℕ) : Fin (2 ^ m) :=
  ⟨(2 ^ m - 1 : ℕ), by have := Nat.two_pow_pos m; omega⟩

/-- The table of `x_0 ⋯ x_{m-1}` on the cube: the indicator of the all-ones point. -/
def prodVars (m : ℕ) : CMlPolynomialEval R m :=
  Vector.ofFn fun i ↦ if i = onesIndex m then 1 else 0

/-- `Σ_x x_0 ⋯ x_{m-1} = 1`. -/
theorem sumCube_prodVars (m : ℕ) : sumCube (prodVars m : CMlPolynomialEval R m) = 1 := by
  simp [sumCube, prodVars]

/-- The Lagrange basis at the all-ones index is the product of the coordinates. -/
theorem lagrangeBasis_onesIndex {m : ℕ} (s : Vector R m) :
    (lagrangeBasis s)[(onesIndex m).val] = ∏ b : Fin m, s[b] := by
  rw [lagrangeBasis_getElem_nat _ (onesIndex m).isLt]
  refine Finset.prod_congr rfl fun b _ ↦ ?_
  simp [onesIndex, Nat.testBit_two_pow_sub_one, b.isLt]

/-- The extension of `x_0 ⋯ x_{m-1}` at `s` is the product of the coordinates of `s`. -/
theorem evalMle_prodVars {m : ℕ} (s : Vector R m) :
    evalMle (prodVars m) s = ∏ b : Fin m, s[b] := by
  rw [evalMle_eq_sum]
  simp only [Fin.getElem_fin, prodVars, Vector.getElem_ofFn, Fin.eta, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact lagrangeBasis_onesIndex s

/-- A table of `k` variables lifted to `k + m` variables by `∏_{c ≥ k} X_c`: its entries sit
where the high coordinates are all ones, and everything else is zero. -/
def padHigh {k : ℕ} (t : CMlPolynomialEval R k) (m : ℕ) : CMlPolynomialEval R (k + m) :=
  Vector.ofFn fun x ↦
    if x.val / 2 ^ k = 2 ^ m - 1 then t[x.val % 2 ^ k]'(Nat.mod_lt _ (Nat.two_pow_pos k)) else 0

theorem slice_padHigh_ones {k m : ℕ} (t : CMlPolynomialEval R k) :
    slice (padHigh t m) (onesIndex m) = t := by
  apply Vector.ext
  intro i hi
  have hdiv := cubeIndex_div (⟨i, hi⟩ : Fin (2 ^ k)) (onesIndex m)
  simp only [cubeIndex_val, onesIndex] at hdiv
  simp [slice, padHigh, hdiv, onesIndex, Nat.mod_eq_of_lt hi]

theorem slice_padHigh_of_ne {k m : ℕ} (t : CMlPolynomialEval R k) {j : Fin (2 ^ m)}
    (hj : j ≠ onesIndex m) : slice (padHigh t m) j = Vector.replicate (2 ^ k) 0 := by
  apply Vector.ext
  intro i hi
  have hdiv := cubeIndex_div (⟨i, hi⟩ : Fin (2 ^ k)) j
  simp only [cubeIndex_val] at hdiv
  have hj' : j.val ≠ 2 ^ m - 1 := fun h ↦ hj (Fin.ext h)
  simp [slice, padHigh, hdiv, hj']

/-- Back-loaded padding preserves the sum over the cube. -/
theorem sumCube_padHigh {k : ℕ} (t : CMlPolynomialEval R k) (m : ℕ) :
    sumCube (padHigh t m) = sumCube t := by
  rw [sumCube, sum_cube_split, Finset.sum_eq_single (onesIndex m)]
  · simp only [← slice_getElem, slice_padHigh_ones]
    rfl
  · intro j _ hj
    simp only [← slice_getElem, slice_padHigh_of_ne t hj]
    simp
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The extension of a padded table is the table's extension times the product of the high
coordinates. -/
theorem evalMle_padHigh {k m : ℕ} (t : CMlPolynomialEval R k) (z : Vector R k)
    (s : Vector R m) :
    evalMle (padHigh t m) (z ++ s) = evalMle t z * ∏ b : Fin m, s[b] := by
  rw [evalMle_split, Finset.sum_eq_single (onesIndex m)]
  · rw [slice_padHigh_ones, Fin.getElem_fin, lagrangeBasis_onesIndex, mul_comm]
  · intro j _ hj
    rw [slice_padHigh_of_ne t hj, evalMle_replicate_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

end
end LeanerVM.Protocol
