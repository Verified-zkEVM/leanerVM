/-
  LeanerVM.Protocol.ToCompPoly.Doubling

  Tables that factor over the bits of their index, the Lagrange basis among them, built by
  doubling; the multilinear extension with one product per entry; both registered for
  compilation. Candidate for CompPoly.
-/

module

public import CompPoly.Multilinear.Basic
public import LeanerVM.Protocol.ToCompPoly.FinLoop

/-!
# Tables that factor over the bits, by doubling

A table on `n` coordinates whose entry at `i` is `∏_k f k (bit k of i)` is built one coordinate at
a time: the table on the first `k + 1` coordinates is the table on the first `k` scaled by
`f k false`, followed by the same table scaled by `f k true` (`doublingTable`, `2^(n+1)`
products). CompPoly's `lagrangeBasis` takes the product per entry, `n · 2^n` products; its
doubling (`lagrangeBasisFast`) scales by `w_k` and takes the other half as the difference,
`a·(1 - w_k) = a - a·w_k`, so that it costs `2^n` products and `2^n` subtractions.

CompPoly's `evalMle` interpolates one coordinate at a time as `(1 - x)·a + x·b`, two products per
entry; `evalMleFast` takes `a + x·(b - a)`, one.

`lagrangeBasis_eq_lagrangeBasisFast`, `evalMle_eq_evalMleFast` and `eval₂Mle_eq_eval₂MleFast` are
`@[csimp]` theorems: code compiled after this module runs the fast versions. They change no
definition; the kernel never sees them. Over an arbitrary commutative ring. Nothing here
transcribes a source.
-/

namespace LeanerVM.Protocol

open CompPoly CMlPolynomialEval

@[expose] public section

variable {R : Type*} [CommRing R]

/-! ## Doubling a table that factors over the bits -/

/-- The entries of a table that factors over the bits of its index, on its first `k`
coordinates, by doubling. -/
def doublingArray {n : ℕ} (f : Fin n → Bool → R) : (k : ℕ) → k ≤ n → Array R
  | 0, _ => #[1]
  | k + 1, h =>
    let a := doublingArray f k (Nat.le_of_succ_le h)
    a.map (· * f ⟨k, h⟩ false) ++ a.map (· * f ⟨k, h⟩ true)

/-- The doubling on `k` coordinates has `2 ^ k` entries. -/
theorem size_doublingArray {n : ℕ} (f : Fin n → Bool → R) :
    ∀ (k : ℕ) (h : k ≤ n), (doublingArray f k h).size = 2 ^ k
  | 0, _ => rfl
  | k + 1, h => by
    simp only [doublingArray, Array.size_append, Array.size_map, size_doublingArray f k, pow_succ]
    omega

/-- Bit `j` of `2^k · 1 + r`, for `r < 2^k`: bit `j` of `r` below `k`, and `1` at `k`. -/
private theorem testBit_two_pow_add {k r : ℕ} (hr : r < 2 ^ k) (j : ℕ) (hj : j ≤ k) :
    (2 ^ k + r).testBit j = if j < k then r.testBit j else true := by
  have h := Nat.testBit_two_pow_mul_add 1 hr j
  rwa [mul_one, show j - k = 0 by omega] at h

/-- Entry `i` of the doubling on `k` coordinates is the product of the first `k` factors at the
bits of `i`. -/
theorem getElem_doublingArray {n : ℕ} (f : Fin n → Bool → R) :
    ∀ (k : ℕ) (h : k ≤ n) (i : ℕ) (hi : i < (doublingArray f k h).size),
      (doublingArray f k h)[i] = ∏ j : Fin k, f ⟨j, by omega⟩ (i.testBit j)
  | 0, _, i, hi => by
    obtain rfl : i = 0 := by simpa [doublingArray] using hi
    simp [doublingArray]
  | k + 1, h, i, hi => by
    have hs := size_doublingArray f k (Nat.le_of_succ_le h)
    have hi' : i < 2 ^ (k + 1) := by rwa [size_doublingArray] at hi
    rw [Fin.prod_univ_castSucc]
    simp only [doublingArray, Array.getElem_append, Array.size_map, Array.getElem_map, hs]
    split_ifs with h'
    · rw [getElem_doublingArray f k _ i (by rw [hs]; exact h')]
      simp only [Fin.val_castSucc, Fin.val_last, Nat.testBit_lt_two_pow h']
    · have hlt : i - 2 ^ k < 2 ^ k := by rw [pow_succ] at hi'; omega
      rw [getElem_doublingArray f k _ _ (by rw [hs]; exact hlt)]
      have hi2 : i = 2 ^ k + (i - 2 ^ k) := by omega
      conv_rhs => rw [hi2]
      simp only [Fin.val_castSucc, Fin.val_last]
      congr 1
      · refine Finset.prod_congr rfl fun j _ ↦ ?_
        rw [testBit_two_pow_add hlt j.val (by omega), ite_eq_left_of_eq_true _ _ (eq_true j.isLt)]
      · rw [testBit_two_pow_add hlt k le_rfl, ite_eq_right_of_eq_false _ _ (eq_false (lt_irrefl k))]

/-- The table whose entry at `i` is `∏_k f k (bit k of i)`, built by doubling. -/
def doublingTable {n : ℕ} (f : Fin n → Bool → R) : CMlPolynomialEval R n :=
  ⟨doublingArray f n le_rfl, size_doublingArray f n le_rfl⟩

/-- Entry `i` of the doubling is the product of the factors at the bits of `i`. -/
theorem doublingTable_getElem {n : ℕ} (f : Fin n → Bool → R) {i : ℕ} (hi : i < 2 ^ n) :
    (doublingTable f)[i] = ∏ k : Fin n, f k (i.testBit k) :=
  getElem_doublingArray f n le_rfl i (by rw [size_doublingArray]; exact hi)

/-! ## The Lagrange basis -/

/-- The Lagrange basis at `w` on its first `k` coordinates, by doubling: the entries with bit `k`
set are the previous ones times `w_k`, the others the previous ones less those. -/
def lagrangeArray {n : ℕ} (w : Vector R n) : (k : ℕ) → k ≤ n → Array R
  | 0, _ => #[1]
  | k + 1, h =>
    let a := lagrangeArray w k (Nat.le_of_succ_le h)
    let hi := a.map (· * w[k])
    Array.zipWith (· - ·) a hi ++ hi

/-- The doubling of the Lagrange basis is the doubling of its factors. -/
theorem lagrangeArray_eq {n : ℕ} (w : Vector R n) :
    ∀ (k : ℕ) (h : k ≤ n),
      lagrangeArray w k h = doublingArray (fun j b ↦ if b then w[j] else 1 - w[j]) k h
  | 0, _ => rfl
  | k + 1, h => by
    simp only [lagrangeArray, doublingArray, lagrangeArray_eq w k (Nat.le_of_succ_le h)]
    congr 1
    apply Array.ext
    · simp
    · intro i h1 h2
      simp only [Array.getElem_zipWith, Array.getElem_map]
      split_ifs <;> simp <;> ring

/-- The Lagrange basis by doubling. -/
def lagrangeBasisFast {S : Type*} {n : ℕ} [CommRing S] (w : Vector S n) : Vector S (2 ^ n) :=
  ⟨lagrangeArray w n le_rfl, by
    rw [lagrangeArray_eq]
    exact size_doublingArray _ n le_rfl⟩

/-- The doubling is the Lagrange basis. -/
theorem lagrangeBasisFast_eq {n : ℕ} (w : Vector R n) : lagrangeBasisFast w = lagrangeBasis w := by
  apply Vector.ext
  intro i hi
  have h := lagrangeBasis_getElem (w := w) ⟨i, hi⟩
  simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_ofFin] at h
  rw [h]
  change (lagrangeArray w n le_rfl)[i]'_ = _
  simp only [lagrangeArray_eq, getElem_doublingArray]
  rfl

/-- Compiled code builds the Lagrange basis by doubling. -/
@[csimp] theorem lagrangeBasis_eq_lagrangeBasisFast :
    @lagrangeBasis = @lagrangeBasisFast := by
  funext R n _ w
  exact (lagrangeBasisFast_eq w).symm

/-! ## Evaluating the multilinear extension -/

/-- One layer of the multilinear extension's interpolation, `a + x0·(b - a)`: one product per
entry, where CompPoly's `evalMleStep` takes `(1 - x0)·a + x0·b`, two. -/
def evalMleStepFast {S : Type*} [CommRing S] {n : ℕ} (values : Vector S (2 ^ (n + 1))) (x0 : S) :
    Vector S (2 ^ n) :=
  Vector.ofFn fun j : Fin (2 ^ n) ↦
    let a := values.get ⟨2 * j.val, by omega⟩
    a + x0 * (values.get ⟨2 * j.val + 1, by omega⟩ - a)

/-- The multilinear extension by `evalMleStepFast`. -/
@[specialize] def evalMleValuesFast {S : Type*} [CommRing S] :
    {n : ℕ} → Vector S (2 ^ n) → Vector S n → S
  | 0, values, _ => values.get ⟨0, by norm_num⟩
  | _ + 1, values, x => evalMleValuesFast (evalMleStepFast values x.head) x.tail

/-- `evalMleValuesFast` is CompPoly's interpolation. -/
theorem evalMleValuesFast_eq {S : Type*} [CommRing S] :
    ∀ {n : ℕ} (values : Vector S (2 ^ n)) (x : Vector S n),
      evalMleValuesFast values x = evalMleValues values x
  | 0, _, _ => rfl
  | n + 1, values, x => by
    have h : evalMleStepFast values x.head = evalMleStep values x.head := by
      apply Vector.ext
      intro j hj
      simp only [evalMleStepFast, evalMleStep, Vector.getElem_ofFn]
      ring
    rw [evalMleValuesFast, h, evalMleValuesFast_eq]
    rfl

/-- `evalMle` through `evalMleStepFast`. -/
@[inline] def evalMleFast {S : Type*} {n : ℕ} [CommRing S] (p : CMlPolynomialEval S n)
    (x : Vector S n) : S :=
  evalMleValuesFast p x

/-- Compiled code interpolates with one product per entry. -/
@[csimp] theorem evalMle_eq_evalMleFast : @evalMle = @evalMleFast := by
  funext S n _ p x
  exact (evalMleValuesFast_eq p x).symm

/-- `eval₂Mle` through `evalMleFast`. -/
def eval₂MleFast {S : Type*} {n : ℕ} [CommRing S] {T : Type*} [CommRing T]
    (p : CMlPolynomialEval S n) (f : S →+* T) (x : Vector T n) : T :=
  evalMleFast (CMlPolynomialEval.map f p) x

/-- Compiled code interpolates a mapped table with one product per entry. -/
@[csimp] theorem eval₂Mle_eq_eval₂MleFast : @eval₂Mle = @eval₂MleFast := by
  funext S n _ T _ p f x
  exact (evalMleValuesFast_eq _ x).symm

end
end LeanerVM.Protocol
