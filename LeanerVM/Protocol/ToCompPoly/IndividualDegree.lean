/-
  LeanerVM.Protocol.ToCompPoly.IndividualDegree

  Functions of a point that are polynomials of bounded degree in each coordinate separately, and
  the operations that keep the bound. Candidate for CompPoly.
-/

module

public import LeanerVM.Protocol.ToCompPoly.Multilinear
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Degree in each coordinate

`IndividualDegreeLE f d`: fixing every coordinate of the point but one, `f` is a polynomial of
degree at most `d` in the remaining one. It is what a sumcheck needs of its summand: the round
polynomial, a sum of such restrictions, then has degree at most `d`.

Constants have degree `0` (`const`), the extension of a table has degree `1` (`evalMle`), and
the bound adds under products (`mul`, `pow`, `prod`), takes the maximum under sums (`add`,
`sum`), and is kept by a polynomial of total degree `d` applied to functions of degree `1`
(`mvPolynomial_eval`): the composition by which a constraint of degree `d` on a row of
multilinear columns has degree `d` in each variable. Over an arbitrary commutative ring;
nothing here transcribes a source.
-/

namespace LeanerVM.Protocol

open CompPoly CMlPolynomialEval Polynomial

@[expose] public section

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Fixing every coordinate but one, `f` is a polynomial of degree at most `d` in that one. -/
def IndividualDegreeLE (f : Vector R n → R) (d : ℕ) : Prop :=
  ∀ (z : Vector R n) (k : ℕ) (hk : k < n),
    ∃ p : R[X], p.natDegree ≤ d ∧ ∀ x, f (z.set k x hk) = p.eval x

namespace IndividualDegreeLE

variable {f g : Vector R n → R} {d e : ℕ}

theorem mono (hf : IndividualDegreeLE f d) (h : d ≤ e) : IndividualDegreeLE f e := fun z k hk ↦
  let ⟨p, hp, hev⟩ := hf z k hk
  ⟨p, hp.trans h, hev⟩

theorem const (c : R) : IndividualDegreeLE (fun _ : Vector R n ↦ c) 0 := fun _ _ _ ↦
  ⟨C c, by simp, fun _ ↦ by simp⟩

theorem add (hf : IndividualDegreeLE f d) (hg : IndividualDegreeLE g d) :
    IndividualDegreeLE (fun z ↦ f z + g z) d := fun z k hk ↦
  let ⟨p, hp, hpe⟩ := hf z k hk
  let ⟨q, hq, hqe⟩ := hg z k hk
  ⟨p + q, (natDegree_add_le _ _).trans (max_le hp hq), fun x ↦ by simp [hpe, hqe]⟩

theorem mul (hf : IndividualDegreeLE f d) (hg : IndividualDegreeLE g e) :
    IndividualDegreeLE (fun z ↦ f z * g z) (d + e) := fun z k hk ↦
  let ⟨p, hp, hpe⟩ := hf z k hk
  let ⟨q, hq, hqe⟩ := hg z k hk
  ⟨p * q, natDegree_mul_le.trans (add_le_add hp hq), fun x ↦ by simp [hpe, hqe]⟩

theorem sum {ι : Type*} (s : Finset ι) {f : ι → Vector R n → R}
    (hf : ∀ i ∈ s, IndividualDegreeLE (f i) d) : IndividualDegreeLE (fun z ↦ ∑ i ∈ s, f i z) d := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ((const (0 : R)).mono (Nat.zero_le d) :
      IndividualDegreeLE (fun _ : Vector R n ↦ (0 : R)) d)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

theorem prod {ι : Type*} (s : Finset ι) {f : ι → Vector R n → R} {d : ι → ℕ}
    (hf : ∀ i ∈ s, IndividualDegreeLE (f i) (d i)) :
    IndividualDegreeLE (fun z ↦ ∏ i ∈ s, f i z) (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const (1 : R) : IndividualDegreeLE (fun _ : Vector R n ↦ (1 : R)) 0)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    exact mul (hf a (Finset.mem_insert_self a s))
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

theorem pow (hf : IndividualDegreeLE f d) (m : ℕ) :
    IndividualDegreeLE (fun z ↦ f z ^ m) (m * d) := by
  simpa using prod (Finset.univ : Finset (Fin m)) (f := fun _ ↦ f) (d := fun _ ↦ d)
    fun _ _ ↦ hf

/-- The extension of a table has degree `1` in each coordinate. -/
theorem evalMle (t : CMlPolynomialEval R n) :
    IndividualDegreeLE (fun z ↦ CMlPolynomialEval.evalMle t z) 1 := fun z k hk ↦
  ⟨C (CMlPolynomialEval.evalMle t (z.set k 0 hk)) +
      X * C (CMlPolynomialEval.evalMle t (z.set k 1 hk) -
        CMlPolynomialEval.evalMle t (z.set k 0 hk)),
    (natDegree_add_le _ _).trans (max_le (by simp)
      (natDegree_mul_le.trans (by simpa using natDegree_X_le))),
    fun x ↦ by
      show CMlPolynomialEval.evalMle t (z.set k x hk) = _
      rw [evalMle_set t z hk x]
      simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
      ring⟩

/-- A polynomial of total degree at most `d`, applied to functions of degree `1` in each
coordinate, has degree at most `d` in each coordinate. -/
theorem mvPolynomial_eval {σ : Type*} (p : MvPolynomial σ R) (hp : p.totalDegree ≤ d)
    {f : σ → Vector R n → R} (hf : ∀ i, IndividualDegreeLE (f i) 1) :
    IndividualDegreeLE (fun z ↦ MvPolynomial.eval (fun i ↦ f i z) p) d := by
  classical
  have key : ∀ m ∈ p.support, IndividualDegreeLE
      (fun z ↦ p.coeff m * ∏ i ∈ m.support, f i z ^ m i) d := by
    intro m hm
    have hdeg : ∑ i ∈ m.support, m i * 1 ≤ d := by
      simpa [Finsupp.sum] using (MvPolynomial.le_totalDegree hm).trans hp
    exact ((const _).mul (prod m.support fun i _ ↦ (hf i).pow (m i))).mono (by simpa using hdeg)
  simpa [MvPolynomial.eval_eq] using sum p.support key

end IndividualDegreeLE

end
end LeanerVM.Protocol
