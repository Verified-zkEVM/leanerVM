/-
  LeanerVM.Protocol.ToArkLib.WhirSumcheck

  The family of claims of WHIR's sumcheck: a plain sumcheck on the product of the extensions of
  two tables, binding the lowest variable first, with its honest round polynomials. Candidate for
  ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.SumcheckRound
public import LeanerVM.Protocol.ToCompPoly.PlainSum

/-!
# The sumcheck of a weighted claim

WHIR's opening reduces a weighted claim `<W, f> = c` on a table `f` of `n` variables, `W` the
weight, to a claim on the table with its lane coordinates bound. The reduction is a plain
sumcheck on `Σ_x W̃(x) f̃(x)`, the product of the two tables' multilinear extensions, binding the
lowest variable first (`verifier.py`: the first fold challenge binds coordinate `0`). After `j`
rounds, with the challenges `c`, the running claim is `Σ_x W̃(c, x) f̃(c, x)` over the remaining
coordinates (`claim`); the honest round polynomial (`roundPoly`) is that sum with the next
coordinate left free, a polynomial of degree `2`, since each extension is affine in it. Its three
coefficients are written out (`roundPoly`), sums over the remaining coordinates of the products
of the two extensions' values at `0` and `1`.

`family tab` is the `SumcheckRound.Family` of this sumcheck for a way of reading the two tables
off the round's context (the public data, the oracles, the witness): the weight is in the public
data, and `f` is the witness. It is honest (`family_honest`): the honest polynomial passes the
verifier's check on the unit-weight domain `0, 1` and evaluates at the challenge to the next
claim. The rounds are `SumcheckRound.rounds` on it.
-/

namespace LeanerVM.Protocol

open CompPoly CMlPolynomialEval

@[expose] public section

namespace WhirSum

variable {F : Type} [Field F] {n : ℕ} (A B : CMlPolynomialEval F n)

/-- The summand: the product of the two tables' extensions at a point. -/
def summand (z : Vector F n) : F := evalMle A z * evalMle B z

/-- The running claim after `j` rounds: the sum of the summand over the remaining coordinates,
the first `j` fixed to the challenges. -/
def claim (j : ℕ) (c : Vector F j) : F := plainSum (summand A B) j c

/-- The extension of a table at the point with the first `j + 1` coordinates the challenges and
the free one `z`, the rest the cube point `x'`. -/
def atFree (T : CMlPolynomialEval F n) {j : ℕ} (hj : j < n) (c : Vector F j)
    (x' : Fin (2 ^ (n - (j + 1)))) (z : F) : F :=
  evalMle T (fixLow hj (c.push z) (boolVec x'))

/-- The extension of a table is affine in the free coordinate: its value at `z` is the
interpolation of its values at `0` and `1`. -/
private theorem atFree_eq {j : ℕ} (T : CMlPolynomialEval F n) (hj : j < n) (c : Vector F j)
    (x' : Fin (2 ^ (n - (j + 1)))) (z : F) :
    atFree T hj c x' z = atFree T hj c x' 0 + z * (atFree T hj c x' 1 - atFree T hj c x' 0) := by
  have key : ∀ y : F, atFree T hj c x' y =
      evalMle T ((fixLow hj (c.push 0) (boolVec x')).set j y hj) := fun y ↦ by
    unfold atFree
    rw [fixLow_push_set]
  rw [key z, key 0, key 1, evalMle_set T _ hj z]
  ring

/-- The honest round polynomial's constant coefficient. -/
def coef0 {j : ℕ} (hj : j < n) (c : Vector F j) : F :=
  ∑ x' : Fin (2 ^ (n - (j + 1))), atFree A hj c x' 0 * atFree B hj c x' 0

/-- The honest round polynomial's linear coefficient. -/
def coef1 {j : ℕ} (hj : j < n) (c : Vector F j) : F :=
  ∑ x' : Fin (2 ^ (n - (j + 1))),
    (atFree A hj c x' 0 * (atFree B hj c x' 1 - atFree B hj c x' 0) +
      (atFree A hj c x' 1 - atFree A hj c x' 0) * atFree B hj c x' 0)

/-- The honest round polynomial's quadratic coefficient. -/
def coef2 {j : ℕ} (hj : j < n) (c : Vector F j) : F :=
  ∑ x' : Fin (2 ^ (n - (j + 1))),
    (atFree A hj c x' 1 - atFree A hj c x' 0) * (atFree B hj c x' 1 - atFree B hj c x' 0)

/-- The honest round polynomial as a message, its three coefficients; zero past the last
round. -/
def roundPoly (j : ℕ) (c : Vector F j) : SumcheckRound.Message F 2 :=
  if h : j < n then #v[coef0 A B h c, coef1 A B h c, coef2 A B h c] else #v[0, 0, 0]

/-- A message of degree two evaluates as its three coefficients. -/
private theorem evaluate_two (q : SumcheckRound.Message F 2) (x : F) :
    SumcheckRound.evaluate 2 q x = q[0] + q[1] * x + q[2] * x ^ 2 := by
  simp [SumcheckRound.evaluate, Fin.sum_univ_succ]
  ring

/-- The honest polynomial's value at `x` is the claim with one more coordinate fixed to `x`. -/
theorem roundPoly_eval {j : ℕ} (hj : j < n) (c : Vector F j) (x : F) :
    SumcheckRound.evaluate 2 (roundPoly A B j c) x = claim A B (j + 1) (c.push x) := by
  rw [roundPoly, dite_eq_left hj, evaluate_two, claim, plainSum,
    dite_eq_left (Nat.succ_le_of_lt hj)]
  have hterm : ∀ x' : Fin (2 ^ (n - (j + 1))),
      summand A B (fixLow (Nat.succ_le_of_lt hj) (c.push x) (boolVec x')) =
        atFree A hj c x' 0 * atFree B hj c x' 0 +
          (atFree A hj c x' 0 * (atFree B hj c x' 1 - atFree B hj c x' 0) +
            (atFree A hj c x' 1 - atFree A hj c x' 0) * atFree B hj c x' 0) * x +
          ((atFree A hj c x' 1 - atFree A hj c x' 0) *
            (atFree B hj c x' 1 - atFree B hj c x' 0)) * x ^ 2 := fun x' ↦ by
    change atFree A hj c x' x * atFree B hj c x' x = _
    rw [atFree_eq A hj c x' x, atFree_eq B hj c x' x]
    ring
  simp only [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  rfl

/-- The honest polynomial passes the verifier's check on the unit-weight domain: its values at
`0` and `1` sum to the claim before the round. -/
theorem roundPoly_check {j : ℕ} (hj : j < n) (c : Vector F j) :
    SumcheckRound.weightedSum 2 [((0 : F), (1 : F)), (1, 1)] (roundPoly A B j c) =
      claim A B j c := by
  simp only [SumcheckRound.weightedSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, one_mul]
  rw [roundPoly_eval A B hj c 0, roundPoly_eval A B hj c 1, claim, claim, claim,
    plainSum_split _ hj c]

/-! ## The family -/

variable {X : Type} {ι : Type} {O : ι → Type} {W : Type}

/-- The family of claims of the sumcheck of two tables read off the context: the running claims,
the honest polynomials, the unit-weight domain, no side invariant. -/
def family (tab : SumcheckRound.Ctx X O W → CMlPolynomialEval F n × CMlPolynomialEval F n) :
    SumcheckRound.Family F X O W 2 where
  claim := fun ctx j c ↦ claim (tab ctx).1 (tab ctx).2 j c
  poly := fun ctx j c ↦ roundPoly (tab ctx).1 (tab ctx).2 j c
  weight := fun _ _ ↦ [(0, 1), (1, 1)]
  inv := fun _ _ _ ↦ True

/-- The family is honest up to the last variable. -/
theorem family_honest
    (tab : SumcheckRound.Ctx X O W → CMlPolynomialEval F n × CMlPolynomialEval F n) {m : ℕ}
    (hm : m ≤ n) : (family tab).Honest m where
  check := fun _ _ c hj ↦ roundPoly_check _ _ (lt_of_lt_of_le hj hm) c
  next := fun _ _ c x hj ↦ roundPoly_eval _ _ (lt_of_lt_of_le hj hm) c x
  inv_push := fun _ _ _ _ _ h ↦ h

end WhirSum

end

end LeanerVM.Protocol
