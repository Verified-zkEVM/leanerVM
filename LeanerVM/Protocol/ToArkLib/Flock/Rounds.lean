/-
  LeanerVM.Protocol.ToArkLib.Flock.Rounds

  The honest round polynomials of the two quadratic sumchecks of a Flock argument: the
  normalized zerocheck round on `A · B - C` binding the lowest variable first, and the plain
  lincheck round on a sum of products binding the highest variable first. Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.Flock.Tables
public import LeanerVM.Protocol.ToArkLib.SumcheckRound
public import LeanerVM.Protocol.ToCompPoly.HighSum
public import LeanerVM.Protocol.ToCompPoly.PartialSum
public import LeanerVM.Protocol.ToCompPoly.TableFold

/-!
# Quadratic round polynomials

Both sumchecks of a Flock argument have a summand of degree two in each variable: the
zerocheck's `g(v) = Ã(v) · B̃(v) - C̃(v)` against `eq(r, ·)` (a normalized round, the equality
factor outside the message), and the lincheck's `Σ_i M̃_i(v) · Z̃_i(v)` with unit weights (a plain
round). The honest round message is the three coefficients, low degree first, of the running
claim with the next coordinate left free: every extension is affine in it (`evalMle_set`), so the
coefficients are sums of products of the values at `0` and `1`.

* `normRound`, `evaluate_normRound`: the zerocheck round binding coordinate `j`; its message
  evaluates to the next partial sum `partialSum g r (j + 1) (c.push X)`, and
  `weightedSum_normRound` is the check `(1 - r_j) · h(0) + r_j · h(1)` against the running claim.
* `highRound`, `evaluate_highRound`: the lincheck round binding coordinate `m - 1 - j`; its
  message evaluates to `highSum (linFun M Z) (j + 1) (c.push X)`, and `weightedSum_highRound` is
  the check `h(0) + h(1)`.

Compiled code computes both messages from tables bound once to the challenges
(`normRound_eq_normRoundFolded`, `highRound_eq_highRoundFolded`, `@[csimp]` theorems). Nothing here
transcribes a source.
-/

namespace LeanerVM.Protocol

namespace Flock

open CompPoly CMlPolynomialEval SumcheckRound

@[expose] public section

variable {F : Type} [Field F]

/-- `Σ_{i < 3} q_i X^i` for the message `#v[q₀, q₁, q₂]`. -/
theorem evaluate_three (q₀ q₁ q₂ X : F) :
    evaluate 2 (#v[q₀, q₁, q₂] : Message F 2) X = q₀ + q₁ * X + q₂ * X ^ 2 := by
  simp [evaluate, Fin.sum_univ_three]

/-! ## The zerocheck round -/

/-- The zerocheck summand on three tables: `Ã · B̃ - C̃`. -/
def prodSub {n : ℕ} (tA tB tC : CMlPolynomialEval F n) (v : Vector F n) : F :=
  evalMle tA v * evalMle tB v - evalMle tC v

/-- The honest normalized round message binding coordinate `j`, the first `j` coordinates fixed
to `c`: the three coefficients of `X ↦ Σ_b eq(r_{>j}, b) · g(c, X, b)`. -/
def normRound {n : ℕ} (tA tB tC : CMlPolynomialEval F n) (r : Vector F n) (j : ℕ)
    (c : Vector F j) : Message F 2 :=
  if hj : j < n then
    let L := lagrangeBasis (r.drop (j + 1))
    let pt := fun (b : Fin (2 ^ (n - (j + 1)))) (X : F) ↦
      (fixLow hj (c.push 0) (boolVec b)).set j X hj
    let e := fun (t : CMlPolynomialEval F n) (b : Fin (2 ^ (n - (j + 1)))) (X : F) ↦
      evalMle t (pt b X)
    #v[∑ b, L[b] * (e tA b 0 * e tB b 0 - e tC b 0),
      ∑ b, L[b] * (e tA b 0 * (e tB b 1 - e tB b 0) + (e tA b 1 - e tA b 0) * e tB b 0 -
        (e tC b 1 - e tC b 0)),
      ∑ b, L[b] * ((e tA b 1 - e tA b 0) * (e tB b 1 - e tB b 0))]
  else 0

/-- The normalized round message evaluates to the next partial sum. -/
theorem evaluate_normRound {n : ℕ} (tA tB tC : CMlPolynomialEval F n) (r : Vector F n) {j : ℕ}
    (hj : j < n) (c : Vector F j) (X : F) :
    evaluate 2 (normRound tA tB tC r j c) X =
      partialSum (prodSub tA tB tC) r (j + 1) (c.push X) := by
  have hj' : j + 1 ≤ n := hj
  rw [normRound, dite_eq_left hj]
  dsimp only
  rw [evaluate_three, partialSum, dite_eq_left hj', evalMle_eq_sum, Finset.sum_mul,
    Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  have hrt : (restrictTable (prodSub tA tB tC) hj' (c.push X))[b] =
      prodSub tA tB tC (fixLow hj' (c.push X) (boolVec b)) := by
    simp [restrictTable]
  have hset : ∀ t : CMlPolynomialEval F n, evalMle t (fixLow hj' (c.push X) (boolVec b)) =
      (1 - X) * evalMle t ((fixLow hj (c.push 0) (boolVec b)).set j 0 hj) +
        X * evalMle t ((fixLow hj (c.push 0) (boolVec b)).set j 1 hj) := fun t ↦ by
    rw [fixLow_push_set hj]
    exact evalMle_set t _ hj X
  rw [hrt, prodSub, hset, hset, hset]
  ring

/-- The normalized round's check: the weighted sum of the honest message over `0, 1` with the
weights `1 - r_j, r_j` is the running claim. -/
theorem weightedSum_normRound {X : Type} {n : ℕ} (tA tB tC : CMlPolynomialEval F n)
    (pt : X → Vector F n) (x : X) {j : ℕ} (hj : j < n) (c : Vector F j) :
    weightedSum 2 (normalizedWeights pt x j) (normRound tA tB tC (pt x) j c) =
      partialSum (prodSub tA tB tC) (pt x) j c := by
  rw [normalizedWeights, dite_eq_left hj, weightedSum, partialSum_split _ _ hj]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    evaluate_normRound tA tB tC (pt x) hj]

/-! ## The lincheck round -/

/-- The honest plain round message binding coordinate `m - 1 - j`, the last `j` coordinates fixed
to the reversed `c`: the three coefficients of `X ↦ Σ_b Σ_i M̃_i(b, X, c) · Z̃_i(b, X, c)`. -/
def highRound {s m : ℕ} (M Z : CMlPolynomialEval F (s + m)) (j : ℕ) (c : Vector F j) :
    Message F 2 :=
  if hj : j < m then
    let pt := fun (b : Fin (2 ^ (m - (j + 1)))) (X : F) ↦
      (highFix hj (c.push 0) (boolVec b)).set (m - (j + 1)) X (by omega)
    let e := fun (t : CMlPolynomialEval F (s + m)) (i : Fin (2 ^ s))
      (b : Fin (2 ^ (m - (j + 1)))) (X : F) ↦ evalMle (sliceLow t i) (pt b X)
    #v[∑ b, ∑ i, e M i b 0 * e Z i b 0,
      ∑ b, ∑ i, (e M i b 0 * (e Z i b 1 - e Z i b 0) + (e M i b 1 - e M i b 0) * e Z i b 0),
      ∑ b, ∑ i, (e M i b 1 - e M i b 0) * (e Z i b 1 - e Z i b 0)]
  else 0

/-- The plain round message evaluates to the next high sum. -/
theorem evaluate_highRound {s m : ℕ} (M Z : CMlPolynomialEval F (s + m)) {j : ℕ} (hj : j < m)
    (c : Vector F j) (X : F) :
    evaluate 2 (highRound M Z j c) X = highSum (linFun M Z) (j + 1) (c.push X) := by
  have hj' : j + 1 ≤ m := hj
  have hk : m - (j + 1) < m := by omega
  rw [highRound, dite_eq_left hj]
  dsimp only
  rw [evaluate_three, highSum, dite_eq_left hj', Finset.sum_mul, Finset.sum_mul,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  have hset : ∀ t : CMlPolynomialEval F m, evalMle t (highFix hj' (c.push X) (boolVec b)) =
      (1 - X) * evalMle t ((highFix hj (c.push 0) (boolVec b)).set (m - (j + 1)) 0 hk) +
        X * evalMle t ((highFix hj (c.push 0) (boolVec b)).set (m - (j + 1)) 1 hk) :=
    fun t ↦ by
      rw [highFix_push_set hj]
      exact evalMle_set t _ hk X
  rw [linFun, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hset, hset]
  ring

/-- The plain round's check: the sum of the honest message at `0` and `1` is the running
claim. -/
theorem weightedSum_highRound {s m : ℕ} (M Z : CMlPolynomialEval F (s + m)) {j : ℕ} (hj : j < m)
    (c : Vector F j) :
    weightedSum 2 [(0, 1), (1, 1)] (highRound M Z j c) = highSum (linFun M Z) j c := by
  rw [weightedSum, highSum_split _ hj]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul,
    evaluate_highRound M Z hj]

/-! ## The compiled rounds

Both round messages evaluate the tables' extensions afresh at every point of the free
coordinates, `4 ^ n` work per round. Compiled code runs `normRoundFolded` and `highRoundFolded`
instead, through the `@[csimp]` theorems `normRound_eq_normRoundFolded` and
`highRound_eq_highRoundFolded`: each table, or each low slice of one, is bound once to the
challenges, and the three coefficients are one pass over the bound tables' entries. -/

/-- The zerocheck round message from the tables bound to the challenges. -/
def normRoundFolded {n : ℕ} (tA tB tC : CMlPolynomialEval F n) (r : Vector F n) (j : ℕ)
    (c : Vector F j) : Message F 2 :=
  if hj : j < n then
    let L := lagrangeBasis (r.drop (j + 1))
    let a := bindLowsNext hj tA c
    let b := bindLowsNext hj tB c
    let e := bindLowsNext hj tC c
    let s := sumFin fun x : Fin (2 ^ (n - (j + 1))) ↦
      let i0 := 2 * x.val
      have h0 : i0 < 2 ^ (n - (j + 1) + 1) := by have := two_mul_add_one_lt x.isLt; omega
      have h1 : i0 + 1 < 2 ^ (n - (j + 1) + 1) := two_mul_add_one_lt x.isLt
      let a0 := a[i0]
      let a1 := a[i0 + 1]
      let b0 := b[i0]
      let b1 := b[i0 + 1]
      let e0 := e[i0]
      let e1 := e[i0 + 1]
      let l := L[x]
      (l * (a0 * b0 - e0), l * (a0 * (b1 - b0) + (a1 - a0) * b0 - (e1 - e0)),
        l * ((a1 - a0) * (b1 - b0)))
    #v[s.1, s.2.1, s.2.2]
  else 0

/-- The zerocheck round message from bound tables is the honest one. -/
@[csimp] theorem normRound_eq_normRoundFolded : @normRound = @normRoundFolded := by
  funext F _ n tA tB tC r j c
  by_cases hj : j < n
  · have h0 : ∀ (t : CMlPolynomialEval F n) (x : Fin (2 ^ (n - (j + 1)))),
        evalMle t ((fixLow hj (c.push 0) (boolVec x)).set j 0 hj) =
          (bindLowsNext hj t c)[2 * x.val]'(by have := two_mul_add_one_lt x.isLt; omega) :=
      fun t x ↦ by rw [← fixLow_push_set, evalMle_fixLow_push_zero]
    have h1 : ∀ (t : CMlPolynomialEval F n) (x : Fin (2 ^ (n - (j + 1)))),
        evalMle t ((fixLow hj (c.push 0) (boolVec x)).set j 1 hj) =
          (bindLowsNext hj t c)[2 * x.val + 1]'(two_mul_add_one_lt x.isLt) :=
      fun t x ↦ by rw [← fixLow_push_set, evalMle_fixLow_push_one]
    simp only [normRound, normRoundFolded, hj, dite_true, sumFin_eq_sum, Prod.fst_sum,
      Prod.snd_sum, h0, h1]
  · simp only [normRound, normRoundFolded, hj, dite_false]

/-- The lincheck round message from the low slices of the tables bound to the challenges. -/
def highRoundFolded {s m : ℕ} (M Z : CMlPolynomialEval F (s + m)) (j : ℕ) (c : Vector F j) :
    Message F 2 :=
  if hj : j < m then
    let Ms := Vector.ofFn fun i : Fin (2 ^ s) ↦ bindHighsNext hj (sliceLow M i) c
    let Zs := Vector.ofFn fun i : Fin (2 ^ s) ↦ bindHighsNext hj (sliceLow Z i) c
    let tot := sumFin fun x : Fin (2 ^ (m - (j + 1))) ↦ sumFin fun i : Fin (2 ^ s) ↦
      have h0 : x.val < 2 ^ (m - (j + 1) + 1) := lt_two_pow_succ_of_lt x.isLt
      have h1 : x.val + 2 ^ (m - (j + 1)) < 2 ^ (m - (j + 1) + 1) := add_two_pow_lt x.isLt
      let m0 := Ms[i][x.val]
      let m1 := Ms[i][x.val + 2 ^ (m - (j + 1))]
      let z0 := Zs[i][x.val]
      let z1 := Zs[i][x.val + 2 ^ (m - (j + 1))]
      (m0 * z0, m0 * (z1 - z0) + (m1 - m0) * z0, (m1 - m0) * (z1 - z0))
    #v[tot.1, tot.2.1, tot.2.2]
  else 0

/-- The lincheck round message from bound slices is the honest one. -/
@[csimp] theorem highRound_eq_highRoundFolded : @highRound = @highRoundFolded := by
  funext F _ s m M Z j c
  by_cases hj : j < m
  · have hk : m - (j + 1) < m := by omega
    have h0 : ∀ (t : CMlPolynomialEval F m) (x : Fin (2 ^ (m - (j + 1)))),
        evalMle t ((highFix hj (c.push 0) (boolVec x)).set (m - (j + 1)) 0 hk) =
          (bindHighsNext hj t c)[x.val]'(lt_two_pow_succ_of_lt x.isLt) :=
      fun t x ↦ by rw [← highFix_push_set, evalMle_highFix_push_zero]
    have h1 : ∀ (t : CMlPolynomialEval F m) (x : Fin (2 ^ (m - (j + 1)))),
        evalMle t ((highFix hj (c.push 0) (boolVec x)).set (m - (j + 1)) 1 hk) =
          (bindHighsNext hj t c)[x.val + 2 ^ (m - (j + 1))]'(add_two_pow_lt x.isLt) :=
      fun t x ↦ by rw [← highFix_push_set, evalMle_highFix_push_one]
    simp only [highRound, highRoundFolded, hj, dite_true, sumFin_eq_sum, Prod.fst_sum,
      Prod.snd_sum, h0, h1, Fin.getElem_fin, Vector.getElem_ofFn]
  · simp only [highRound, highRoundFolded, hj, dite_false]

end

end Flock

end LeanerVM.Protocol
