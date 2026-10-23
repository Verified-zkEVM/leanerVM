/-
  LeanerVM.Protocol.ToCompPoly.TableFold

  Binding the coordinates of a hypercube table to values one at a time, from the highest or from
  the lowest, and weighted sums over the cube by halving a table of values: linear-time
  evaluations, each proved equal to the evaluation it replaces. Candidate for CompPoly.
-/

module

public import LeanerVM.Protocol.ToCompPoly.FinLoop
public import LeanerVM.Protocol.ToCompPoly.HighSum
public import LeanerVM.Protocol.ToCompPoly.PartialSum
public import LeanerVM.Protocol.ToCompPoly.WeightedCube

/-!
# Folding hypercube tables

Evaluating a table's multilinear extension afresh at every point of a subcube, the other
coordinates fixed, costs `2 ^ n` per point. Binding the fixed coordinates once, and reading the
bound table at the subcube's Boolean points, costs `2 ^ n` for all of them. Over an arbitrary
commutative ring, on CompPoly's tables (`CMlPolynomialEval R n`, bit `k` of the index being
coordinate `k`):

* **From the top.** `bindHigh t r` binds the highest coordinate of `t` to `r`: entry `x` is
  `t(x, 0) + r · (t(x, 1) - t(x, 0))` (`bindHighAt`), and its extension is `t`'s with the highest
  coordinate at `r` (`evalMle_push`). `bindHighs t s` binds the top coordinates to `s`, given in
  coordinate order and bound the highest first (`evalMle_append_eq_bindHighs`).
  `evalMle_push_append_boolVec` reads a table bound on all but one coordinate at the Boolean
  points below it: an entry of the bound table, with the free coordinate at `a`.
* **From the bottom.** `bindLow t r` binds the lowest coordinate, CompPoly's `evalMleLayer` with
  one product instead of two (`bindLow_eq_evalMleLayer`); `bindLows t s` binds the low
  coordinates to `s`, lowest first (`evalMle_append_eq_bindLows`), and
  `evalMle_fixLow_push_boolVec` is the low mirror of `evalMle_push_append_boolVec`.
* **Bound up to the next coordinate.** `bindLowsNext` and `bindHighsNext` bind a table's low or
  top `j` coordinates to `c`, as a table of the next coordinate and the free ones beyond it; the
  extension at `c`, the next coordinate `0` or `1` and a Boolean point is one entry
  (`evalMle_fixLow_push_zero`, `evalMle_highFix_push_one`, …).
* **Sums.** `weightFold w v` is the weighted sum `Σ_x (∏_k w_k(x_k)) · v[x]` of a table of values,
  by halving from the highest coordinate (`weightFold_eq_sum`), so that the weighted sum of a
  function over the cube is the fold of its table of values (`weightedCubeSum_eq_weightFold`).
* **Weights at a point.** `prodWeightFast` is `prodWeight` as a loop that reads a factor at `0`
  or `1` off without a product (`lineAt`) and stops multiplying at zero
  (`prodWeightFast_eq`).

Nothing here transcribes a source.
-/

namespace LeanerVM.Protocol

open CompPoly CMlPolynomialEval

@[expose] public section

variable {R : Type*} [CommRing R]

/-- An index below `2 ^ k` is below `2 ^ (k + 1)`. -/
theorem lt_two_pow_succ_of_lt {k i : ℕ} (h : i < 2 ^ k) : i < 2 ^ (k + 1) := by
  rw [pow_succ]
  omega

/-- An index below `2 ^ k`, shifted by `2 ^ k`, is below `2 ^ (k + 1)`. -/
theorem add_two_pow_lt {k i : ℕ} (h : i < 2 ^ k) : i + 2 ^ k < 2 ^ (k + 1) := by
  rw [pow_succ]
  omega

/-- Twice an index below `2 ^ k`, plus one, is below `2 ^ (k + 1)`. -/
theorem two_mul_add_one_lt {k i : ℕ} (h : i < 2 ^ k) : 2 * i + 1 < 2 ^ (k + 1) := by
  rw [pow_succ]
  omega

/-- A table's extension is its own on a cast of the number of variables. -/
theorem evalMle_cast_point {a b : ℕ} (h : a = b) (t : CMlPolynomialEval R b) (y : Vector R a) :
    evalMle t (Vector.cast h y) = evalMle (Vector.cast (congrArg (2 ^ ·) h.symm) t) y := by
  subst h
  rfl

/-! ## Binding the highest coordinates -/

/-- Entry `x` of a table with its highest coordinate bound to `r`: the line through the two entries
that differ only there, `t(x, 0) + r · (t(x, 1) - t(x, 0))`. -/
def bindHighAt {k : ℕ} (t : CMlPolynomialEval R (k + 1)) (r : R) (x : Fin (2 ^ k)) : R :=
  t[x.val]'(lt_two_pow_succ_of_lt x.isLt) +
    r * (t[x.val + 2 ^ k]'(add_two_pow_lt x.isLt) - t[x.val]'(lt_two_pow_succ_of_lt x.isLt))

/-- A table with its highest coordinate bound to `r`. -/
def bindHigh {k : ℕ} (t : CMlPolynomialEval R (k + 1)) (r : R) : CMlPolynomialEval R k :=
  Vector.ofFn (bindHighAt t r)

omit [CommRing R] in
private theorem push_eq_append {k : ℕ} (z : Vector R k) (r : R) : z.push r = z ++ #v[r] := by
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_push, Vector.getElem_append]
  split <;> simp

/-- Binding the highest coordinate: the extension of the bound table is the table's with its
highest coordinate at `r`. -/
theorem evalMle_push {k : ℕ} (t : CMlPolynomialEval R (k + 1)) (z : Vector R k) (r : R) :
    evalMle t (z.push r) = evalMle (bindHigh t r) z := by
  have hL0 : (lagrangeBasis #v[r])[(0 : Fin (2 ^ 1))] = 1 - r := by
    rw [Fin.getElem_fin, lagrangeBasis_getElem_nat _ (by norm_num), Fin.prod_univ_one]
    simp
  have hL1 : (lagrangeBasis #v[r])[(1 : Fin (2 ^ 1))] = r := by
    rw [Fin.getElem_fin, lagrangeBasis_getElem_nat _ (by norm_num), Fin.prod_univ_one]
    simp
  have hb : bindHigh t r = Vector.ofFn fun x ↦
      ∑ j ∈ Finset.univ, (lagrangeBasis #v[r])[j] * (slice (m := 1) t j)[x] := by
    apply Vector.ext
    intro x hx
    -- The index type is `Fin (2 ^ 1)`, which is `Fin 2` only after unfolding.
    erw [Vector.getElem_ofFn, Vector.getElem_ofFn, Fin.sum_univ_two]
    rw [hL0, hL1, Fin.getElem_fin, Fin.getElem_fin, slice_getElem_nat _ _ hx,
      slice_getElem_nat _ _ hx]
    simp only [bindHighAt, Fin.val_zero, Fin.val_one, mul_zero, add_zero, mul_one]
    ring
  rw [push_eq_append, evalMle_split (m := 1), hb, evalMle_ofFn_sum]

/-- A table with its top `j` coordinates bound to `s`, given in coordinate order: the highest
coordinate, `s`'s last, first. -/
def bindHighs {k : ℕ} : {j : ℕ} → CMlPolynomialEval R (k + j) → Vector R j → CMlPolynomialEval R k
  | 0, t, _ => t
  | j + 1, t, s => bindHighs (bindHigh t s[j]) s.pop

omit [CommRing R] in
private theorem append_zero {k : ℕ} (z : Vector R k) (s : Vector R 0) : z ++ s = z := by
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_append_left hi]

omit [CommRing R] in
private theorem append_eq_push {k j : ℕ} (z : Vector R k) (s : Vector R (j + 1)) :
    z ++ s = (z ++ s.pop).push s[j] := by
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_append, Vector.getElem_push]
  by_cases h1 : i < k
  · simp [h1, show i < k + j by omega, Vector.getElem_append_left h1]
  · by_cases h2 : i < k + j
    · simp [h1, h2, Vector.getElem_append_right (show i < k + j by omega) (by omega)]
    · have hi' : i = k + j := by omega
      subst hi'
      simp

/-- Binding the top coordinates: the extension of the bound table at `z` is the table's at `z`
followed by `s`. -/
theorem evalMle_append_eq_bindHighs {k : ℕ} :
    {j : ℕ} → (t : CMlPolynomialEval R (k + j)) → (z : Vector R k) → (s : Vector R j) →
      evalMle t (z ++ s) = evalMle (bindHighs t s) z
  | 0, t, z, s => by rw [append_zero, bindHighs]
  | j + 1, t, z, s => by
    rw [append_eq_push, evalMle_push, evalMle_append_eq_bindHighs, bindHighs]

/-- A table bound on its top `j` coordinates to `s`, read at the Boolean point `x` below its free
coordinate, with that one at `a`: an entry of the line through two entries of the bound table. -/
theorem evalMle_push_append_boolVec {k j : ℕ} (t : CMlPolynomialEval R (k + 1 + j))
    (x : Fin (2 ^ k)) (a : R) (s : Vector R j) :
    evalMle t ((boolVec x : Vector R k).push a ++ s) = bindHighAt (bindHighs t s) a x := by
  rw [evalMle_append_eq_bindHighs, evalMle_push, evalMle_boolVec, bindHigh, Fin.getElem_fin,
    Vector.getElem_ofFn]

/-! ## Binding the lowest coordinates -/

/-- Entry `x` of a table with its lowest coordinate bound to `r`:
`t(0, x) + r · (t(1, x) - t(0, x))`. -/
def bindLowAt {k : ℕ} (t : CMlPolynomialEval R (k + 1)) (r : R) (x : Fin (2 ^ k)) : R :=
  t[2 * x.val]'(by have := two_mul_add_one_lt x.isLt; omega) +
    r * (t[2 * x.val + 1]'(two_mul_add_one_lt x.isLt) -
      t[2 * x.val]'(by have := two_mul_add_one_lt x.isLt; omega))

/-- A table with its lowest coordinate bound to `r`. -/
def bindLow {k : ℕ} (t : CMlPolynomialEval R (k + 1)) (r : R) : CMlPolynomialEval R k :=
  Vector.ofFn (bindLowAt t r)

/-- `bindLow` is CompPoly's interpolation layer `evalMleLayer`, with one product. -/
theorem bindLow_eq_evalMleLayer {k : ℕ} (t : CMlPolynomialEval R (k + 1)) (r : R) :
    bindLow t r = evalMleLayer t r := by
  apply Vector.ext
  intro x hx
  have h := evalMleLayer_get t r ⟨x, hx⟩
  simp only [Vector.get_eq_getElem] at h
  rw [h]
  simp only [bindLow, bindLowAt, Vector.getElem_ofFn]
  ring

/-- The lowest coordinate first: the extension at `(a, z)`, the point cast to `k + 1`
coordinates, is the extension of the table with its lowest coordinate bound to `a` at `z`. -/
theorem evalMle_cons {k : ℕ} (t : CMlPolynomialEval R (k + 1)) (a : R) (z : Vector R k) :
    evalMle t (Vector.cast (Nat.add_comm 1 k) (#v[a] ++ z)) = evalMle (bindLow t a) z := by
  rw [evalMle_succ, bindLow_eq_evalMleLayer]
  congr 1
  · congr 1
    simp [Vector.head]
  · apply Vector.ext
    intro i hi
    simp only [Vector.tail_eq_cast_extract, Vector.getElem_cast, Vector.getElem_extract]
    rw [Vector.getElem_append_right (by omega) (by omega)]
    congr 1
    omega

/-- A table with its low `j` coordinates bound to `s`, lowest first. -/
def bindLows {k : ℕ} : {j : ℕ} → CMlPolynomialEval R (j + k) → Vector R j → CMlPolynomialEval R k
  | 0, t, _ => Vector.cast (congrArg (2 ^ ·) (Nat.zero_add k)) t
  | j + 1, t, s =>
    bindLow (bindLows (k := k + 1) (Vector.cast (congrArg (2 ^ ·) (by omega)) t) s.pop) s[j]

omit [CommRing R] in
private theorem append_eq_pop_append {k j : ℕ} (s : Vector R (j + 1)) (z : Vector R k) :
    Vector.cast (by omega) (s ++ z) =
      s.pop ++ Vector.cast (Nat.add_comm 1 k) (#v[s[j]] ++ z) := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_cast, Vector.getElem_append, Vector.getElem_pop,
    Nat.add_sub_cancel]
  by_cases h1 : i < j
  · simp [h1, show i < j + 1 by omega]
  · by_cases h2 : i = j
    · subst h2
      simp
    · simp only [h1, show ¬ i < j + 1 by omega, dite_false, show ¬ i - j < 1 by omega]
      congr 1

/-- Binding the low coordinates: the extension of the bound table at `z` is the table's at `s`
followed by `z`. -/
theorem evalMle_append_eq_bindLows {k : ℕ} :
    {j : ℕ} → (t : CMlPolynomialEval R (j + k)) → (s : Vector R j) → (z : Vector R k) →
      evalMle t (s ++ z) = evalMle (bindLows t s) z
  | 0, t, s, z => by
    have hz : s ++ z = Vector.cast (Nat.zero_add k).symm z := by
      apply Vector.ext
      intro i hi
      simp only [Vector.getElem_cast]
      rw [Vector.getElem_append_right (by omega) (by omega)]
      congr 1
    rw [hz, evalMle_cast_point, bindLows]
  | j + 1, t, s, z => by
    have h : j + 1 + k = j + (k + 1) := by omega
    rw [← evalMle_cast h t (s ++ z), append_eq_pop_append, evalMle_append_eq_bindLows,
      evalMle_cons, bindLows]

/-- A table bound on its low `j` coordinates to `c`, read at the Boolean point `x` above its free
coordinate, with that one at `a`: an entry of the line through two entries of the bound table. -/
theorem evalMle_fixLow_push_boolVec {n j : ℕ} (hj : j < n) (t : CMlPolynomialEval R n)
    (c : Vector R j) (a : R) (x : Fin (2 ^ (n - (j + 1)))) :
    evalMle t (fixLow hj (c.push a) (boolVec x)) =
      bindLowAt (bindLows (k := n - (j + 1) + 1)
        (Vector.cast (congrArg (2 ^ ·) (by omega)) t) c) a x := by
  have hp : fixLow hj (c.push a) (boolVec x) = Vector.cast (by omega)
      (c ++ Vector.cast (Nat.add_comm 1 _) (#v[a] ++ (boolVec x : Vector R (n - (j + 1))))) := by
    apply Vector.ext
    intro i hi
    simp only [fixLow, Vector.getElem_cast]
    rw [Vector.getElem_append, Vector.getElem_append]
    by_cases h1 : i < j
    · simp [h1, show i < j + 1 by omega, Vector.getElem_push_lt h1]
    · by_cases h2 : i = j
      · subst h2
        simp
      · simp only [h1, show ¬ i < j + 1 by omega, dite_false, Vector.getElem_cast]
        rw [Vector.getElem_append_right (by omega) (by omega)]
        congr 1
  rw [hp, evalMle_cast_point, evalMle_append_eq_bindLows, evalMle_cons, evalMle_boolVec, bindLow,
    Fin.getElem_fin, Vector.getElem_ofFn]

/-! ## Bound up to the next coordinate

Reading a table's extension with `j` coordinates fixed to `c`, the next one at `0` or `1` and the
rest Boolean: bound once to `c`, the table is a table of the next coordinate and the free ones
beyond it, and each such read is one entry. -/

/-- A table with its low `j` coordinates bound to `c`, lowest first, as a table of the next
coordinate, `j`, and the `n - (j + 1)` above it. -/
def bindLowsNext {n j : ℕ} (hj : j < n) (t : CMlPolynomialEval R n) (c : Vector R j) :
    CMlPolynomialEval R (n - (j + 1) + 1) :=
  bindLows (k := n - (j + 1) + 1) (Vector.cast (congrArg (2 ^ ·) (by omega)) t) c

/-- The extension at `c`, the next coordinate `0` and a Boolean point above is an even entry of
the bound table. -/
theorem evalMle_fixLow_push_zero {n j : ℕ} (hj : j < n) (t : CMlPolynomialEval R n)
    (c : Vector R j) (x : Fin (2 ^ (n - (j + 1)))) :
    evalMle t (fixLow hj (c.push 0) (boolVec x)) =
      (bindLowsNext hj t c)[2 * x.val]'(by have := two_mul_add_one_lt x.isLt; omega) := by
  rw [evalMle_fixLow_push_boolVec, bindLowAt, zero_mul, add_zero]
  rfl

/-- At the next coordinate `1`: the next, odd, entry. -/
theorem evalMle_fixLow_push_one {n j : ℕ} (hj : j < n) (t : CMlPolynomialEval R n)
    (c : Vector R j) (x : Fin (2 ^ (n - (j + 1)))) :
    evalMle t (fixLow hj (c.push 1) (boolVec x)) =
      (bindLowsNext hj t c)[2 * x.val + 1]'(two_mul_add_one_lt x.isLt) := by
  rw [evalMle_fixLow_push_boolVec, bindLowAt, one_mul, add_sub_cancel]
  rfl

/-- A table with its top `j` coordinates bound to `c`, `c`'s first value the highest coordinate,
as a table of the next coordinate, `n - 1 - j`, and the `n - (j + 1)` below it. -/
def bindHighsNext {n j : ℕ} (hj : j < n) (t : CMlPolynomialEval R n) (c : Vector R j) :
    CMlPolynomialEval R (n - (j + 1) + 1) :=
  bindHighs (Vector.cast (congrArg (2 ^ ·) (by omega)) t) c.reverse

omit [CommRing R] in
/-- The point with the top coordinates `c` (the first the highest), the next coordinate `a` and
the low ones `x`: `x`, then `a`, then `c` reversed. -/
theorem highFix_push_append {n j : ℕ} (hj : j < n) (c : Vector R j) (a : R)
    (x : Vector R (n - (j + 1))) :
    highFix (Nat.succ_le_of_lt hj) (c.push a) x =
      Vector.cast (by omega) (x.push a ++ c.reverse) := by
  apply Vector.ext
  intro k hk
  simp only [highFix, Vector.getElem_cast, Vector.getElem_append, Vector.getElem_push,
    Vector.getElem_reverse]
  by_cases h1 : k < n - (j + 1)
  · simp [h1, show k < n - (j + 1) + 1 by omega]
  · by_cases h2 : k = n - (j + 1)
    · subst h2
      simp
    · simp only [h1, show ¬ k < n - (j + 1) + 1 by omega, dite_false,
        show j + 1 - 1 - (k - (n - (j + 1))) < j by omega, dite_true]
      congr 1
      omega

/-- The extension at a Boolean point below the next coordinate `a` and `c` above is an entry of
the line through two entries of the bound table. -/
theorem evalMle_highFix_push_boolVec {n j : ℕ} (hj : j < n) (t : CMlPolynomialEval R n)
    (c : Vector R j) (a : R) (x : Fin (2 ^ (n - (j + 1)))) :
    evalMle t (highFix (Nat.succ_le_of_lt hj) (c.push a) (boolVec x)) =
      bindHighAt (bindHighsNext hj t c) a x := by
  rw [highFix_push_append hj, evalMle_cast_point, evalMle_push_append_boolVec, bindHighsNext]

/-- At the next coordinate `0`: an entry of the low half of the bound table. -/
theorem evalMle_highFix_push_zero {n j : ℕ} (hj : j < n) (t : CMlPolynomialEval R n)
    (c : Vector R j) (x : Fin (2 ^ (n - (j + 1)))) :
    evalMle t (highFix (Nat.succ_le_of_lt hj) (c.push 0) (boolVec x)) =
      (bindHighsNext hj t c)[x.val]'(lt_two_pow_succ_of_lt x.isLt) := by
  rw [evalMle_highFix_push_boolVec, bindHighAt, zero_mul, add_zero]

/-- At the next coordinate `1`: the entry of the high half. -/
theorem evalMle_highFix_push_one {n j : ℕ} (hj : j < n) (t : CMlPolynomialEval R n)
    (c : Vector R j) (x : Fin (2 ^ (n - (j + 1)))) :
    evalMle t (highFix (Nat.succ_le_of_lt hj) (c.push 1) (boolVec x)) =
      (bindHighsNext hj t c)[x.val + 2 ^ (n - (j + 1))]'(add_two_pow_lt x.isLt) := by
  rw [evalMle_highFix_push_boolVec, bindHighAt, one_mul, add_sub_cancel]

/-! ## Sums -/

section Fold

variable [BEq R] [LawfulBEq R]

/-- One halving step of `weightFold`: the two halves of the highest coordinate combined by its
weights, without products when both are one. -/
def foldHalves {k : ℕ} (wk : R × R) (v : Vector R (2 ^ (k + 1))) : Vector R (2 ^ k) :=
  if wk.1 == 1 && wk.2 == 1 then
    Vector.ofFn fun x : Fin (2 ^ k) ↦
      v[x.val]'(lt_two_pow_succ_of_lt x.isLt) + v[x.val + 2 ^ k]'(add_two_pow_lt x.isLt)
  else
    Vector.ofFn fun x : Fin (2 ^ k) ↦
      wk.1 * v[x.val]'(lt_two_pow_succ_of_lt x.isLt) +
        wk.2 * v[x.val + 2 ^ k]'(add_two_pow_lt x.isLt)

theorem foldHalves_getElem {k : ℕ} (wk : R × R) (v : Vector R (2 ^ (k + 1))) (x : Fin (2 ^ k)) :
    (foldHalves wk v)[x] = wk.1 * v[x.val]'(lt_two_pow_succ_of_lt x.isLt) +
      wk.2 * v[x.val + 2 ^ k]'(add_two_pow_lt x.isLt) := by
  unfold foldHalves
  by_cases h : (wk.1 == 1 && wk.2 == 1) = true
  · rw [ite_eq_left h]
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · rw [ite_eq_right h]
    simp

/-- The weighted sum `Σ_x (∏_k w_k(x_k)) · v[x]` of a table of values over the cube, by halving:
the two halves of the highest coordinate combined by its weights, then the rest. -/
def weightFold : {k : ℕ} → (Fin k → R × R) → Vector R (2 ^ k) → R
  | 0, _, v => v[0]
  | k + 1, w, v => weightFold (fun a ↦ w a.castSucc) (foldHalves (w (Fin.last k)) v)

/-- The fold is the weighted sum of the values. -/
theorem weightFold_eq_sum : {k : ℕ} → (w : Fin k → R × R) → (v : Vector R (2 ^ k)) →
    weightFold w v = ∑ x : Fin (2 ^ k), cubeWeight w x * v[x]
  | 0, w, v => by
    rw [weightFold]
    simp [cubeWeight]
  | k + 1, w, v => by
    rw [weightFold, weightFold_eq_sum, sum_cube_split (k := k) (m := 1)]
    -- The index type is `Fin (2 ^ 1)`, which is `Fin 2` only after unfolding.
    erw [Fin.sum_univ_two]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    have hw : ∀ b : Fin (2 ^ 1), cubeWeight w (cubeIndex x b) =
        cubeWeight (fun a ↦ w a.castSucc) x * bitWeight (w (Fin.last k)) (b.val.testBit 0) := by
      intro b
      rw [cubeWeight, Fin.prod_univ_castSucc, cubeWeight]
      simp only [testBit_cubeIndex, Fin.val_last, Fin.val_castSucc, Fin.is_lt, ite_true,
        lt_irrefl, ite_false, Nat.sub_self]
    rw [hw, hw, foldHalves_getElem]
    simp only [Fin.getElem_fin, cubeIndex_val, Fin.val_zero, Fin.val_one,
      mul_zero, add_zero, mul_one, bitWeight, Nat.testBit_zero]
    simp
    ring

/-- The weighted sum of a function over the cube is the fold of its table of values. -/
theorem weightedCubeSum_eq_weightFold {k : ℕ} (w : Fin k → R × R) (g : Vector R k → R) :
    weightedCubeSum w g = weightFold w (Vector.ofFn fun x ↦ g (boolVec x)) := by
  rw [weightFold_eq_sum, weightedCubeSum]
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]

end Fold

/-! ## Weights at a point -/

section Weights

variable [BEq R] [LawfulBEq R]

/-- The line through a coordinate's two weights at `z`, `(1 - z) · w.1 + z · w.2`, read off
without a product at `0` and at `1`. -/
def lineAt (w : R × R) (z : R) : R :=
  if z == 0 then w.1 else if z == 1 then w.2 else (1 - z) * w.1 + z * w.2

theorem lineAt_eq (w : R × R) (z : R) : lineAt w z = (1 - z) * w.1 + z * w.2 := by
  unfold lineAt
  split
  · rename_i h
    rw [beq_iff_eq.mp h]
    ring
  · split
    · rename_i h
      rw [beq_iff_eq.mp h]
      ring
    · rfl

/-- `prodWeight` as a loop: each factor by `lineAt`, and no product once a factor was zero. -/
def prodWeightFast {k : ℕ} (w : Fin k → R × R) (z : Vector R k) : R :=
  Fin.foldl k (fun acc a ↦ if acc == 0 then 0 else acc * lineAt (w a) z[a]) 1

/-- The loop is the weight at the point. -/
theorem prodWeightFast_eq {k : ℕ} (w : Fin k → R × R) (z : Vector R k) :
    prodWeightFast w z = prodWeight w z := by
  have h : (fun acc a ↦ if acc == 0 then 0 else acc * lineAt (w a) z[a]) =
      fun (acc : R) (a : Fin k) ↦ acc * ((1 - z[a]) * (w a).1 + z[a] * (w a).2) := by
    funext acc a
    rw [lineAt_eq]
    split
    · rename_i h
      rw [beq_iff_eq.mp h, zero_mul]
    · rfl
  rw [prodWeightFast, h, ← prodFin, prodFin_eq_prod, prodWeight]

end Weights

end
end LeanerVM.Protocol
