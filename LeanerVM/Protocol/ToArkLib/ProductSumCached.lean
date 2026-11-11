/-
  LeanerVM.Protocol.ToArkLib.ProductSumCached

  The sumcheck of a product of two tables with its tables bound once per challenge: the bound
  tables carried from round to round, the round polynomial read off them, and the round cache of
  the cached rounds. Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.ProductSumcheck
public import LeanerVM.Protocol.ToArkLib.CachedRounds
public import LeanerVM.Protocol.ToCompPoly.BindStep

/-!
# The product sumcheck's bound tables

`ProductSum.roundPoly A B j c` binds both tables to the `j` challenges afresh, `2 · 2 ^ n` work at
every round. The cached prover keeps them bound (`lowCache`: the table bound on its low `j`
coordinates to `c`, the first challenge the lowest), reads each round polynomial off them
(`roundOfBound`, the fold of `roundPolyFolded`), and binds each challenge once, one halving per
table (`stepLow`, by `bindLow_bindLows`). `roundCache` packages this as a
`SumcheckRound.RoundCache` for a family whose tables are read off the context.
-/

namespace LeanerVM.Protocol

open CompPoly CMlPolynomialEval

@[expose] public section

namespace ProductSum

variable {F : Type} [Field F] {n : ℕ}

/-- A table with its low `j` coordinates bound to the challenges `c`, the first the lowest. -/
def lowCache (T : CMlPolynomialEval F n) (j : ℕ) (c : Vector F j) :
    CMlPolynomialEval F (n - j) :=
  if hj : j ≤ n then
    bindLows (k := n - j) (Vector.cast (congrArg (2 ^ ·) (Nat.add_sub_cancel' hj).symm) T) c
  else Vector.replicate _ 0

/-- The bound table, read at round `j`, is the table `roundPolyFolded` binds. -/
theorem cast_lowCache (T : CMlPolynomialEval F n) {j : ℕ} (hj : j < n) (c : Vector F j) :
    Vector.cast (congrArg (2 ^ ·) (by omega)) (lowCache T j c) = boundLow T hj c := by
  rw [lowCache, dite_eq_left hj.le, bindLows_cast (by omega), Vector.cast_cast]
  rfl

/-- The honest round polynomial of round `j`, from the two tables bound to the challenges: one
pass over the free coordinates. -/
def roundOfBound {j : ℕ} (a b : CMlPolynomialEval F (n - j)) : SumcheckRound.Message F 2 :=
  if h : j < n then
    let a : CMlPolynomialEval F (n - (j + 1) + 1) := Vector.cast (congrArg (2 ^ ·) (by omega)) a
    let b : CMlPolynomialEval F (n - (j + 1) + 1) := Vector.cast (congrArg (2 ^ ·) (by omega)) b
    let s := sumFin fun x : Fin (2 ^ (n - (j + 1))) ↦
      let a0 := a[2 * x.val]'(by have := two_mul_add_one_lt x.isLt; omega)
      let a1 := a[2 * x.val + 1]'(two_mul_add_one_lt x.isLt)
      let b0 := b[2 * x.val]'(by have := two_mul_add_one_lt x.isLt; omega)
      let b1 := b[2 * x.val + 1]'(two_mul_add_one_lt x.isLt)
      (a0 * b0, a0 * (b1 - b0) + (a1 - a0) * b0, (a1 - a0) * (b1 - b0))
    #v[s.1, s.2.1, s.2.2]
  else #v[0, 0, 0]

/-- The round polynomial read off the bound tables is the honest one. -/
theorem roundOfBound_lowCache (A B : CMlPolynomialEval F n) (j : ℕ) (c : Vector F j) :
    roundOfBound (lowCache A j c) (lowCache B j c) = roundPoly A B j c := by
  rw [roundPoly_eq_roundPolyFolded, roundOfBound, roundPolyFolded]
  by_cases h : j < n
  · rw [dite_eq_left h, dite_eq_left h]
    simp only [cast_lowCache A h c, cast_lowCache B h c]
  · rw [dite_eq_right h, dite_eq_right h]

/-- The bound table after one more challenge: bound at its lowest free coordinate. -/
def stepLow {j : ℕ} (a : CMlPolynomialEval F (n - j)) (x : F) : CMlPolynomialEval F (n - (j + 1)) :=
  if h : j < n then bindLow (Vector.cast (congrArg (2 ^ ·) (by omega)) a) x
  else Vector.replicate _ 0

/-- Binding the next challenge updates the bound table. -/
theorem stepLow_lowCache (T : CMlPolynomialEval F n) {j : ℕ} (hj : j < n) (c : Vector F j)
    (x : F) : stepLow (lowCache T j c) x = lowCache T (j + 1) (c.push x) := by
  rw [stepLow, dite_eq_left hj, lowCache, dite_eq_left hj.le, lowCache,
    dite_eq_left (Nat.succ_le_of_lt hj), bindLows_cast (by omega), bindLow_bindLows,
    Vector.cast_cast, Vector.cast_cast]

/-- The bound table on every one of the first `j` coordinates, for `j ≤ n`, as a table on the
others: at `j = n`, the one entry is the extension at the challenges. -/
theorem lowCache_eq_foldBind (T : CMlPolynomialEval F n) {j : ℕ} (hj : j ≤ n) (c : Vector F j) :
    lowCache T j c =
      bindLows (k := n - j) (Vector.cast (congrArg (2 ^ ·) (Nat.add_sub_cancel' hj).symm) T) c := by
  rw [lowCache, dite_eq_left hj]

variable {X : Type} {ι : Type} {O : ι → Type} {W : Type}

/-- The round cache of the sumcheck of two tables read off the context: the tables bound to the
challenges, the round polynomial read off them, one halving per table at each challenge. -/
def roundCache (tab : SumcheckRound.Ctx X O W → CMlPolynomialEval F n × CMlPolynomialEval F n)
    {m : ℕ} (hm : m ≤ n) :
    SumcheckRound.RoundCache (fun ctx j c ↦ roundPoly (tab ctx).1 (tab ctx).2 j c) m where
  C j := CMlPolynomialEval F (n - j) × CMlPolynomialEval F (n - j)
  cache j ctx c := (lowCache (tab ctx).1 j c, lowCache (tab ctx).2 j c)
  msg _ _ _ ab := roundOfBound ab.1 ab.2
  step _ _ _ ab x := (stepLow ab.1 x, stepLow ab.2 x)
  msg_eq j ctx c _ := roundOfBound_lowCache _ _ j c
  step_eq j ctx c x hj := by
    simp only [stepLow_lowCache _ (lt_of_lt_of_le hj hm)]

end ProductSum

end
end LeanerVM.Protocol
