/-
  LeanerVM.Protocol.ProductSumWords

  The product sumcheck's bound tables over `E`, with `E`'s sums and products on words: the round
  polynomial read off the bound tables and the binding of a challenge, proved to be the generic
  ones, and the round cache built from them.
-/

module

public import LeanerVM.Protocol.ExtWords
public import LeanerVM.Protocol.ToArkLib.ProductSumCached

/-!
# The product sumcheck over `E` on words

`ProductSum.roundCache` runs the product sumcheck's rounds on tables bound once per challenge,
over any field through its instances. Over `E` every product and sum then converts each limb to
a machine word and back. `roundOfBoundW` and `bindLowW` are `roundOfBound` and `bindLow` with
`ExtWords.mulW` and `ExtWords.addW` (`roundOfBoundW_eq`, `bindLowW_eq`; in characteristic two a
difference is a sum), and `roundCacheW` is `roundCache` with them, the same cache.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly CMlPolynomialEval ExtWords

@[expose] public section

namespace ProductSum

variable {n : ℕ}

/-- `bindLow` over `E` on words. -/
def bindLowW {k : ℕ} (t : CMlPolynomialEval E (k + 1)) (r : E) : CMlPolynomialEval E k :=
  Vector.ofFn fun x ↦
    let t0 := t[2 * x.val]'(by have := two_mul_add_one_lt x.isLt; omega)
    let t1 := t[2 * x.val + 1]'(two_mul_add_one_lt x.isLt)
    addW t0 (mulW r (addW t1 t0))

/-- `bindLowW` is `bindLow`. -/
theorem bindLowW_eq {k : ℕ} (t : CMlPolynomialEval E (k + 1)) (r : E) :
    bindLowW t r = bindLow t r := by
  refine Vector.ext fun x hx ↦ ?_
  simp only [bindLowW, bindLow, bindLowAt, Vector.getElem_ofFn, addW_eq, mulW_eq,
    CharTwo.sub_eq_add]

/-- `stepLow` over `E` on words. -/
def stepLowW {j : ℕ} (a : CMlPolynomialEval E (n - j)) (x : E) :
    CMlPolynomialEval E (n - (j + 1)) :=
  if h : j < n then bindLowW (Vector.cast (congrArg (2 ^ ·) (by omega)) a) x
  else Vector.replicate _ 0

/-- `stepLowW` is `stepLow`. -/
theorem stepLowW_eq {j : ℕ} (a : CMlPolynomialEval E (n - j)) (x : E) :
    stepLowW a x = stepLow a x := by
  unfold stepLowW stepLow
  split
  · exact bindLowW_eq _ x
  · rfl

/-- The summands of a round polynomial at a pair of entries, on words, added to `acc`. -/
private def pairStepW (acc : E × E × E) (a0 a1 b0 b1 : E) : E × E × E :=
  let da := addW a1 a0
  let db := addW b1 b0
  (addW acc.1 (mulW a0 b0), addW acc.2.1 (addW (mulW a0 db) (mulW da b0)),
    addW acc.2.2 (mulW da db))

/-- `pairStepW` adds the pair's summands. -/
private theorem pairStepW_eq (acc : E × E × E) (a0 a1 b0 b1 : E) :
    pairStepW acc a0 a1 b0 b1 = acc + (a0 * b0, a0 * (b1 - b0) + (a1 - a0) * b0,
      (a1 - a0) * (b1 - b0)) := by
  simp only [pairStepW, addW_eq, mulW_eq, CharTwo.sub_eq_add]
  rfl

/-- `roundOfBound` over `E` on words. -/
@[no_expose] def roundOfBoundW {j : ℕ} (a b : CMlPolynomialEval E (n - j)) :
    SumcheckRound.Message E 2 :=
  if h : j < n then
    let a : CMlPolynomialEval E (n - (j + 1) + 1) := Vector.cast (congrArg (2 ^ ·) (by omega)) a
    let b : CMlPolynomialEval E (n - (j + 1) + 1) := Vector.cast (congrArg (2 ^ ·) (by omega)) b
    let s := Fin.foldl (2 ^ (n - (j + 1))) (fun acc x ↦
      pairStepW acc (a[2 * x.val]'(by have := two_mul_add_one_lt x.isLt; omega))
        (a[2 * x.val + 1]'(two_mul_add_one_lt x.isLt))
        (b[2 * x.val]'(by have := two_mul_add_one_lt x.isLt; omega))
        (b[2 * x.val + 1]'(two_mul_add_one_lt x.isLt))) (0, 0, 0)
    #v[s.1, s.2.1, s.2.2]
  else #v[0, 0, 0]

/-- `roundOfBoundW` is `roundOfBound`. -/
theorem roundOfBoundW_eq {j : ℕ} (a b : CMlPolynomialEval E (n - j)) :
    roundOfBoundW a b = roundOfBound a b := by
  unfold roundOfBoundW roundOfBound
  split
  · simp only [sumFin, pairStepW_eq]
    rfl
  · rfl

variable {X : Type} {ι : Type} {O : ι → Type} {W : Type}

/-- `roundCache` over `E` on words: the same cache, the round polynomials and the bindings by
`roundOfBoundW` and `stepLowW`. -/
def roundCacheW (tab : SumcheckRound.Ctx X O W → CMlPolynomialEval E n × CMlPolynomialEval E n)
    {m : ℕ} (hm : m ≤ n) :
    SumcheckRound.RoundCache (fun ctx j c ↦ roundPoly (tab ctx).1 (tab ctx).2 j c) m where
  C j := CMlPolynomialEval E (n - j) × CMlPolynomialEval E (n - j)
  cache j ctx c := (lowCache (tab ctx).1 j c, lowCache (tab ctx).2 j c)
  msg _ _ _ ab := roundOfBoundW ab.1 ab.2
  step _ _ _ ab x := (stepLowW ab.1 x, stepLowW ab.2 x)
  msg_eq j ctx c _ := by
    rw [roundOfBoundW_eq]
    exact roundOfBound_lowCache _ _ j c
  step_eq j ctx c x hj := by
    simp only [stepLowW_eq, stepLow_lowCache _ (lt_of_lt_of_le hj hm)]

end ProductSum

end

end LeanerVM.Protocol
