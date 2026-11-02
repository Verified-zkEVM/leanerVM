module

public import LeanVM.Protocol.Extraction.Fast.FFT.Basis
public import LeanVM.Protocol.Extraction.Fast.FFT.Transform
import all CompPoly.Univariate.Basic

/-!
# The additive FFT over `K`: transform, product, contexts

**The transform** (`novelTransform : PointTransform K`, `maxLog = 64`, points `x_v = K.ofBits v`):
`fwd j p` converts `p`'s monomial coefficients to the novel basis (`toNovel j`, `Fast/FFT/Basis`)
and evaluates on `U_j = {x_v | v < 2^j}` by lean_vm's additive NTT (`novelFwd j 0`);
`inv j y` interpolates (`novelInv j`) and converts back (`fromNovel j`). Its laws (`fwd_getD`,
`inv_eq`, `size_inv`, `fwd_inv`) come from `novelFwd_getD`, `novelInv_eval`,
`novelFwd_novelInv` and the conversions' `toNovel_spec`, `fromNovel_spec`.
`fftTransform : EvalMat.EvalTransform K` is the same transform for the evaluation-domain matrix
products (`EvalMat/Runtime.lean`'s `evalRuntime`).

**The product** `mulFFT p q` (`mulVia novelTransform fftCutoff`): schoolbook when a factor has at
most `fftCutoff` coefficients, else on the least `2^j ≥ |p| + |q| − 1` points (`j ≤ 64`, else
schoolbook); `mulFFT_eq : mulFFT p q = p * q`. CompPoly's contexts: `fftMulContext`,
`fftMulLowContext` (the truncated product as one product of truncated factors),
`fftRawMulLowContext`, and `fftModContext` (monic remainders by reversal on it).

**Cost** (`K` products, `N = 2^j`): `toNovel j` `≈ N·j(j+1)/4` (the division by `W_i` at level `i`
`≈ (i+1)·2^i` per block of `2^(i+1)`), `fromNovel j` the same, `novelFwd j 0` `≈ 3N·j/2`
(`N` butterflies' products and `N/2` twiddle products per stage), `novelInv j` `≈ N·j`; the product
`2 toNovel + 2 novelFwd + N + novelInv + fromNovel ≈ 3N·j²/4 + 5N·j`, and `≈ 3j` inversions.
-/

namespace LeanVM.Extraction.Fast.FFT

open CompPoly LeanVM.Parameters LeanVM.Extraction LeanVM.Extraction.NovelProofs Polynomial

public section

/-! ## Polynomials of arrays -/

theorem polyN_val {n : ℕ} (p : CPolynomial K) (hp : p.val.size ≤ n) : polyN n p.val = p.toPoly := by
  refine Polynomial.ext fun d ↦ ?_
  rw [coeff_polyN, CPolynomial.toPoly_coeff]
  split
  · rfl
  · rw [CPolynomial.coeff_eq_zero_of_size_le _ (by omega)]

theorem toPoly_ofArray (a : Array K) : (CPolynomial.ofArray a).toPoly = polyN a.size a := by
  refine Polynomial.ext fun d ↦ ?_
  rw [coeff_polyN, CPolynomial.toPoly_coeff, CPolynomial.coeff_ofArray]
  split
  · rfl
  · rfl

theorem size_ofArray_le (a : Array K) : (CPolynomial.ofArray a).val.size ≤ a.size :=
  size_le_of_coeff_eq_zero _ fun i hi ↦ by
    rw [CPolynomial.coeff_ofArray, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hi,
      Option.getD_none]

theorem ofFn_getD_self {n : ℕ} (c : Array K) (hc : c.size = n) :
    (Array.ofFn fun t : Fin n ↦ c.getD t.val 0) = c := by
  apply array_eq_of_getD (by rw [Array.size_ofFn, hc])
  intro p hp
  rw [Array.size_ofFn] at hp
  rw [getD_ofFn _ hp]

/-! ## The transform -/

/-- The evaluations on `U_j` of `p`'s first `2^j` coefficients. -/
@[expose] def novelFwdPoly (j : ℕ) (p : CPolynomial K) : Array K := novelFwd j 0 (toNovel j p.val)

/-- The polynomial of at most `2^j` coefficients with the values `y` on `U_j`. -/
@[expose] def novelInvPoly (j : ℕ) (y : Array K) : CPolynomial K :=
  CPolynomial.ofArray (fromNovel j (novelInv j y))

theorem getD_novelFwd_eval {j : ℕ} (hj : j ≤ 64) (c : Array K) {v : ℕ} (hv : v < 2 ^ j) :
    (novelFwd j 0 c).getD v 0 = (novelSum (2 ^ j) c).eval (K.ofBits v) := by
  rw [novelFwd_getD hj c (by simpa using hv), eval_novelSum]

theorem novelFwdPoly_getD {j : ℕ} (hj : j ≤ 64) (p : CPolynomial K) (hp : p.val.size ≤ 2 ^ j)
    {v : ℕ} (hv : v < 2 ^ j) : (novelFwdPoly j p).getD v 0 = p.eval (K.ofBits v) := by
  rw [novelFwdPoly, getD_novelFwd_eval hj _ hv, (toNovel_spec hj _).2, polyN_val p hp,
    CPolynomial.eval_toPoly]

theorem toPoly_novelInvPoly {j : ℕ} (hj : j ≤ 64) (y : Array K) :
    (novelInvPoly j y).toPoly = novelSum (2 ^ j) (novelInv j y) := by
  rw [novelInvPoly, toPoly_ofArray, (fromNovel_spec hj _).1, (fromNovel_spec hj _).2]

theorem size_novelInvPoly {j : ℕ} (hj : j ≤ 64) (y : Array K) :
    (novelInvPoly j y).val.size ≤ 2 ^ j :=
  (size_ofArray_le _).trans (fromNovel_spec hj _).1.le

/-- **The novel-basis transform** over `K`: `2^j` points `x_v`, `j ≤ 64`. -/
@[expose] def novelTransform : PointTransform K where
  maxLog := 64
  point v := K.ofBits v
  fwd := novelFwdPoly
  inv := novelInvPoly
  size_fwd j p := by rw [novelFwdPoly, size_novelFwd, Nat.add_zero]
  fwd_getD p hj hp _ hv := novelFwdPoly_getD hj p hp hv
  inv_eq {j} y p hj hy hp hval := by
    have hc := (toNovel_spec hj p.val).1
    have hinv : novelInv j y = toNovel j p.val := by
      rw [novelInv_eval hj (fun t ↦ (toNovel j p.val).getD t 0) y hy fun v hv ↦ by
        rw [hval v hv, CPolynomial.eval_toPoly, ← polyN_val p hp, ← (toNovel_spec hj _).2,
          eval_novelSum], ofFn_getD_self _ hc]
    apply CPolynomial.toPoly_injective
    rw [toPoly_novelInvPoly hj y, hinv, (toNovel_spec hj _).2, polyN_val p hp]
  size_inv y hj _ := size_novelInvPoly hj y
  fwd_inv {j} y hj hy := by
    have hsz : (novelFwdPoly j (novelInvPoly j y)).size = 2 ^ j := by
      rw [novelFwdPoly, size_novelFwd, Nat.add_zero]
    apply array_eq_of_getD (by rw [hsz, hy])
    intro v hv
    rw [hsz] at hv
    rw [novelFwdPoly_getD hj _ (size_novelInvPoly hj y) hv, CPolynomial.eval_toPoly,
      toPoly_novelInvPoly hj y, ← getD_novelFwd_eval hj _ hv, novelFwd_novelInv y hy]

/-- The transform for the evaluation-domain matrix products (`EvalMat`). -/
@[expose] def fftTransform : EvalMat.EvalTransform K := novelTransform.toEvalMat

/-! ## The product and CompPoly's contexts -/

/-- Below this many coefficients in a factor, the schoolbook product. -/
@[expose] def fftCutoff : ℕ := 32

/-- **The additive-FFT product** over `K`. -/
@[expose] def mulFFT (p q : CPolynomial K) : CPolynomial K := mulVia novelTransform fftCutoff p q

theorem mulFFT_eq (p q : CPolynomial K) : mulFFT p q = p * q := mulVia_eq _ _ p q

/-- CompPoly's multiplication context for the additive-FFT product. -/
@[expose] def fftMulContext : CPolynomial.MulContext K := mulContextOf novelTransform fftCutoff

/-- CompPoly's polynomial-matrix low-product context for the additive-FFT product. -/
@[expose] def fftMulLowContext : PolynomialMatrix.MulLowContext K :=
  mulLowContextOf novelTransform fftCutoff

/-- CompPoly's raw low-product context for the additive-FFT product. -/
@[expose] def fftRawMulLowContext : CPolynomial.Raw.MulLowContext K :=
  rawMulLowContextOf novelTransform fftCutoff

/-- CompPoly's monic-remainder context by reversal, on the additive-FFT low products. -/
@[expose] def fftModContext : CPolynomial.ModContext K :=
  CPolynomial.ModContext.reversal fftRawMulLowContext

end

end LeanVM.Extraction.Fast.FFT
