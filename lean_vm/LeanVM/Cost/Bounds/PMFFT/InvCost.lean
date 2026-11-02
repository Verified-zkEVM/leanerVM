module

public import LeanVM.Cost.Bounds.PMFFT.KarCost
import all CompPoly.Univariate.Raw.Ops

/-!
# Bounds of the PM decoder's FFT: low products, Newton's inverse, the remainder

`fftRawMulLowContext`'s low product (`rawMulLowFFTC`: both factors truncated at `k`, one product),
Newton's inverse modulo `X^k` on it (`inverseModXFFTC`: precisions `2, 4, …, k`, two low products
each, the products' prices doubling with the size so their sum at most twice the last), and
`fftModContext`'s remainder by reversal (`modByMonicFFTC`).
-/

namespace LeanVM.Cost.Bounds.PMFFT

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Cost.Extractor LeanVM.Parameters
open LeanVM.Extraction.Fast LeanVM.Cost.Bounds.PMBasis

public section

variable (P : MachineProgram)

theorem polyMulPrice_mono (p : PMPrices) {a b : ℕ} (h : a ≤ b) : polyMulPrice p a ≤ polyMulPrice p b := by
  unfold polyMulPrice
  have := fwdPrice_mono p h
  have := invPrice_mono p h
  have := Nat.mul_le_mul_left p.mac (Nat.pow_le_pow_right (show 0 < 2 by norm_num) h)
  omega

/-- **The low product** (`rawMulLowFFTC`, `fftRawMulLowContext.mulLow k`), `1 ≤ k ≤ 2^35`: at most
`polyMulPrice p (clog2 (2k − 1)) + karMax + 49·k + 46`. -/
theorem rawMulLowFFTC_cost (hP : Includes P rawMulLowFFTC.costDeps) (p : PMPrices) (hp : FFTPricesOK p)
    (k : ℕ) (hk : k ≤ 2 ^ 35) (a b : CompPoly.CPolynomial.Raw K) :
    machineCost P rawMulLowFFTC.costIdx [encodeValue k, encodeValue a, encodeValue b] ≤
      polyMulPrice p (clog2 (2 * k - 1)) + karMax + 49 * k + 46 := by
  rw [rawMulLowFFTC.costEq P hP]
  have ha : (a.extract 0 k).size ≤ k := by simp
  have hb : (b.extract 0 k).size ≤ k := by simp
  have h1 := Decoder.ofArray_cost P (by includes) (a.extract 0 k) (by omega)
  have h2 := Decoder.ofArray_cost P (by includes) (b.extract 0 k) (by omega)
  have sa := FFT.size_ofArray_le (a.extract 0 k)
  have sb := FFT.size_ofArray_le (b.extract 0 k)
  have hm := mulViaFFTC_cost P (by includes) p hp (CompPoly.CPolynomial.ofArray (a.extract 0 k))
    (CompPoly.CPolynomial.ofArray (b.extract 0 k)) (by omega)
  have hmono := polyMulPrice_mono p (clog2_mono (show
    (CompPoly.CPolynomial.ofArray (a.extract 0 k)).val.size +
      (CompPoly.CPolynomial.ofArray (b.extract 0 k)).val.size - 1 ≤ 2 * k - 1 by omega))
  have hr : (Array.extract (FFT.mulVia FFT.novelTransform FFT.fftSchedule
      (CompPoly.CPolynomial.ofArray (a.extract 0 k)) (CompPoly.CPolynomial.ofArray (b.extract 0 k))).val
      0 k).size ≤ k := by simp
  omega

/-- **A subtraction of raw polynomials** (`Raw.sub.c152`): at most `126·max(|x|, |y|) + 170`. -/
theorem subC_cost (hP : Includes P Auto.CompPoly.CPolynomial.Raw.sub.c152.costDeps)
    (x y : CompPoly.CPolynomial.Raw K) (hx : x.size < 2 ^ 40) (hy : y.size < 2 ^ 40) :
    machineCost P Auto.CompPoly.CPolynomial.Raw.sub.c152.costIdx [encodeValue x, encodeValue y] ≤
      126 * max x.size y.size + 170 := by
  rw [Auto.CompPoly.CPolynomial.Raw.sub.c152.costEq P hP]
  have hm := map_cost P (by includes) (fun a : K ↦ -a)
    (.closure Auto.CompPoly.CPolynomial.Raw.sub.c152.lam0.costIdx [])
    (fun a ↦ RunsApp.of_spec (Auto.CompPoly.CPolynomial.Raw.sub.c152.lam0.costSpec P (by includes) a)) 1
    y.toList (fun a _ ↦ by
      simp only [appCost_fn, List.nil_append]
      rw [Auto.CompPoly.CPolynomial.Raw.sub.c152.lam0.costEq P (by includes)])
  have hn : (CompPoly.CPolynomial.Raw.neg y).size = y.size := by
    simp [CompPoly.CPolynomial.Raw.neg]
  have ha := Decoder.addK_cost P (by includes) x (CompPoly.CPolynomial.Raw.neg y) (by omega) (by omega)
  rw [hn] at ha
  simp only [Array.length_toList, List.length_map] at hm ⊢
  have : max x.size y.size ≥ y.size := le_max_right _ _
  omega

end

end LeanVM.Cost.Bounds.PMFFT
