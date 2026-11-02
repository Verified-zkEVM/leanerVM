module

public import LeanVM.Cost.Bounds.PMFFT.KarCost
import all CompPoly.Univariate.Raw.Ops
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Basic
public import LeanVM.Cost.Bounds.Decoder.Roots

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

/-- **The additive-FFT product** (`mulFFTC`, `mulVia novelTransform fftSchedule`):
`mulViaFFTC`'s price and `3`. -/
theorem mulFFTC_cost (hP : Includes P mulFFTC.costDeps) (p : PMPrices) (hp : FFTPricesOK p)
    (f g : CompPoly.CPolynomial K) (hj : f.val.size + g.val.size - 1 ≤ 2 ^ 36) :
    machineCost P mulFFTC.costIdx [encodeValue f, encodeValue g] ≤
      polyMulPrice p (clog2 (f.val.size + g.val.size - 1)) + karMax + 3 := by
  rw [mulFFTC.costEq P hP]
  have := mulViaFFTC_cost P (by includes) p hp f g hj
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

/-- Newton's price per step beyond its two products, at precision `≤ k`: the `karMax` and the
`2^20` of each product (the latter left over from the products' telescoping), the subtraction. -/
@[expose] def newtonExtra (k : ℕ) : ℕ := 2 * karMax + 224 * k + 2 ^ 21 + 500

/-- **Newton's inverse modulo `X^k`, proved price**: four products at the last precision (the
precisions `2, 4, …, k` double, so do the products' prices: their sum is at most twice the last's,
two products a step) and `⌈log₂ k⌉` times `newtonExtra k`, the inversion of the constant term. -/
@[expose] def newtonBound (p : PMPrices) (k : ℕ) : ℕ :=
  4 * polyMulPrice p (clog2 (2 * k - 1)) + clog2 k * newtonExtra k + k + 19740

/-- A product over twice the points costs at least twice as much, but for the `2^20`. -/
theorem polyMulPrice_succ (p : PMPrices) (j : ℕ) :
    2 * polyMulPrice p j ≤ polyMulPrice p (j + 1) + 2 ^ 20 := by
  unfold polyMulPrice fwdPrice invPrice
  rw [show 2 ^ (j + 1) = 2 ^ j * 2 from pow_succ 2 j]
  generalize 2 ^ j = X
  nlinarith [Nat.zero_le ((p.toNovel + p.fwd) * X), Nat.zero_le ((p.fromNovel + p.inv) * X)]

/-- Newton's precision doubling from `2^i` to `k' > 2^i`: four products at the former within two
at the latter. -/
theorem polyMulPrice_newton (p : PMPrices) {i k' : ℕ} (h : 2 ^ i < k') :
    4 * polyMulPrice p (clog2 (2 * 2 ^ i - 1)) ≤ 2 * polyMulPrice p (clog2 (2 * k' - 1)) + 2 ^ 21 := by
  have h1 : clog2 (2 * 2 ^ i - 1) ≤ i + 1 := PMBasis.clog2_le (by rw [pow_succ]; omega)
  have h2 : i + 1 + 1 ≤ clog2 (2 * k' - 1) := by
    by_contra hc
    have e1 := PMBasis.le_two_pow_clog2 (2 * k' - 1)
    have e2 := Nat.pow_le_pow_right (show 0 < 2 by norm_num)
      (show clog2 (2 * k' - 1) ≤ i + 1 by omega)
    rw [pow_succ] at e2
    omega
  have := polyMulPrice_succ p (i + 1)
  have := polyMulPrice_mono p h1
  have := polyMulPrice_mono p h2
  omega

/-- **Newton's loop** (`inverseModX.go.c903`) from precision `a ≤ k` with `k ≤ a·2^m`, `a` a power
of two or `k`: its price and four products at precision `a` within four at `k` and
`m · newtonExtra k + k + 20`. -/
theorem newtonGo_cost (hP : Includes P Auto.CompPoly.CPolynomial.Raw.inverseModX.go.c903.costDeps)
    (p : PMPrices) (hp : FFTPricesOK p) (k : ℕ) (hk : k ≤ 2 ^ 35) (f : CompPoly.CPolynomial.Raw K) :
    ∀ m fuel a (acc : CompPoly.CPolynomial.Raw K), 1 ≤ a → a ≤ k → k ≤ a * 2 ^ m → fuel < 2 ^ 64 →
      (a = k ∨ ∃ i, a = 2 ^ i) →
      machineCost P Auto.CompPoly.CPolynomial.Raw.inverseModX.go.c903.costIdx [encodeValue k,
        encodeValue f, encodeValue fuel, encodeValue a, encodeValue acc] +
          4 * polyMulPrice p (clog2 (2 * a - 1)) ≤
        4 * polyMulPrice p (clog2 (2 * k - 1)) + m * newtonExtra k + k + 20 := by
  intro m
  induction m with
  | zero =>
    intro fuel a acc ha hak hkm hf _
    have hs : (acc.extract 0 k).size ≤ k := by simp
    have hmono := polyMulPrice_mono p (clog2_mono (show 2 * a - 1 ≤ 2 * k - 1 by omega))
    rw [Auto.CompPoly.CPolynomial.Raw.inverseModX.go.c903.costEq P hP]
    cases fuel with
    | zero => cost_simp; omega
    | succ n =>
      cost_simp
      rw [ite_eq_left (by simpa using hkm)]
      omega
  | succ m ih =>
    intro fuel a acc ha hak hkm hf hpow
    have hs : (acc.extract 0 k).size ≤ k := by simp
    have hmono := polyMulPrice_mono p (clog2_mono (show 2 * a - 1 ≤ 2 * k - 1 by omega))
    rw [Auto.CompPoly.CPolynomial.Raw.inverseModX.go.c903.costEq P hP]
    cases fuel with
    | zero => cost_simp; omega
    | succ n =>
      cost_simp
      by_cases hka : k ≤ a
      · rw [ite_eq_left hka]; omega
      · rw [ite_eq_right hka]
        obtain ⟨i, hi⟩ : ∃ i, a = 2 ^ i := hpow.resolve_left (by omega)
        set k' := min k (2 * a) with hk'
        rw [show k.min (2 * a) = k' from rfl]
        have hk'k : k' ≤ k := min_le_left _ _
        have hk'1 : 1 ≤ k' := by omega
        have hak' : a < k' := by omega
        have r1 := rawMulLowFFTC_cost P (by includes) p hp k' (by omega) f acc
        have hml := FFT.fftRawMulLowContext.size_le k' f acc
        have hC : (CompPoly.CPolynomial.Raw.C (2 : K)).size = 1 := rfl
        have s1 := subC_cost P (by includes) (CompPoly.CPolynomial.Raw.C 2)
          (FFT.fftRawMulLowContext.mulLow k' f acc) (by omega) (by omega)
        have r2 := rawMulLowFFTC_cost P (by includes) p hp k' (by omega) acc
          (CompPoly.CPolynomial.Raw.C 2 - FFT.fftRawMulLowContext.mulLow k' f acc)
        have hrec := ih n k' (FFT.fftRawMulLowContext.mulLow k' acc
          (CompPoly.CPolynomial.Raw.C 2 - FFT.fftRawMulLowContext.mulLow k' f acc)) hk'1 hk'k
          (by
            rcases Nat.le_total k (2 * a) with h | h
            · have : k' = k := by omega
              rw [this]; exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
            · have : k' = 2 * a := by omega
              rw [this, pow_succ] at *; nlinarith) (by omega)
          (by
            rcases Nat.le_total k (2 * a) with h | h
            · left; omega
            · right; exact ⟨i + 1, by rw [pow_succ]; omega⟩)
        have hnew := polyMulPrice_newton p (i := i) (k' := k') (by omega)
        rw [← hi] at hnew
        have hmax : max (CompPoly.CPolynomial.Raw.C (2 : K)).size
            (FFT.fftRawMulLowContext.mulLow k' f acc).size ≤ k' := by rw [hC]; omega
        unfold newtonExtra at hrec ⊢
        have e : (m + 1) * (2 * karMax + 224 * k + 2 ^ 21 + 500) =
            m * (2 * karMax + 224 * k + 2 ^ 21 + 500) + (2 * karMax + 224 * k + 2 ^ 21 + 500) := by
          ring
        rw [e]
        split_ifs <;> omega

/-- **Newton's inverse modulo `X^k`** (`inverseModXFFTC`), `k ≤ 2^35`: at most
`newtonBound p k` (four products at precision `k`, `⌈log₂ k⌉` steps' extras, one inversion). -/
theorem inverseModXFFTC_cost (hP : Includes P inverseModXFFTC.costDeps) (p : PMPrices)
    (hp : FFTPricesOK p) (k : ℕ) (hk : k ≤ 2 ^ 35) (f : CompPoly.CPolynomial.Raw K) :
    machineCost P inverseModXFFTC.costIdx [encodeValue k, encodeValue f] ≤ newtonBound p k := by
  rw [inverseModXFFTC.costEq P hP]
  unfold newtonBound
  by_cases hk0 : k = 0
  · simp [hk0]
  · rw [ite_eq_right hk0]
    have hc := le_two_pow_clog2 k
    have h1 := invK_cost P (by includes) (f.coeff 0)
    have h2 := newtonGo_cost P (by includes) p hp k hk f (clog2 k) (k + 1) 1
      (CompPoly.CPolynomial.Raw.C (f.coeff 0)⁻¹) le_rfl (by omega) (by omega) (by omega)
      (Or.inr ⟨0, rfl⟩)
    cost_simp
    omega

/-- **A reversal** (`Raw.reverse.c906`) of `n < 2^40` coefficients: at most `30·n + 20`. -/
theorem reverseC_cost (hP : Includes P Auto.CompPoly.CPolynomial.Raw.reverse.c906.costDeps) (n : ℕ)
    (hn : n < 2 ^ 40) (f : CompPoly.CPolynomial.Raw K) :
    machineCost P Auto.CompPoly.CPolynomial.Raw.reverse.c906.costIdx [encodeValue n, encodeValue f] ≤
      30 * n + 20 := by
  rw [Auto.CompPoly.CPolynomial.Raw.reverse.c906.costEq P hP]
  have hof := ofFnFrom_cost P (by includes) (n := n) (by omega) _
    (.closure Auto.CompPoly.CPolynomial.Raw.reverse.c906.lam0.costIdx [encodeValue n, encodeValue f])
    (fun i ↦ RunsApp.of_spec (Auto.CompPoly.CPolynomial.Raw.reverse.c906.lam0.costSpec P (by includes)
      n f i)) 11
    (fun i ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [Auto.CompPoly.CPolynomial.Raw.reverse.c906.lam0.costEq P (by includes)]
      have := i.isLt
      cost_simp
      omega) 0 (Nat.zero_le _)
  simp only [Nat.sub_zero] at hof
  try rw [ofFnFrom_length]
  omega

theorem newtonExtra_mono {a b : ℕ} (h : a ≤ b) : newtonExtra a ≤ newtonExtra b := by
  unfold newtonExtra; omega

theorem newtonBound_mono (p : PMPrices) {a b : ℕ} (h : a ≤ b) : newtonBound p a ≤ newtonBound p b := by
  unfold newtonBound
  have := polyMulPrice_mono p (clog2_mono (show 2 * a - 1 ≤ 2 * b - 1 by omega))
  have := Nat.mul_le_mul (clog2_mono h) (newtonExtra_mono h)
  omega

/-- At most half of `N` coefficients: one doubling fewer. -/
theorem clog2_half {x N : ℕ} (h : 2 * x ≤ N) : clog2 (2 * x - 1) ≤ clog2 (2 * N - 1) - 1 := by
  apply PMBasis.clog2_le
  have e := PMBasis.le_two_pow_clog2 (2 * N - 1)
  rcases Nat.eq_zero_or_pos (clog2 (2 * N - 1)) with h0 | h0
  · rw [h0] at e ⊢; simp at e ⊢; omega
  · obtain ⟨t, ht⟩ : ∃ t, clog2 (2 * N - 1) = t + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h0).symm⟩
    rw [ht] at e ⊢
    rw [pow_succ] at e
    simp only [Nat.add_sub_cancel]
    omega

/-- **The remainder's products**: five at precision `k` (Newton's four, the quotient's) and one at
`q` (the back-product), `k + q ≤ N`, within five at `N` and one at half of it. -/
theorem polyMulPrice_mod_split (p : PMPrices) {k q N : ℕ} (h : k + q ≤ N) :
    5 * polyMulPrice p (clog2 (2 * k - 1)) + polyMulPrice p (clog2 (2 * q - 1)) ≤
      5 * polyMulPrice p (clog2 (2 * N - 1)) + polyMulPrice p (clog2 (2 * N - 1) - 1) := by
  have hTT := polyMulPrice_mono p (show clog2 (2 * N - 1) - 1 ≤ clog2 (2 * N - 1) by omega)
  rcases Nat.le_total (2 * k) N with hk | hk
  · have h1 := polyMulPrice_mono p (clog2_half hk)
    have h2 := polyMulPrice_mono p (clog2_mono (show 2 * q - 1 ≤ 2 * N - 1 by omega))
    omega
  · have h1 := polyMulPrice_mono p (clog2_mono (show 2 * k - 1 ≤ 2 * N - 1 by omega))
    have h2 := polyMulPrice_mono p (clog2_half (show 2 * q ≤ N by omega))
    omega

/-- The proved price of a remainder by a monic polynomial, the dividend of `N` coefficients: five
products at `N` and one at half of it (`≈ 5.5` products), Newton's and the operands' extras. -/
@[expose] def modBound (p : PMPrices) (N : ℕ) : ℕ :=
  5 * polyMulPrice p (clog2 (2 * N - 1)) + polyMulPrice p (clog2 (2 * N - 1) - 1) +
    clog2 N * newtonExtra N + 2 * karMax + 501 * N + 40740

/-- **`fftModContext`'s remainder** (`modByMonicFFTC`, by reversal), `g` monic, `f` of at most
`N ≤ 2^35` coefficients (and `g` too): at most `modBound p N` (Newton's inverse of the reversed
divisor at precision `|f| − |g| + 1`, the quotient's and the back-product's low products; the
two precisions sum to `|f| ≤ N`, so one of them is at most half of `N`). -/
theorem modByMonicFFTC_cost (hP : Includes P modByMonicFFTC.costDeps) (p : PMPrices)
    (hp : FFTPricesOK p) (f g : CompPoly.CPolynomial K) (N : ℕ) (hN : N ≤ 2 ^ 35)
    (hf : f.val.size ≤ N) (hgN : g.val.size ≤ N) (hg1 : 0 < g.val.size) (hg : g.leadingCoeff = 1) :
    machineCost P modByMonicFFTC.costIdx [encodeValue f, encodeValue g] ≤ modBound p N := by
  rw [modByMonicFFTC.costEq P hP, Auto.CompPoly.CPolynomial.Raw.modByMonicByReversal.c905.costEq P
    (by includes)]
  have hlc : (CompPoly.CPolynomial.Raw.leadingCoeff g.val == 1) = true := by
    unfold CompPoly.CPolynomial.Raw.leadingCoeff
    unfold CompPoly.CPolynomial.leadingCoeff at hg
    rw [CompPoly.CPolynomial.trim_eq]
    exact beq_iff_eq.mpr hg
  simp only [CompPoly.CPolynomial.trim_eq, beq_self_eq_true, Bool.and_self, hlc,
    ite_true]
  set F := f.val.size
  set Q := g.val.size
  have t1 := Decoder.trimLen_cost P (by includes) f.val F (by omega)
  have t2 := Decoder.trimLen_cost P (by includes) g.val Q (by omega)
  have b1 := listBeqK_cost P (by includes) f.val.toList f.val.toList
  have b2 := listBeqK_cost P (by includes) g.val.toList g.val.toList
  have gl := Decoder.getLastDC_cost P (by includes) g.val 0 (by omega)
  have e1 : (f.val.extract 0 (CompPolyLib.trimLen f.val F)).size ≤ F := by
    simp only [Array.size_extract]; omega
  have e2 : (g.val.extract 0 (CompPolyLib.trimLen g.val Q)).size ≤ Q := by
    simp only [Array.size_extract]; omega
  simp only [Array.length_toList] at b1 b2
  have hcm : clog2 (F - Q + 1) * newtonExtra (F - Q + 1) ≤ clog2 N * newtonExtra N :=
    Nat.mul_le_mul (clog2_mono (show F - Q + 1 ≤ N by omega)) (newtonExtra_mono (by omega))
  unfold modBound
  cost_simp
  split_ifs with hlt
  · omega
  · set k := F - Q + 1
    have r1 := reverseC_cost P (by includes) F (by omega) f.val
    have r2 := reverseC_cost P (by includes) Q (by omega) g.val
    have iv := inverseModXFFTC_cost P (by includes) p hp k (by omega)
      (CompPoly.CPolynomial.Raw.reverse Q g.val)
    have l1 := rawMulLowFFTC_cost P (by includes) p hp k (by omega)
      (CompPoly.CPolynomial.Raw.reverse F f.val)
      (CompPoly.CPolynomial.Raw.inverseModX FFT.fftRawMulLowContext k
        (CompPoly.CPolynomial.Raw.reverse Q g.val))
    have r3 := reverseC_cost P (by includes) k (by omega)
      (FFT.fftRawMulLowContext.mulLow k (CompPoly.CPolynomial.Raw.reverse F f.val)
        (CompPoly.CPolynomial.Raw.inverseModX FFT.fftRawMulLowContext k
          (CompPoly.CPolynomial.Raw.reverse Q g.val)))
    have l2 := rawMulLowFFTC_cost P (by includes) p hp (Q - 1) (by omega) g.val
      (CompPoly.CPolynomial.Raw.reverse k
        (FFT.fftRawMulLowContext.mulLow k (CompPoly.CPolynomial.Raw.reverse F f.val)
          (CompPoly.CPolynomial.Raw.inverseModX FFT.fftRawMulLowContext k
            (CompPoly.CPolynomial.Raw.reverse Q g.val))))
    have hml := FFT.fftRawMulLowContext.size_le (Q - 1) g.val
      (CompPoly.CPolynomial.Raw.reverse k
        (FFT.fftRawMulLowContext.mulLow k (CompPoly.CPolynomial.Raw.reverse F f.val)
          (CompPoly.CPolynomial.Raw.inverseModX FFT.fftRawMulLowContext k
            (CompPoly.CPolynomial.Raw.reverse Q g.val))))
    have htr : (CompPoly.CPolynomial.Raw.truncate (Q - 1) f.val).size ≤ F := by
      simp only [CompPoly.CPolynomial.Raw.truncate, Array.size_extract]; omega
    have sb := subC_cost P (by includes) (CompPoly.CPolynomial.Raw.truncate (Q - 1) f.val)
      (FFT.fftRawMulLowContext.mulLow (Q - 1) g.val
        (CompPoly.CPolynomial.Raw.reverse k
          (FFT.fftRawMulLowContext.mulLow k (CompPoly.CPolynomial.Raw.reverse F f.val)
            (CompPoly.CPolynomial.Raw.inverseModX FFT.fftRawMulLowContext k
              (CompPoly.CPolynomial.Raw.reverse Q g.val))))) (by omega) (by omega)
    have hmax : max (CompPoly.CPolynomial.Raw.truncate (Q - 1) f.val).size
        (FFT.fftRawMulLowContext.mulLow (Q - 1) g.val
          (CompPoly.CPolynomial.Raw.reverse k
            (FFT.fftRawMulLowContext.mulLow k (CompPoly.CPolynomial.Raw.reverse F f.val)
              (CompPoly.CPolynomial.Raw.inverseModX FFT.fftRawMulLowContext k
                (CompPoly.CPolynomial.Raw.reverse Q g.val))))).size ≤ N := max_le (by omega) (by omega)
    have e3 : (f.val.extract 0 (Q - 1)).size ≤ N := by simp only [Array.size_extract]; omega
    have hsp := polyMulPrice_mod_split p (k := k) (q := Q - 1) (N := N) (by omega)
    unfold newtonBound at iv
    omega

end

end LeanVM.Cost.Bounds.PMFFT
