module

public import LeanVM.Cost.Bounds.PMFFT.KaratsubaDefs
public import LeanVM.Cost.Bounds.Decoder.GsRun
public import LeanVM.Cost.Bounds.PMLane.Names
public import LeanVM.Cost.Extractor.PMFFT
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Raw.Ops
import all CompPoly.Univariate.Basic

/-!
# Bounds: Karatsuba's product and the schoolbook branch of the FFT product, compiled

`fftMulContext`'s product (`mulViaFFTC`, `FFT.mulVia novelTransform fftSchedule`) away from its
transform branch:

* **`karatsubaC_cost`**: the compiled `karatsuba fuel p q` (the schedule's middle branch, at the
  fuel `64`), factors of at most `n ≤ 32·2^fuel` coefficients: at most `karaBound n`
  (`KaratsubaDefs.lean`: three products of half the size per level, the four splits
  (`coeffsBetweenC_cost`), two sums, the differences and the two shifts, `2000·n + 5000`, down to
  the schoolbook product at `32` coefficients);
* **`mulViaFFTC_cost_school`**: a factor of at most `32` coefficients: the schoolbook product
  folding over the small factor (`a76cca79`), linear in the other (`schoolMulBound`);
* **`mulViaFFTC_cost_kara`**: both factors of `33` to `4096` coefficients: Karatsuba's product,
  at most `karaBound 4096 + 100`.

The on-demand functions (`karatsuba`, `coeffsBetween`) are named by their terms (`cost_const%`),
so the bounds survive the chain's renumbering.
-/

namespace LeanVM.Cost.Bounds.PMFFT

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Cost.Extractor LeanVM.Parameters
open LeanVM.Extraction.Fast LeanVM.Cost.Bounds.Decoder CompPoly
open LeanVM.Cost.Auto.CompPoly.CPolynomial.Raw

public section

variable (P : MachineProgram)

/-! ## Pieces -/

/-- The negation's map (`-z` over `K`, inlined in a difference): `12` per coefficient. -/
theorem negMapC_cost (hM : Includes P Auto.List.map.c12.costDeps)
    (hL : Includes P sub.c152.lam0.costDeps) (z : CPolynomial K) :
    machineCost P Auto.List.map.c12.costIdx
        [.closure sub.c152.lam0.costIdx [], encodeValue z.val.toList] ≤ 12 * z.val.size + 3 := by
  have hf := fun a ↦ RunsApp.of_spec (us := []) (vs := [encodeValue a])
    (sub.c152.lam0.costSpec P hL a)
  have hm := listMap_le P Auto.List.map.c12.costIdx (.closure sub.c152.lam0.costIdx [])
    (Auto.List.map.c12.costEq_nil P hM _ _ hf)
    (Auto.List.map.c12.costEq_cons P hM _ _ hf) 1 z.val.toList
    (fun a _ ↦ by rw [appCost_fn, List.nil_append, sub.c152.lam0.costEq P hL])
  simp only [Array.length_toList] at hm
  omega

/-- **Coefficients `[lo, hi)`** (`coeffsBetween`): at most `24·(hi − lo) + 21`. -/
theorem coeffsBetweenC_cost
    (hP : Includes P (cost_const% (coeffsBetween (F := K)) costDeps)) (p : CPolynomial K)
    (lo hi : ℕ) (hhi : hi < 2 ^ 60) :
    machineCost P (cost_const% (coeffsBetween (F := K)) costIdx)
        [encodeValue p, encodeValue lo, encodeValue hi] ≤ 24 * (hi - lo) + 21 := by
  rw [(cost_const% (coeffsBetween (F := K)) costEq) P hP]
  have hs : (Array.extract p.val lo hi).size ≤ hi - lo := by simp; omega
  have := ofArray_cost P (by includes_sub) (Array.extract p.val lo hi) (by omega)
  omega

theorem coeffsBetween_size_le (p : CPolynomial K) (lo hi : ℕ) :
    (coeffsBetween p lo hi).val.size ≤ hi - lo :=
  (raw_trim_size_le _).trans (by simp; omega)

theorem karatsuba_size_le (fuel : ℕ) (p q : CPolynomial K) :
    (karatsuba fuel p q).val.size ≤ p.val.size + q.val.size := by
  rw [karatsuba_eq]; exact cpoly_mul_size_le p q

theorem shiftX_size_le (t : ℕ) (r : CPolynomial K) : (shiftX t r).val.size ≤ t + r.val.size :=
  (raw_trim_size_le _).trans (by simp)

theorem cpoly_sub_size_le' (x y : CPolynomial K) :
    (x - y).val.size ≤ max x.val.size y.val.size := by
  have h : x - y = x + -y := sub_eq_add_neg _ _
  rw [h]
  have := cpoly_add_size_le x (-y)
  rw [neg_val_size] at this
  exact this

/-- The schoolbook product (`Raw.mul` over `K`, folding over its first factor), the first factor
of at most `32` coefficients, the second of at most `n`. -/
theorem mulSmallC_cost (hP : Includes P mul.c55.costDeps) (p q : CPolynomial.Raw K) (n : ℕ)
    (hp : p.size ≤ 32) (hq : q.size ≤ n) (hn : n < 2 ^ 40) :
    machineCost P mul.c55.costIdx [encodeValue p, encodeValue q] ≤ 29015 * n + 102810 := by
  have := mulK_cost P hP p q (by omega) (by omega)
  have h1 : q.size * p.size ≤ n * 32 := Nat.mul_le_mul hq hp
  have h2 : p.size * p.size ≤ 32 * 32 := Nat.mul_le_mul hp hp
  omega

/-! ## Karatsuba's recursion -/

/-- **Karatsuba's product, compiled** (`karatsuba fuel p q`), factors of at most `n` coefficients,
`n ≤ 32·2^fuel` (the fuel never runs out above the schoolbook size), `fuel ≤ 64`: at most
`karaBound n`. -/
theorem karatsubaC_cost (hP : Includes P (cost_const% (karatsuba (F := K)) costDeps)) :
    ∀ (fuel : ℕ) (p q : CPolynomial K) (n : ℕ), p.val.size ≤ n → q.val.size ≤ n →
      n ≤ 32 * 2 ^ fuel → fuel ≤ 64 → n < 2 ^ 40 →
      machineCost P (cost_const% (karatsuba (F := K)) costIdx)
          [encodeValue fuel, encodeValue p, encodeValue q] ≤ karaBound n := by
  intro fuel
  induction fuel with
  | zero =>
    intro p q n hp hq hn _ hn'
    rw [(cost_const% (karatsuba (F := K)) costEq_zero) P hP]
    have := mulSmallC_cost P (by includes_sub) p.val q.val 32 (by simp at hn; omega)
      (by simp at hn; omega) (by norm_num)
    have := karaBase_le_karaBound n
    unfold schoolMulBound karaBase at *
    omega
  | succ fuel ih =>
    intro p q n hp hq hn hf hn'
    rw [(cost_const% (karatsuba (F := K)) costEq_succ) P hP]
    have hb := karaBase_le_karaBound n
    have h2f : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by rw [pow_succ]; ring
    rw [limbs_of_lt (show fuel + 1 < 2 ^ 64 by omega),
      limbs_of_lt (show p.val.size < 2 ^ 64 by omega), limbs_of_lt (show q.val.size < 2 ^ 64 by omega),
      limbs_of_lt (show max p.val.size q.val.size < 2 ^ 64 by omega),
      limbs_of_lt (show karatsubaCutoff < 2 ^ 64 by unfold karatsubaCutoff; norm_num)]
    by_cases hsm : max p.val.size q.val.size ≤ karatsubaCutoff
    · simp only [hsm, ↓reduceIte]
      unfold karatsubaCutoff at hsm
      have := mulSmallC_cost P (by includes_sub) p.val q.val 32 (by omega) (by omega) (by norm_num)
      unfold schoolMulBound karaBase at *
      split_ifs <;> omega
    · simp only [hsm, ↓reduceIte]
      unfold karatsubaCutoff at hsm
      have hn32 : ¬ n ≤ 32 := by omega
      rw [karaBound_eq n]
      simp only [hn32, ↓reduceIte]
      set m := max p.val.size q.val.size with hm
      set h := (m + 1) / 2 with hh
      have hmn : m ≤ n := max_le hp hq
      have hpm : p.val.size ≤ m := le_max_left _ _
      have hqm : q.val.size ≤ m := le_max_right _ _
      have hhf : h ≤ 32 * 2 ^ fuel := by omega
      rw [limbs_of_lt (show m + 1 < 2 ^ 64 by omega)]
      -- the splits
      have c1 := coeffsBetweenC_cost P (by includes_sub) p 0 h (by omega)
      have c2 := coeffsBetweenC_cost P (by includes_sub) p h m (by omega)
      have c3 := coeffsBetweenC_cost P (by includes_sub) q 0 h (by omega)
      have c4 := coeffsBetweenC_cost P (by includes_sub) q h m (by omega)
      have hmh : m - h ≤ h := by omega
      have hh0 : h - 0 = h := Nat.sub_zero h
      set p₀ := coeffsBetween p 0 h with hp₀
      set p₁ := coeffsBetween p h m with hp₁
      set q₀ := coeffsBetween q 0 h with hq₀
      set q₁ := coeffsBetween q h m with hq₁
      have sp₀ : p₀.val.size ≤ h := (coeffsBetween_size_le p 0 h).trans (by omega)
      have sp₁ : p₁.val.size ≤ h := (coeffsBetween_size_le p h m).trans (by omega)
      have sq₀ : q₀.val.size ≤ h := (coeffsBetween_size_le q 0 h).trans (by omega)
      have sq₁ : q₁.val.size ≤ h := (coeffsBetween_size_le q h m).trans (by omega)
      have sps : (p₀ + p₁).val.size ≤ h := (cpoly_add_size_le p₀ p₁).trans (by omega)
      have sqs : (q₀ + q₁).val.size ≤ h := (cpoly_add_size_le q₀ q₁).trans (by omega)
      have a1 : machineCost P add.c49.costIdx [encodeValue p₀.val, encodeValue p₁.val] ≤ 110 * h + 160 := by
        have := addK_cost P (by includes_sub) p₀.val p₁.val (by omega) (by omega); omega
      have a2 : machineCost P add.c49.costIdx [encodeValue q₀.val, encodeValue q₁.val] ≤ 110 * h + 160 := by
        have := addK_cost P (by includes_sub) q₀.val q₁.val (by omega) (by omega); omega
      -- the three products
      have hmono := karaBound_mono (show h ≤ (n + 1) / 2 by omega)
      have k0 := ih p₀ q₀ h sp₀ sq₀ hhf (by omega) (by omega)
      have k2 := ih p₁ q₁ h sp₁ sq₁ hhf (by omega) (by omega)
      have k1 := ih (p₀ + p₁) (q₀ + q₁) h sps sqs hhf (by omega) (by omega)
      set z₀ := karatsuba fuel p₀ q₀ with hz₀
      set z₂ := karatsuba fuel p₁ q₁ with hz₂
      set z₁ := karatsuba fuel (p₀ + p₁) (q₀ + q₁) with hz₁
      have sz₀ : z₀.val.size ≤ 2 * h := (karatsuba_size_le _ _ _).trans (by omega)
      have sz₂ : z₂.val.size ≤ 2 * h := (karatsuba_size_le _ _ _).trans (by omega)
      have sz₁ : z₁.val.size ≤ 2 * h := (karatsuba_size_le _ _ _).trans (by omega)
      -- the differences, the shifts, the sums
      have n0 := negMapC_cost P (by includes_sub) (by includes_sub) z₀
      have n2 := negMapC_cost P (by includes_sub) (by includes_sub) z₂
      have sn0 := neg_val_size z₀
      have sn2 := neg_val_size z₂
      have d1 : machineCost P add.c49.costIdx [encodeValue z₁.val, encodeValue (-z₀).val] ≤
          220 * h + 160 := by
        have := addK_cost P (by includes_sub) z₁.val (-z₀).val (by omega) (by omega); omega
      have sd1 : (z₁ - z₀).val.size ≤ 2 * h := (cpoly_sub_size_le' z₁ z₀).trans (by omega)
      have d2 : machineCost P add.c49.costIdx [encodeValue (z₁ - z₀).val, encodeValue (-z₂).val] ≤
          220 * h + 160 := by
        have := addK_cost P (by includes_sub) (z₁ - z₀).val (-z₂).val (by omega) (by omega); omega
      have sd2 : (z₁ - z₀ - z₂).val.size ≤ 2 * h := (cpoly_sub_size_le' _ z₂).trans (by omega)
      have s1 : machineCost P (cost_const% (shiftX (F := K)) costIdx) [encodeValue h, encodeValue (z₁ - z₀ - z₂)] ≤
          75 * h + 22 := by
        have := shiftXC_cost P (by includes_sub) h (z₁ - z₀ - z₂) (by omega); omega
      have ss1 : (shiftX h (z₁ - z₀ - z₂)).val.size ≤ 3 * h := (shiftX_size_le _ _).trans (by omega)
      have e1 : machineCost P add.c49.costIdx [encodeValue z₀.val,
          encodeValue (shiftX h (z₁ - z₀ - z₂)).val] ≤ 330 * h + 160 := by
        have := addK_cost P (by includes_sub) z₀.val (shiftX h (z₁ - z₀ - z₂)).val (by omega)
          (by omega)
        omega
      have se1 : (z₀ + shiftX h (z₁ - z₀ - z₂)).val.size ≤ 3 * h :=
        (cpoly_add_size_le _ _).trans (by omega)
      have s2 : machineCost P (cost_const% (shiftX (F := K)) costIdx) [encodeValue (2 * h), encodeValue z₂] ≤
          100 * h + 22 := by
        have := shiftXC_cost P (by includes_sub) (2 * h) z₂ (by omega); omega
      have ss2 : (shiftX (2 * h) z₂).val.size ≤ 4 * h := (shiftX_size_le _ _).trans (by omega)
      have e2 : machineCost P add.c49.costIdx [encodeValue (z₀ + shiftX h (z₁ - z₀ - z₂)).val,
          encodeValue (shiftX (2 * h) z₂).val] ≤ 440 * h + 160 := by
        have := addK_cost P (by includes_sub) (z₀ + shiftX h (z₁ - z₀ - z₂)).val
          (shiftX (2 * h) z₂).val (by omega) (by omega)
        omega
      simp only [List.length_map, Array.length_toList] at *
      rw [limbs_of_lt (show h < 2 ^ 64 by omega)]
      simp only [ite_self, Nat.sub_zero] at *
      have hm2 : 2 * h ≤ m + 1 := by omega
      omega

/-! ## The product's branches -/

theorem fftSchedule_small : FFT.fftSchedule.small = 32 := rfl

theorem fftSchedule_mid : FFT.fftSchedule.mid = 4096 := rfl

/-- **`fftMulContext`'s product, a factor of at most `32` coefficients** (`mulViaFFTC`, the
schoolbook branch, folding over the small factor): at most `schoolMulBound n`, the other factor
of at most `n` coefficients. -/
theorem mulViaFFTC_cost_school (hP : Includes P mulViaFFTC.costDeps) (f g : CPolynomial K) (n : ℕ)
    (hsmall : f.val.size ≤ 32 ∨ g.val.size ≤ 32) (hf : f.val.size ≤ n) (hg : g.val.size ≤ n)
    (hn : n < 2 ^ 40) :
    machineCost P mulViaFFTC.costIdx [encodeValue f, encodeValue g] ≤ schoolMulBound n := by
  rw [mulViaFFTC.costEq P hP]
  simp only [fftSchedule_small, fftSchedule_mid]
  rw [limbs_of_lt (show g.val.size < 2 ^ 64 by omega), limbs_of_lt (show f.val.size < 2 ^ 64 by omega),
    limbs_of_lt (show (32 : ℕ) < 2 ^ 64 by norm_num)]
  by_cases hg32 : g.val.size ≤ 32
  · simp only [hg32, ↓reduceIte]
    have := mulSmallC_cost P (by includes_sub) g.val f.val n hg32 hf hn
    unfold schoolMulBound at *
    omega
  · simp only [hg32, ↓reduceIte]
    have hf32 : f.val.size ≤ 32 := by omega
    simp only [hf32, ↓reduceIte]
    have := mulSmallC_cost P (by includes_sub) f.val g.val n hf32 hg hn
    unfold schoolMulBound at *
    omega

/-- **`fftMulContext`'s product, both factors of `33` to `4096` coefficients** (`mulViaFFTC`,
Karatsuba's branch at the fuel `64`): at most `karaBound 4096 + 100`. -/
theorem mulViaFFTC_cost_kara (hP : Includes P mulViaFFTC.costDeps) (f g : CPolynomial K)
    (hf : 32 < f.val.size) (hg : 32 < g.val.size) (hf' : f.val.size ≤ 4096)
    (hg' : g.val.size ≤ 4096) :
    machineCost P mulViaFFTC.costIdx [encodeValue f, encodeValue g] ≤ karaBound 4096 + 100 := by
  rw [mulViaFFTC.costEq P hP]
  simp only [fftSchedule_small, fftSchedule_mid]
  rw [limbs_of_lt (show g.val.size < 2 ^ 64 by omega), limbs_of_lt (show f.val.size < 2 ^ 64 by omega),
    limbs_of_lt (show (32 : ℕ) < 2 ^ 64 by norm_num), limbs_of_lt (show (4096 : ℕ) < 2 ^ 64 by norm_num)]
  simp only [show ¬ g.val.size ≤ 32 by omega, show ¬ f.val.size ≤ 32 by omega, hf', hg', and_self,
    ↓reduceIte]
  have := karatsubaC_cost P (by includes_sub) 64 f g 4096 hf' hg' (by norm_num) le_rfl (by norm_num)
  omega

end

end LeanVM.Cost.Bounds.PMFFT
