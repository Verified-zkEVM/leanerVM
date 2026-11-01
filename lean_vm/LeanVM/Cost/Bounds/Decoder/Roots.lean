module

public import LeanVM.Cost.Bounds.Decoder.Interpolate
public import LeanVM.Cost.Bounds.Sizes.RootFinder
public import LeanVM.Cost.Bounds.Sizes.Splitter
public import LeanVM.Cost.Extractor.Roots
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Raw.Ops
import all CompPoly.Univariate.Raw.Context
import all CompPoly.Univariate.Raw.Division
import all CompPoly.Univariate.Raw.Modular
import all CompPoly.Univariate.Basic

/-!
# Bound: arithmetic modulo a polynomial over `K`, compiled

The prices of the root finder's arithmetic (`Cost/Extractor/Roots.lean`) on polynomials of at
most `B` coefficients, `B` word-sized:

* `monicNormalize` (an inverse and a scaling), the remainder-only long division
  (`modByMonicRemainderOnly.go`: each step rebuilds the remainder, `≤ 360·A + 100` for a
  remainder of `≤ A` coefficients);
* the product modulo `u` (`mulModWithC_cost`: `≤ mulModBound B = 2500·B² + 1000·B + 20000`), the
  binary powering (`powModBinaryAuxC_cost`: `log₂ n + 1` steps of two products), `X^q − X mod u`
  (`xPowSubXModC_cost`);
* the remainder `p mod q` (`rawModFastC_cost`) and the monic gcd (`rawGcdMonicWithFuelC_cost`,
  `gcdMonicFastC_cost`: at most `2·B + 1` remainders).

**Honest-cost note.** The remainder-only long division rebuilds the whole remainder at each step
(`subScaledShift` over all `|a|` coefficients, then a trim), so a remainder of `p` by `q` costs
`O(|p|²)`, not `O(|q|·(|p| − |q| + 1))`; the Euclidean gcd is then `O(B³)`, not `O(B²)`.
-/

namespace LeanVM.Cost.Bounds.Decoder

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Bounds.Samples LeanVM.Cost.Library
open LeanVM.Cost.Extractor LeanVM.Parameters CompPoly LeanVM.Extraction.Fast

/-! The functions compiled on demand, by their short names. -/
open LeanVM.Cost.Auto.CompPoly.CPolynomial.Raw LeanVM.Cost.Auto.LeanVM.Extraction.Fast

public section

variable (P : Program)

theorem limbs_le_two {n : ℕ} (h : n < 2 ^ 128) : limbs n ≤ 2 := by
  unfold limbs
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have := (Nat.log2_lt (by omega)).2 h
    omega

theorem size_zero_raw : (0 : CPolynomial.Raw K).size = 0 := rfl

theorem toList_zero_raw : (0 : CPolynomial.Raw K).toList = [] := rfl

theorem size_one_raw : (1 : CPolynomial.Raw K).size = 1 := by
  change (#[] |>.push (1 : K)).size = 1
  simp

theorem size_X_raw : (CPolynomial.Raw.X : CPolynomial.Raw K).size = 2 := by
  simp [CPolynomial.Raw.X]

/-- `getLastD`: at most `8`. -/
theorem getLastDC_cost (hP : Includes P Auto.Array.getLastD.c144.costDeps) (a : Array K) (v : K)
    (ha : a.size < 2 ^ 64) : machineCost P Auto.Array.getLastD.c144.costIdx [enc a, enc v] ≤ 8 := by
  rw [Auto.Array.getLastD.c144.costEq P hP]
  cost_simp
  omega

theorem trim_size_le' (p : CPolynomial.Raw K) : p.trim.size ≤ p.size := raw_trim_size_le p

/-- **`monicNormalize`** (raw): at most `340·|p| + 19800`. -/
theorem monicNormalizeRawC_cost (hP : Includes P monicNormalize.c143.costDeps)
    (p : CPolynomial.Raw K) (hp : p.size < 2 ^ 60) :
    machineCost P monicNormalize.c143.costIdx [enc p] ≤ 340 * p.size + 19800 := by
  rw [monicNormalize.c143.costEq P hP]
  have ht := trim_size_le' p
  have := trimLen_cost P (by includes) p p.size (by omega)
  have := trimLen_cost P (by includes) p.trim p.trim.size (by omega)
  have : (Array.extract p 0 (CompPolyLib.trimLen p p.size)).size ≤ p.size := by simp
  have : (Array.extract p.trim 0 (CompPolyLib.trimLen p.trim p.trim.size)).size ≤ p.size := by
    simp; omega
  have := listBeqK_cost P (by includes) p.trim.toList (Array.toList 0)
  have := getLastDC_cost P (by includes) p.trim.trim 0 (by have := trim_size_le' p.trim; omega)
  have := invK_cost P (by includes) p.trim.leadingCoeff
  have := smulK_cost P (by includes) p.trim.leadingCoeff⁻¹ p.trim
  simp only [Array.length_toList, size_zero_raw] at *
  split_ifs <;> omega

/-- One coefficient of `p − scale·X^shift·q`: at most `284`. -/
theorem subScaledShiftLamC_cost (hP : Includes P subScaledShift.c149.lam0.costDeps)
    (p q : CPolynomial.Raw K) (scale : K) (shift : ℕ) (j : Fin p.size) (hp : p.size < 2 ^ 64)
    (hq : q.size < 2 ^ 64) (hs : shift < 2 ^ 64) :
    machineCost P subScaledShift.c149.lam0.costIdx [enc p, enc q, enc scale, enc shift, enc j] ≤
      284 := by
  rw [subScaledShift.c149.lam0.costEq P hP]
  have := j.isLt
  cost_simp
  split_ifs <;> omega

/-- **`p − scale·X^shift·q`** (`subScaledShift`, the array rebuilt then trimmed): at most
`326·|p| + 34`. -/
theorem subScaledShiftC_cost (hP : Includes P subScaledShift.c149.costDeps)
    (p q : CPolynomial.Raw K) (scale : K) (shift : ℕ) (hp : p.size < 2 ^ 60)
    (hq : q.size < 2 ^ 64) (hs : shift < 2 ^ 64) :
    machineCost P subScaledShift.c149.costIdx [enc p, enc q, enc scale, enc shift] ≤
      326 * p.size + 34 := by
  rw [subScaledShift.c149.costEq P hP]
  have hf := fun j ↦ RunsApp.of_spec (us := [enc p, enc q, enc scale, enc shift]) (vs := [enc j])
    (subScaledShift.c149.lam0.costSpec P (by includes) p q scale shift j)
  have := ofFnFromC_cost P (by includes) (n := p.size) (by omega) _
    (.fn subScaledShift.c149.lam0.costIdx [enc p, enc q, enc scale, enc shift]) hf 284
    (fun j ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      exact subScaledShiftLamC_cost P (by includes) p q scale shift j (by omega) hq hs)
    p.size 0 (by omega) (by omega)
  generalize hA : (CPolynomial.Raw.mk (Array.ofFn fun j : Fin p.size ↦
    p.coeff ↑j - (if shift ≤ ↑j ∧ ↑j - shift < q.size then scale * q.coeff (↑j - shift) else 0)))
      = A at *
  have hAs : A.size = p.size := by rw [← hA]; simp [CPolynomial.Raw.mk]
  have := trimLen_cost P (by includes) A A.size (by omega)
  have : (Array.extract A 0 (CompPolyLib.trimLen A A.size)).size ≤ A.size := by simp
  simp only [length_ofFnFrom, Nat.sub_zero] at *
  omega

/-- **The remainder-only long division** (`modByMonicRemainderOnly.go`, `n` steps, remainders of
at most `A` coefficients): at most `(360·A + 100)·n + 6`. -/
theorem modGoC_cost (hP : Includes P modByMonicRemainderOnly.go.c148.costDeps)
    (q : CPolynomial.Raw K) (A : ℕ) (hA : A < 2 ^ 60) (hq : q.size < 2 ^ 64) :
    ∀ (n : ℕ) (a : CPolynomial.Raw K), n < 2 ^ 63 → a.size ≤ A →
      machineCost P modByMonicRemainderOnly.go.c148.costIdx [enc n, enc a, enc q] ≤
        (360 * A + 100) * n + 6 := by
  intro n
  induction n with
  | zero => intro a _ _; rw [modByMonicRemainderOnly.go.c148.costEq_zero P hP]; omega
  | succ n ih =>
    intro a hn ha
    rw [modByMonicRemainderOnly.go.c148.costEq_succ P hP]
    have hsub := subScaledShift_size_le a q a.leadingCoeff (a.size - q.size)
    have := ih (a.subScaledShift q a.leadingCoeff (a.size - q.size)) (by omega) (by omega)
    have := subScaledShiftC_cost P (by includes) a q a.leadingCoeff (a.size - q.size) (by omega)
      hq (by omega)
    have := trimLen_cost P (by includes) a a.size (by omega)
    have : (Array.extract a 0 (CompPolyLib.trimLen a a.size)).size ≤ a.size := by simp
    have := getLastDC_cost P (by includes) a.trim 0 (by have := trim_size_le' a; omega)
    cost_simp
    have e : (360 * A + 100) * (n + 1) = (360 * A + 100) * n + 360 * A + 100 := by ring
    split_ifs <;> omega

theorem naive_mul_size_le (p q : CPolynomial.Raw K) :
    (CPolynomial.Raw.MulContext.naive.mul p q).size ≤ p.size + q.size :=
  (raw_trim_size_le _).trans (size_mulRaw_le p q)

/-- The bound of a product modulo `u`, operands and `u` of at most `B` coefficients. -/
@[expose] def mulModBound (B : ℕ) : ℕ := 2500 * (B * B) + 1000 * B + 20000

/-- **A product modulo `u`** (`mulModWith`: the schoolbook product, then the remainder by
`monicNormalize u`): at most `mulModBound B`. -/
theorem mulModWithC_cost (hP : Includes P mulModWith.c156.costDeps) {B : ℕ} (hB : B < 2 ^ 28)
    (u p q : CPolynomial.Raw K) (hu : u.size ≤ B) (hp : p.size ≤ B) (hq : q.size ≤ B) :
    machineCost P mulModWith.c156.costIdx [enc u, enc p, enc q] ≤ mulModBound B := by
  rw [mulModWith.c156.costEq P hP]
  have := mulK_cost P (by includes) p q (by omega) (by omega)
  have h1 : q.size * p.size ≤ B * B := Nat.mul_le_mul hq hp
  have h2 : p.size * p.size ≤ B * B := Nat.mul_le_mul hp hp
  have ht := trim_size_le' u
  have := trimLen_cost P (by includes) u u.size (by omega)
  have : (Array.extract u 0 (CompPolyLib.trimLen u u.size)).size ≤ u.size := by simp
  have := listBeqK_cost P (by includes) u.trim.toList (Array.toList 0)
  have := monicNormalizeRawC_cost P (by includes) u (by omega)
  have hm := naive_mul_size_le p q
  have := modGoC_cost P (by includes) u.monicNormalize (2 * B) (by omega)
    (by have := raw_monicNormalize_size_le u; omega)
    (CPolynomial.Raw.MulContext.naive.mul p q).size (CPolynomial.Raw.MulContext.naive.mul p q)
    (by omega) (by omega)
  have h3 : (360 * (2 * B) + 100) * (CPolynomial.Raw.MulContext.naive.mul p q).size ≤
      (360 * (2 * B) + 100) * (2 * B) := Nat.mul_le_mul_left _ (by omega)
  have e : (360 * (2 * B) + 100) * (2 * B) = 1440 * (B * B) + 200 * B := by ring
  simp only [Array.length_toList, size_zero_raw] at *
  unfold mulModBound
  split_ifs <;> omega

theorem sqModC_cost (hP : Includes P sqMod.c172.costDeps) {B : ℕ} (hB : B < 2 ^ 28)
    (u c : CPolynomial.Raw K) (hu : u.size ≤ B) (hc : c.size ≤ B) :
    machineCost P sqMod.c172.costIdx [enc u, enc c] ≤ mulModBound B + 4 := by
  rw [sqMod.c172.costEq P hP]
  have := mulModWithC_cost P (by includes) hB u c c hu hc hc
  omega

theorem mulModWith_size_le {u a b : CPolynomial.Raw K} {B : ℕ} (hu : u.trim ≠ 0)
    (huB : u.size ≤ B) :
    (CPolynomial.Raw.mulModWith CPolynomial.Raw.MulContext.naive
      CPolynomial.Raw.ModContext.remainderOnly u a b).size ≤ B := by
  have := mulModWith_size_lt u a b hu
  have := trim_size_le' u
  omega

/-- **The binary powering modulo `u`** (`powModBinaryAuxWith`: per bit of `n` a squaring and at
most one product): at most `6 + (2·mulModBound B + 50)·(log₂ n + 1)`, `n < 2^65`. -/
theorem powModBinaryAuxC_cost (hP : Includes P powModBinaryAuxWith.c155.costDeps) {B : ℕ}
    (hB : B < 2 ^ 28) (u : CPolynomial.Raw K) (hu : u.trim ≠ 0) (huB : u.size ≤ B)
    (n : ℕ) (acc c : CPolynomial.Raw K) (hn : n < 2 ^ 65) (hacc : acc.size ≤ B)
    (hc : c.size ≤ B) :
    machineCost P powModBinaryAuxWith.c155.costIdx [enc u, enc n, enc acc, enc c] ≤
      6 + (2 * mulModBound B + 50) * (Nat.log2 n + 1) := by
  have key := le_of_halving
    (fun x : ℕ × CPolynomial.Raw K × CPolynomial.Raw K ↦
      x.2.1.size ≤ B ∧ x.2.2.size ≤ B ∧ x.1 < 2 ^ 65)
    (fun x ↦ x.1)
    (fun x ↦ machineCost P powModBinaryAuxWith.c155.costIdx [enc u, enc x.1, enc x.2.1, enc x.2.2])
    (2 * mulModBound B + 50) 6
    (fun x _ h0 ↦ by
      obtain ⟨n, acc, c⟩ := x
      dsimp only at h0 ⊢
      subst h0
      rw [powModBinaryAuxWith.c155.costEq_zero P hP])
    (fun x hI hpos ↦ by
      obtain ⟨n, acc, c⟩ := x
      obtain ⟨hacc, hc, hn⟩ := hI
      dsimp only at hpos hacc hc hn ⊢
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      right
      refine ⟨((k + 1) / 2,
        if ((k + 1) % 2 == 1) = true then CPolynomial.Raw.mulModWith
          CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.remainderOnly u acc c
        else acc,
        CPolynomial.Raw.mulModWith CPolynomial.Raw.MulContext.naive
          CPolynomial.Raw.ModContext.remainderOnly u c c), ⟨?_, ?_, ?_⟩, le_rfl, ?_⟩
      · dsimp only
        split_ifs
        · exact mulModWith_size_le hu huB
        · exact hacc
      · exact mulModWith_size_le hu huB
      · dsimp only; omega
      · dsimp only
        rw [powModBinaryAuxWith.c155.costEq_succ P hP]
        have := mulModWithC_cost P (by includes) hB u acc c huB hacc hc
        have := mulModWithC_cost P (by includes) hB u c c huB hc hc
        have := limbs_le_two (n := k + 1) (by omega)
        have := limbs_le_two (n := k) (by omega)
        have := limbs_le_two (n := (k + 1) % 2) (by omega)
        split_ifs <;> omega)
  exact key (n, acc, c) ⟨hacc, hc, hn⟩


theorem powModWith_size_le {u base : CPolynomial.Raw K} {B : ℕ} (hu : u.trim ≠ 0)
    (huB : u.size ≤ B) (e : ℕ) :
    (CPolynomial.Raw.powModWith CPolynomial.Raw.MulContext.naive
      CPolynomial.Raw.ModContext.remainderOnly u base e).size ≤ B := by
  rw [CPolynomial.Raw.powModWith]
  have : (u.trim == 0) = false := by simpa using hu
  simp only [this, Bool.false_eq_true, ↓reduceIte]
  have := powModBinaryAuxWith_size_lt u hu e _ base (remainderOnly_size_lt u 1 raw_one_trim hu)
  have := trim_size_le' u
  omega

theorem xModWith_size_le {u : CPolynomial.Raw K} {B : ℕ} (hu : u.trim ≠ 0) (huB : u.size ≤ B) :
    (CPolynomial.Raw.xModWith CPolynomial.Raw.ModContext.remainderOnly u).size ≤ B := by
  rw [CPolynomial.Raw.xModWith]
  have : (u.trim == 0) = false := by simpa using hu
  simp only [this, Bool.false_eq_true, ↓reduceIte]
  have := remainderOnly_size_lt u _ raw_X_trim hu
  have := trim_size_le' u
  omega

/-- **`base^e mod u`** (`powModWith`): at most
`400·B + 20800 + (2·mulModBound B + 50)·(log₂ e + 1)`. -/
theorem powModWithC_cost (hP : Includes P powModWith.c154.costDeps) {B : ℕ} (hB : B < 2 ^ 28)
    (hB1 : 1 ≤ B) (u base : CPolynomial.Raw K) (hu : u.trim ≠ 0) (huB : u.size ≤ B)
    (hbase : base.size ≤ B) (e : ℕ) (he : e < 2 ^ 65) :
    machineCost P powModWith.c154.costIdx [enc u, enc base, enc e] ≤
      400 * B + 20800 + (2 * mulModBound B + 50) * (Nat.log2 e + 1) := by
  rw [powModWith.c154.costEq P hP]
  have ht := trim_size_le' u
  have := trimLen_cost P (by includes) u u.size (by omega)
  have : (Array.extract u 0 (CompPolyLib.trimLen u u.size)).size ≤ u.size := by simp
  have := listBeqK_cost P (by includes) u.trim.toList (Array.toList 0)
  have := monicNormalizeRawC_cost P (by includes) u (by omega)
  have := modGoC_cost P (by includes) u.monicNormalize 1 (by omega)
    (by have := raw_monicNormalize_size_le u; omega) (Array.size 1) 1
    (by rw [size_one_raw]; omega) (by rw [size_one_raw])
  have hz : (u.trim == 0) = false := by simpa using hu
  simp only [hz, Bool.false_eq_true, ↓reduceIte, size_one_raw, Array.length_toList,
    size_zero_raw] at *
  have := powModBinaryAuxC_cost P (by includes) hB u hu huB e
    (CPolynomial.Raw.ModContext.remainderOnly.modByMonic 1 u.monicNormalize) base he
    (by have := remainderOnly_size_lt u 1 raw_one_trim hu; omega) hbase
  omega

/-- **`X mod u`** (`xModWith`): at most `400·B + 22000`. -/
theorem xModWithC_cost (hP : Includes P xModWith.c157.costDeps) {B : ℕ} (hB : B < 2 ^ 28)
    (u : CPolynomial.Raw K) (huB : u.size ≤ B) :
    machineCost P xModWith.c157.costIdx [enc u] ≤ 400 * B + 22000 := by
  rw [xModWith.c157.costEq P hP, X.c78.costEq P (by includes)]
  have ht := trim_size_le' u
  have := trimLen_cost P (by includes) u u.size (by omega)
  have : (Array.extract u 0 (CompPolyLib.trimLen u u.size)).size ≤ u.size := by simp
  have := listBeqK_cost P (by includes) u.trim.toList (Array.toList 0)
  have := monicNormalizeRawC_cost P (by includes) u (by omega)
  have := modGoC_cost P (by includes) u.monicNormalize 2 (by omega)
    (by have := raw_monicNormalize_size_le u; omega) (Array.size CPolynomial.Raw.X)
    CPolynomial.Raw.X (by rw [size_X_raw]; omega) (by rw [size_X_raw])
  simp only [size_X_raw, Array.length_toList, size_zero_raw] at *
  split_ifs <;> omega

/-- **`p − q`** (raw): at most `126·max(|p|, |q|) + 170`. -/
theorem subRawC_cost (hP : Includes P sub.c152.costDeps) (p q : CPolynomial.Raw K)
    (hp : p.size < 2 ^ 60) (hq : q.size < 2 ^ 60) :
    machineCost P sub.c152.costIdx [enc p, enc q] ≤ 126 * max p.size q.size + 170 := by
  rw [sub.c152.costEq P hP]
  have hf := fun a ↦ RunsApp.of_spec (us := []) (vs := [enc a])
    (sub.c152.lam0.costSpec P (by includes) a)
  have hm := listMap_le P Auto.List.map.c12.costIdx (.fn sub.c152.lam0.costIdx [])
    (Auto.List.map.c12.costEq_nil P (by includes) _ _ hf)
    (Auto.List.map.c12.costEq_cons P (by includes) _ _ hf) 1 q.toList
    (fun a _ ↦ by rw [appCost_fn, List.nil_append, sub.c152.lam0.costEq P (by includes)])
  have hn : q.neg.size = q.size := by simp [CPolynomial.Raw.neg]
  have := addK_cost P (by includes) p q.neg (by omega) (by omega)
  rw [hn] at this
  simp only [Array.length_toList, List.length_map] at hm ⊢
  omega

/-- **`X^q − X mod u`** (`xPowSubXModWith`, `q < 2^65`). -/
theorem xPowSubXModC_cost (hP : Includes P xPowSubXModWith.c151.costDeps) {B : ℕ}
    (hB : B < 2 ^ 28) (hB2 : 2 ≤ B) (u : CPolynomial.Raw K) (hu : u.trim ≠ 0) (huB : u.size ≤ B)
    (q : ℕ) (hq : q < 2 ^ 65) :
    machineCost P xPowSubXModWith.c151.costIdx [enc q, enc u] ≤
      950 * B + 43000 + (2 * mulModBound B + 50) * (Nat.log2 q + 1) := by
  rw [xPowSubXModWith.c151.costEq P hP, X.c78.costEq P (by includes)]
  have := powModWithC_cost P (by includes) hB (by omega) u CPolynomial.Raw.X hu huB
    (by rw [size_X_raw]; omega) q hq
  have := xModWithC_cost P (by includes) hB u huB
  have h1 := powModWith_size_le (base := CPolynomial.Raw.X) hu huB q
  have h2 := xModWith_size_le hu huB
  have := subRawC_cost P (by includes)
    (CPolynomial.Raw.powModWith CPolynomial.Raw.MulContext.naive
      CPolynomial.Raw.ModContext.remainderOnly u CPolynomial.Raw.X q)
    (CPolynomial.Raw.xModWith CPolynomial.Raw.ModContext.remainderOnly u) (by omega) (by omega)
  omega

/-- The bound of a remainder, operands of at most `B` coefficients. -/
@[expose] def rawModBound (B : ℕ) : ℕ := 400 * (B * B) + 2100 * B + 41000

theorem raw_C_smul_size_le (c : K) (p : CPolynomial.Raw K) :
    (CPolynomial.Raw.C c • p).size ≤ p.size := raw_C_mul_size_le c p

/-- **`p mod q`** (`rawModFast`: both scaled by `q`'s leading inverse, the long division): at
most `rawModBound B`. -/
theorem rawModFastC_cost (hP : Includes P rawModFast.c147.costDeps) {B : ℕ} (hB : B < 2 ^ 28)
    (p q : CPolynomial.Raw K) (hp : p.size ≤ B) (hq : q.size ≤ B) :
    machineCost P rawModFast.c147.costIdx [enc p, enc q] ≤ rawModBound B := by
  rw [rawModFast.c147.costEq P hP]
  have ht := trim_size_le' q
  have := trimLen_cost P (by includes) q q.size (by omega)
  have : (Array.extract q 0 (CompPolyLib.trimLen q q.size)).size ≤ q.size := by simp
  have := getLastDC_cost P (by includes) q.trim 0 (by omega)
  have := invK_cost P (by includes) q.leadingCoeff
  have hC : (CPolynomial.Raw.C q.leadingCoeff⁻¹).size = 1 := rfl
  have h1 := mulK_cost P (by includes) (CPolynomial.Raw.C q.leadingCoeff⁻¹) p (by omega)
    (by omega)
  have h2 := mulK_cost P (by includes) (CPolynomial.Raw.C q.leadingCoeff⁻¹) q (by omega)
    (by omega)
  have hs := raw_C_smul_size_le q.leadingCoeff⁻¹ p
  have := modGoC_cost P (by includes) (CPolynomial.Raw.C q.leadingCoeff⁻¹ * q) B (by omega)
    (by have := raw_C_mul_size_le q.leadingCoeff⁻¹ q; omega)
    (CPolynomial.Raw.C q.leadingCoeff⁻¹ • p).size (CPolynomial.Raw.C q.leadingCoeff⁻¹ • p)
    (by omega) (by omega)
  have h3 : (360 * B + 100) * (CPolynomial.Raw.C q.leadingCoeff⁻¹ • p).size ≤
      (360 * B + 100) * B := Nat.mul_le_mul_left _ (hs.trans hp)
  have e : (360 * B + 100) * B = 360 * (B * B) + 100 * B := by ring
  rw [hC] at h1 h2
  unfold rawModBound
  omega

/-- The bound of a monic gcd's step, operands of at most `B` coefficients. -/
@[expose] def gcdStepBound (B : ℕ) : ℕ := rawModBound B + 61 * B + 60

/-- **The Euclidean chain** (`rawGcdMonicWithFuelFast`, `fuel` steps): at most
`gcdStepBound B·fuel + 400·B + 20000`. -/
theorem rawGcdWithFuelC_cost (hP : Includes P rawGcdMonicWithFuelFast.c146.costDeps) {B : ℕ}
    (hB : B < 2 ^ 28) :
    ∀ (fuel : ℕ) (p q : CPolynomial.Raw K), fuel < 2 ^ 63 → p.size ≤ B → q.size ≤ B →
      machineCost P rawGcdMonicWithFuelFast.c146.costIdx [enc fuel, enc p, enc q] ≤
        gcdStepBound B * fuel + 400 * B + 20000 := by
  intro fuel
  induction fuel with
  | zero =>
    intro p q _ hp _
    rw [rawGcdMonicWithFuelFast.c146.costEq_zero P hP]
    have := monicNormalizeRawC_cost P (by includes) p (by omega)
    omega
  | succ n ih =>
    intro p q hn hp hq
    rw [rawGcdMonicWithFuelFast.c146.costEq_succ P hP]
    have ⟨hq', hr'⟩ := rawGcdStep_size_le hp hq
    have hpt := trim_size_le' p
    have := trimLen_cost P (by includes) p p.size (by omega)
    have : (Array.extract p 0 (CompPolyLib.trimLen p p.size)).size ≤ p.size := by simp
    have := trimLen_cost P (by includes) q q.size (by omega)
    have : (Array.extract q 0 (CompPolyLib.trimLen q q.size)).size ≤ q.size := by simp
    have := listBeqK_cost P (by includes) q.trim.toList (Array.toList 0)
    have := monicNormalizeRawC_cost P (by includes) p.trim (by omega)
    have := rawModFastC_cost P (by includes) hB p.trim q.trim (by omega) hq'
    have := ih q.trim (rawModFast p.trim q.trim) (by omega) hq' hr'
    simp only [Array.length_toList, size_zero_raw] at *
    cost_simp
    have e : gcdStepBound B * (n + 1) = gcdStepBound B * n + gcdStepBound B := by ring
    unfold gcdStepBound at *
    split_ifs <;> omega

/-- The bound of a monic gcd, operands of at most `B` coefficients. -/
@[expose] def gcdBound (B : ℕ) : ℕ := gcdStepBound B * (2 * B + 1) + 430 * B + 20100

/-- **The monic gcd** (raw, `|p| + |q| + 1` steps of fuel): at most `gcdBound B − 30·B − 70`. -/
theorem rawGcdMonicFastC_cost (hP : Includes P rawGcdMonicFast.c145.costDeps) {B : ℕ}
    (hB : B < 2 ^ 28) (p q : CPolynomial.Raw K) (hp : p.size ≤ B) (hq : q.size ≤ B) :
    machineCost P rawGcdMonicFast.c145.costIdx [enc p, enc q] ≤
      gcdStepBound B * (2 * B + 1) + 400 * B + 20020 := by
  rw [rawGcdMonicFast.c145.costEq P hP]
  have := rawGcdWithFuelC_cost P (by includes) hB (p.size + q.size + 1) p q (by omega) hp hq
  have h1 : gcdStepBound B * (p.size + q.size + 1) ≤ gcdStepBound B * (2 * B + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  cost_simp
  omega

/-- **The monic gcd** (`gcdMonicFast`): at most `gcdBound B`. -/
theorem gcdMonicFastC_cost (hP : Includes P gcdMonicFast.c176.costDeps) {B : ℕ}
    (hB : B < 2 ^ 28) (p q : CPolynomial K) (hp : p.val.size ≤ B) (hq : q.val.size ≤ B) :
    machineCost P gcdMonicFast.c176.costIdx [enc p, enc q] ≤ gcdBound B := by
  rw [gcdMonicFast.c176.costEq P hP]
  have := rawGcdMonicFastC_cost P (by includes) hB p.val q.val hp hq
  have hs := rawGcdMonicWithFuelFast_size_le (p.val.size + q.val.size + 1) hp hq
  have hs' : (rawGcdMonicFast p.val q.val).size ≤ B := hs
  have := ofArray_cost P (by includes) (rawGcdMonicFast p.val q.val) (by omega)
  unfold gcdBound
  omega


/-! ## The root product -/

theorem monic_trim_ne_zero (u : CPolynomial.Raw K) (hu : u.trim ≠ 0) :
    (CPolynomial.Raw.monicNormalize u).trim ≠ 0 := by
  have h1 := monicNormalize_getLastD u hu
  have hs := monicNormalize_size u hu
  have hpos : 0 < u.trim.size := by
    rcases Nat.eq_zero_or_pos u.trim.size with h | h
    · exact absurd (Array.eq_empty_of_size_eq_zero h) hu
    · exact h
  have ht : (CPolynomial.Raw.monicNormalize u).trim = CPolynomial.Raw.monicNormalize u :=
    CPolynomial.Raw.Trim.trim_eq_iff_size_eq_zero_or_getLastD_ne_zero.2
      (Or.inr (by rw [h1]; exact one_ne_zero))
  rw [ht]
  intro h
  rw [h, size_zero_raw] at hs
  omega

/-- The bound of the root product, `p` of at most `B` coefficients. -/
@[expose] def rootProductBound (B : ℕ) : ℕ :=
  gcdBound B + 1500 * B + 65000 + (2 * mulModBound B + 50) * 65

/-- **The root product** (`rootProductFast`: `gcd(p, X^(2^64) − X mod p)`): at most
`rootProductBound B`. -/
theorem rootProductFastC_cost (hP : Includes P rootProductFast.c142.costDeps) {B : ℕ}
    (hB : B < 2 ^ 28) (hB2 : 2 ≤ B) (p : CPolynomial K) (hp : p.val.size ≤ B) :
    machineCost P rootProductFast.c142.costIdx [enc p] ≤ rootProductBound B := by
  rw [rootProductFast.c142.costEq P hP]
  have ht := trim_size_le' p.val
  have := trimLen_cost P (by includes) p.val p.val.size (by omega)
  have : (Array.extract p.val 0 (CompPolyLib.trimLen p.val p.val.size)).size ≤ p.val.size := by
    simp
  have := listBeqK_cost P (by includes) p.val.trim.toList (Array.toList 0)
  have hq : LeanVM.Extraction.traceCtx.q = 2 ^ 64 := rfl
  have h64 : (1 <<< 64 : ℕ) = 2 ^ 64 := rfl
  rw [hq, h64]
  have := limbs_le_two (n := 2 ^ 64) (by norm_num)
  simp only [Array.length_toList, size_zero_raw] at *
  generalize hR : (if (p.val.trim == 0) = true then (0 : CPolynomial.Raw K) else
    rawGcdMonicFast p.val.monicNormalize (CPolynomial.Raw.xPowSubXModWith
      CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.remainderOnly (2 ^ 64)
      p.val.monicNormalize)) = R
  have hmn := raw_monicNormalize_size_le p.val
  have hRs : R.size ≤ B := by
    rw [← hR]
    split
    · rw [size_zero_raw]; omega
    · rename_i h
      have hu : p.val.trim ≠ 0 := by simpa using h
      exact rawGcdMonicWithFuelFast_size_le _ (by omega)
        ((xPowSubXModWith_size_lt _ (monic_trim_ne_zero _ hu) _).le.trans
          ((trim_size_le' _).trans (by omega)))
  have := ofArray_cost P (by includes) R (by omega)
  unfold rootProductBound gcdBound
  split
  · omega
  · rename_i h
    have hu : p.val.trim ≠ 0 := by simpa using h
    have hmu := monic_trim_ne_zero _ hu
    have := monicNormalizeRawC_cost P (by includes) p.val (by omega)
    have hx := xPowSubXModC_cost P (by includes) hB hB2 p.val.monicNormalize hmu (by omega)
      (2 ^ 64) (by norm_num)
    have hl : Nat.log2 (2 ^ 64) = 64 := Nat.log2_two_pow
    rw [hl] at hx
    have hxs := (xPowSubXModWith_size_lt _ hmu (2 ^ 64)).le.trans
      ((trim_size_le' _).trans hmn)
    have := rawGcdMonicFastC_cost P (by includes) hB p.val.monicNormalize
      (CPolynomial.Raw.xPowSubXModWith CPolynomial.Raw.MulContext.naive
        CPolynomial.Raw.ModContext.remainderOnly (2 ^ 64) p.val.monicNormalize) (by omega)
      (by omega)
    omega

/-! ## The Frobenius powers and the trace polynomial -/

theorem length_squaringsFrom (u : CPolynomial.Raw K) :
    ∀ (n : ℕ) (c : CPolynomial.Raw K), (squaringsFrom u n c).length = n
  | 0, _ => rfl
  | n + 1, c => by rw [squaringsFrom, List.length_cons, length_squaringsFrom u n]

/-- **The squarings modulo `u`** (`squaringsFrom`, `n` of them): at most
`(mulModBound B + 30)·n + 6`. -/
theorem squaringsFromC_cost (hP : Includes P squaringsFrom.c171.costDeps) {B : ℕ}
    (hB : B < 2 ^ 28) (u : CPolynomial K) (hu : u ≠ 0) (huB : u.val.size ≤ B) :
    ∀ (n : ℕ) (c : CPolynomial.Raw K), n < 2 ^ 63 → c.size ≤ B →
      machineCost P squaringsFrom.c171.costIdx [enc u.val, enc n, enc c] ≤
        (mulModBound B + 30) * n + 6 := by
  intro n
  induction n with
  | zero => intro c _ _; rw [squaringsFrom.c171.costEq_zero P hP]; omega
  | succ n ih =>
    intro c hn hc
    rw [squaringsFrom.c171.costEq_succ P hP]
    have := sqModC_cost P (by includes) hB u.val c huB hc
    have := ih (sqMod u.val c) (by omega) (by have := sqMod_size_lt hu c; omega)
    cost_simp
    have e : (mulModBound B + 30) * (n + 1) = (mulModBound B + 30) * n + mulModBound B + 30 := by
      ring
    omega

/-- The bound of `k` Frobenius powers modulo `u`, `u` of at most `B` coefficients. -/
@[expose] def frobBound (B k : ℕ) : ℕ := (2 * mulModBound B + 23 * B + 70) * k + 450 * B + 21000

/-- **The Frobenius powers** (`frobeniusPowersFast u k`: `k` squarings, each then reduced
`mod u`): at most `frobBound B k`. -/
theorem frobeniusPowersFastC_cost (hP : Includes P frobeniusPowersFast.c169.costDeps) {B : ℕ}
    (hB : B < 2 ^ 28) (hB2 : 2 ≤ B) (u : CPolynomial K) (hu : u ≠ 0) (huB : u.val.size ≤ B)
    (k : ℕ) (hk : k < 2 ^ 63) :
    machineCost P frobeniusPowersFast.c169.costIdx [enc u, enc k] ≤ frobBound B k := by
  rw [frobeniusPowersFast.c169.costEq P hP, X.c78.costEq P (by includes)]
  have hu' := cpoly_trim_ne_zero hu
  have hz : (u.val.trim == 0) = false := by simpa using hu'
  simp only [hz, Bool.false_eq_true, ↓reduceIte]
  have ht := trim_size_le' u.val
  have := trimLen_cost P (by includes) u.val u.val.size (by omega)
  have : (Array.extract u.val 0 (CompPolyLib.trimLen u.val u.val.size)).size ≤ u.val.size := by
    simp
  have := listBeqK_cost P (by includes) u.val.trim.toList (Array.toList 0)
  have := monicNormalizeRawC_cost P (by includes) u.val (by omega)
  have := modGoC_cost P (by includes) u.val.monicNormalize 1 (by omega)
    (by have := raw_monicNormalize_size_le u.val; omega) (Array.size 1) 1
    (by rw [size_one_raw]; omega) (by rw [size_one_raw])
  have := squaringsFromC_cost P (by includes) hB u hu huB k CPolynomial.Raw.X hk
    (by rw [size_X_raw]; omega)
  have hone := remainderOnly_size_lt u.val 1 raw_one_trim hu'
  have hf := fun c ↦ RunsApp.of_spec
    (us := [enc u, enc (CPolynomial.Raw.ModContext.remainderOnly.modByMonic 1
      u.val.monicNormalize)]) (vs := [enc c])
    (frobeniusPowersFast.c169.lam0.costSpec P (by includes) u
      (CPolynomial.Raw.ModContext.remainderOnly.modByMonic 1 u.val.monicNormalize) c)
  have hm := listMap_le P Auto.List.map.c12.costIdx
    (.fn frobeniusPowersFast.c169.lam0.costIdx [enc u, enc (CPolynomial.Raw.ModContext.remainderOnly.modByMonic 1
      u.val.monicNormalize)])
    (Auto.List.map.c12.costEq_nil P (by includes) _ _ hf)
    (Auto.List.map.c12.costEq_cons P (by includes) _ _ hf) (mulModBound B + 23 * B + 21)
    (squaringsFrom u.val k CPolynomial.Raw.X)
    (fun c hc ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [frobeniusPowersFast.c169.lam0.costEq P (by includes)]
      have hcs : c.size ≤ B := by
        rcases squaringsFrom_size_lt hu k CPolynomial.Raw.X c hc with rfl | h
        · rw [size_X_raw]; omega
        · omega
      have := mulModWithC_cost P (by includes) hB u.val
        (CPolynomial.Raw.ModContext.remainderOnly.modByMonic 1 u.val.monicNormalize) c huB
        (by omega) hcs
      have hms := mulModWith_size_le (a := CPolynomial.Raw.ModContext.remainderOnly.modByMonic 1
        u.val.monicNormalize) (b := c) hu' huB
      have := ofArray_cost P (by includes) (CPolynomial.Raw.mulModWith
        CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.remainderOnly u.val
        (CPolynomial.Raw.ModContext.remainderOnly.modByMonic 1 u.val.monicNormalize) c)
        (by omega)
      omega)
  simp only [length_squaringsFrom, List.length_map, size_one_raw, Array.length_toList,
    size_zero_raw] at *
  have e : (mulModBound B + 23 * B + 21 + 11) * k + (mulModBound B + 30) * k + k ≤
      (2 * mulModBound B + 23 * B + 70) * k := by
    have : (mulModBound B + 23 * B + 21 + 11) * k + (mulModBound B + 30) * k + k =
        (2 * mulModBound B + 23 * B + 63) * k := by ring
    rw [this]; exact Nat.mul_le_mul_right _ (by omega)
  unfold frobBound
  omega

/-- The bound of the trace polynomial over `64` powers of at most `B` coefficients. -/
@[expose] def traceBound (B : ℕ) : ℕ := (1040 * B + 1200) * 64 + 1200

/-- **The trace polynomial** (`traceCoordFast`: `Σ_{i<64} β^(2^i)·powers[i]`): at most
`traceBound B`, its value of at most `B + 1` coefficients. -/
theorem traceCoordFastC_cost (hP : Includes P traceCoordFast.c173.costDeps) {B : ℕ}
    (hB : B < 2 ^ 28) (beta : K) (powers : Array (CPolynomial K))
    (hpw : ∀ q ∈ powers, q.val.size ≤ B) :
    machineCost P traceCoordFast.c173.costIdx [enc beta, enc powers] ≤ traceBound B := by
  rw [traceCoordFast.c173.costEq P hP]
  have := rangeLoop_cost P (by includes) 64 [] (by norm_num)
  have hg : ∀ i, (powers.getD i 0).val.size ≤ B := by
    intro i
    rw [Array.getD_eq_getD_getElem?]
    cases h : powers[i]? with
    | none => simp [size_zero_val]
    | some q => exact hpw q (Array.mem_of_getElem? h)
  have hf := listFoldl_le P (by includes) _ (.fn traceCoordFast.c173.lam0.costIdx [enc powers])
    (fun st i ↦ RunsApp.of_spec (us := [enc powers]) (vs := [enc st, enc i])
      (traceCoordFast.c173.lam0.costSpec P (by includes) powers st i))
    (1040 * B + 1150) (fun st : CPolynomial K × K ↦ st.1.val.size ≤ B + 1) (List.range 64)
    (0, beta) (by show (0 : CPolynomial K).val.size ≤ _; simp [size_zero_val])
    (fun st hst i _ ↦ by
      have hC : (CPolynomial.C st.2).val.size ≤ 1 :=
        (raw_trim_size_le _).trans (by simp [CPolynomial.Raw.C])
      have hm := cpoly_mul_size_le (CPolynomial.C st.2) (powers.getD i 0)
      refine ⟨?_, ?_⟩
      · have := cpoly_add_size_le st.1 (CPolynomial.C st.2 * powers.getD i 0)
        have := hg i
        dsimp only
        omega
      · simp only [appCost_fn, List.cons_append, List.nil_append]
        rw [traceCoordFast.c173.lam0.costEq P (by includes)]
        have := cK_cost P (by includes) st.2
        have := hg i
        have h1 := mulK_cost P (by includes) (CPolynomial.C st.2).val (powers.getD i 0).val
          (by omega) (by omega)
        have h2 : (powers.getD i 0).val.size * (CPolynomial.C st.2).val.size ≤ B :=
          (Nat.mul_le_mul (hg i) hC).trans (by omega)
        have h3 : (CPolynomial.C st.2).val.size * (CPolynomial.C st.2).val.size ≤ 1 :=
          Nat.mul_le_mul hC hC
        have := addK_cost P (by includes) st.1.val (CPolynomial.C st.2 * powers.getD i 0).val
          (by omega) (by omega)
        omega)
  simp only [List.length_range] at hf
  unfold traceBound
  omega

end

end LeanVM.Cost.Bounds.Decoder
