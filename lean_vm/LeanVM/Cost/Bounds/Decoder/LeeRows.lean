module

public import LeanVM.Cost.Bounds.Decoder.Interp
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Raw.Ops
import all CompPoly.Univariate.Basic
import all CompPoly.Data.Array.Lemmas
import all CompPoly.Bivariate.GuruswamiSudan.Polynomial
import all CompPoly.Bivariate.FactorMonic
import all CompPoly.Bivariate.CoeffRows

/-!
# Bound: Lee–O'Sullivan's basis rows, compiled

The price of `leeRowsFast R G params` (`Fast/LeeRows.lean`, compiled in
`Cost/Extractor/Interp.lean`) when `R` and `G` have degree at most `N`, `m` the multiplicity and
`w = ℓ + 1` the width (`leeRowsFastC_cost`, the closed form `leeRowsBound m w N`):

* the products over `K[X]` with entries of different sizes (`mulB_cost_ab`: entries of the left
  factor of at most `a` coefficients, of the right one at most `b`, `a + b ≤ s`; the bound
  `mulBBound rp rq a s`, monotone in every argument, `mulBBound_mono`). The schoolbook product
  multiplies each entry of the left factor by each of the right one, so its price is
  `≈ 2760·|p|·|q|·(a + 1)·(s + 1)` (the factor 3 of `Raw.mul`, `Bounds/Decoder/Poly.lean`'s note,
  included);
* `Y − R` (`linearYDivisorC_cost`), `G` as a constant in `Y` (`ofYConstantC_cost`);
* the powers `(Y − R)^t`, `G^t`, `t ≤ m` (`powersFromC_cost`: one product per power, the short
  factor first), their sizes from `Bounds/Sizes/Interp.lean` (`linearYDivisor_pow_sizes`,
  `ofYConstant_pow_sizes`: `t + 1` rows, entries of at most `t·N + 1` coefficients);
* a row (`leeRowsLamC_cost`): for `i ≤ m` the product `G^(m−i)·(Y − R)^i` (entries of at most
  `(m − i)·N + 1` and `i·N + 1` coefficients, so `a + b = m·N + 2` whatever `i`), for `i > m` the
  shift `Y^(i−m)·(Y − R)^m` (`shiftYC_cost`), then its coefficient row (`toCoeffRowC_cost`).

At the worst shape `(28, 4)` (`m = 415`, `w = 1662`, `N = 2^26`) the rows cost at most
`leeRowsBound 415 1662 (2^26) ≈ 2^98.2` (`leeRowsBound_28_4`), the `m + 1` row products
`G^(m−i)·(Y − R)^i` dominating (`≈ 2760·m²·(m·N)²`).
-/

namespace LeanVM.Cost.Bounds.Decoder

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Bounds.Samples LeanVM.Cost.Library
open LeanVM.Cost.Extractor LeanVM.Parameters CompPoly LeanVM.Extraction.Fast

/-! The functions compiled on demand, by their short names. -/
open LeanVM.Cost.Auto.CompPoly.CPolynomial.Raw

public section

variable (P : Program)

/-! ## Products over `K[X]`, entries of different sizes -/

/-- A product over `K` of `≤ a` by `≤ b` coefficients: at most `906·(a + 1)·(a + b + 1)`. -/
theorem mulK_cost_ab (hP : Includes P mul.c55.costDeps) (p q : CPolynomial.Raw K) (a b : ℕ)
    (ha : a < 2 ^ 60) (hb : b < 2 ^ 60) (hp : p.size ≤ a) (hq : q.size ≤ b) :
    machineCost P mul.c55.costIdx [enc p, enc q] ≤ 906 * ((a + 1) * (a + b + 1)) := by
  have := mulK_cost P hP p q (by omega) (by omega)
  have h1 : q.size * p.size ≤ b * a := Nat.mul_le_mul hq hp
  have h2 : p.size * p.size ≤ a * a := Nat.mul_le_mul hp hp
  have e : (a + 1) * (a + b + 1) = a * a + b * a + 2 * a + b + 1 := by ring
  omega

theorem InnerLe.smul_ab {q : CPolynomial.Raw (CPolynomial K)} {b : ℕ} (h : InnerLe q b)
    (r : CPolynomial K) {a : ℕ} (hr : r.val.size ≤ a) :
    InnerLe (CPolynomial.Raw.smul r q) (a + b) := by
  intro x hx
  simp only [CPolynomial.Raw.smul, Array.mem_map] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  have := cpoly_mul_size_le r c
  have := h c hc
  omega

/-- `smul r q` over `K[X]`, `r` of at most `a` coefficients, `q`'s entries of at most `b`: at most
`930·(a + 1)·(a + b + 1)·|q| + 10`. -/
theorem smulB_cost_ab (hP : Includes P smul.c53.costDeps) (r : CPolynomial K)
    (q : CPolynomial.Raw (CPolynomial K)) (a b : ℕ) (ha : a < 2 ^ 60) (hb : b < 2 ^ 60)
    (hr : r.val.size ≤ a) (hq : InnerLe q b) :
    machineCost P smul.c53.costIdx [enc r, enc q] ≤
      930 * (((a + 1) * (a + b + 1)) * q.size) + 10 := by
  rw [smul.c53.costEq P hP]
  have hf := fun c ↦ RunsApp.of_spec (us := [enc r]) (vs := [enc c])
    (smul.c53.lam0.costSpec P (by includes) r c)
  have hm := listMap_le P Auto.List.map.c12.costIdx (.fn smul.c53.lam0.costIdx [enc r])
    (Auto.List.map.c12.costEq_nil P (by includes) _ _ hf)
    (Auto.List.map.c12.costEq_cons P (by includes) _ _ hf) (906 * ((a + 1) * (a + b + 1)) + 3)
    q.toList
    (fun c hc ↦ by
      rw [appCost_fn, List.singleton_append, smul.c53.lam0.costEq P (by includes)]
      have := mulK_cost_ab P (by includes) r.val c.val a b ha hb hr (hq c (by simpa using hc))
      omega)
  simp only [Array.length_toList, List.length_map] at hm ⊢
  have h1 : 1 ≤ (a + 1) * (a + b + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
  have e : (906 * ((a + 1) * (a + b + 1)) + 3 + 11) * q.size =
      906 * (((a + 1) * (a + b + 1)) * q.size) + 14 * q.size := by ring
  have : q.size ≤ ((a + 1) * (a + b + 1)) * q.size := Nat.le_mul_of_pos_left _ (by omega)
  omega

theorem InnerLe.mulRaw_ab {p q : CPolynomial.Raw (CPolynomial K)} {a b : ℕ} (hp : InnerLe p a)
    (hq : InnerLe q b) : InnerLe (CPolynomial.Raw.mulRaw p q) (a + b) := by
  unfold CPolynomial.Raw.mulRaw
  rw [← Array.foldl_toList]
  suffices ∀ (l : List (CPolynomial K × ℕ)) (acc : CPolynomial.Raw (CPolynomial K)),
      InnerLe acc (a + b) → (∀ x ∈ l, x.1 ∈ p) →
      InnerLe (l.foldl (fun acc x ↦ acc.addRaw ((CPolynomial.Raw.smul x.1 q).mulPowX x.2)) acc)
        (a + b) by
    apply this _ _ (fun x hx ↦ by simp at hx)
    intro x hx
    rw [Array.toList_zipIdx] at hx
    have := List.mem_zipIdx hx
    simp only [Nat.sub_zero] at this
    rw [this.2.2]; simp
  intro l
  induction l with
  | nil => intro acc h _; exact h
  | cons x l ih =>
    intro acc h hl
    exact ih _ (h.addRaw ((hq.smul_ab x.1 (hp _ (hl x (by simp)))).mulPowX x.2))
      (fun y hy ↦ hl y (by simp [hy]))

/-- The schoolbook product over `K[X]`, `≤ rp` rows of entries of `≤ a` coefficients by `≤ rq`
rows of entries of `≤ b`. -/
theorem mulRawB_cost_ab (hP : Includes P mulRaw.c44.costDeps)
    (p q : CPolynomial.Raw (CPolynomial K)) (a b rp rq : ℕ) (ha : a < 2 ^ 57) (hb : b < 2 ^ 57)
    (hp : InnerLe p a) (hq : InnerLe q b) (hps : p.size ≤ rp) (hqs : q.size ≤ rq)
    (hr : rp + rq < 2 ^ 57) :
    machineCost P mulRaw.c44.costIdx [enc p, enc q] ≤
      (930 * (((a + 1) * (a + b + 1)) * rq) + 110 * ((a + b) * (rp + rq)) + 200 * (rp + rq) +
        112) * rp + 20 := by
  rw [mulRaw.c44.costEq P hP]
  have hz := zipIdxC_cost P (by includes) p.toList 0 (by simp; omega)
  have hf := listFoldl_le P (by includes) _ (.fn mulRaw.c44.lam0.costIdx [enc q])
    (fun acc x ↦ RunsApp.of_spec (us := [enc q]) (vs := [enc acc, enc x])
      (mulRaw.c44.lam0.costSpec P (by includes) q acc x))
    (930 * (((a + 1) * (a + b + 1)) * rq) + 110 * ((a + b) * (rp + rq)) + 200 * (rp + rq) + 80)
    (fun acc ↦ acc.size ≤ p.size + q.size ∧ InnerLe acc (a + b))
    (Array.zipIdx p).toList (CPolynomial.Raw.mk #[]) ⟨by simp, fun x hx ↦ by simp at hx⟩
    (fun acc hacc x hx ↦ by
      have hi := mem_zipIdx_lt hx
      have hxp : x.1 ∈ p := by
        rw [Array.toList_zipIdx] at hx
        have := List.mem_zipIdx hx
        simp only [Nat.sub_zero] at this
        rw [this.2.2]; simp
      obtain ⟨c, i⟩ := x
      dsimp only at hi hxp ⊢
      have hsh : InnerLe (CPolynomial.Raw.mulPowX i (CPolynomial.Raw.smul c q)) (a + b) :=
        (hq.smul_ab c (hp c hxp)).mulPowX i
      refine ⟨⟨?_, hacc.2.addRaw hsh⟩, ?_⟩
      · rw [size_addRaw, size_mulPowX, size_smul]; omega
      · rw [appCost_fn, List.singleton_append, mulRaw.c44.lam0.costEq P (by includes)]
        have := smulB_cost_ab P (by includes) c q a b (by omega) (by omega) (hp c hxp) hq
        have := mulPowXB_cost P (by includes) i (CPolynomial.Raw.smul c q)
        have := addRawB_cost P (by includes) acc
          (CPolynomial.Raw.mulPowX i (CPolynomial.Raw.smul c q)) (a + b) (by omega) hacc.2 hsh
          (by omega) (by rw [size_mulPowX, size_smul]; omega)
        rw [size_mulPowX, size_smul] at *
        have hm : max acc.size (i + q.size) ≤ rp + rq := by omega
        have : (a + b) * max acc.size (i + q.size) ≤ (a + b) * (rp + rq) :=
          Nat.mul_le_mul_left _ hm
        have : ((a + 1) * (a + b + 1)) * q.size ≤ ((a + 1) * (a + b + 1)) * rq :=
          Nat.mul_le_mul_left _ hqs
        dsimp only
        omega)
  have hle := Nat.mul_le_mul_left
    (930 * (((a + 1) * (a + b + 1)) * rq) + 110 * ((a + b) * (rp + rq)) + 200 * (rp + rq) + 80 + 9)
    hps
  have e : (930 * (((a + 1) * (a + b + 1)) * rq) + 110 * ((a + b) * (rp + rq)) + 200 * (rp + rq) +
      112) * rp = (930 * (((a + 1) * (a + b + 1)) * rq) + 110 * ((a + b) * (rp + rq)) +
        200 * (rp + rq) + 80 + 9) * rp + 23 * rp := by ring
  simp only [Array.length_toList, Array.size_zipIdx, List.length_zipIdx] at hz hf hle ⊢
  omega

/-- The bound of a product over `K[X]`: `≤ rp` rows of entries of `≤ a` coefficients by `≤ rq`
rows, the two factors' entry sizes summing to at most `s`. -/
@[expose] def mulBBound (rp rq a s : ℕ) : ℕ :=
  3 * ((930 * (((a + 1) * (s + 1)) * rq) + 110 * (s * (rp + rq)) + 200 * (rp + rq) + 112) * rp) +
    (3 * s + 41) * (rp + rq) + 100

theorem mulBBound_mono {rp rq a s rp' rq' a' s' : ℕ} (h1 : rp ≤ rp') (h2 : rq ≤ rq') (h3 : a ≤ a')
    (h4 : s ≤ s') : mulBBound rp rq a s ≤ mulBBound rp' rq' a' s' := by
  unfold mulBBound
  gcongr

/-- **The product over `K[X]`** (`mul`: `mulRaw` thrice, the trim), entries of different sizes:
at most `mulBBound rp rq a s`. -/
theorem mulB_cost_ab (hP : Includes P mul.c43.costDeps) (p q : CPolynomial.Raw (CPolynomial K))
    (a b s rp rq : ℕ) (hs : a + b ≤ s) (hs' : s < 2 ^ 57) (hp : InnerLe p a) (hq : InnerLe q b)
    (hps : p.size ≤ rp) (hqs : q.size ≤ rq) (hr : rp + rq < 2 ^ 57) :
    machineCost P mul.c43.costIdx [enc p, enc q] ≤ mulBBound rp rq a s := by
  rw [mul.c43.costEq P hP]
  have h1 := mulRawB_cost_ab P (by includes) p q a b rp rq (by omega) (by omega) hp hq hps hqs hr
  have hsz := size_mulRaw_le p q
  have := trimLenB_cost P (by includes) (p.mulRaw q) (a + b) (hp.mulRaw_ab hq) (p.mulRaw q).size
    (by omega)
  have h2 : (Array.extract (p.mulRaw q) 0
      (CompPolyLib.trimLen (p.mulRaw q) (p.mulRaw q).size)).size ≤ (p.mulRaw q).size := by simp
  have h3 : (3 * (a + b) + 40) * (p.mulRaw q).size ≤ (3 * s + 40) * (rp + rq) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h4 : (930 * (((a + 1) * (a + b + 1)) * rq) + 110 * ((a + b) * (rp + rq)) + 200 * (rp + rq) +
      112) * rp ≤ (930 * (((a + 1) * (s + 1)) * rq) + 110 * (s * (rp + rq)) + 200 * (rp + rq) +
      112) * rp := by gcongr
  unfold mulBBound
  have e : (3 * s + 41) * (rp + rq) = (3 * s + 40) * (rp + rq) + (rp + rq) := by ring
  omega

/-! ## Sizes -/

theorem innerLe_of_coeff {p : CBivariate K} {A : ℕ} (h : ∀ j, (p.val.coeff j).val.size ≤ A) :
    InnerLe p.val A := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem hx
  have := h j
  rwa [CPolynomial.Raw.coeff, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj,
    Option.getD_some] at this

/-- `(Y − R)^t`: entries of at most `t·N + 1` coefficients. -/
theorem innerLe_linearYDivisor_pow (R : CPolynomial K) {N : ℕ} (hR : R.natDegree ≤ N) (t : ℕ) :
    InnerLe (CBivariate.linearYDivisor R ^ t).val (t * N + 1) :=
  innerLe_of_coeff fun j ↦ by
    have := (linearYDivisor_pow_sizes R t).2 j
    have := Nat.mul_le_mul_left t hR
    omega

/-- `G^t`, `G` a constant in `Y`: entries of at most `t·N + 1` coefficients. -/
theorem innerLe_ofYConstant_pow (G : CPolynomial K) {N : ℕ} (hG : G.natDegree ≤ N) (t : ℕ) :
    InnerLe (CBivariate.ofYConstant G ^ t).val (t * N + 1) :=
  innerLe_of_coeff fun j ↦ by
    have := (ofYConstant_pow_sizes G t).2 j
    have := Nat.mul_le_mul_left t hG
    omega

theorem InnerLe.trim {p : CPolynomial.Raw (CPolynomial K)} {A : ℕ} (h : InnerLe p A) :
    InnerLe p.trim A := by
  intro x hx
  rw [CompPolyLib.trim_eq] at hx
  obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem hx
  rw [Array.getElem_extract]
  exact h _ (Array.getElem_mem _)

/-! ## The powers -/

set_option linter.auxLemma false in
/-- The product of `CBivariate K` (its `Semiring` instance's multiplication, compiled under the
instance's auxiliary name): `Raw.mul` on the values, `+ 3`. -/
theorem mulBivC_eq (hP : Includes P
      Auto.CompPoly.CBivariate.instSemiring._aux_3.c42.costDeps) (x y : CBivariate K) :
    machineCost P Auto.CompPoly.CBivariate.instSemiring._aux_3.c42.costIdx [enc x, enc y] =
      machineCost P mul.c43.costIdx [enc x.val, enc y.val] + 3 :=
  Auto.CompPoly.CBivariate.instSemiring._aux_3.c42.costEq P hP x y

set_option linter.auxLemma false in
/-- The `1` of `CBivariate K` (compiled under its instance's auxiliary name): `13`. -/
theorem oneBivC_eq (hP : Includes P Auto.CompPoly.CBivariate.instSemiring._aux_1.c64.costDeps) :
    machineCost P Auto.CompPoly.CBivariate.instSemiring._aux_1.c64.costIdx [] = 13 :=
  Auto.CompPoly.CBivariate.instSemiring._aux_1.c64.costEq P hP

set_option linter.auxLemma false in
/-- The `0` of `CBivariate K`'s coefficients (an instance's auxiliary): `2`. -/
theorem zeroBivC_eq
    (hP : Includes P Auto.CompPoly.CBivariate.instAddCommMonoid._aux_1.c101.costDeps) :
    machineCost P Auto.CompPoly.CBivariate.instAddCommMonoid._aux_1.c101.costIdx [] = 2 :=
  Auto.CompPoly.CBivariate.instAddCommMonoid._aux_1.c101.costEq P hP

/-- **The powers** (`powersFrom a 1 n`, from `a^j`): `n` products `a · a^t`, `t < N`, each at
most `C`: at most `(C + 20)·n + 6`. -/
theorem powersFromC_cost (hP : Includes P Auto.LeanVM.Extraction.Fast.powersFrom.c96.costDeps)
    (a : CBivariate K) (C N : ℕ)
    (hC : ∀ t, t < N → machineCost P mul.c43.costIdx [enc a.val, enc (a ^ t).val] + 3 ≤ C) :
    ∀ n j, j + n ≤ N → n < 2 ^ 63 →
      machineCost P Auto.LeanVM.Extraction.Fast.powersFrom.c96.costIdx
        [enc a, enc (a ^ j), enc n] ≤ (C + 20) * n + 6 := by
  intro n
  induction n with
  | zero => intro j _ _; rw [Auto.LeanVM.Extraction.Fast.powersFrom.c96.costEq_zero P hP]; omega
  | succ n ih =>
    intro j hj hn
    rw [Auto.LeanVM.Extraction.Fast.powersFrom.c96.costEq_succ P hP, ← pow_succ',
      mulBivC_eq P (by includes)]
    have := ih (j + 1) (by omega) (by omega)
    have := hC j (by omega)
    cost_simp
    have e : (C + 20) * (n + 1) = (C + 20) * n + C + 20 := by ring
    omega

theorem length_powersFrom {α : Type} [Mul α] (a : α) : ∀ (x : α) (n : ℕ),
    (powersFrom a x n).length = n
  | _, 0 => rfl
  | x, n + 1 => by rw [powersFrom, List.length_cons, length_powersFrom a (a * x) n]

theorem powersFrom_toArray_getD (a : CBivariate K) {n i : ℕ} (hi : i < n) :
    (powersFrom a 1 n).toArray.getD i 0 = a ^ i := by
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD]
  rw [getD_powersFrom _ _ _ hi, mul_one]


/-- `powersFromC_cost` from `1 = a^0`. -/
theorem powersFromC_cost_one (hP : Includes P Auto.LeanVM.Extraction.Fast.powersFrom.c96.costDeps)
    (a : CBivariate K) (C n : ℕ) (hn : n < 2 ^ 63)
    (hC : ∀ t, t < n → machineCost P mul.c43.costIdx [enc a.val, enc (a ^ t).val] + 3 ≤ C) :
    machineCost P Auto.LeanVM.Extraction.Fast.powersFrom.c96.costIdx
        [enc a, enc (1 : CBivariate K), enc n] ≤ (C + 20) * n + 6 := by
  have := powersFromC_cost P hP a C n hC n 0 (by omega) hn
  rw [pow_zero] at this
  exact this

/-! ## `Y − R`, `G`, the shift, the coefficient row -/

theorem innerLe_rawC (f : CPolynomial K) : InnerLe (CPolynomial.Raw.C f) f.val.size := by
  intro x hx
  simp only [CPolynomial.Raw.C, Array.mem_singleton] at hx
  rw [hx]

theorem size_C_le (f : CPolynomial K) : (CPolynomial.C f).val.size ≤ 1 :=
  (raw_trim_size_le _).trans (by simp [CPolynomial.Raw.C])

theorem innerLe_C (f : CPolynomial K) : InnerLe (CPolynomial.C f).val f.val.size :=
  (innerLe_rawC f).trim

/-- `C f` over `K[X]` (one row `f`, trimmed): at most `3·|f| + 72`. -/
theorem cB_cost (hP : Includes P Auto.CompPoly.CPolynomial.C.c71.costDeps) (f : CPolynomial K) :
    machineCost P Auto.CompPoly.CPolynomial.C.c71.costIdx [enc f] ≤ 3 * f.val.size + 72 := by
  rw [Auto.CompPoly.CPolynomial.C.c71.costEq P hP]
  have hs : (CPolynomial.Raw.C f).size = 1 := rfl
  have := trimLenB_cost P (by includes) (CPolynomial.Raw.C f) f.val.size (innerLe_rawC f)
    (CPolynomial.Raw.C f).size (by rw [hs]; norm_num)
  have h1 : (Array.extract (CPolynomial.Raw.C f) 0 (CompPolyLib.trimLen (CPolynomial.Raw.C f)
      (CPolynomial.Raw.C f).size)).size ≤ 1 := by simp [CPolynomial.Raw.C]
  have e : (3 * f.val.size + 40) * (CPolynomial.Raw.C f).size = 3 * f.val.size + 40 := by
    rw [hs]; ring
  omega

theorem neg_val_size {R : Type} [Ring R] [BEq R] [LawfulBEq R] (y : CPolynomial R) :
    (-y).val.size = y.val.size := by
  show (Array.map (fun a ↦ -a) y.val).size = y.val.size
  simp

theorem InnerLe.neg {c : CBivariate K} {A : ℕ} (h : InnerLe c.val A) : InnerLe (-c).val A := by
  intro x hx
  change x ∈ Array.map (fun a ↦ -a) c.val at hx
  obtain ⟨y, hy, rfl⟩ := Array.mem_map.1 hx
  rw [neg_val_size]
  exact h y hy

theorem size_one_K : (1 : CPolynomial K).val.size ≤ 1 := by
  have := val_size_le_natDegree_add_one (1 : CPolynomial K)
  rw [CPolynomial.natDegree_one] at this
  exact this

theorem innerLe_X : InnerLe (CPolynomial.X : CBivariate K).val 1 := by
  intro x hx
  change x ∈ (#[0, 1] : Array (CPolynomial K)) at hx
  simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact Nat.zero_le _
  · exact size_one_K

/-- **`Y − f`** (`linearYDivisor`): at most `700·|f| + 2300`. -/
theorem linearYDivisorC_cost
    (hP : Includes P Auto.CompPoly.CBivariate.linearYDivisor.c65.costDeps) (f : CPolynomial K)
    (hf : f.val.size < 2 ^ 56) :
    machineCost P Auto.CompPoly.CBivariate.linearYDivisor.c65.costIdx [enc f] ≤
      700 * f.val.size + 2300 := by
  rw [Auto.CompPoly.CBivariate.linearYDivisor.c65.costEq P hP,
    Auto.CompPoly.CPolynomial.X.c67.costEq P (by includes),
    Auto.CompPoly.CPolynomial.Raw.X.c68.costEq P (by includes)]
  have := cB_cost P (by includes) f
  have hC := size_C_le f
  have hf0 := fun a ↦ RunsApp.of_spec (us := []) (vs := [enc a])
    (Auto.CompPoly.CBivariate.linearYDivisor.c65.lam0.lam0.costSpec P (by includes) a)
  have hf1 := fun a ↦ RunsApp.of_spec (us := []) (vs := [enc a])
    (Auto.CompPoly.CBivariate.linearYDivisor.c65.lam0.costSpec P (by includes) a)
  have hm := listMap_le P Auto.List.map.c12.costIdx
    (.fn Auto.CompPoly.CBivariate.linearYDivisor.c65.lam0.costIdx [])
    (Auto.List.map.c12.costEq_nil P (by includes) _ _ hf1)
    (Auto.List.map.c12.costEq_cons P (by includes) _ _ hf1) (16 * f.val.size + 8)
    (CPolynomial.C f).val.toList
    (fun a ha ↦ by
      have hsa := innerLe_C f a (by simpa using ha)
      rw [appCost_fn, List.nil_append,
        Auto.CompPoly.CBivariate.linearYDivisor.c65.lam0.costEq P (by includes)]
      have := listMap_le P Auto.List.map.c12.costIdx
        (.fn Auto.CompPoly.CBivariate.linearYDivisor.c65.lam0.lam0.costIdx [])
        (Auto.List.map.c12.costEq_nil P (by includes) _ _ hf0)
        (Auto.List.map.c12.costEq_cons P (by includes) _ _ hf0) 1 a.val.toList
        (fun b _ ↦ by
          rw [appCost_fn, List.nil_append,
            Auto.CompPoly.CBivariate.linearYDivisor.c65.lam0.lam0.costEq P (by includes)])
      simp only [Array.length_toList, List.length_map] at this ⊢
      omega)
  have hX : (CPolynomial.X : CBivariate K).val.size = 2 := rfl
  have hn : (-CPolynomial.C f : CBivariate K).val.size ≤ 1 := by rw [neg_val_size]; exact hC
  have ha := addB_cost P (by includes) (CPolynomial.X : CBivariate K).val
    (-CPolynomial.C f : CBivariate K).val (f.val.size + 1) (by omega)
    (innerLe_X.mono (by omega)) ((innerLe_C f).neg.mono (by omega)) (by omega) (by omega)
  have hmax : max (CPolynomial.X : CBivariate K).val.size
      (-CPolynomial.C f : CBivariate K).val.size = 2 := by omega
  rw [hmax] at ha
  have hl : (16 * f.val.size + 8 + 11) * (CPolynomial.C f).val.toList.length ≤
      16 * f.val.size + 19 := by
    simp only [Array.length_toList]
    calc _ ≤ (16 * f.val.size + 8 + 11) * 1 := Nat.mul_le_mul_left _ hC
      _ = _ := by ring
  simp only [Array.length_toList, List.length_map] at hm hl ⊢
  omega

/-- **`G` as a constant in `Y`** (`ofYConstant`): at most `3·|G| + 74`. -/
theorem ofYConstantC_cost (hP : Includes P Auto.CompPoly.CBivariate.ofYConstant.c97.costDeps)
    (G : CPolynomial K) :
    machineCost P Auto.CompPoly.CBivariate.ofYConstant.c97.costIdx [enc G] ≤
      3 * G.val.size + 74 := by
  rw [Auto.CompPoly.CBivariate.ofYConstant.c97.costEq P hP]
  have := cB_cost P (by includes) G
  omega

/-- `ofArray` over `K[X]`, entries of at most `A` coefficients: at most `(3·A + 41)·n + 15`. -/
theorem ofArrayB_cost (hP : Includes P Auto.CompPoly.CPolynomial.ofArray.c103.costDeps)
    (coeffs : Array (CPolynomial K)) (A : ℕ) (hA : ∀ x ∈ coeffs, x.val.size ≤ A)
    (hs : coeffs.size < 2 ^ 63) :
    machineCost P Auto.CompPoly.CPolynomial.ofArray.c103.costIdx [enc coeffs] ≤
      (3 * A + 41) * coeffs.size + 15 := by
  rw [Auto.CompPoly.CPolynomial.ofArray.c103.costEq P hP]
  have := trimLenB_cost P (by includes) coeffs A hA coeffs.size hs
  have : (coeffs.extract 0 (CompPolyLib.trimLen coeffs coeffs.size)).size ≤ coeffs.size := by
    simp
  have e : (3 * A + 41) * coeffs.size = (3 * A + 40) * coeffs.size + coeffs.size := by ring
  omega

/-- **`Y^k·Q`** (`shiftY`: `k` zero rows prepended): at most `(3·A + 41)·(k + |Q|) + 2·k + |Q| + 22`,
`Q`'s entries of at most `A` coefficients. -/
theorem shiftYC_cost (hP : Includes P Auto.LeanVM.Extraction.Fast.shiftY.c102.costDeps) (k : ℕ)
    (Q : CBivariate K) (A : ℕ) (hA : InnerLe Q.val A) (hs : k + Q.val.size < 2 ^ 63) :
    machineCost P Auto.LeanVM.Extraction.Fast.shiftY.c102.costIdx [enc k, enc Q] ≤
      (3 * A + 41) * (k + Q.val.size) + 2 * k + Q.val.size + 22 := by
  rw [Auto.LeanVM.Extraction.Fast.shiftY.c102.costEq P hP]
  have := ofArrayB_cost P (by includes) (Array.replicate k 0 ++ Q.val) A
    (fun x hx ↦ by
      rcases Array.mem_append.1 hx with hx | hx
      · rw [(Array.mem_replicate.1 hx).2]; exact Nat.zero_le _
      · exact hA x hx)
    (by simp; omega)
  simp only [Array.size_append, Array.size_replicate] at this ⊢
  omega

/-- **A coefficient row** (`toCoeffRow w Q`, `w` lookups): at most `34·w + 17`. -/
theorem toCoeffRowC_cost (hP : Includes P Auto.CompPoly.CBivariate.toCoeffRow.c99.costDeps)
    (w : ℕ) (Q : CBivariate K) (hw : w < 2 ^ 64) :
    machineCost P Auto.CompPoly.CBivariate.toCoeffRow.c99.costIdx [enc w, enc Q] ≤ 34 * w + 17 := by
  rw [Auto.CompPoly.CBivariate.toCoeffRow.c99.costEq P hP]
  have := rangeLoop_cost P (by includes) w [] hw
  have hf := fun j ↦ RunsApp.of_spec (us := [enc Q]) (vs := [enc j])
    (Auto.CompPoly.CBivariate.toCoeffRow.c99.lam0.costSpec P (by includes) Q j)
  have hm := listMap_le P Auto.List.map.c12.costIdx
    (.fn Auto.CompPoly.CBivariate.toCoeffRow.c99.lam0.costIdx [enc Q])
    (Auto.List.map.c12.costEq_nil P (by includes) _ _ hf)
    (Auto.List.map.c12.costEq_cons P (by includes) _ _ hf) 5 (List.range w)
    (fun j _ ↦ by
      rw [appCost_fn, List.singleton_append,
        Auto.CompPoly.CBivariate.toCoeffRow.c99.lam0.costEq P (by includes)])
  simp only [List.length_range, List.length_map] at hm ⊢
  omega

/-! ## The rows -/

/-- A row `i ≤ m`: the product `G^(m−i)·(Y − R)^i` and its coefficient row. -/
@[expose] def rowProdBound (m w N : ℕ) : ℕ :=
  mulBBound 1 (m + 1) (m * N + 1) (m * N + 2) + 34 * w + 50

/-- A row `i > m`: the shift `Y^(i−m)·(Y − R)^m` and its coefficient row. -/
@[expose] def rowShiftBound (m w N : ℕ) : ℕ :=
  (3 * (m * N + 1) + 41) * (w + m + 1) + 2 * w + m + 34 * w + 60

theorem natDeg_le_size_pred {f : CPolynomial K} {N : ℕ} (h : f.natDegree ≤ N) :
    f.val.size ≤ N + 1 :=
  (cpoly_size_le_natDegree f).trans (by omega)

/-- **Row `i` of the basis** (`leeRowsFast`'s closure, the powers built): at most
`rowProdBound m w N` for `i ≤ m`, `rowShiftBound m w N` beyond. -/
theorem leeRowsLamC_cost (hP : Includes P
      Auto.LeanVM.Extraction.Fast.leeRowsFast.c95.lam0.costDeps)
    (R G : CPolynomial K) {N : ℕ} (hR : R.natDegree ≤ N) (hG : G.natDegree ≤ N) (m w i : ℕ)
    (hi : i < w) (hw : w < 2 ^ 55) (hm : m < 2 ^ 55) (hN : (m + 1) * N + 2 < 2 ^ 55) :
    machineCost P Auto.LeanVM.Extraction.Fast.leeRowsFast.c95.lam0.costIdx
        [enc (powersFrom (CBivariate.linearYDivisor R) 1 (m + 1)).toArray,
          enc (powersFrom (CBivariate.ofYConstant G) 1 (m + 1)).toArray, enc w, enc m, enc i] ≤
      if i ≤ m then rowProdBound m w N else rowShiftBound m w N := by
  rw [Auto.LeanVM.Extraction.Fast.leeRowsFast.c95.lam0.costEq P hP]
  have hmN : m * N + 1 < 2 ^ 55 := by
    have : (m + 1) * N = m * N + N := by ring
    omega
  have hz := zeroBivC_eq P (by includes)
  cost_simp
  split_ifs with h
  · rw [powersFrom_toArray_getD _ (by omega : m - i < m + 1),
      powersFrom_toArray_getD _ (by omega : i < m + 1), mulBivC_eq P (by includes)]
    have hrow := toCoeffRowC_cost P (by includes) w
      (CBivariate.ofYConstant G ^ (m - i) * CBivariate.linearYDivisor R ^ i) (by omega)
    have hsum : (m - i) * N + i * N = m * N := by rw [← Nat.add_mul, Nat.sub_add_cancel h]
    have hle : (m - i) * N ≤ m * N := Nat.mul_le_mul_right N (Nat.sub_le m i)
    have := mulB_cost_ab P (by includes) (CBivariate.ofYConstant G ^ (m - i)).val
      (CBivariate.linearYDivisor R ^ i).val ((m - i) * N + 1) (i * N + 1) (m * N + 2) 1 (m + 1)
      (by omega) (by omega) (innerLe_ofYConstant_pow G hG (m - i))
      (innerLe_linearYDivisor_pow R hR i) (ofYConstant_pow_sizes G (m - i)).1
      (by have := (linearYDivisor_pow_sizes R i).1; omega) (by omega)
    have := mulBBound_mono (rp := 1) (rq := m + 1) (s := m * N + 2) (s' := m * N + 2) le_rfl
      le_rfl (show (m - i) * N + 1 ≤ m * N + 1 by omega) le_rfl
    unfold rowProdBound
    omega
  · rw [powersFrom_toArray_getD _ (by omega : m < m + 1)]
    have hrow := toCoeffRowC_cost P (by includes) w
      (shiftY (i - m) (CBivariate.linearYDivisor R ^ m)) (by omega)
    have hsz := (linearYDivisor_pow_sizes R m).1
    have := shiftYC_cost P (by includes) (i - m) (CBivariate.linearYDivisor R ^ m) (m * N + 1)
      (innerLe_linearYDivisor_pow R hR m) (by omega)
    have h1 : (3 * (m * N + 1) + 41) * (i - m + (CBivariate.linearYDivisor R ^ m).val.size) ≤
        (3 * (m * N + 1) + 41) * (w + m + 1) := Nat.mul_le_mul_left _ (by omega)
    unfold rowShiftBound
    omega

/-- **`List.map` with two prices**: `B₁` on the elements of a predicate, `B₂` on the others; `11`
per element, `3` at the end. -/
theorem listMap_le_two (i : ℕ) {α : Type} [Enc α] (fVal : Val)
    (h0 : machineCost P i [fVal, enc ([] : List α)] = 3)
    (hs : ∀ (x : α) (l : List α), machineCost P i [fVal, enc (x :: l)] =
      appCost P fVal [enc x] + machineCost P i [fVal, enc l] + 11)
    (p : α → Bool) (B₁ B₂ : ℕ) : ∀ l : List α,
      (∀ a ∈ l, appCost P fVal [enc a] ≤ if p a then B₁ else B₂) →
      machineCost P i [fVal, enc l] ≤ (B₁ + 11) * l.countP p + (B₂ + 11) * l.length + 3 := by
  intro l
  induction l with
  | nil => intro _; rw [h0]; simp
  | cons x l ih =>
    intro hB
    rw [hs]
    have h1 := ih fun a ha ↦ hB a (by simp [ha])
    have h2 := hB x (by simp)
    simp only [List.length_cons, List.countP_cons]
    cases hp : p x
    · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h2 ⊢; nlinarith
    · simp only [hp, ↓reduceIte] at h2 ⊢; nlinarith

theorem countP_range_le (w m : ℕ) : (List.range w).countP (fun i ↦ decide (i ≤ m)) ≤ m + 1 := by
  rw [List.countP_eq_length_filter]
  have hsub : List.Subperm ((List.range w).filter (fun i ↦ decide (i ≤ m))) (List.range (m + 1)) :=
    (List.nodup_range.filter _).subperm fun x hx ↦ by
      simp only [List.mem_filter, decide_eq_true_eq] at hx
      simp only [List.mem_range]
      omega
  simpa using hsub.length_le

/-- The bound of `leeRowsFast`: `Y − R` and `G`, the `m + 1` powers of each, `m + 1` products
`G^(m−i)·(Y − R)^i` and `w` shifts, `w` coefficient rows. -/
@[expose] def leeRowsBound (m w N : ℕ) : ℕ :=
  703 * (N + 1) + 2460 + (mulBBound 2 (m + 1) (N + 1) ((m + 1) * N + 2) + 3 + 20) * (m + 1) +
    (mulBBound 1 1 (N + 1) ((m + 1) * N + 2) + 3 + 20) * (m + 1) + 2 * (m + 1) + 18 * w +
    (rowProdBound m w N + 11) * (m + 1) + (rowShiftBound m w N + 11) * w + 120

/-- **Lee–O'Sullivan's basis rows, compiled** (`leeRowsFast R G params`, `R` and `G` of degree at
most `N`): at most `leeRowsBound m w N`, `m` the multiplicity, `w = ℓ + 1` the width. -/
theorem leeRowsFastC_cost (hP : Includes P Auto.LeanVM.Extraction.Fast.leeRowsFast.c95.costDeps)
    (R G : CPolynomial K) (params : GuruswamiSudan.GSInterpParams) {N : ℕ} (hR : R.natDegree ≤ N)
    (hG : G.natDegree ≤ N) (hk : params.messageDegree < 2 ^ 64)
    (hW : params.weightedDegreeBound < 2 ^ 64) (hy : GuruswamiSudan.yWeight params < 2 ^ 64)
    (hw : GuruswamiSudan.interpolationYCap params + 1 < 2 ^ 55)
    (hm : params.multiplicity < 2 ^ 55) (hN : (params.multiplicity + 1) * N + 2 < 2 ^ 55) :
    machineCost P Auto.LeanVM.Extraction.Fast.leeRowsFast.c95.costIdx [enc R, enc G, enc params] ≤
      leeRowsBound params.multiplicity (GuruswamiSudan.interpolationYCap params + 1) N := by
  rw [Auto.LeanVM.Extraction.Fast.leeRowsFast.c95.costEq P hP, oneBivC_eq P (by includes)]
  have hwid : GuruswamiSudan.leeOSullivanWidth params =
      GuruswamiSudan.interpolationYCap params + 1 := rfl
  simp only [length_powersFrom, List.length_range, List.length_map]
  rw [hwid]
  cost_simp
  generalize params.multiplicity = m at *
  generalize GuruswamiSudan.interpolationYCap params + 1 = w at *
  have hRs := natDeg_le_size_pred hR
  have hGs := natDeg_le_size_pred hG
  have hmN : (m + 1) * N = m * N + N := by ring
  have hlin := linearYDivisorC_cost P (by includes) R (by omega)
  have hvan := ofYConstantC_cost P (by includes) G
  have hp1 := powersFromC_cost_one P (by includes) (CBivariate.linearYDivisor R)
    (mulBBound 2 (m + 1) (N + 1) ((m + 1) * N + 2) + 3) (m + 1) (by omega) (fun t ht ↦ by
      have h1 := innerLe_linearYDivisor_pow R hR 1
      have hs1 := (linearYDivisor_pow_sizes R 1).1
      rw [pow_one] at h1 hs1
      have htN : t * N ≤ m * N := Nat.mul_le_mul_right N (by omega)
      have := mulB_cost_ab P (by includes) (CBivariate.linearYDivisor R).val
        (CBivariate.linearYDivisor R ^ t).val (1 * N + 1) (t * N + 1) ((m + 1) * N + 2) 2 (m + 1)
        (by omega) (by omega) h1 (innerLe_linearYDivisor_pow R hR t) hs1
        (by have := (linearYDivisor_pow_sizes R t).1; omega) (by omega)
      have := mulBBound_mono (rp := 2) (rq := m + 1) (s := (m + 1) * N + 2)
        (s' := (m + 1) * N + 2) le_rfl le_rfl (show 1 * N + 1 ≤ N + 1 by omega) le_rfl
      omega)
  have hp2 := powersFromC_cost_one P (by includes) (CBivariate.ofYConstant G)
    (mulBBound 1 1 (N + 1) ((m + 1) * N + 2) + 3) (m + 1) (by omega) (fun t ht ↦ by
      have h1 := innerLe_ofYConstant_pow G hG 1
      have hs1 := (ofYConstant_pow_sizes G 1).1
      rw [pow_one] at h1 hs1
      have htN : t * N ≤ m * N := Nat.mul_le_mul_right N (by omega)
      have := mulB_cost_ab P (by includes) (CBivariate.ofYConstant G).val
        (CBivariate.ofYConstant G ^ t).val (1 * N + 1) (t * N + 1) ((m + 1) * N + 2) 1 1
        (by omega) (by omega) h1 (innerLe_ofYConstant_pow G hG t) hs1
        (ofYConstant_pow_sizes G t).1 (by omega)
      have := mulBBound_mono (rp := 1) (rq := 1) (s := (m + 1) * N + 2)
        (s' := (m + 1) * N + 2) le_rfl le_rfl (show 1 * N + 1 ≤ N + 1 by omega) le_rfl
      omega)
  have hr := rangeLoop_cost P (by includes) w [] (by omega)
  have hf := fun i ↦ RunsApp.of_spec
    (us := [enc (powersFrom (CBivariate.linearYDivisor R) 1 (m + 1)).toArray,
      enc (powersFrom (CBivariate.ofYConstant G) 1 (m + 1)).toArray, enc w, enc m]) (vs := [enc i])
    (Auto.LeanVM.Extraction.Fast.leeRowsFast.c95.lam0.costSpec P (by includes)
      (powersFrom (CBivariate.linearYDivisor R) 1 (m + 1)).toArray
      (powersFrom (CBivariate.ofYConstant G) 1 (m + 1)).toArray w m i)
  have hmap := listMap_le_two P Auto.List.map.c12.costIdx
    (.fn Auto.LeanVM.Extraction.Fast.leeRowsFast.c95.lam0.costIdx
      [enc (powersFrom (CBivariate.linearYDivisor R) 1 (m + 1)).toArray,
        enc (powersFrom (CBivariate.ofYConstant G) 1 (m + 1)).toArray, enc w, enc m])
    (Auto.List.map.c12.costEq_nil P (by includes) _ _ hf)
    (Auto.List.map.c12.costEq_cons P (by includes) _ _ hf) (fun i ↦ decide (i ≤ m))
    (rowProdBound m w N) (rowShiftBound m w N) (List.range w) (fun i hi ↦ by
      rw [List.mem_range] at hi
      simp only [appCost_fn, List.cons_append, List.nil_append, decide_eq_true_eq]
      exact leeRowsLamC_cost P (by includes) R G hR hG m w i hi (by omega) (by omega) (by omega))
  have hc := Nat.mul_le_mul_left (rowProdBound m w N + 11) (countP_range_le w m)
  simp only [List.length_range] at hmap
  unfold leeRowsBound
  omega

end

end LeanVM.Cost.Bounds.Decoder
