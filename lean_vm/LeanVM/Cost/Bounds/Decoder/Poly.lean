module

public import LeanVM.Cost.Bounds.Decoder.MsReduce
public import LeanVM.Cost.Extractor.Interp
import all CompPoly.Univariate.Raw.Ops
import all CompPoly.Data.Array.Lemmas

/-!
# Bounds: polynomial arithmetic, compiled

The prices of CompPoly's raw polynomial operations as the decoder compiles them
(`Cost/Extractor/Interp.lean`), over `K` (`…K_cost`) and over `K[X]` (bivariate polynomials,
`…B_cost`), in the operands' sizes:

* addition (`addRaw`: pad, zip; `add`: then trim), scaling (`smul`), shifting (`mulPowX`);
* the schoolbook product (`mulRaw`: for each coefficient `a_i` of `p`, `acc + X^i·(a_i·q)`;
  `mul`: then trim), `O(|p|·(|p| + |q|))` operations on coefficients.

**Honest-cost note.** `Raw.add` and `Raw.mul` compute their raw result three times: the
compiler's rewrite of `trim` (`CompPolyLib.trim_eq`, `p.trim = p.extract 0 (trimLen p p.size)`)
names `p` three times and the compiler unfolds it with `p := addRaw a b` (or `mulRaw a b`)
unshared. A factor 3 on every sum and product, not an order.
-/

namespace LeanVM.Cost.Bounds.Decoder

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Bounds.Samples LeanVM.Cost.Library
open LeanVM.Cost.Extractor LeanVM.Parameters CompPoly

/-! The functions compiled on demand, by their short names. -/
open LeanVM.Cost.Auto.CompPoly.CPolynomial.Raw

public section

/-! ## Sizes -/

section Sizes

variable {R : Type} [Zero R] [Add R]

theorem size_addRaw (p q : CPolynomial.Raw R) : (p.addRaw q).size = max p.size q.size := by
  simp [CPolynomial.Raw.addRaw, Array.size_zipWith, Array.size_rightpad]
  omega

theorem size_smul {R : Type} [Mul R] (r : R) (p : CPolynomial.Raw R) :
    (CPolynomial.Raw.smul r p).size = p.size := by
  simp [CPolynomial.Raw.smul]

omit [Add R] in
theorem size_mulPowX (i : ℕ) (p : CPolynomial.Raw R) :
    (CPolynomial.Raw.mulPowX i p).size = i + p.size := by
  simp [CPolynomial.Raw.mulPowX]

theorem foldl_mulRaw_size_le {R : Type} [Semiring R] (q : CPolynomial.Raw R) (B : ℕ) :
    ∀ (l : List (R × ℕ)) (acc : CPolynomial.Raw R), acc.size ≤ B + q.size →
      (∀ x ∈ l, x.2 ≤ B) →
      (l.foldl (fun acc x ↦ acc.addRaw ((CPolynomial.Raw.smul x.1 q).mulPowX x.2)) acc).size ≤
        B + q.size := by
  intro l
  induction l with
  | nil => intro acc h _; exact h
  | cons x l ih =>
    intro acc h hl
    apply ih
    · dsimp only
      rw [size_addRaw, size_mulPowX, size_smul]
      have := hl x (by simp)
      omega
    · exact fun y hy ↦ hl y (by simp [hy])

theorem size_mulRaw_le {R : Type} [Semiring R] (p q : CPolynomial.Raw R) :
    (CPolynomial.Raw.mulRaw p q).size ≤ p.size + q.size := by
  unfold CPolynomial.Raw.mulRaw
  have := foldl_mulRaw_size_le q p.size p.zipIdx.toList (CPolynomial.Raw.mk #[]) (by simp)
    (fun x hx ↦ by
      rw [Array.toList_zipIdx] at hx
      have := List.mem_zipIdx hx
      simp at this
      omega)
  rw [Array.foldl_toList] at this
  convert this using 2

end Sizes

variable (P : Program)

/-! ## Over `K` -/

/-- `Array.rightpad n a xs` (polymorphic): `9 + (n − |xs|) + max n |xs|`, word-sized lengths. -/
theorem rightpadC_cost {α : Type} [Enc α] (hP : Includes P Auto.Array.rightpad.c47.costDeps)
    (n : ℕ) (a : α) (xs : Array α) (hn : n < 2 ^ 64) (hs : xs.size < 2 ^ 64) :
    machineCost P Auto.Array.rightpad.c47.costIdx [enc n, enc a, enc xs] ≤
      9 + (n - xs.size) + max n xs.size := by
  rw [Auto.Array.rightpad.c47.costEq P hP]
  simp only [limbs_of_lt hn, limbs_of_lt hs, Array.size_replicate]
  omega

/-- **`addRaw` over `K`**: at most `44 + 28·max(|p|, |q|)`. -/
theorem addRawK_cost (hP : Includes P addRaw.c50.costDeps) (p q : CPolynomial.Raw K)
    (hp : p.size < 2 ^ 64) (hq : q.size < 2 ^ 64) :
    machineCost P addRaw.c50.costIdx [enc p, enc q] ≤ 44 + 28 * max p.size q.size := by
  rw [addRaw.c50.costEq P hP]
  have hz := listZipWith_le P (by includes) (fun x y : K ↦ x + y) (.fn addRaw.c50.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (addRaw.c50.lam0.costSpec P (by includes) a b)) 3
    (p.rightpad q.size 0).toList (q.rightpad p.size 0).toList
    (fun a _ b _ ↦ by rw [appCost_fn, List.nil_append, addRaw.c50.lam0.costEq P (by includes)])
  have := rightpadC_cost P (by includes) q.size (0 : K) p hq hp
  have := rightpadC_cost P (by includes) p.size (0 : K) q hp hq
  simp only [Array.length_toList, Array.size_rightpad,
    List.length_zipWith] at hz ⊢
  omega

/-- **`add` over `K`** (`addRaw`, three times, and the trim): at most `110·max(|p|, |q|) + 160`. -/
theorem addK_cost (hP : Includes P add.c49.costDeps) (p q : CPolynomial.Raw K)
    (hp : p.size < 2 ^ 62) (hq : q.size < 2 ^ 62) :
    machineCost P add.c49.costIdx [enc p, enc q] ≤ 110 * max p.size q.size + 160 := by
  rw [add.c49.costEq P hP]
  have := addRawK_cost P (by includes) p q (by omega) (by omega)
  have := trimLen_cost P (by includes) (p.addRaw q) (p.addRaw q).size
    (by rw [size_addRaw]; omega)
  have h1 : (Array.extract (p.addRaw q) 0
      (CompPolyLib.trimLen (p.addRaw q) (p.addRaw q).size)).size ≤ (p.addRaw q).size := by simp
  rw [size_addRaw] at *
  omega

/-- `smul` over `K`: at most `273·|p| + 10`. -/
theorem smulK_cost (hP : Includes P smul.c59.costDeps) (r : K) (p : CPolynomial.Raw K) :
    machineCost P smul.c59.costIdx [enc r, enc p] ≤ 273 * p.size + 10 := by
  rw [smul.c59.costEq P hP]
  have hf := fun a ↦ RunsApp.of_spec (us := [enc r]) (vs := [enc a])
    (smul.c59.lam0.costSpec P (by includes) r a)
  have := listMap_le P Auto.List.map.c12.costIdx (.fn smul.c59.lam0.costIdx [enc r])
    (Auto.List.map.c12.costEq_nil P (by includes) _ _ hf)
    (Auto.List.map.c12.costEq_cons P (by includes) _ _ hf) 258 p.toList
    (fun a _ ↦ by rw [appCost_fn, List.singleton_append, smul.c59.lam0.costEq P (by includes)])
  simp only [Array.length_toList, List.length_map] at this ⊢
  omega

/-- `mulPowX` over `K`: `2·i + |p| + 5`. -/
theorem mulPowXK_cost (hP : Includes P mulPowX.c58.costDeps) (i : ℕ) (p : CPolynomial.Raw K) :
    machineCost P mulPowX.c58.costIdx [enc i, enc p] = 2 * i + p.size + 5 := by
  rw [mulPowX.c58.costEq P hP]
  simp only [Array.size_replicate]
  omega

theorem mem_zipIdx_lt {α : Type} {p : Array α} {x : α × ℕ} (h : x ∈ (Array.zipIdx p).toList) :
    x.2 < p.size := by
  rw [Array.toList_zipIdx] at h
  have := List.mem_zipIdx h
  simp at this
  omega

/-- **The schoolbook product over `K`** (`mulRaw`): at most
`302·|q|·|p| + 30·|p|² + 102·|p| + 20`. -/
theorem mulRawK_cost (hP : Includes P mulRaw.c56.costDeps) (p q : CPolynomial.Raw K)
    (hp : p.size < 2 ^ 62) (hq : q.size < 2 ^ 62) :
    machineCost P mulRaw.c56.costIdx [enc p, enc q] ≤
      302 * (q.size * p.size) + 30 * (p.size * p.size) + 102 * p.size + 20 := by
  rw [mulRaw.c56.costEq P hP]
  have hz := zipIdx_cost P (by includes) p.toList 0 (by simp; omega)
  have hf := listFoldl_le P (by includes) _ (.fn mulRaw.c56.lam0.costIdx [enc q])
    (fun acc x ↦ RunsApp.of_spec (us := [enc q]) (vs := [enc acc, enc x])
      (mulRaw.c56.lam0.costSpec P (by includes) q acc x))
    (302 * q.size + 30 * p.size + 70) (fun acc ↦ acc.size ≤ p.size + q.size)
    (Array.zipIdx p).toList (CPolynomial.Raw.mk #[]) (by simp)
    (fun acc hacc x hx ↦ by
      have hi := mem_zipIdx_lt hx
      obtain ⟨a, i⟩ := x
      dsimp only at hi ⊢
      refine ⟨?_, ?_⟩
      · rw [size_addRaw, size_mulPowX, size_smul]; omega
      · rw [appCost_fn, List.singleton_append, mulRaw.c56.lam0.costEq P (by includes)]
        have := smulK_cost P (by includes) a q
        have := mulPowXK_cost P (by includes) i (CPolynomial.Raw.smul a q)
        have := addRawK_cost P (by includes) acc
          (CPolynomial.Raw.mulPowX i (CPolynomial.Raw.smul a q)) (by omega)
          (by rw [size_mulPowX, size_smul]; omega)
        rw [size_mulPowX, size_smul] at *
        dsimp only
        omega)
  have e : (302 * q.size + 30 * p.size + 70 + 9) * (Array.zipIdx p).toList.length =
      302 * (q.size * p.size) + 30 * (p.size * p.size) + 79 * p.size := by
    simp only [Array.length_toList, Array.size_zipIdx]; ring
  simp only [Array.length_toList, Array.size_zipIdx, List.length_zipIdx] at hz hf e ⊢
  omega

/-- **The product over `K`** (`mul`: `mulRaw` three times, the trim): at most
`906·|q|·|p| + 90·|p|² + 330·|p| + 23·|q| + 90`. -/
theorem mulK_cost (hP : Includes P mul.c55.costDeps) (p q : CPolynomial.Raw K)
    (hp : p.size < 2 ^ 61) (hq : q.size < 2 ^ 61) :
    machineCost P mul.c55.costIdx [enc p, enc q] ≤
      906 * (q.size * p.size) + 90 * (p.size * p.size) + 330 * p.size + 23 * q.size + 90 := by
  rw [mul.c55.costEq P hP]
  have := mulRawK_cost P (by includes) p q (by omega) (by omega)
  have hs := size_mulRaw_le p q
  have := trimLen_cost P (by includes) (p.mulRaw q) (p.mulRaw q).size (by omega)
  have h1 : (Array.extract (p.mulRaw q) 0
      (CompPolyLib.trimLen (p.mulRaw q) (p.mulRaw q).size)).size ≤ (p.mulRaw q).size := by simp
  omega

/-! ## Over `K[X]`: bivariate polynomials -/

theorem raw_trim_size_le {R : Type} [Zero R] [BEq R] (p : CPolynomial.Raw R) :
    p.trim.size ≤ p.size := by
  rw [CompPolyLib.trim_eq]; simp

theorem cpoly_add_size_le (x y : CPolynomial K) :
    (x + y).val.size ≤ max x.val.size y.val.size := by
  show (x.val.addRaw y.val).trim.size ≤ _
  have := raw_trim_size_le (x.val.addRaw y.val)
  rw [size_addRaw] at this
  exact this

theorem cpoly_mul_size_le (x y : CPolynomial K) :
    (x * y).val.size ≤ x.val.size + y.val.size := by
  show (x.val.mulRaw y.val).trim.size ≤ _
  exact (raw_trim_size_le _).trans (size_mulRaw_le _ _)

/-- Every entry of a bivariate polynomial has at most `A` coefficients. -/
@[expose] def InnerLe (p : CPolynomial.Raw (CPolynomial K)) (A : ℕ) : Prop :=
  ∀ x ∈ p, x.val.size ≤ A

theorem mem_zipWith_exists {α β γ : Type} {f : α → β → γ} {l : List α} {l' : List β} {x : γ}
    (h : x ∈ List.zipWith f l l') : ∃ a ∈ l, ∃ b ∈ l', x = f a b := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 h
  simp only [List.length_zipWith] at hi
  rw [List.getElem_zipWith]
  exact ⟨_, List.getElem_mem (by omega), _, List.getElem_mem (by omega), rfl⟩

theorem InnerLe.rightpad {p : CPolynomial.Raw (CPolynomial K)} {A : ℕ} (h : InnerLe p A) (n : ℕ) :
    ∀ x ∈ (p.rightpad n 0).toList, x.val.size ≤ A := by
  intro x hx
  rw [Array.rightpad_toList] at hx
  simp only [List.rightpad, List.mem_append, Array.mem_toList_iff, List.mem_replicate] at hx
  rcases hx with hx | ⟨_, rfl⟩
  · exact h x hx
  · exact Nat.zero_le _

theorem InnerLe.addRaw {p q : CPolynomial.Raw (CPolynomial K)} {A : ℕ} (hp : InnerLe p A)
    (hq : InnerLe q A) : InnerLe (p.addRaw q) A := by
  intro x hx
  simp only [CPolynomial.Raw.addRaw] at hx
  rw [← Array.mem_toList_iff, Array.toList_zipWith] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_zipWith_exists hx
  have := cpoly_add_size_le a b
  have := hp.rightpad q.size a ha
  have := hq.rightpad p.size b hb
  omega

/-- `List.beq` against the empty list: at most `7`. -/
theorem beqNilK_cost (hP : Includes P Auto.List.beq.c27.costDeps) (a : List K) :
    machineCost P Auto.List.beq.c27.costIdx [enc a, enc ([] : List K)] ≤ 7 := by
  cases a with
  | nil => rw [Auto.List.beq.c27.costEq_nil P hP]; simp
  | cons x a => rw [Auto.List.beq.c27.costEq_cons P hP]; simp

/-- `trimLen` over `K[X]`: at most `(3·A + 40)·n + 6`, entries of at most `A` coefficients. -/
theorem trimLenB_cost (hP : Includes P Auto.LeanVM.Cost.CompPolyLib.trimLen.c62.costDeps)
    (p : Array (CPolynomial K)) (A : ℕ) (hA : ∀ x ∈ p, x.val.size ≤ A) :
    ∀ n : ℕ, n < 2 ^ 63 →
      machineCost P Auto.LeanVM.Cost.CompPolyLib.trimLen.c62.costIdx [enc p, enc n] ≤
        (3 * A + 40) * n + 6 := by
  intro n
  induction n with
  | zero => intro _; rw [Auto.LeanVM.Cost.CompPolyLib.trimLen.c62.costEq_zero P hP]; omega
  | succ k ih =>
    intro hk
    rw [Auto.LeanVM.Cost.CompPolyLib.trimLen.c62.costEq_succ P hP]
    have := ih (by omega)
    have hb := beqNilK_cost P (by includes) (↑(p.getD k 0) : Array K).toList
    have hs : (p.getD k 0).val.size ≤ A := by
      rw [Array.getD_eq_getD_getElem?]
      cases h : p[k]? with
      | none => exact Nat.zero_le _
      | some x => exact hA x (Array.mem_of_getElem? h)
    simp only [toList_zero_val, size_zero_val]
    cost_simp
    have : (3 * A + 40) * (k + 1) = (3 * A + 40) * k + 3 * A + 40 := by ring
    split_ifs <;> omega

/-- **`addRaw` over `K[X]`**: at most `110·A·m + 190·m + 50`, `m = max(|p|, |q|)` rows of entries
of at most `A` coefficients. -/
theorem addRawB_cost (hP : Includes P addRaw.c46.costDeps) (p q : CPolynomial.Raw (CPolynomial K))
    (A : ℕ) (hA : A < 2 ^ 60) (hp : InnerLe p A) (hq : InnerLe q A) (hps : p.size < 2 ^ 60)
    (hqs : q.size < 2 ^ 60) :
    machineCost P addRaw.c46.costIdx [enc p, enc q] ≤
      110 * (A * max p.size q.size) + 190 * max p.size q.size + 50 := by
  rw [addRaw.c46.costEq P hP]
  have hz := listZipWith_le P (by includes) (fun x y : CPolynomial K ↦ x + y)
    (.fn addRaw.c46.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (addRaw.c46.lam0.costSpec P (by includes) a b)) (110 * A + 163)
    (p.rightpad q.size 0).toList (q.rightpad p.size 0).toList
    (fun a ha b hb ↦ by
      rw [appCost_fn, List.nil_append, addRaw.c46.lam0.costEq P (by includes)]
      have := addK_cost P (by includes) a.val b.val
        (by have := hp.rightpad q.size a ha; omega) (by have := hq.rightpad p.size b hb; omega)
      have := hp.rightpad q.size a ha
      have := hq.rightpad p.size b hb
      have : 110 * max a.val.size b.val.size ≤ 110 * A := by omega
      omega)
  have := rightpadC_cost P (by includes) q.size (0 : CPolynomial K) p (by omega) (by omega)
  have := rightpadC_cost P (by includes) p.size (0 : CPolynomial K) q (by omega) (by omega)
  simp only [Array.length_toList, Array.size_rightpad, List.length_zipWith] at hz ⊢
  have e : (110 * A + 163 + 15) * min (max q.size p.size) (max p.size q.size) =
      110 * (A * max p.size q.size) + 178 * max p.size q.size := by
    rw [Nat.max_comm q.size, Nat.min_self]; ring
  omega

/-- **`add` over `K[X]`** (`addRaw` thrice, the trim): at most `333·A·m + 615·m + 170`. -/
theorem addB_cost (hP : Includes P add.c66.costDeps) (p q : CPolynomial.Raw (CPolynomial K))
    (A : ℕ) (hA : A < 2 ^ 60) (hp : InnerLe p A) (hq : InnerLe q A) (hps : p.size < 2 ^ 60)
    (hqs : q.size < 2 ^ 60) :
    machineCost P add.c66.costIdx [enc p, enc q] ≤
      333 * (A * max p.size q.size) + 615 * max p.size q.size + 170 := by
  rw [add.c66.costEq P hP]
  have := addRawB_cost P (by includes) p q A hA hp hq hps hqs
  have := trimLenB_cost P (by includes) (p.addRaw q) A (hp.addRaw hq) (p.addRaw q).size
    (by rw [size_addRaw]; omega)
  have h1 : (Array.extract (p.addRaw q) 0
      (CompPolyLib.trimLen (p.addRaw q) (p.addRaw q).size)).size ≤ (p.addRaw q).size := by simp
  rw [size_addRaw] at *
  have e : (3 * A + 40) * max p.size q.size =
      3 * (A * max p.size q.size) + 40 * max p.size q.size := by
    ring
  omega

theorem InnerLe.mono {p : CPolynomial.Raw (CPolynomial K)} {A B : ℕ} (h : InnerLe p A)
    (hAB : A ≤ B) : InnerLe p B := fun x hx ↦ (h x hx).trans hAB

theorem InnerLe.smul {p : CPolynomial.Raw (CPolynomial K)} {A : ℕ} (h : InnerLe p A)
    (r : CPolynomial K) (hr : r.val.size ≤ A) : InnerLe (CPolynomial.Raw.smul r p) (2 * A) := by
  intro x hx
  simp only [CPolynomial.Raw.smul, Array.mem_map] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  have := cpoly_mul_size_le r a
  have := h a ha
  omega

theorem InnerLe.mulPowX {p : CPolynomial.Raw (CPolynomial K)} {A : ℕ} (h : InnerLe p A) (i : ℕ) :
    InnerLe (CPolynomial.Raw.mulPowX i p) A := by
  intro x hx
  simp only [CPolynomial.Raw.mulPowX, Array.mem_append, Array.mem_replicate] at hx
  rcases hx with ⟨_, rfl⟩ | hx
  · exact Nat.zero_le _
  · exact h x hx

/-- The product of two entries of at most `A` coefficients: at most `1440·(A + 1)²`. -/
theorem mulK_cost_sq (hP : Includes P mul.c55.costDeps) (p q : CPolynomial.Raw K) (A : ℕ)
    (hA : A < 2 ^ 60) (hp : p.size ≤ A) (hq : q.size ≤ A) :
    machineCost P mul.c55.costIdx [enc p, enc q] ≤ 1440 * ((A + 1) * (A + 1)) := by
  have := mulK_cost P hP p q (by omega) (by omega)
  have h1 : q.size * p.size ≤ (A + 1) * (A + 1) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : p.size * p.size ≤ (A + 1) * (A + 1) := Nat.mul_le_mul (by omega) (by omega)
  have h3 : A + 1 ≤ (A + 1) * (A + 1) := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- `smul` over `K[X]`: at most `1460·(A + 1)²·|p| + 10`, `r` and the entries of at most `A`
coefficients. -/
theorem smulB_cost (hP : Includes P smul.c53.costDeps) (r : CPolynomial K)
    (p : CPolynomial.Raw (CPolynomial K)) (A : ℕ) (hA : A < 2 ^ 60) (hr : r.val.size ≤ A)
    (hp : InnerLe p A) :
    machineCost P smul.c53.costIdx [enc r, enc p] ≤
      1460 * (((A + 1) * (A + 1)) * p.size) + 10 := by
  rw [smul.c53.costEq P hP]
  have hf := fun a ↦ RunsApp.of_spec (us := [enc r]) (vs := [enc a])
    (smul.c53.lam0.costSpec P (by includes) r a)
  have hm := listMap_le P Auto.List.map.c12.costIdx (.fn smul.c53.lam0.costIdx [enc r])
    (Auto.List.map.c12.costEq_nil P (by includes) _ _ hf)
    (Auto.List.map.c12.costEq_cons P (by includes) _ _ hf) (1440 * ((A + 1) * (A + 1)) + 3)
    p.toList
    (fun a ha ↦ by
      rw [appCost_fn, List.singleton_append, smul.c53.lam0.costEq P (by includes)]
      have := mulK_cost_sq P (by includes) r.val a.val A hA hr (hp a (by simpa using ha))
      omega)
  simp only [Array.length_toList, List.length_map] at hm ⊢
  have h1 : 1 ≤ (A + 1) * (A + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
  have e : (1440 * ((A + 1) * (A + 1)) + 3 + 11) * p.size =
      1440 * (((A + 1) * (A + 1)) * p.size) + 14 * p.size := by ring
  have : p.size ≤ ((A + 1) * (A + 1)) * p.size := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- `mulPowX` over `K[X]`: `2·i + |p| + 6`. -/
theorem mulPowXB_cost (hP : Includes P mulPowX.c52.costDeps) (i : ℕ)
    (p : CPolynomial.Raw (CPolynomial K)) :
    machineCost P mulPowX.c52.costIdx [enc i, enc p] = 2 * i + p.size + 6 := by
  rw [mulPowX.c52.costEq P hP]
  simp only [Array.size_replicate]
  omega

/-- **The schoolbook product over `K[X]`** (`mulRaw`), entries of at most `A` coefficients:
at most `1460·(A+1)²·|q|·|p| + 220·A·(|p|+|q|)·|p| + 195·(|p|+|q|)·|p| + 112·|p| + 20`. -/
theorem mulRawB_cost (hP : Includes P mulRaw.c44.costDeps) (p q : CPolynomial.Raw (CPolynomial K))
    (A : ℕ) (hA : A < 2 ^ 58) (hp : InnerLe p A) (hq : InnerLe q A) (hps : p.size < 2 ^ 58)
    (hqs : q.size < 2 ^ 58) :
    machineCost P mulRaw.c44.costIdx [enc p, enc q] ≤
      1460 * ((((A + 1) * (A + 1)) * q.size) * p.size) + 220 * ((A * (p.size + q.size)) * p.size) +
        195 * ((p.size + q.size) * p.size) + 112 * p.size + 20 := by
  rw [mulRaw.c44.costEq P hP]
  have hz := zipIdx_cost P (by includes) p.toList 0 (by simp; omega)
  have hf := listFoldl_le P (by includes) _ (.fn mulRaw.c44.lam0.costIdx [enc q])
    (fun acc x ↦ RunsApp.of_spec (us := [enc q]) (vs := [enc acc, enc x])
      (mulRaw.c44.lam0.costSpec P (by includes) q acc x))
    (1460 * (((A + 1) * (A + 1)) * q.size) + 220 * (A * (p.size + q.size)) +
      195 * (p.size + q.size) + 80)
    (fun acc ↦ acc.size ≤ p.size + q.size ∧ InnerLe acc (2 * A))
    (Array.zipIdx p).toList (CPolynomial.Raw.mk #[]) ⟨by simp, fun x hx ↦ by simp at hx⟩
    (fun acc hacc x hx ↦ by
      have hi := mem_zipIdx_lt hx
      have hxp : x.1 ∈ p := by
        rw [Array.toList_zipIdx] at hx
        have := List.mem_zipIdx hx
        simp only [Nat.sub_zero] at this
        rw [this.2.2]; simp
      obtain ⟨a, i⟩ := x
      dsimp only at hi hxp ⊢
      have hsh : InnerLe (CPolynomial.Raw.mulPowX i (CPolynomial.Raw.smul a q)) (2 * A) :=
        (hq.smul a (hp a hxp)).mulPowX i
      refine ⟨⟨?_, hacc.2.addRaw hsh⟩, ?_⟩
      · rw [size_addRaw, size_mulPowX, size_smul]; omega
      · rw [appCost_fn, List.singleton_append, mulRaw.c44.lam0.costEq P (by includes)]
        have := smulB_cost P (by includes) a q A (by omega) (hp a hxp) hq
        have := mulPowXB_cost P (by includes) i (CPolynomial.Raw.smul a q)
        have := addRawB_cost P (by includes) acc
          (CPolynomial.Raw.mulPowX i (CPolynomial.Raw.smul a q)) (2 * A) (by omega) hacc.2 hsh
          (by omega) (by rw [size_mulPowX, size_smul]; omega)
        rw [size_mulPowX, size_smul] at *
        have hm : max acc.size (i + q.size) ≤ p.size + q.size := by omega
        have : 2 * A * max acc.size (i + q.size) ≤ 2 * (A * (p.size + q.size)) := by
          rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left A hm)
        dsimp only
        omega)
  have e : (1460 * (((A + 1) * (A + 1)) * q.size) + 220 * (A * (p.size + q.size)) +
      195 * (p.size + q.size) + 80 + 9) * (Array.zipIdx p).toList.length =
      1460 * ((((A + 1) * (A + 1)) * q.size) * p.size) + 220 * ((A * (p.size + q.size)) * p.size) +
        195 * ((p.size + q.size) * p.size) + 89 * p.size := by
    simp only [Array.length_toList, Array.size_zipIdx]; ring
  simp only [Array.length_toList, Array.size_zipIdx, List.length_zipIdx] at hz hf e ⊢
  omega

theorem InnerLe.mulRaw {p q : CPolynomial.Raw (CPolynomial K)} {A : ℕ} (hp : InnerLe p A)
    (hq : InnerLe q A) : InnerLe (CPolynomial.Raw.mulRaw p q) (2 * A) := by
  unfold CPolynomial.Raw.mulRaw
  rw [← Array.foldl_toList]
  suffices ∀ (l : List (CPolynomial K × ℕ)) (acc : CPolynomial.Raw (CPolynomial K)),
      InnerLe acc (2 * A) → (∀ x ∈ l, x.1 ∈ p) →
      InnerLe (l.foldl (fun acc x ↦ acc.addRaw ((CPolynomial.Raw.smul x.1 q).mulPowX x.2)) acc)
        (2 * A) by
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
    exact ih _ (h.addRaw ((hq.smul x.1 (hp _ (hl x (by simp)))).mulPowX x.2))
      (fun y hy ↦ hl y (by simp [hy]))

/-- **The product over `K[X]`** (`mul`: `mulRaw` thrice, the trim). -/
theorem mulB_cost (hP : Includes P mul.c43.costDeps) (p q : CPolynomial.Raw (CPolynomial K))
    (A : ℕ) (hA : A < 2 ^ 58) (hp : InnerLe p A) (hq : InnerLe q A) (hps : p.size < 2 ^ 58)
    (hqs : q.size < 2 ^ 58) :
    machineCost P mul.c43.costIdx [enc p, enc q] ≤
      4380 * ((((A + 1) * (A + 1)) * q.size) * p.size) + 660 * ((A * (p.size + q.size)) * p.size) +
        585 * ((p.size + q.size) * p.size) + 336 * p.size +
        6 * (A * (p.size + q.size)) + 41 * (p.size + q.size) + 80 := by
  rw [mul.c43.costEq P hP]
  have := mulRawB_cost P (by includes) p q A hA hp hq hps hqs
  have hs := size_mulRaw_le p q
  have := trimLenB_cost P (by includes) (p.mulRaw q) (2 * A) (hp.mulRaw hq) (p.mulRaw q).size
    (by omega)
  have h1 : (Array.extract (p.mulRaw q) 0
      (CompPolyLib.trimLen (p.mulRaw q) (p.mulRaw q).size)).size ≤ (p.mulRaw q).size := by simp
  have : (3 * (2 * A) + 40) * (p.mulRaw q).size ≤
      6 * (A * (p.size + q.size)) + 40 * (p.size + q.size) := by
    have := Nat.mul_le_mul_left (3 * (2 * A) + 40) hs
    have e : (3 * (2 * A) + 40) * (p.size + q.size) =
        6 * (A * (p.size + q.size)) + 40 * (p.size + q.size) := by
      ring
    omega
  omega

end

end LeanVM.Cost.Bounds.Decoder
