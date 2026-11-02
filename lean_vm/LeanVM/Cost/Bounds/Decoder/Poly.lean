module

public import LeanVM.Cost.Bounds.Decoder.Rows
public import LeanVM.Cost.Extractor.PMLane
import all CompPoly.Univariate.Raw.Ops
import all CompPoly.Data.Array.Lemmas

/-!
# Bounds: polynomial arithmetic, compiled

The prices of CompPoly's raw polynomial operations as the decoder compiles them, over `K`
(`…K_cost`), in the operands' sizes, and `trimLen` over `K[X]` (`trimLenB_cost`):

* addition (`addRaw`: pad, zip; `add`: then trim), scaling (`smul`), shifting (`mulPowX`);
* the schoolbook product (`mulRaw`: for each coefficient `a_i` of `p`, `acc + X^i·(a_i·q)`;
  `mul`: then trim), `O(|p|·(|p| + |q|))` operations on coefficients.

**Honest-cost note.** `Raw.add` and `Raw.mul` compute their raw result once
(`CompPolyLib.trim_addRaw_shared`, `trim_mulRaw_shared`: the untrimmed sum or product bound by a
`let` before `trim_eq`, which names its argument three times). The bounds here were proved when it
was computed thrice, and are kept: they still hold, about three times loose on sums and products.
-/

namespace LeanVM.Cost.Bounds.Decoder

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library
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

variable (P : MachineProgram)

/-! ## Over `K` -/

/-- `Array.rightpad n a xs` (polymorphic): `9 + (n − |xs|) + max n |xs|`, word-sized lengths. -/
theorem rightpadC_cost {α : Type} [MachineEncoding α] (hP : Includes P Auto.Array.rightpad.c39.costDeps)
    (n : ℕ) (a : α) (xs : Array α) (hn : n < 2 ^ 64) (hs : xs.size < 2 ^ 64) :
    machineCost P Auto.Array.rightpad.c39.costIdx [encodeValue n, encodeValue a, encodeValue xs] ≤
      9 + (n - xs.size) + max n xs.size := by
  rw [Auto.Array.rightpad.c39.costEq P hP]
  simp only [limbs_of_lt hn, limbs_of_lt hs, Array.size_replicate]
  omega

/-- **`addRaw` over `K`**: at most `44 + 28·max(|p|, |q|)`. -/
theorem addRawK_cost (hP : Includes P addRaw.c38.costDeps) (p q : CPolynomial.Raw K)
    (hp : p.size < 2 ^ 64) (hq : q.size < 2 ^ 64) :
    machineCost P addRaw.c38.costIdx [encodeValue p, encodeValue q] ≤ 44 + 28 * max p.size q.size := by
  rw [addRaw.c38.costEq P hP]
  have hz := listZipWith_le P (by includes) (fun x y : K ↦ x + y) (.closure addRaw.c38.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (addRaw.c38.lam0.costSpec P (by includes) a b)) 3
    (p.rightpad q.size 0).toList (q.rightpad p.size 0).toList
    (fun a _ b _ ↦ by rw [appCost_fn, List.nil_append, addRaw.c38.lam0.costEq P (by includes)])
  have := rightpadC_cost P (by includes) q.size (0 : K) p hq hp
  have := rightpadC_cost P (by includes) p.size (0 : K) q hp hq
  simp only [Array.length_toList, Array.size_rightpad,
    List.length_zipWith] at hz ⊢
  omega

/-- **`add` over `K`** (`addRaw` and the trim; the bound from when `addRaw` was computed thrice): at most `110·max(|p|, |q|) + 160`. -/
theorem addK_cost (hP : Includes P add.c49.costDeps) (p q : CPolynomial.Raw K)
    (hp : p.size < 2 ^ 62) (hq : q.size < 2 ^ 62) :
    machineCost P add.c49.costIdx [encodeValue p, encodeValue q] ≤ 110 * max p.size q.size + 160 := by
  rw [add.c49.costEq P hP]
  have := addRawK_cost P (by includes) p q (by omega) (by omega)
  have := trimLen_cost P (by includes) (p.addRaw q) (p.addRaw q).size
    (by rw [size_addRaw]; omega)
  have h1 : (Array.extract (p.addRaw q) 0
      (CompPolyLib.trimLen (p.addRaw q) (p.addRaw q).size)).size ≤ (p.addRaw q).size := by simp
  rw [size_addRaw] at *
  omega

/-- `smul` over `K`: at most `273·|p| + 10`. -/
theorem smulK_cost (hP : Includes P smul.c28.costDeps) (r : K) (p : CPolynomial.Raw K) :
    machineCost P smul.c28.costIdx [encodeValue r, encodeValue p] ≤ 273 * p.size + 10 := by
  rw [smul.c28.costEq P hP]
  have hf := fun a ↦ RunsApp.of_spec (us := [encodeValue r]) (vs := [encodeValue a])
    (smul.c28.lam0.costSpec P (by includes) r a)
  have := listMap_le P Auto.List.map.c29.costIdx (.closure smul.c28.lam0.costIdx [encodeValue r])
    (Auto.List.map.c29.costEq_nil P (by includes) _ _ hf)
    (Auto.List.map.c29.costEq_cons P (by includes) _ _ hf) 258 p.toList
    (fun a _ ↦ by rw [appCost_fn, List.singleton_append, smul.c28.lam0.costEq P (by includes)])
  simp only [Array.length_toList, List.length_map] at this ⊢
  omega

/-- `mulPowX` over `K`: `2·i + |p| + 5`. -/
theorem mulPowXK_cost (hP : Includes P mulPowX.c41.costDeps) (i : ℕ) (p : CPolynomial.Raw K) :
    machineCost P mulPowX.c41.costIdx [encodeValue i, encodeValue p] = 2 * i + p.size + 5 := by
  rw [mulPowX.c41.costEq P hP]
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
theorem mulRawK_cost (hP : Includes P mulRaw.c36.costDeps) (p q : CPolynomial.Raw K)
    (hp : p.size < 2 ^ 62) (hq : q.size < 2 ^ 62) :
    machineCost P mulRaw.c36.costIdx [encodeValue p, encodeValue q] ≤
      302 * (q.size * p.size) + 30 * (p.size * p.size) + 102 * p.size + 20 := by
  rw [mulRaw.c36.costEq P hP]
  have hz := zipIdx_cost P (by includes) p.toList 0 (by simp; omega)
  have hf := listFoldl_le P (by includes) _ (.closure mulRaw.c36.lam0.costIdx [encodeValue q])
    (fun acc x ↦ RunsApp.of_spec (us := [encodeValue q]) (vs := [encodeValue acc, encodeValue x])
      (mulRaw.c36.lam0.costSpec P (by includes) q acc x))
    (302 * q.size + 30 * p.size + 70) (fun acc ↦ acc.size ≤ p.size + q.size)
    (Array.zipIdx p).toList (CPolynomial.Raw.mk #[]) (by simp)
    (fun acc hacc x hx ↦ by
      have hi := mem_zipIdx_lt hx
      obtain ⟨a, i⟩ := x
      dsimp only at hi ⊢
      refine ⟨?_, ?_⟩
      · rw [size_addRaw, size_mulPowX, size_smul]; omega
      · rw [appCost_fn, List.singleton_append, mulRaw.c36.lam0.costEq P (by includes)]
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

/-- **The product over `K`** (`mul`: `mulRaw`, the trim; the bound from when it was computed thrice): at most
`906·|q|·|p| + 90·|p|² + 330·|p| + 23·|q| + 90`. -/
theorem mulK_cost (hP : Includes P mul.c35.costDeps) (p q : CPolynomial.Raw K)
    (hp : p.size < 2 ^ 61) (hq : q.size < 2 ^ 61) :
    machineCost P mul.c35.costIdx [encodeValue p, encodeValue q] ≤
      906 * (q.size * p.size) + 90 * (p.size * p.size) + 330 * p.size + 23 * q.size + 90 := by
  rw [mul.c35.costEq P hP]
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

/-- `List.beq` against the empty list: at most `7`. -/
theorem beqNilK_cost (hP : Includes P Auto.List.beq.c4.costDeps) (a : List K) :
    machineCost P Auto.List.beq.c4.costIdx [encodeValue a, encodeValue ([] : List K)] ≤ 7 := by
  cases a with
  | nil => rw [Auto.List.beq.c4.costEq_nil P hP]; simp
  | cons x a => rw [Auto.List.beq.c4.costEq_cons P hP]; simp

/-- `trimLen` over `K[X]`: at most `(3·A + 40)·n + 6`, entries of at most `A` coefficients. -/
theorem trimLenB_cost (hP : Includes P Auto.LeanVM.Cost.CompPolyLib.trimLen.c88.costDeps)
    (p : Array (CPolynomial K)) (A : ℕ) (hA : ∀ x ∈ p, x.val.size ≤ A) :
    ∀ n : ℕ, n < 2 ^ 63 →
      machineCost P Auto.LeanVM.Cost.CompPolyLib.trimLen.c88.costIdx [encodeValue p, encodeValue n] ≤
        (3 * A + 40) * n + 6 := by
  intro n
  induction n with
  | zero => intro _; rw [Auto.LeanVM.Cost.CompPolyLib.trimLen.c88.costEq_zero P hP]; omega
  | succ k ih =>
    intro hk
    rw [Auto.LeanVM.Cost.CompPolyLib.trimLen.c88.costEq_succ P hP]
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

theorem InnerLe.mono {p : CPolynomial.Raw (CPolynomial K)} {A B : ℕ} (h : InnerLe p A)
    (hAB : A ≤ B) : InnerLe p B := fun x hx ↦ (h x hx).trans hAB

/-- `X^t·p` (`shiftX`): at most `25·t + 24·|p| + 22`. -/
theorem shiftXC_cost (hP : Includes P Auto.LeanVM.Extraction.Fast.shiftX.c102.costDeps) (t : ℕ)
    (p : CPolynomial K) (h : t + p.val.size < 2 ^ 60) :
    machineCost P Auto.LeanVM.Extraction.Fast.shiftX.c102.costIdx [encodeValue t, encodeValue p] ≤
      25 * t + 24 * p.val.size + 22 := by
  rw [Auto.LeanVM.Extraction.Fast.shiftX.c102.costEq P hP]
  have := ofArray_cost P (by includes) (Array.replicate t 0 ++ p.val) (by simp; omega)
  simp only [Array.size_append, Array.size_replicate] at this ⊢
  omega

end

end LeanVM.Cost.Bounds.Decoder
