module

public import LeanVM.Cost.Bounds.Basic
public import LeanVM.Cost.Extractor.Runner

/-!
# Bounds: the novel-basis transforms, the pruning and the stacks

The functions the fast path (`fastStacksFast`) and the decoder's pruning (`pruneUpToDistinct`,
`decodeStacksDistinct`) share, compiled in the decoder's chain (`Cost/Extractor/Decode.lean`), and
the list functions they call. With `N = 2^m` the buffer:

* `ofFnFrom_cost`: `Array.ofFn` of `n` entries, `B + 18` per entry; `rangeLoop_cost`,
  `reverseAux_cost`, `filter_cost`, `filterMap_cost`, `map_cost`, `foldr_cost`, `flatten_cost`;
* `subspacePoly_cost` (`276·2^j + 15`), `invK_cost` (`19676`), `novelTwiddles_cost`
  (`430·N + 19730`);
* **`novelInvStage_cost`**, **`novelFwdStage_cost`** (`750·N + 19760` per butterfly stage),
  **`novelInv_cost`** (`κ` stages over `2^κ`), **`novelFwd_cost`** (`κ` stages over `2^(κ+R)`);
* **`pruneStep_cost`**: `|st|·(|L|·((B + 29)·n + 9·U + 61) + 32) + 16` for `|st|` survivors of at
  most `n` columns and `U` lanes, `|L|` candidates, `B` the symbol's price;
* **`stackOf_cost`**: `(15·|cs| + 56)·2^μ + 19`.

Word-size hypotheses: the buffers below `2^62` entries.
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Cost.Library LeanVM.Parameters LeanVM.Extraction

public section

variable (P : Program)

theorem limbs_two_pow {k : ℕ} (hk : k < 64) : limbs (2 ^ k) = 1 :=
  limbs_of_lt (Nat.pow_lt_pow_right (by norm_num) hk)

theorem limbs_shift {k : ℕ} (hk : k < 64) : limbs (1 <<< k) = 1 := by
  rw [Nat.one_shiftLeft]; exact limbs_two_pow hk

theorem ofFnFrom_length {α : Type} {n : ℕ} (f : Fin n → α) : (Rewrite.ofFnFrom f 0).length = n := by
  rw [Rewrite.ofFnFrom_eq f (n - 0) 0 rfl]; simp

/-! ## List functions -/

/-- `Array.ofFn` through `ofFnFrom` (`ofFnFrom.c117`): `B + 18` per entry, `6` at the end. -/
theorem ofFnFrom_cost (hP : Includes P Auto.LeanVM.Cost.Rewrite.ofFnFrom.c117.costDeps)
    {α : Type} [Enc α] {n : ℕ} (hn : n < 2 ^ 64) (f : Fin n → α) (fVal : Val)
    (hf : ∀ a : Fin n, RunsApp P fVal [enc a] (enc (f a))) (B : ℕ)
    (hB : ∀ a : Fin n, appCost P fVal [enc a] ≤ B) :
    ∀ i, i ≤ n → machineCost P Auto.LeanVM.Cost.Rewrite.ofFnFrom.c117.costIdx [enc n, fVal, enc i] ≤
      (B + 18) * (n - i) + 6 := by
  intro i hi
  induction hk : n - i generalizing i with
  | zero =>
    rw [Auto.LeanVM.Cost.Rewrite.ofFnFrom.c117.costEq P hP f fVal hf i,
      limbs_of_lt (by omega : i < 2 ^ 64), limbs_of_lt hn]
    simp only [show ¬i < n by omega, ↓reduceDIte]
    omega
  | succ k ih =>
    rw [Auto.LeanVM.Cost.Rewrite.ofFnFrom.c117.costEq P hP f fVal hf i]
    simp only [show i < n by omega, ↓reduceDIte]
    have h1 := ih (i + 1) (by omega) (by omega)
    have h2 := hB ⟨i, by omega⟩
    rw [limbs_of_lt (by omega : i < 2 ^ 64), limbs_of_lt hn]
    simp only [max_self]
    nlinarith

/-- `List.range` (`range.loop.c20`): `17` per element, `6` at the end. -/
theorem rangeLoop_cost (hP : Includes P Auto.List.range.loop.c20.costDeps) :
    ∀ (n : ℕ) (l : List ℕ), n < 2 ^ 64 →
      machineCost P Auto.List.range.loop.c20.costIdx [enc n, enc l] ≤ 17 * n + 6 := by
  intro n
  induction n with
  | zero => intro l _; rw [Auto.List.range.loop.c20.costEq_zero P hP]
  | succ n ih =>
    intro l hn
    rw [Auto.List.range.loop.c20.costEq_succ P hP, limbs_of_lt hn]
    have := ih (n :: l) (by omega)
    omega

/-- `List.reverseAux` (`reverseAux.c23`): `9` per element, `3` at the end. -/
theorem reverseAux_cost (hP : Includes P Auto.List.reverseAux.c23.costDeps) {α : Type} [Enc α] :
    ∀ (l acc : List α), machineCost P Auto.List.reverseAux.c23.costIdx [enc l, enc acc] ≤
      9 * l.length + 3 := by
  intro l
  induction l with
  | nil => intro acc; rw [Auto.List.reverseAux.c23.costEq_nil P hP]; omega
  | cons x l ih =>
    intro acc
    rw [Auto.List.reverseAux.c23.costEq_cons P hP]
    have := ih (x :: acc)
    simp only [List.length_cons]
    omega

/-- `List.length` (`length.c229`): `7` per element, `3` at the end, for word-sized lists. -/
theorem listLength_cost (hP : Includes P Auto.List.length.c229.costDeps) {α : Type} [Enc α] :
    ∀ l : List α, l.length < 2 ^ 64 →
      machineCost P Auto.List.length.c229.costIdx [enc l] ≤ 7 * l.length + 3 := by
  intro l
  induction l with
  | nil => intro _; rw [Auto.List.length.c229.costEq_nil P hP]; omega
  | cons x l ih =>
    intro hl
    simp only [List.length_cons] at hl
    rw [Auto.List.length.c229.costEq_cons P hP, limbs_of_lt (by omega : l.length < 2 ^ 64)]
    have := ih (by omega)
    simp only [List.length_cons]
    omega

/-- `List.append` (`append.c264`): `9` per element of the first, `3` at the end. -/
theorem append_cost (hP : Includes P Auto.List.append.c264.costDeps) {α : Type} [Enc α] :
    ∀ (a b : List α), machineCost P Auto.List.append.c264.costIdx [enc a, enc b] ≤
      9 * a.length + 3 := by
  intro a
  induction a with
  | nil => intro b; rw [Auto.List.append.c264.costEq_nil P hP]; omega
  | cons x a ih =>
    intro b
    rw [Auto.List.append.c264.costEq_cons P hP]
    have := ih b
    simp only [List.length_cons]
    omega

/-- `List.filter` (`filter.c140`): `13` per element and the predicate's price, `3` at the end. -/
theorem filter_cost (hP : Includes P Auto.List.filter.c140.costDeps) {α : Type} [Enc α]
    (p : α → Bool) (pVal : Val) (hp : ∀ a : α, RunsApp P pVal [enc a] (enc (p a))) (B : ℕ)
    (hB : ∀ a : α, appCost P pVal [enc a] ≤ B) :
    ∀ l : List α, machineCost P Auto.List.filter.c140.costIdx [pVal, enc l] ≤ (B + 13) * l.length + 3 := by
  intro l
  induction l with
  | nil => rw [Auto.List.filter.c140.costEq_nil P hP p pVal hp]; omega
  | cons x l ih =>
    rw [Auto.List.filter.c140.costEq_cons P hP p pVal hp]
    have := hB x
    simp only [List.length_cons]
    cases p x <;> dsimp only <;> nlinarith

/-- `List.filterMap` (`filterMap.c131`): `13` per element and the closure's price, `3` at the end. -/
theorem filterMap_cost (hP : Includes P Auto.List.filterMap.c131.costDeps) {α β : Type} [Enc α]
    [Enc β] (f : α → Option β) (fVal : Val) (hf : ∀ a : α, RunsApp P fVal [enc a] (enc (f a))) (B : ℕ) :
    ∀ l : List α, (∀ a ∈ l, appCost P fVal [enc a] ≤ B) →
      machineCost P Auto.List.filterMap.c131.costIdx [fVal, enc l] ≤ (B + 13) * l.length + 3 := by
  intro l
  induction l with
  | nil => intro _; rw [Auto.List.filterMap.c131.costEq_nil P hP f fVal hf]; omega
  | cons x l ih =>
    intro hB
    rw [Auto.List.filterMap.c131.costEq_cons P hP f fVal hf]
    have h1 := ih fun a ha ↦ hB a (by simp [ha])
    have h2 := hB x (by simp)
    simp only [List.length_cons]
    cases f x <;> dsimp only <;> nlinarith

/-- `List.map` (`map.c12`): `11` per element and the closure's price, `3` at the end. -/
theorem map_cost (hP : Includes P Auto.List.map.c12.costDeps) {α β : Type} [Enc α] [Enc β]
    (f : α → β) (fVal : Val) (hf : ∀ a : α, RunsApp P fVal [enc a] (enc (f a))) (B : ℕ) :
    ∀ l : List α, (∀ a ∈ l, appCost P fVal [enc a] ≤ B) →
      machineCost P Auto.List.map.c12.costIdx [fVal, enc l] ≤ (B + 11) * l.length + 3 :=
  listMap_le P _ fVal (Auto.List.map.c12.costEq_nil P hP f fVal hf)
    (fun x l ↦ Auto.List.map.c12.costEq_cons P hP f fVal hf x l) B

/-- `List.foldr` (`foldr.c86`): `9` per element and the closure's price, `3` at the end. -/
theorem foldr_cost (hP : Includes P Auto.List.foldr.c86.costDeps) {α β : Type} [Enc α] [Enc β]
    (f : α → β → β) (fVal : Val) (hf : ∀ (a : α) (b : β), RunsApp P fVal [enc a, enc b] (enc (f a b))) (B : ℕ)
    (init : β) : ∀ l : List α, (∀ a ∈ l, ∀ b : β, appCost P fVal [enc a, enc b] ≤ B) →
      machineCost P Auto.List.foldr.c86.costIdx [fVal, enc init, enc l] ≤ (B + 9) * l.length + 3 := by
  intro l
  induction l with
  | nil => intro _; rw [Auto.List.foldr.c86.costEq_nil P hP f fVal hf]; omega
  | cons x l ih =>
    intro hB
    rw [Auto.List.foldr.c86.costEq_cons P hP f fVal hf]
    have h1 := ih fun a ha ↦ hB a (by simp [ha])
    have h2 := hB x (by simp) (l.foldr f init)
    simp only [List.length_cons]
    nlinarith

/-- `List.flatten` (`flatten.c263`): `9` per element of the pieces and `9` per piece, `3`. -/
theorem flatten_cost (hP : Includes P Auto.List.flatten.c263.costDeps) {α : Type} [Enc α]
    (M : ℕ) : ∀ ls : List (List α), (∀ l ∈ ls, l.length ≤ M) →
      machineCost P Auto.List.flatten.c263.costIdx [enc ls] ≤ (9 * M + 9) * ls.length + 3 := by
  intro ls
  induction ls with
  | nil => intro _; rw [Auto.List.flatten.c263.costEq_nil P hP]; omega
  | cons l ls ih =>
    intro hM
    rw [Auto.List.flatten.c263.costEq_cons P hP]
    have h1 := ih fun a ha ↦ hM a (by simp [ha])
    have h2 := append_cost P (by includes) l ls.flatten
    have h3 := hM l (by simp)
    simp only [List.length_cons]
    nlinarith

/-- `List.flatten` of a `List.map`: `9` per element of the pieces and `9` per piece, `3`. -/
theorem flatten_map_cost (hP : Includes P Auto.List.flatten.c263.costDeps) {α σ : Type} [Enc α]
    (M : ℕ) (f : σ → List α) (st : List σ) (hM : ∀ s ∈ st, (f s).length ≤ M) :
    machineCost P Auto.List.flatten.c263.costIdx [enc (st.map f)] ≤ (9 * M + 9) * st.length + 3 := by
  have := flatten_cost P hP M (st.map f) (fun l hl ↦ by
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hl
    exact hM s hs)
  simpa using this

/-- `List.get?` (`get?Internal.c275`): `15` per element, `3` at the end, for word-sized indices. -/
theorem getInternal_cost (hP : Includes P Auto.List.get?Internal.c275.costDeps) {α : Type} [Enc α] :
    ∀ (l : List α) (k : ℕ), k < 2 ^ 64 →
      machineCost P Auto.List.get?Internal.c275.costIdx [enc l, enc k] ≤ 15 * l.length + 3 := by
  intro l
  induction l with
  | nil => intro k _; rw [Auto.List.get?Internal.c275.costEq_nil P hP]; omega
  | cons x l ih =>
    intro k hk
    rw [Auto.List.get?Internal.c275.costEq_cons P hP, limbs_of_lt hk]
    cases k with
    | zero => simp only [List.length_cons, Nat.rec_zero]; omega
    | succ k =>
      have := ih k (by omega)
      simp only [List.length_cons]
      omega

/-- `List.getD` (`getD.c274`): `15` per element, `8` at the end. -/
theorem getD_cost (hP : Includes P Auto.List.getD.c274.costDeps) {α : Type} [Enc α]
    (l : List α) (k : ℕ) (hk : k < 2 ^ 64) (d : α) :
    machineCost P Auto.List.getD.c274.costIdx [enc l, enc k, enc d] ≤ 15 * l.length + 8 := by
  rw [Auto.List.getD.c274.costEq P hP]
  have := getInternal_cost P (by includes) l k hk
  generalize l[k]? = o
  cases o <;> dsimp only <;> omega

/-! ## Field arithmetic: the subspace polynomial and the inverse -/

/-- A product over `range n` (`prodRange.c221`): `B + 272` per factor, `6` at the end. -/
theorem prodRange_cost (hP : Includes P Auto.LeanVM.Cost.Rewrite.prodRange.c221.costDeps)
    (f : ℕ → K) (fVal : Val) (hf : ∀ a : ℕ, RunsApp P fVal [enc a] (enc (f a))) (B : ℕ)
    (hB : ∀ a : ℕ, appCost P fVal [enc a] ≤ B) :
    ∀ n, n < 2 ^ 64 →
      machineCost P Auto.LeanVM.Cost.Rewrite.prodRange.c221.costIdx [fVal, enc n] ≤
        (B + 272) * n + 6 := by
  intro n
  induction n with
  | zero => intro _; rw [Auto.LeanVM.Cost.Rewrite.prodRange.c221.costEq_zero P hP f fVal hf]; omega
  | succ n ih =>
    intro hn
    rw [Auto.LeanVM.Cost.Rewrite.prodRange.c221.costEq_succ P hP f fVal hf, limbs_of_lt hn]
    have := ih (by omega)
    have := hB n
    nlinarith

/-- **The subspace polynomial** `W_j(x)` (`subspacePoly.c220`): `2^j` products, at most
`276·2^j + 15`. -/
theorem subspacePoly_cost (hP : Includes P Auto.LeanVM.Extraction.subspacePoly.c220.costDeps)
    (j : ℕ) (hj : j < 64) (x : K) :
    machineCost P Auto.LeanVM.Extraction.subspacePoly.c220.costIdx [enc j, enc x] ≤
      276 * 2 ^ j + 15 := by
  rw [Auto.LeanVM.Extraction.subspacePoly.c220.costEq P hP, limbs_shift hj,
    limbs_of_lt (by omega : j < 2 ^ 64)]
  have := prodRange_cost P (by includes) _
    (.fn Auto.LeanVM.Extraction.subspacePoly.c220.lam0.costIdx [enc x])
    (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.subspacePoly.c220.lam0.costSpec P
      (by includes) x a)) 4
    (fun a ↦ by
      rw [appCost_fn, List.singleton_append,
        Auto.LeanVM.Extraction.subspacePoly.c220.lam0.costEq P (by includes)])
    (2 ^ j) (Nat.pow_lt_pow_right (by norm_num) hj)
  omega

theorem powTwoPow34_cost (hP : Includes P Auto.BF64.powTwoPow.c34.costDeps) :
    ∀ (k : ℕ) (a : BF64), k < 2 ^ 64 →
      machineCost P Auto.BF64.powTwoPow.c34.costIdx [enc a, enc k] = 6 + 270 * k := by
  intro k
  induction k with
  | zero => intro a _; rw [Auto.BF64.powTwoPow.c34.costEq_zero P hP]
  | succ k ih =>
    intro a hk
    rw [Auto.BF64.powTwoPow.c34.costEq_succ P hP, ih (a * a) (by omega)]
    cost_simp
    omega

/-- **The inverse in `K`** (Itoh–Tsujii, `invItohTsujii.c33`): at most `19676`. -/
theorem invK_cost (hP : Includes P Auto.BF64.invItohTsujii.c33.costDeps) (a : BF64) :
    machineCost P Auto.BF64.invItohTsujii.c33.costIdx [enc a] ≤ 19676 := by
  have h6 : Includes P Auto.BF64.powTwoPow.c34.costDeps := by includes
  rw [Auto.BF64.invItohTsujii.c33.costEq P hP]
  simp (disch := omega) only [powTwoPow34_cost P h6]
  split_ifs <;> omega

/-- `Nat.testBit` (`testBit.c225`): `13` on words. -/
theorem testBit_cost (hP : Includes P Auto.Nat.testBit.c225.costDeps) (a b : ℕ) (ha : a < 2 ^ 64)
    (hb : b < 2 ^ 64) : machineCost P Auto.Nat.testBit.c225.costIdx [enc a, enc b] ≤ 13 := by
  rw [Auto.Nat.testBit.c225.costEq P hP, limbs_of_lt ha, limbs_of_lt hb,
    limbs_of_lt (lt_of_le_of_lt (Nat.shiftRight_le a b) ha),
    limbs_of_lt (lt_of_le_of_lt (Nat.and_le_left (n := 1) (m := a >>> b)) (by norm_num))]

/-! ## The novel-basis transforms -/

theorem pow_split {i m : ℕ} (h : i < m) : 2 ^ i * 2 ^ (m - (i + 1)) * 2 = 2 ^ m := by
  rw [← pow_add, ← pow_succ]; congr 1; omega

/-- **Stage `i`'s twiddles** over `2^m` (`novelTwiddles.c219`): `2^(m−i−1)` subspace polynomials
of `2^i` factors and one inverse: at most `430·2^m + 19730`. -/
theorem novelTwiddles_cost (hP : Includes P Auto.LeanVM.Extraction.novelTwiddles.c219.costDeps)
    (m i : ℕ) (hi : i < m) (hm : m ≤ 62) :
    machineCost P Auto.LeanVM.Extraction.novelTwiddles.c219.costIdx [enc m, enc i] ≤
      430 * 2 ^ m + 19730 := by
  rw [Auto.LeanVM.Extraction.novelTwiddles.c219.costEq P hP]
  have hsub := subspacePoly_cost P (by includes) i (by omega) (K.ofBits (2 ^ i))
  have hinv := invK_cost P (by includes) (subspacePoly i (K.ofBits (2 ^ i)))
  have hw : 2 ^ (m - (i + 1)) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hof := ofFnFrom_cost P (by includes) hw _
    (.fn Auto.LeanVM.Extraction.novelTwiddles.c219.lam0.costIdx
      [enc m, enc i, enc (subspacePoly i (K.ofBits (2 ^ i)))⁻¹])
    (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.novelTwiddles.c219.lam0.costSpec P
      (by includes) m i _ a)) (276 * 2 ^ i + 286)
    (fun a ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [Auto.LeanVM.Extraction.novelTwiddles.c219.lam0.costEq P (by includes),
        limbs_of_lt (by omega : i < 2 ^ 64), limbs_shift (by omega : i + 1 < 64),
        limbs_of_lt (by omega : i + 1 < 2 ^ 64), limbs_two_pow (by omega : i + 1 < 64),
        limbs_of_lt (by have := a.isLt; omega : (a : ℕ) < 2 ^ 64)]
      have := subspacePoly_cost P (by includes) i (by omega) (K.ofBits (↑a * 2 ^ (i + 1)))
      omega) 0 (Nat.zero_le _)
  rw [ofFnFrom_length, limbs_shift (by omega : i < 64), limbs_of_lt (by omega : i < 2 ^ 64),
    limbs_of_lt (by omega : m < 2 ^ 64), limbs_of_lt (by omega : i + 1 < 2 ^ 64),
    limbs_shift (by omega : m - (i + 1) < 64), limbs_of_lt (by omega : m - (i + 1) < 2 ^ 64)]
  have e := pow_split hi
  have h1 : 2 ^ i * 2 ≤ 2 ^ m := by
    have := Nat.pow_le_pow_right (n := 2) (by norm_num) (show i + 1 ≤ m by omega)
    rw [pow_succ] at this; omega
  have h2 : 2 ^ (m - (i + 1)) * 2 ≤ 2 ^ m := by
    have := Nat.pow_le_pow_right (n := 2) (by norm_num) (show m - (i + 1) + 1 ≤ m by omega)
    rw [pow_succ] at this; omega
  simp only [max_self, Nat.sub_zero] at hof ⊢
  nlinarith

/-- **An inverse butterfly stage** over `2^m` (`novelInvStage.c246`): at most `750·2^m + 19760`. -/
theorem novelInvStage_cost (hP : Includes P Auto.LeanVM.Extraction.novelInvStage.c246.costDeps)
    (m i : ℕ) (hi : i < m) (hm : m ≤ 62) (b : Array K) :
    machineCost P Auto.LeanVM.Extraction.novelInvStage.c246.costIdx [enc m, enc i, enc b] ≤
      760 * 2 ^ m + 19760 := by
  rw [Auto.LeanVM.Extraction.novelInvStage.c246.costEq P hP]
  have htw := novelTwiddles_cost P (by includes) m i hi hm
  have hN : 2 ^ m < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hof := ofFnFrom_cost P (by includes) hN _
    (.fn Auto.LeanVM.Extraction.novelInvStage.c246.lam0.costIdx
      [enc m, enc i, enc b, enc (novelTwiddles m i)])
    (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.novelInvStage.c246.lam0.costSpec P
      (by includes) m i b _ a)) 310
    (fun a ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      have ha : (a : ℕ) < 2 ^ 64 := by have := a.isLt; omega
      rw [Auto.LeanVM.Extraction.novelInvStage.c246.lam0.costEq P (by includes),
        limbs_of_lt (by omega : i < 2 ^ 64), limbs_shift (by omega : i + 1 < 64),
        limbs_of_lt (by omega : i + 1 < 2 ^ 64), limbs_two_pow (by omega : i + 1 < 64),
        limbs_of_lt ha, limbs_shift (by omega : i < 64), limbs_two_pow (by omega : i < 64)]
      have := testBit_cost P (by includes) a i ha (by omega)
      split_ifs <;> simp only [max_self] <;> omega) 0 (Nat.zero_le _)
  rw [ofFnFrom_length, limbs_shift (by omega : m < 64), limbs_of_lt (by omega : m < 2 ^ 64)]
  simp only [Nat.sub_zero] at hof
  omega

/-- **A forward butterfly stage** over `2^m` (`novelFwdStage.c218`): at most `750·2^m + 19760`. -/
theorem novelFwdStage_cost (hP : Includes P Auto.LeanVM.Extraction.novelFwdStage.c218.costDeps)
    (m i : ℕ) (hi : i < m) (hm : m ≤ 62) (b : Array K) :
    machineCost P Auto.LeanVM.Extraction.novelFwdStage.c218.costIdx [enc m, enc i, enc b] ≤
      760 * 2 ^ m + 19760 := by
  rw [Auto.LeanVM.Extraction.novelFwdStage.c218.costEq P hP]
  have htw := novelTwiddles_cost P (by includes) m i hi hm
  have hN : 2 ^ m < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hof := ofFnFrom_cost P (by includes) hN _
    (.fn Auto.LeanVM.Extraction.novelFwdStage.c218.lam0.costIdx
      [enc m, enc i, enc b, enc (novelTwiddles m i)])
    (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.novelFwdStage.c218.lam0.costSpec P
      (by includes) m i b _ a)) 310
    (fun a ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      have ha : (a : ℕ) < 2 ^ 64 := by have := a.isLt; omega
      rw [Auto.LeanVM.Extraction.novelFwdStage.c218.lam0.costEq P (by includes),
        limbs_of_lt (by omega : i < 2 ^ 64), limbs_shift (by omega : i + 1 < 64),
        limbs_of_lt (by omega : i + 1 < 2 ^ 64), limbs_two_pow (by omega : i + 1 < 64),
        limbs_of_lt ha, limbs_shift (by omega : i < 64), limbs_two_pow (by omega : i < 64)]
      have := testBit_cost P (by includes) a i ha (by omega)
      split_ifs <;> simp only [max_self] <;> omega) 0 (Nat.zero_le _)
  rw [ofFnFrom_length, limbs_shift (by omega : m < 64), limbs_of_lt (by omega : m < 2 ^ 64)]
  simp only [Nat.sub_zero] at hof
  omega

/-- **The inverse transform** over `2^κ` (`novelInv κ y`, a fold of `novelInvStage` through
`toNovelFast.c244.lam0` over `range κ`): at most `κ·(760·2^κ + 19773) + 3`. -/
theorem novelInv_cost (hP : Includes P Auto.LeanVM.Extraction.Fast.toNovelFast.c244.lam0.costDeps)
    (hF : Includes P listFoldl.costDeps) (κ : ℕ) (hκ : κ ≤ 62) (y : Array K) :
    machineCost P listFoldl.costIdx
        [.fn Auto.LeanVM.Extraction.Fast.toNovelFast.c244.lam0.costIdx [enc κ], enc y,
          enc (List.range κ)] ≤ κ * (760 * 2 ^ κ + 19773) + 3 := by
  have := listFoldl_le P hF _ (.fn Auto.LeanVM.Extraction.Fast.toNovelFast.c244.lam0.costIdx [enc κ])
    (fun a b ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.Fast.toNovelFast.c244.lam0.costSpec P
      (by includes) κ a b)) (760 * 2 ^ κ + 19764) (fun _ ↦ True) (List.range κ) y trivial
    (fun acc _ i hi ↦ ⟨trivial, by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [Auto.LeanVM.Extraction.Fast.toNovelFast.c244.lam0.costEq P (by includes)]
      have := novelInvStage_cost P (by includes) κ i (List.mem_range.1 hi) hκ acc
      omega⟩)
  rw [List.length_range] at this
  nlinarith

/-- **The forward transform** (`novelFwd.c216`): the `2^κ` coefficients tiled over
`N = 2^(κ+R)` and `κ` forward stages: at most `κ·(760·N + 19793) + 30·N + 42`. -/
theorem novelFwd_cost (hP : Includes P Auto.LeanVM.Extraction.novelFwd.c216.costDeps)
    (κ R : ℕ) (hκR : κ + R ≤ 62) (c : Array K) :
    machineCost P Auto.LeanVM.Extraction.novelFwd.c216.costIdx [enc κ, enc R, enc c] ≤
      κ * (760 * 2 ^ (κ + R) + 19793) + 30 * 2 ^ (κ + R) + 42 := by
  rw [Auto.LeanVM.Extraction.novelFwd.c216.costEq P hP]
  have hN : 2 ^ (κ + R) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hof := ofFnFrom_cost P (by includes) hN _
    (.fn Auto.LeanVM.Extraction.novelFwd.c216.lam1.costIdx [enc κ, enc R, enc c])
    (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.novelFwd.c216.lam1.costSpec P
      (by includes) κ R c a)) 11
    (fun a ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      have ha : (a : ℕ) < 2 ^ 64 := by have := a.isLt; omega
      rw [Auto.LeanVM.Extraction.novelFwd.c216.lam1.costEq P (by includes),
        limbs_shift (by omega : κ < 64), limbs_of_lt (by omega : κ < 2 ^ 64), limbs_of_lt ha,
        limbs_two_pow (by omega : κ < 64)]) 0 (Nat.zero_le _)
  have hr := rangeLoop_cost P (by includes) κ [] (by omega)
  have hfr := foldr_cost P (by includes) _
    (.fn Auto.LeanVM.Extraction.novelFwd.c216.lam0.costIdx [enc κ, enc R])
    (fun a b ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.novelFwd.c216.lam0.costSpec P
      (by includes) κ R a b)) (760 * 2 ^ (κ + R) + 19767)
    (Array.ofFn fun p : Fin (2 ^ (κ + R)) ↦ c.getD (p % 2 ^ κ) 0) (List.range κ)
    (fun i hi b ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [Auto.LeanVM.Extraction.novelFwd.c216.lam0.costEq P (by includes),
        limbs_of_lt (by omega : κ < 2 ^ 64), limbs_of_lt (by omega : R < 2 ^ 64)]
      have := novelFwdStage_cost P (by includes) (κ + R) i (by have := List.mem_range.1 hi; omega)
        hκR b
      simp only [max_self]
      omega)
  rw [ofFnFrom_length, limbs_of_lt (by omega : κ < 2 ^ 64), limbs_of_lt (by omega : R < 2 ^ 64),
    limbs_shift (by omega : κ + R < 64), limbs_of_lt (by omega : κ + R < 2 ^ 64)]
  rw [List.length_range] at hfr
  simp only [Nat.sub_zero, max_self] at hof ⊢
  nlinarith

/-! ## The pruning and the stacks -/

/-- **One pruning step** (`pruneStep.c262`): for `|st|` survivors of at most `n` columns and `U`
lanes each, `|L|` candidates, and the symbol's price at most `B`: at most
`|st|·(|L|·((B + 29)·n + 9·U + 61) + 32) + 16`. -/
theorem pruneStep_cost (hP : Includes P Auto.LeanVM.Extraction.pruneStep.c262.costDeps) (A : ℕ)
    (hA : A < 2 ^ 64) (sym : ℕ → K) (symVal : Val) (hsym : ∀ a : ℕ, RunsApp P symVal [enc a] (enc (sym a)))
    (B : ℕ) (hB : ∀ v : ℕ, appCost P symVal [enc v] ≤ B) (L : List (Array K × Array K))
    (st : List (List (Array K) × List ℕ)) (n U : ℕ) (hn : n < 2 ^ 64)
    (hst : ∀ s ∈ st, s.2.length ≤ n ∧ s.1.length ≤ U) :
    machineCost P Auto.LeanVM.Extraction.pruneStep.c262.costIdx [enc A, symVal, enc L, enc st] ≤
      st.length * (L.length * ((B + 29) * n + 9 * U + 61) + 32) + 16 := by
  rw [Auto.LeanVM.Extraction.pruneStep.c262.costEq P hP A sym symVal hsym]
  -- one survivor and one candidate
  have hce : ∀ s ∈ st, ∀ ce : Array K × Array K,
      appCost P (.fn Auto.LeanVM.Extraction.pruneStep.c262.lam0.lam0.costIdx [enc A, symVal, enc s])
        [enc ce] ≤ (B + 29) * n + 9 * U + 39 := by
    intro s hs ce
    obtain ⟨h2, h1⟩ := hst s hs
    simp only [appCost_fn, List.cons_append, List.nil_append]
    rw [Auto.LeanVM.Extraction.pruneStep.c262.lam0.lam0.costEq P (by includes) A sym symVal hsym]
    have hf := filter_cost P (by includes) _
      (.fn Auto.LeanVM.Extraction.pruneStep.c262.lam0.lam0.lam0.costIdx [symVal, enc ce])
      (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.pruneStep.c262.lam0.lam0.lam0.costSpec P
        (by includes) sym symVal hsym ce a)) (B + 9)
      (fun v ↦ by
        simp only [appCost_fn, List.cons_append, List.nil_append]
        rw [Auto.LeanVM.Extraction.pruneStep.c262.lam0.lam0.lam0.costEq P (by includes) sym symVal
          hsym]
        have := hB v
        omega) s.2
    have hlf := List.length_filter_le (fun v ↦ decide (ce.2.getD v 0 = sym v)) s.2
    have hl := listLength_cost P (by includes)
      (List.filter (fun v ↦ decide (ce.2.getD v 0 = sym v)) s.2) (by omega)
    have ha := append_cost P (by includes) s.1 [ce.1]
    rw [limbs_of_lt hA, limbs_of_lt (by omega :
      (List.filter (fun v ↦ decide (ce.2.getD v 0 = sym v)) s.2).length < 2 ^ 64)]
    have : (B + 9 + 13) * s.2.length ≤ (B + 22) * n := Nat.mul_le_mul_left _ h2
    split_ifs <;> simp only [max_self] <;> nlinarith
  have hs : ∀ s ∈ st,
      appCost P (.fn Auto.LeanVM.Extraction.pruneStep.c262.lam0.costIdx [enc A, symVal, enc L])
        [enc s] ≤ ((B + 29) * n + 9 * U + 52) * L.length + 12 := by
    intro s hs
    simp only [appCost_fn, List.cons_append, List.nil_append]
    rw [Auto.LeanVM.Extraction.pruneStep.c262.lam0.costEq P (by includes) A sym symVal hsym]
    have := filterMap_cost P (by includes) _
      (.fn Auto.LeanVM.Extraction.pruneStep.c262.lam0.lam0.costIdx [enc A, symVal, enc s])
      (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.pruneStep.c262.lam0.lam0.costSpec P
        (by includes) A sym symVal hsym s a)) _ L (fun ce _ ↦ hce s hs ce)
    nlinarith
  have hm := map_cost P (by includes) _
    (.fn Auto.LeanVM.Extraction.pruneStep.c262.lam0.costIdx [enc A, symVal, enc L])
    (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.pruneStep.c262.lam0.costSpec P
      (by includes) A sym symVal hsym L a)) _ st hs
  refine (Nat.add_le_add_right (Nat.add_le_add hm
    (flatten_map_cost P (by includes) L.length _ st ?_)) 10).trans ?_
  · intro s _
    exact List.length_filterMap_le _ _
  · nlinarith

/-- **A stack from its lanes** (`stackOf.c272`): `2^μ` cells, each a lookup among the `|cs|`
lanes: at most `(15·|cs| + 56)·2^μ + 19`. -/
theorem stackOf_cost (hP : Includes P Auto.LeanVM.Extraction.stackOf.c272.costDeps) (μ : ℕ)
    (hμ : μ ≤ 62) (cs : List (Array K)) :
    machineCost P Auto.LeanVM.Extraction.stackOf.c272.costIdx [enc μ, enc cs] ≤
      (15 * cs.length + 56) * 2 ^ μ + 19 := by
  rw [Auto.LeanVM.Extraction.stackOf.c272.costEq P hP]
  have hN : 2 ^ μ < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hof := ofFnFrom_cost P (by includes) hN _
    (.fn Auto.LeanVM.Extraction.stackOf.c272.lam0.costIdx [enc μ, enc cs])
    (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.stackOf.c272.lam0.costSpec P
      (by includes) μ cs a)) (15 * cs.length + 37)
    (fun a ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      have ha : (a : ℕ) < 2 ^ 64 := by have := a.isLt; omega
      rw [Auto.LeanVM.Extraction.stackOf.c272.lam0.costEq P (by includes),
        limbs_of_lt (by omega : μ < 2 ^ 64),
        limbs_of_lt (by unfold Whir.initialFold; omega : Whir.initialFold < 2 ^ 64),
        limbs_shift (by omega : μ - Whir.initialFold < 64),
        limbs_of_lt (by omega : μ - Whir.initialFold < 2 ^ 64), limbs_of_lt ha,
        limbs_two_pow (by omega : μ - Whir.initialFold < 64)]
      have := getD_cost P (by includes) cs (a / 2 ^ (μ - Whir.initialFold))
        (lt_of_le_of_lt (Nat.div_le_self _ _) ha) #[]
      simp only [max_self]
      omega) 0 (Nat.zero_le _)
  rw [ofFnFrom_length, limbs_shift (by omega : μ < 64), limbs_of_lt (by omega : μ < 2 ^ 64)]
  simp only [Nat.sub_zero] at hof
  nlinarith

/-! ## The Johnson threshold: square roots on two-limb numbers -/

theorem limbs_le_two {x : ℕ} (h : x < 2 ^ 128) : limbs x ≤ 2 := by
  unfold limbs
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · have := (Nat.log2_lt (by omega)).2 h
    omega

/-- `Nat.log2` by halving (`log2Rec.c280`): at most `7 + 15·(log₂ n + 1)` below `2^128`. -/
theorem log2Rec_cost (hP : Includes P Auto.LeanVM.Cost.Rewrite.log2Rec.c280.costDeps) (n : ℕ)
    (hn : n < 2 ^ 128) :
    machineCost P Auto.LeanVM.Cost.Rewrite.log2Rec.c280.costIdx [enc n] ≤
      7 + 15 * (Nat.log2 n + 1) := by
  have := le_of_halving (α := ℕ) (fun x ↦ x < 2 ^ 128) id
    (fun x ↦ machineCost P Auto.LeanVM.Cost.Rewrite.log2Rec.c280.costIdx [enc x]) 15 7 ?hz ?h n hn
  · simpa using this
  · intro x hx h0
    simp only [id] at h0
    rw [Auto.LeanVM.Cost.Rewrite.log2Rec.c280.costEq P hP, limbs_of_lt (by omega : x < 2 ^ 64)]
    split_ifs <;> omega
  · intro x hx hpos
    simp only [id] at hpos
    rw [Auto.LeanVM.Cost.Rewrite.log2Rec.c280.costEq P hP]
    have h1 := limbs_le_two hx
    by_cases h2 : 2 ≤ x
    · right
      refine ⟨x / 2, show x / 2 < 2 ^ 128 by omega, by simp, ?_⟩
      simp only [h2, ↓reduceIte]
      have : Rewrite.log2Rec (x / 2) < 2 ^ 64 := by
        rw [← Rewrite.natLog2]
        have := Nat.log2_le_self (x / 2)
        have := (Nat.log2_lt (n := x) (k := 128) (by omega)).2 hx
        have := log2_mono (Nat.div_le_self x 2)
        omega
      rw [limbs_of_lt this]
      omega
    · left
      simp only [h2, ↓reduceIte]
      omega

/-- Newton's step from above, on naturals: never below `√n`. -/
theorem newton_ge (n g : ℕ) (hg : 0 < g) : Nat.sqrt n ≤ (g + n / g) / 2 := by
  have hs := Nat.sqrt_le n
  set s := Nat.sqrt n
  suffices 2 * s ≤ g + n / g by omega
  by_cases h : 2 * s ≤ g
  · exact le_trans h (Nat.le_add_right _ _)
  · obtain ⟨t, ht⟩ : ∃ t, t + g = 2 * s := ⟨2 * s - g, by omega⟩
    have key : t * g ≤ s * s := by
      have : (t : ℤ) * g ≤ (s : ℤ) * s := by
        have ht' : (t : ℤ) + g = 2 * s := by exact_mod_cast ht
        nlinarith [sq_nonneg ((t : ℤ) - g)]
      exact_mod_cast this
    have : t ≤ n / g := (Nat.le_div_iff_mul_le hg).2 (by omega)
    omega

/-- Newton's step from above halves the excess over `√n`. -/
theorem newton_half (n g : ℕ) (hg : Nat.sqrt n < g) :
    (g + n / g) / 2 - Nat.sqrt n ≤ (g - Nat.sqrt n) / 2 := by
  have hs := Nat.lt_succ_sqrt n
  have : n / g ≤ Nat.sqrt n := by
    have : n / g < Nat.sqrt n + 1 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      calc n < (Nat.sqrt n).succ * (Nat.sqrt n).succ := hs
        _ ≤ (Nat.sqrt n + 1) * g := Nat.mul_le_mul_left _ (by omega)
    omega
  omega

/-- **Newton's iteration** (`Nat.sqrt.iter.c279`) from a guess `g ≥ √n`, `n < 2^127`, `g ≤ 2^126`: at most `23 + 25·(log₂(g − √n) + 1)` (`√n ≤ g`: each step halves the excess, `newton_half`). -/
theorem sqrtIter_cost (hP : Includes P Auto.Nat.sqrt.iter.c279.costDeps) (n : ℕ) (hn : n < 2 ^ 127) :
    ∀ g, Nat.sqrt n ≤ g → g ≤ 2 ^ 126 →
      machineCost P Auto.Nat.sqrt.iter.c279.costIdx [enc n, enc g] ≤
        23 + 25 * (Nat.log2 (g - Nat.sqrt n) + 1) := by
  intro g hg hg1
  have hl : ∀ x, x < 2 ^ 128 → limbs x ≤ 2 := fun x h ↦ limbs_le_two h
  -- the common price of a step's arithmetic
  have hstep : ∀ g, g ≤ 2 ^ 126 →
      limbs n * limbs g + max (limbs g) (limbs (n / g)) + limbs (g + n / g) +
        max (limbs ((g + n / g) / 2)) (limbs g) ≤ 10 := by
    intro g hg1
    have h1 := hl n (by omega)
    have h2 := hl g (by omega)
    have h3 := hl (n / g) (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))
    have h4 := hl (g + n / g) (by have := Nat.div_le_self n g; omega)
    have h5 := hl ((g + n / g) / 2) (by have := Nat.div_le_self n g; omega)
    have : limbs n * limbs g ≤ 4 := by nlinarith
    omega
  have := le_of_halving (α := ℕ) (fun x ↦ Nat.sqrt n ≤ x ∧ x ≤ 2 ^ 126)
    (fun x ↦ x - Nat.sqrt n)
    (fun x ↦ machineCost P Auto.Nat.sqrt.iter.c279.costIdx [enc n, enc x]) 25 23 ?hz ?h g
    ⟨hg, hg1⟩
  · simpa using this
  · rintro x ⟨hx1, hx3⟩ h0
    rw [Auto.Nat.sqrt.iter.c279.costEq P hP]
    have := hstep x hx3
    rcases Nat.eq_zero_or_pos x with rfl | hx2
    · simp only [Nat.div_zero, Nat.add_zero, Nat.zero_div, Nat.lt_irrefl, ↓reduceDIte] at this ⊢
      omega
    · have := newton_ge n x hx2
      simp only [show ¬(x + n / x) / 2 < x by omega, ↓reduceDIte]
      omega
  · rintro x ⟨hx1, hx3⟩ hpos
    rw [Auto.Nat.sqrt.iter.c279.costEq P hP]
    have hx2 : 0 < x := by omega
    have hge := newton_ge n x hx2
    have := hstep x hx3
    by_cases hlt : (x + n / x) / 2 < x
    · right
      refine ⟨(x + n / x) / 2, ⟨hge, by omega⟩, newton_half n x (by omega), ?_⟩
      simp only [hlt, ↓reduceDIte]
      omega
    · left
      simp only [hlt, ↓reduceDIte]
      omega

/-- **`Nat.sqrt`** (`Nat.sqrt.c278`) below `2^127`: at most `5200`. -/
theorem sqrt_cost (hP : Includes P Auto.Nat.sqrt.c278.costDeps) (n : ℕ) (hn : n < 2 ^ 127) :
    machineCost P Auto.Nat.sqrt.c278.costIdx [enc n] ≤ 5200 := by
  rw [Auto.Nat.sqrt.c278.costEq P hP]
  have h1 := limbs_le_two (x := n) (by omega)
  by_cases h : n ≤ 1
  · simp only [h, ↓reduceIte]; omega
  · simp only [h, ↓reduceIte]
    have hlog : Nat.log2 n < 127 := (Nat.log2_lt (by omega)).2 hn
    have hlr := log2Rec_cost P (by includes) n (by omega)
    set k := Nat.log2 n / 2 + 1
    have hk : k ≤ 64 := by omega
    have hg : 1 <<< k ≤ 2 ^ 126 := by
      rw [Nat.one_shiftLeft]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hsq : Nat.sqrt n ≤ 1 <<< k := by
      rw [Nat.one_shiftLeft]
      have hs := Nat.sqrt_le n
      have hl := Nat.lt_log2_self (n := n)
      have : 2 ^ (Nat.log2 n + 1) ≤ 2 ^ k * 2 ^ k := by
        rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      by_contra hc
      have : 2 ^ k * 2 ^ k < Nat.sqrt n * Nat.sqrt n := Nat.mul_lt_mul'' (by omega) (by omega)
      omega
    have hit := sqrtIter_cost P (by includes) n hn (1 <<< k) hsq hg
    have : Nat.log2 (1 <<< k - Nat.sqrt n) ≤ 126 := by
      have := log2_mono (show 1 <<< k - Nat.sqrt n ≤ 2 ^ 126 by omega)
      rw [Nat.log2_two_pow] at this; exact this
    have := limbs_le_two (x := 1 <<< k) (by omega)
    rw [limbs_of_lt (by omega : Nat.log2 n < 2 ^ 64), limbs_of_lt (by omega : Nat.log2 n / 2 < 2 ^ 64),
      limbs_of_lt (by omega : k < 2 ^ 64)]
    omega

/-- `⌈√x⌉` (`ceilSqrt.c277`) below `2^127`: at most `15620`. -/
theorem ceilSqrt_cost (hP : Includes P Auto.LeanVM.Extraction.ceilSqrt.c277.costDeps) (x : ℕ)
    (hx : x < 2 ^ 127) : machineCost P Auto.LeanVM.Extraction.ceilSqrt.c277.costIdx [enc x] ≤ 15620 := by
  rw [Auto.LeanVM.Extraction.ceilSqrt.c277.costEq P hP]
  have hs := sqrt_cost P (by includes) x hx
  have h1 := Nat.sqrt_le x
  have h2 := Nat.sqrt_le_self x
  have l1 := limbs_le_two (x := Nat.sqrt x) (by omega)
  have l2 := limbs_le_two (x := Nat.sqrt x * Nat.sqrt x) (by omega)
  have l3 := limbs_le_two (x := x) (by omega)
  have : limbs (Nat.sqrt x) * limbs (Nat.sqrt x) ≤ 4 := by nlinarith
  split_ifs <;> omega

theorem johnsonSlack_row_length (i : ℕ) : (johnsonSlack.getD i []).length ≤ 14 := by
  rcases i with _ | _ | _ | _ | i <;> simp [johnsonSlack]

theorem johnsonSlackOf_le (μ R : ℕ) : johnsonSlackOf μ R ≤ 975 := by
  unfold johnsonSlackOf
  have hrow : ∀ i, ∀ x ∈ johnsonSlack.getD i [], x ≤ 975 := by
    intro i
    rcases i with _ | _ | _ | _ | i <;> simp [johnsonSlack]
  rw [List.getD_eq_getElem?_getD]
  generalize h : (johnsonSlack.getD (R - 1) [])[μ - Whir.minLogStack]? = o
  cases o with
  | none => simp
  | some x => exact hrow _ x (List.mem_of_getElem? h)

/-- The slack table lookup (`johnsonSlackOf.c281`): at most `540`. -/
theorem johnsonSlackOf_cost (hP : Includes P Auto.LeanVM.Extraction.johnsonSlackOf.c281.costDeps)
    (μ R : ℕ) (hμ : μ < 2 ^ 64) (hR : R < 2 ^ 64) :
    machineCost P Auto.LeanVM.Extraction.johnsonSlackOf.c281.costIdx [enc μ, enc R] ≤ 540 := by
  rw [Auto.LeanVM.Extraction.johnsonSlackOf.c281.costEq P hP,
    Auto.LeanVM.Extraction.johnsonSlack.c282.costEq P (by includes), limbs_of_lt hR,
    limbs_of_lt hμ, limbs_of_lt (by unfold Whir.minLogStack; omega : Whir.minLogStack < 2 ^ 64)]
  have h1 := getD_cost P (by includes) johnsonSlack (R - 1) (by omega) []
  have h2 := getD_cost P (by includes) (johnsonSlack.getD (R - 1) []) (μ - Whir.minLogStack)
    (by omega) 0
  have h3 := johnsonSlack_row_length (R - 1)
  have h4 : johnsonSlack.length = 4 := rfl
  simp only [max_self]
  omega

/-- **The Johnson threshold** (`johnsonThreshold.c276`): two `⌈√·⌉`s' worth of `Nat.sqrt` on a
number below `2^126`, the slack table and a few two-limb operations: at most `16300`, for
`2κ + R ≤ 80` (`κ = μ − 6`). -/
theorem johnsonThreshold_cost (hP : Includes P Auto.LeanVM.Extraction.johnsonThreshold.c276.costDeps)
    (μ R : ℕ) (hμ : μ < 2 ^ 64) (hκR : 2 * (μ - Whir.initialFold) + R ≤ 80) :
    machineCost P Auto.LeanVM.Extraction.johnsonThreshold.c276.costIdx [enc μ, enc R] ≤ 16300 := by
  rw [Auto.LeanVM.Extraction.johnsonThreshold.c276.costEq P hP]
  have hf : Whir.initialFold = 6 := rfl
  set κ := μ - Whir.initialFold with hκ
  have hL : ∀ x, x < 2 ^ 128 → limbs x ≤ 2 := fun x h ↦ limbs_le_two h
  have hN : 2 ^ (κ + R) ≤ 2 ^ 80 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hK : 2 ^ κ ≤ 2 ^ 40 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hX : 2 ^ 44 * (2 ^ κ - 1) * 2 ^ (κ + R) < 2 ^ 126 := by
    have : 2 ^ 44 * (2 ^ κ - 1) * 2 ^ (κ + R) ≤ 2 ^ 44 * 2 ^ κ * 2 ^ (κ + R) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    have e : 2 ^ 44 * 2 ^ κ * 2 ^ (κ + R) = 2 ^ (44 + κ + (κ + R)) := by rw [← pow_add, ← pow_add]
    have : 2 ^ (44 + κ + (κ + R)) < 2 ^ 126 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  set X := 2 ^ 44 * (2 ^ κ - 1) * 2 ^ (κ + R) with hXdef
  have hcs := ceilSqrt_cost P (by includes) X (by omega)
  have hsl := johnsonSlackOf_cost P (by includes) μ R hμ (by omega)
  have hsl' := johnsonSlackOf_le μ R
  have hcsv : ceilSqrt X ≤ X + 1 := by
    unfold ceilSqrt; have := Nat.sqrt_le_self X; split_ifs <;> omega
  have hslN : johnsonSlackOf μ R * 2 ^ (κ + R) ≤ 975 * 2 ^ 80 :=
    Nat.mul_le_mul hsl' hN
  have l1 := hL μ (by omega)
  have l2 := hL κ (by omega)
  have l3 := hL R (by omega)
  have l4 := hL (1 <<< (κ + R)) (by rw [Nat.one_shiftLeft]; omega)
  have l5 := hL (κ + R) (by omega)
  have l6 := hL (1 <<< κ) (by rw [Nat.one_shiftLeft]; omega)
  have l7 := hL (2 ^ κ) (by omega)
  have l8 := hL (2 ^ κ - 1) (by omega)
  have l9 := hL (2 ^ 44 * (2 ^ κ - 1)) (by
    have : 2 ^ 44 * (2 ^ κ - 1) ≤ 2 ^ 44 * 2 ^ 40 := Nat.mul_le_mul_left _ (by omega)
    omega)
  have l10 := hL (2 ^ (κ + R)) (by omega)
  have l11 := hL (johnsonSlackOf μ R) (by omega)
  have l12 := hL (ceilSqrt X) (by omega)
  have l13 := hL (johnsonSlackOf μ R * 2 ^ (κ + R)) (by omega)
  have l14 := hL (ceilSqrt X + johnsonSlackOf μ R * 2 ^ (κ + R)) (by omega)
  have l15 := hL (ceilSqrt X + johnsonSlackOf μ R * 2 ^ (κ + R) + 2 ^ 22) (by omega)
  have l16 := hL (ceilSqrt X + johnsonSlackOf μ R * 2 ^ (κ + R) + 2 ^ 22 - 1) (by omega)
  have l17 := hL (Whir.initialFold) (by omega)
  have p1 : limbs (2 ^ 44) * limbs (2 ^ κ - 1) ≤ 4 := by
    rw [limbs_two_pow (by norm_num)]; omega
  have p2 : limbs (2 ^ 44 * (2 ^ κ - 1)) * limbs (2 ^ (κ + R)) ≤ 4 := by nlinarith
  have p3 : limbs (johnsonSlackOf μ R) * limbs (2 ^ (κ + R)) ≤ 4 := by nlinarith
  have p4 : limbs (ceilSqrt X + johnsonSlackOf μ R * 2 ^ (κ + R) + 2 ^ 22 - 1) * limbs (2 ^ 22) ≤ 4 := by
    rw [limbs_two_pow (by norm_num)]; omega
  rw [limbs_shift (by norm_num : 44 < 64), limbs_shift (by norm_num : 22 < 64),
    limbs_two_pow (by norm_num : 22 < 64)]
  have m1 := max_le l1 l17
  have m2 := max_le l2 l3
  have m3 := max_le l12 l13
  have m4 := max_le l14 (show limbs 1 ≤ 2 by simp)
  omega

end

end LeanVM.Cost.Bounds
