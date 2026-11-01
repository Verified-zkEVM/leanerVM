module

public import LeanVM.Cost.Bounds.Basic
public import LeanVM.Cost.Extractor.Transcript

/-!
# Bounds: the library's list functions, compiled

One bound per function of Init's lists (and `Option.map`, the merge sort of `Cost/InitLib.lean`,
`ofFnFrom` and `log2Rec` of `Cost/Rules.lean`) as the extractor's chain compiles it, through
`Cost/Extractor/Transcript.lean` (each at one index, `….cN`, reused by the later modules), for
every bound that calls it:

* by the list's length: `rangeLoop_cost`, `reverseAux_cost`, `length_cost`, `append_cost`,
  `filter_cost`, `filterMap_cost`, `map_cost`, `findSome_cost`, `all_cost`, `zipIdx_cost`,
  `foldr_cost` (`foldrSuffix_cost`, the closure's price bounded on the suffixes),
  `flatten_cost`, `getInternal_cost`, `getD_cost`, `take_cost_length`, `drop_cost_length`,
  `listBeqK_cost`, `ofFnFrom_cost`;
* by the index or count: `getInternal_cost_idx`, `getD_cost_idx`, `take_cost`, `drop_cost`,
  `replicate_cost`, `optionMap_cost`;
* `Nat.log2` by halving: `log2Rec_cost` (below `2^128`), `log2Rec_cost_word` (below `2^64`);
* the merge sort: `mergeList_cost`, `mergeSortList_cost` (`n log n`), `mergeSortList_cost_sq`
  (quadratic).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Cost.Library LeanVM.Parameters

public section

variable (P : Program)

theorem ofFnFrom_length {α : Type} {n : ℕ} (f : Fin n → α) : (Rewrite.ofFnFrom f 0).length = n := by
  rw [Rewrite.ofFnFrom_eq f (n - 0) 0 rfl]; simp

section
variable {α : Type} [Enc α]

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
theorem length_cost (hP : Includes P Auto.List.length.c229.costDeps) {α : Type} [Enc α] :
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

/-- `List.filter` (`filter.c140`): `13` per element and the predicate's price, `3`. -/
theorem filter_cost (hP : Includes P Auto.List.filter.c140.costDeps) {α : Type} [Enc α]
    (p : α → Bool) (pVal : Val) (hp : ∀ a, RunsApp P pVal [enc a] (enc (p a))) (B : ℕ) :
    ∀ l : List α, (∀ a ∈ l, appCost P pVal [enc a] ≤ B) →
      machineCost P Auto.List.filter.c140.costIdx [pVal, enc l] ≤ (B + 13) * l.length + 3 := by
  intro l
  induction l with
  | nil => intro _; rw [Auto.List.filter.c140.costEq_nil P hP p pVal hp]; omega
  | cons a l ih =>
    intro hB
    rw [Auto.List.filter.c140.costEq_cons P hP p pVal hp]
    have h1 := ih fun a' ha ↦ hB a' (by simp [ha])
    have h2 := hB a (by simp)
    simp only [List.length_cons]
    generalize p a = b
    cases b <;> dsimp only <;> nlinarith

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

/-- `List.findSome?` (`findSome?.c125`), any element type: `9` per element and the closure's
price, `3` at the end. -/
theorem findSome_cost (hP : Includes P Auto.List.findSome?.c125.costDeps) {α β : Type} [Enc α]
    [Enc β] (f : α → Option β) (fVal : Val) (hf : ∀ a, RunsApp P fVal [enc a] (enc (f a)))
    (B : ℕ) : ∀ ls : List α, (∀ l ∈ ls, appCost P fVal [enc l] ≤ B) →
      machineCost P Auto.List.findSome?.c125.costIdx [fVal, enc ls] ≤ (B + 9) * ls.length + 3 := by
  intro ls
  induction ls with
  | nil => intro _; rw [Auto.List.findSome?.c125.costEq_nil P hP f fVal hf]; omega
  | cons l ls ih =>
    intro hB
    rw [Auto.List.findSome?.c125.costEq_cons P hP f fVal hf]
    have h1 := ih fun l' hl ↦ hB l' (by simp [hl])
    have h2 := hB l (by simp)
    simp only [List.length_cons]
    generalize f l = o
    cases o <;> dsimp only <;> nlinarith

/-- `List.all` (`all.c240`): `9` per element and the predicate's price, `3`. -/
theorem all_cost (hP : Includes P Auto.List.all.c240.costDeps) {β : Type} [Enc β]
    (p : β → Bool) (pVal : Val) (hp : ∀ a, RunsApp P pVal [enc a] (enc (p a))) (B : ℕ) :
    ∀ l : List β, (∀ a ∈ l, appCost P pVal [enc a] ≤ B) →
      machineCost P Auto.List.all.c240.costIdx [enc l, pVal] ≤ (B + 9) * l.length + 3 := by
  intro l
  induction l with
  | nil => intro _; rw [Auto.List.all.c240.costEq_nil P hP p pVal hp]; omega
  | cons a l ih =>
    intro hB
    rw [Auto.List.all.c240.costEq_cons P hP a l p pVal hp]
    have h1 := ih fun a' ha ↦ hB a' (by simp [ha])
    have h2 := hB a (by simp)
    simp only [List.length_cons]
    split_ifs <;> nlinarith

/-- `List.zipIdx` (`zipIdx.c61`): `16` per element, `3` at the end, for word-sized indices. -/
theorem zipIdx_cost (hP : Includes P Auto.List.zipIdx.c61.costDeps) :
    ∀ (l : List α) (n : ℕ), n + l.length < 2 ^ 64 →
      machineCost P Auto.List.zipIdx.c61.costIdx [enc l, enc n] ≤ 16 * l.length + 3
  | [], n, _ => by rw [Auto.List.zipIdx.c61.costEq_nil P hP n]; omega
  | x :: l, n, h => by
    rw [Auto.List.zipIdx.c61.costEq_cons P hP x l n, limbs_of_lt (by simp at h; omega)]
    have := zipIdx_cost hP l (n + 1) (by simp at h; omega)
    simp only [List.length_cons]
    omega

/-- `List.foldr` (`foldr.c86`), the closure's price bounded on the suffixes: `9` per element and
the closure's price, `3` at the end. -/
theorem foldrSuffix_cost (hP : Includes P Auto.List.foldr.c86.costDeps) {α β : Type} [Enc α]
    [Enc β] (f : α → β → β) (fVal : Val)
    (hf : ∀ a b, RunsApp P fVal [enc a, enc b] (enc (f a b))) (B : ℕ) (init : β) :
    ∀ l : List α, (∀ x tl, x :: tl <:+ l → appCost P fVal [enc x, enc (tl.foldr f init)] ≤ B) →
      machineCost P Auto.List.foldr.c86.costIdx [fVal, enc init, enc l] ≤ (B + 9) * l.length + 3 := by
  intro l
  induction l with
  | nil => intro _; rw [Auto.List.foldr.c86.costEq_nil P hP f fVal hf]; omega
  | cons x l ih =>
    intro hB
    rw [Auto.List.foldr.c86.costEq_cons P hP f fVal hf]
    have h1 := ih fun y tl h ↦ hB y tl (h.trans (List.suffix_cons x l))
    have h2 := hB x l List.suffix_rfl
    simp only [List.length_cons]
    nlinarith

/-- `List.foldr` (`foldr.c86`): `9` per element and the closure's price, `3` at the end. -/
theorem foldr_cost (hP : Includes P Auto.List.foldr.c86.costDeps) {α β : Type} [Enc α] [Enc β]
    (f : α → β → β) (fVal : Val) (hf : ∀ (a : α) (b : β), RunsApp P fVal [enc a, enc b] (enc (f a b)))
    (B : ℕ) (init : β) (l : List α) (hB : ∀ a ∈ l, ∀ b : β, appCost P fVal [enc a, enc b] ≤ B) :
    machineCost P Auto.List.foldr.c86.costIdx [fVal, enc init, enc l] ≤ (B + 9) * l.length + 3 :=
  foldrSuffix_cost P hP f fVal hf B init l fun x tl h ↦ hB x (h.subset (by simp)) _

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

/-- `List.flatten` (`flatten.c263`), by the total length: `9` per element, `18` per piece, `3`. -/
theorem flatten_cost_length (hP : Includes P Auto.List.flatten.c263.costDeps) :
    ∀ xss : List (List α),
      machineCost P Auto.List.flatten.c263.costIdx [enc xss] ≤ 9 * xss.flatten.length + 18 * xss.length + 3
  | [] => by rw [Auto.List.flatten.c263.costEq_nil P hP]; omega
  | xs :: xss => by
    rw [Auto.List.flatten.c263.costEq_cons P hP]
    have h1 := flatten_cost_length hP xss
    have h2 := append_cost P (by includes) xs xss.flatten
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    omega

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

/-- `List.get?` at index `k`: `15·k + 10` at most. -/
theorem getInternal_cost_idx (hP : Includes P Auto.List.«get?Internal».c275.costDeps) {α : Type} [Enc α] :
    ∀ (l : List α) (k : ℕ), k < 2 ^ 64 →
      machineCost P Auto.List.«get?Internal».c275.costIdx [enc l, enc k] ≤ 15 * k + 10 := by
  intro l
  induction l with
  | nil => intro k _; rw [Auto.List.«get?Internal».c275.costEq_nil P hP]; omega
  | cons x l ih =>
    intro k hk
    rw [Auto.List.«get?Internal».c275.costEq_cons P hP, limbs_of_lt hk]
    cases k with
    | zero => simp only [Nat.rec_zero]; omega
    | succ k =>
      have := ih k (by omega)
      simp only
      omega

/-- `List.getD` (`getD.c274`): `15` per element, `8` at the end. -/
theorem getD_cost (hP : Includes P Auto.List.getD.c274.costDeps) {α : Type} [Enc α]
    (l : List α) (k : ℕ) (d : α) (hk : k < 2 ^ 64) :
    machineCost P Auto.List.getD.c274.costIdx [enc l, enc k, enc d] ≤ 15 * l.length + 8 := by
  rw [Auto.List.getD.c274.costEq P hP]
  have := getInternal_cost P (by includes) l k hk
  generalize l[k]? = o
  cases o <;> dsimp only <;> omega

/-- `List.getD` at index `k`: `15·k + 15` at most. -/
theorem getD_cost_idx (hP : Includes P Auto.List.getD.c274.costDeps) {α : Type} [Enc α]
    (l : List α) (k : ℕ) (d : α) (hk : k < 2 ^ 64) :
    machineCost P Auto.List.getD.c274.costIdx [enc l, enc k, enc d] ≤ 15 * k + 15 := by
  rw [Auto.List.getD.c274.costEq P hP]
  have := getInternal_cost_idx P (by includes) l k hk
  generalize l[k]? = o
  cases o <;> dsimp only <;> omega

/-- `List.take n` (`take.c231`): at most `19·n + 6`, whatever the list. -/
theorem take_cost (hP : Includes P Auto.List.take.c231.costDeps) {α : Type} [Enc α] :
    ∀ (n : ℕ) (xs : List α), n < 2 ^ 64 →
      machineCost P Auto.List.take.c231.costIdx [enc n, enc xs] ≤ 19 * n + 6 := by
  intro n
  induction n with
  | zero => intro xs _; rw [Auto.List.take.c231.costEq P hP]; simp [limbs_of_lt]
  | succ k ih =>
    intro xs hk
    rw [Auto.List.take.c231.costEq P hP, limbs_of_lt hk]
    cases xs with
    | nil => dsimp only; omega
    | cons x xs => have := ih xs (by omega); dsimp only; omega

/-- `List.take n` (`take.c231`), by the list's length: `19` per element, `13` at the end. -/
theorem take_cost_length (hP : Includes P Auto.List.take.c231.costDeps) :
    ∀ (n : ℕ) (l : List α), n < 2 ^ 64 →
      machineCost P Auto.List.take.c231.costIdx [enc n, enc l] ≤ 19 * l.length + 13
  | 0, l, _ => by rw [Auto.List.take.c231.costEq_zero P hP]; omega
  | n + 1, [], h => by rw [Auto.List.take.c231.costEq_succ P hP, limbs_of_lt h]; simp
  | n + 1, x :: l, h => by
    rw [Auto.List.take.c231.costEq_succ P hP, limbs_of_lt h]
    have := take_cost_length hP n l (by omega)
    simp only [List.length_cons]
    omega

/-- `List.drop n` (`drop.c232`): at most `15·n + 6`, whatever the list. -/
theorem drop_cost (hP : Includes P Auto.List.drop.c232.costDeps) {α : Type} [Enc α] :
    ∀ (n : ℕ) (xs : List α), n < 2 ^ 64 →
      machineCost P Auto.List.drop.c232.costIdx [enc n, enc xs] ≤ 15 * n + 6 := by
  intro n
  induction n with
  | zero => intro xs _; rw [Auto.List.drop.c232.costEq P hP]; simp [limbs_of_lt]
  | succ k ih =>
    intro xs hk
    rw [Auto.List.drop.c232.costEq P hP, limbs_of_lt hk]
    cases xs with
    | nil => dsimp only; omega
    | cons x xs => have := ih xs (by omega); dsimp only; omega

/-- `List.drop n` (`drop.c232`), by the list's length: `15` per element, `13` at the end. -/
theorem drop_cost_length (hP : Includes P Auto.List.drop.c232.costDeps) :
    ∀ (n : ℕ) (l : List α), n < 2 ^ 64 →
      machineCost P Auto.List.drop.c232.costIdx [enc n, enc l] ≤ 15 * l.length + 13
  | 0, l, _ => by rw [Auto.List.drop.c232.costEq_zero P hP]; omega
  | n + 1, [], h => by rw [Auto.List.drop.c232.costEq_succ P hP, limbs_of_lt h]; simp
  | n + 1, x :: l, h => by
    rw [Auto.List.drop.c232.costEq_succ P hP, limbs_of_lt h]
    have := drop_cost_length hP n l (by omega)
    simp only [List.length_cons]
    omega

/-- `List.replicate n a`: at most `17·n + 6`. -/
theorem replicate_cost (hP : Includes P Auto.List.replicate.c346.costDeps) {α : Type} [Enc α]
    (a : α) : ∀ n, n < 2 ^ 64 →
      machineCost P Auto.List.replicate.c346.costIdx [enc n, enc a] ≤ 17 * n + 6 := by
  intro n
  induction n with
  | zero => intro _; rw [Auto.List.replicate.c346.costEq_zero P hP]
  | succ n ih =>
    intro hn
    rw [Auto.List.replicate.c346.costEq_succ P hP, limbs_of_lt hn]
    have := ih (by omega)
    omega

/-- `Option.map` (`map.c106`): at most the closure's price `+ 7`. -/
theorem optionMap_cost (hP : Includes P Auto.Option.map.c106.costDeps) {α β : Type} [Enc α]
    [Enc β] (f : α → β) (fVal : Val) (hf : ∀ a, RunsApp P fVal [enc a] (enc (f a))) (B : ℕ)
    (o : Option α) (hB : ∀ a, o = some a → appCost P fVal [enc a] ≤ B) :
    machineCost P Auto.Option.map.c106.costIdx [fVal, enc o] ≤ B + 7 := by
  cases o with
  | none => rw [Auto.Option.map.c106.costEq_none P hP f fVal hf]; omega
  | some a => rw [Auto.Option.map.c106.costEq_some P hP f fVal hf]; have := hB a rfl; omega

/-- `List.beq` on coefficients: at most `12` per coefficient and `7`. -/
theorem listBeqK_cost (hP : Includes P Auto.List.beq.c27.costDeps) :
    ∀ a b : List K, machineCost P Auto.List.beq.c27.costIdx [enc a, enc b] ≤ 12 * a.length + 7 := by
  intro a
  induction a with
  | nil => intro b; rw [Auto.List.beq.c27.costEq P hP]; cases b <;> simp
  | cons x a ih =>
    intro b
    rw [Auto.List.beq.c27.costEq P hP]
    cases b with
    | nil => simp
    | cons y b =>
      have := ih b
      simp only [List.length_cons]
      split_ifs <;> omega

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

/-- `Nat.log2` by halving (`log2Rec.c280`), word-sized: at most `13·log₂ n + 6`. -/
theorem log2Rec_cost_word (hP : Includes P Auto.LeanVM.Cost.Rewrite.log2Rec.c280.costDeps) :
    ∀ n : ℕ, n < 2 ^ 64 →
      machineCost P Auto.LeanVM.Cost.Rewrite.log2Rec.c280.costIdx [enc n] ≤ 13 * Nat.log2 n + 6 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  rw [Auto.LeanVM.Cost.Rewrite.log2Rec.c280.costEq P hP, limbs_of_lt hn]
  by_cases h2 : 2 ≤ n
  · simp only [h2, ↓reduceIte]
    have := ih (n / 2) (by omega) (by omega)
    have hl := log2_half h2
    have hr : Rewrite.log2Rec (n / 2) < 2 ^ 64 := by
      rw [← Rewrite.natLog2]; have := Nat.log2_le_self (n / 2); omega
    rw [limbs_of_lt hr]
    omega
  · simp only [h2, ↓reduceIte]; omega

/-! ## Merge sort -/

/-- The merge (`mergeList.c230`): `B + 21` per element, the comparisons on elements of `Q`. -/
theorem mergeList_cost (hP : Includes P Auto.LeanVM.Cost.InitLib.mergeList.c230.costDeps)
    (le : α → α → Bool) (leVal : Val) (hle : ∀ a b, RunsApp P leVal [enc a, enc b] (enc (le a b)))
    (B : ℕ) (Q : α → Prop) (hB : ∀ a b, Q a → Q b → appCost P leVal [enc a, enc b] ≤ B) :
    ∀ (n : ℕ) (xs ys : List α), xs.length + ys.length ≤ n → (∀ a ∈ xs, Q a) → (∀ b ∈ ys, Q b) →
      machineCost P Auto.LeanVM.Cost.InitLib.mergeList.c230.costIdx [enc xs, enc ys, leVal] ≤
        (B + 21) * (xs.length + ys.length) + 5 := by
  intro n
  induction n with
  | zero =>
    intro xs ys hn _ _
    cases xs with
    | nil => rw [Auto.LeanVM.Cost.InitLib.mergeList.c230.costEq_nil P hP _ le leVal hle]; omega
    | cons => simp at hn
  | succ n ih =>
    intro xs ys hn hxs hys
    cases xs with
    | nil => rw [Auto.LeanVM.Cost.InitLib.mergeList.c230.costEq_nil P hP _ le leVal hle]; omega
    | cons x xs =>
      rw [Auto.LeanVM.Cost.InitLib.mergeList.c230.costEq_cons P hP x xs ys le leVal hle]
      cases ys with
      | nil =>
        dsimp only
        simp only [List.length_cons, List.length_nil]
        nlinarith
      | cons y ys =>
        have hxy := hB x y (hxs x (by simp)) (hys y (by simp))
        simp only [List.length_cons] at hn ⊢
        split
        · have := ih xs (y :: ys) (by simp; omega) (fun a ha ↦ hxs a (by simp [ha])) hys
          simp only [List.length_cons] at this
          nlinarith
        · have := ih (x :: xs) ys (by simp; omega) hxs (fun b hb ↦ hys b (by simp [hb]))
          simp only [List.length_cons] at this
          nlinarith

omit [Enc α] in
theorem length_mergeSortList (l : List α) (le : α → α → Bool) :
    (InitLib.mergeSortList l le).length = l.length := by
  rw [← InitLib.mergeSort_eq_mergeSortList, List.length_mergeSort]

omit [Enc α] in
theorem mem_mergeSortList {l : List α} {le : α → α → Bool} {a : α}
    (h : a ∈ InitLib.mergeSortList l le) : a ∈ l := by
  rw [← InitLib.mergeSort_eq_mergeSortList] at h
  exact (List.mem_mergeSort).1 h

/-- **The merge sort** (`mergeSortList.c228`), the comparison at most `Bc` on elements of `S`:
at most `(Bc + 100)·n² + 10` (a quadratic bound). -/
theorem mergeSortList_cost_sq (hP : Includes P Auto.LeanVM.Cost.InitLib.mergeSortList.c228.costDeps)
    (le : α → α → Bool) (leVal : Val) (hle : ∀ a b, RunsApp P leVal [enc a, enc b] (enc (le a b)))
    (S : α → Prop) (Bc : ℕ) (hB : ∀ a b, S a → S b → appCost P leVal [enc a, enc b] ≤ Bc) :
    ∀ (n : ℕ) (l : List α), l.length = n → n < 2 ^ 60 → (∀ a ∈ l, S a) →
      machineCost P Auto.LeanVM.Cost.InitLib.mergeSortList.c228.costIdx [enc l, leVal] ≤
        (Bc + 100) * (n * n) + 10 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro l hl hn hS
  cases l with
  | nil => rw [Auto.LeanVM.Cost.InitLib.mergeSortList.c228.costEq_nil P hP le leVal hle]; omega
  | cons x t =>
    rw [Auto.LeanVM.Cost.InitLib.mergeSortList.c228.costEq_cons P hP x t le leVal hle]
    cases t with
    | nil => dsimp only; omega
    | cons y t =>
      dsimp only
      simp only [List.length_cons] at hl
      set h2 := (t.length + 2 + 1) / 2 with hh
      have hlt : (x :: y :: t).length = t.length + 2 := by simp
      have ha := List.length_take (i := h2) (l := x :: y :: t)
      have hb := List.length_drop (i := h2) (l := x :: y :: t)
      rw [hlt] at ha hb
      have hS1 : ∀ a ∈ List.take h2 (x :: y :: t), S a := fun a h ↦ hS a (List.mem_of_mem_take h)
      have hS2 : ∀ a ∈ List.drop h2 (x :: y :: t), S a := fun a h ↦ hS a (List.mem_of_mem_drop h)
      have i1 := ih (min h2 (t.length + 2)) (by omega) _ ha (by omega) hS1
      have i2 := ih (t.length + 2 - h2) (by omega) _ hb (by omega) hS2
      have hm : machineCost P Auto.LeanVM.Cost.InitLib.mergeList.c230.costIdx
          [enc (InitLib.mergeSortList (List.take h2 (x :: y :: t)) le),
            enc (InitLib.mergeSortList (List.drop h2 (x :: y :: t)) le), leVal] ≤
          (Bc + 21) * (t.length + 2) + 9 := by
        have := mergeList_cost P (by includes) le leVal hle Bc S hB (t.length + 2)
          (InitLib.mergeSortList (List.take h2 (x :: y :: t)) le)
          (InitLib.mergeSortList (List.drop h2 (x :: y :: t)) le)
          (by rw [length_mergeSortList, length_mergeSortList, ha, hb]; omega)
          (fun a h ↦ hS1 a (mem_mergeSortList h)) (fun a h ↦ hS2 a (mem_mergeSortList h))
        rw [length_mergeSortList, length_mergeSortList, ha, hb,
          show min h2 (t.length + 2) + (t.length + 2 - h2) = t.length + 2 by omega] at this
        omega
      have := length_cost P (by includes) t (by omega)
      have := take_cost P (by includes) h2 (x :: y :: t) (by omega)
      have := drop_cost P (by includes) h2 (x :: y :: t) (by omega)
      cost_simp
      -- the halves' squares
      generalize hA : min h2 (t.length + 2) = a at i1
      generalize hB' : t.length + 2 - h2 = b at i2
      have hab : a + b = n := by omega
      have ha1 : 1 ≤ a := by omega
      have hb1 : 1 ≤ b := by omega
      have hsq : n * n = a * a + b * b + 2 * (a * b) := by rw [← hab]; ring
      have h1 : a ≤ a * b := Nat.le_mul_of_pos_right a hb1
      have h2' : b ≤ a * b := Nat.le_mul_of_pos_left b ha1
      have e1 : (Bc + 100) * (n * n) = (Bc + 100) * (a * a) + (Bc + 100) * (b * b) +
          (Bc + 100) * (2 * (a * b)) := by rw [hsq]; ring
      have e2 : (Bc + 100) * (2 * (a * b)) ≥ (Bc + 100) * n := by
        apply Nat.mul_le_mul_left; omega
      have e3 : (Bc + 100) * n = (Bc + 21) * n + 79 * n := by ring
      have e4 : (Bc + 21) * (t.length + 2) = (Bc + 21) * n := by rw [hl]
      omega

theorem clog_half {n : ℕ} (hn : 2 ≤ n) : Nat.clog 2 ((n + 1) / 2) + 1 = Nat.clog 2 n := by
  rw [Nat.clog_of_two_le (by norm_num) hn, show n + 2 - 1 = n + 1 by omega]

/-- The merge sort's recurrence closed, `n log n`: two halves of sizes `a ≥ b ≥ 1`, `a + b = n`,
each at most `c·m·⌈log₂ m⌉ + 89m − 80`, and `c·n + 80` of work. -/
theorem nlogn_halves (c a b L T1 T2 W : ℕ) (hab : b ≤ a)
    (hL : Nat.clog 2 a + 1 = L)
    (h1 : T1 + 80 ≤ c * (a * Nat.clog 2 a) + 89 * a) (h2 : T2 + 80 ≤ c * (b * Nat.clog 2 b) + 89 * b)
    (hW : W ≤ c * (a + b) + 80) :
    T1 + T2 + W + 80 ≤ c * ((a + b) * L) + 89 * (a + b) := by
  have hLb : Nat.clog 2 b ≤ Nat.clog 2 a := Nat.clog_mono_right 2 hab
  have e1 : c * (b * Nat.clog 2 b) ≤ c * (b * Nat.clog 2 a) :=
    Nat.mul_le_mul_left c (Nat.mul_le_mul_left b hLb)
  have e2 : c * ((a + b) * L) = c * (a * Nat.clog 2 a) + c * (b * Nat.clog 2 a) + c * (a + b) := by
    rw [← hL]; ring
  omega

/-- **Merge sort** (`mergeSortList.c228`), `n log n`: at most
`(B + 64)·n·⌈log₂ n⌉ + 89·n + 3`, `B` the comparison's price on elements of `Q`. -/
theorem mergeSortList_cost_nlogn
    (hP : Includes P Auto.LeanVM.Cost.InitLib.mergeSortList.c228.costDeps)
    (le : α → α → Bool) (leVal : Val) (hle : ∀ a b, RunsApp P leVal [enc a, enc b] (enc (le a b)))
    (B : ℕ) (Q : α → Prop) (hB : ∀ a b, Q a → Q b → appCost P leVal [enc a, enc b] ≤ B) :
    ∀ (n : ℕ) (l : List α), l.length ≤ n → l.length < 2 ^ 63 → (∀ a ∈ l, Q a) → l ≠ [] →
      machineCost P Auto.LeanVM.Cost.InitLib.mergeSortList.c228.costIdx [enc l, leVal] + 80 ≤
        (B + 64) * (l.length * Nat.clog 2 l.length) + 89 * l.length := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro l hn hw hS hne
  rcases l with _ | ⟨x, _ | ⟨y, t⟩⟩
  · exact absurd rfl hne
  · rw [Auto.LeanVM.Cost.InitLib.mergeSortList.c228.costEq_cons P hP x [] le leVal hle]
    simp
  · rw [Auto.LeanVM.Cost.InitLib.mergeSortList.c228.costEq_cons P hP x (y :: t) le leVal hle]
    dsimp only
    simp only [List.length_cons] at hn hw ⊢
    have hw' : t.length + 2 + 1 < 2 ^ 64 := by omega
    set h1 := (t.length + 2 + 1) / 2 with hh1
    rw [limbs_of_lt (by omega : t.length < 2 ^ 64), limbs_of_lt (by omega : t.length + 2 < 2 ^ 64),
      limbs_of_lt hw']
    have hlen := length_cost P (by includes) t (by omega)
    have htake := take_cost_length P (by includes) h1 (x :: y :: t) (by omega)
    have hdrop := drop_cost_length P (by includes) h1 (x :: y :: t) (by omega)
    have hlt : (List.take h1 (x :: y :: t)).length = h1 := by simp; omega
    have hld : (List.drop h1 (x :: y :: t)).length = t.length + 2 - h1 := by simp
    have hmemT : ∀ a ∈ List.take h1 (x :: y :: t), Q a :=
      fun a ha ↦ hS a (List.mem_of_mem_take ha)
    have hmemD : ∀ a ∈ List.drop h1 (x :: y :: t), Q a :=
      fun a ha ↦ hS a (List.mem_of_mem_drop ha)
    have ih1 := ih h1 (by omega) (List.take h1 (x :: y :: t)) (by omega) (by omega) hmemT
      (by rw [← List.length_pos_iff_ne_nil, hlt]; omega)
    have ih2 := ih (t.length + 2 - h1) (by omega) (List.drop h1 (x :: y :: t)) (by omega)
      (by omega) hmemD (by rw [← List.length_pos_iff_ne_nil, hld]; omega)
    have hmerge := mergeList_cost P (by includes) le leVal hle B Q hB (h1 + (t.length + 2 - h1))
      (InitLib.mergeSortList (List.take h1 (x :: y :: t)) le)
      (InitLib.mergeSortList (List.drop h1 (x :: y :: t)) le)
      (by simp only [length_mergeSortList]; omega)
      (fun a ha ↦ hmemT a (mem_mergeSortList ha))
      (fun a ha ↦ hmemD a (mem_mergeSortList ha))
    simp only [length_mergeSortList, hlt, hld, List.length_cons] at ih1 ih2 hmerge htake hdrop
    have hsum : h1 + (t.length + 2 - h1) = t.length + 2 := by omega
    have hL := clog_half (n := t.length + 2) (by omega)
    have := nlogn_halves (B + 64) h1 (t.length + 2 - h1) (Nat.clog 2 (t.length + 2)) _ _
      (machineCost P Auto.LeanVM.Cost.InitLib.mergeList.c230.costIdx
        [enc (InitLib.mergeSortList (List.take h1 (x :: y :: t)) le),
          enc (InitLib.mergeSortList (List.drop h1 (x :: y :: t)) le), leVal] +
        machineCost P Auto.List.length.c229.costIdx [enc t] + 3 +
        machineCost P Auto.List.take.c231.costIdx [enc h1, enc (x :: y :: t)] +
        machineCost P Auto.List.drop.c232.costIdx [enc h1, enc (x :: y :: t)] + 41)
      (by omega) (by rw [← hL, hh1]) ih1 ih2 (by rw [hsum]; nlinarith)
    rw [hsum] at this
    rw [show t.length + 1 + 1 = t.length + 2 by omega]
    omega

/-- **Merge sort**, any list: at most `(B + 64)·n·⌈log₂ n⌉ + 89·n + 3`. -/
theorem mergeSortList_cost
    (hP : Includes P Auto.LeanVM.Cost.InitLib.mergeSortList.c228.costDeps)
    (le : α → α → Bool) (leVal : Val) (hle : ∀ a b, RunsApp P leVal [enc a, enc b] (enc (le a b)))
    (B : ℕ) (Q : α → Prop) (hB : ∀ a b, Q a → Q b → appCost P leVal [enc a, enc b] ≤ B)
    (l : List α) (hw : l.length < 2 ^ 63) (hS : ∀ a ∈ l, Q a) :
    machineCost P Auto.LeanVM.Cost.InitLib.mergeSortList.c228.costIdx [enc l, leVal] ≤
      (B + 64) * (l.length * Nat.clog 2 l.length) + 89 * l.length + 3 := by
  cases l with
  | nil => rw [Auto.LeanVM.Cost.InitLib.mergeSortList.c228.costEq_nil P hP le leVal hle]; omega
  | cons x l =>
    have := mergeSortList_cost_nlogn P hP le leVal hle B Q hB _ (x :: l) le_rfl hw hS (by simp)
    omega

end

end

end LeanVM.Cost.Bounds
