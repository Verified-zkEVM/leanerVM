module

public import LeanVM.Protocol.Extraction.Fast.SortedMap
public import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Set
import Mathlib.Tactic.ByContra
import Mathlib.Data.List.Nodup
import all LeanVM.Protocol.Extraction.Fast.SortedMap

/-!
# The decoder's count-driven searches, by sorting and binary search

The guest decoder reads a child's claims off the coverage table by scans (`B1.Main.slotOf`,
`segCount`, `kidOf`): a `find?` or a `filter` over a whole region per query, quadratic in the
counts. Here the same answers, on every input (no monotonicity of the memory assumed), from tables
built once:

* `lowerBound t e lo hi`: binary search in a sorted array, the number of its entries below `e`
  (`countP_lt_lowerBound`);
* `coverTable ps`: the pairs `(mark, slot)` of a region sorted (a `SortedMap` keyed by the pair,
  its levels merged), as two arrays: the marks in order and their slots;
  * **`slotIn_coverTable`**: `slotIn` (one binary search) is the first slot holding a mark, the
    `find?` of `slotOf`;
  * **`countIn_coverTable`**: `countIn` (two binary searches) is the number of slots whose marks
    lie in `[a, b)`, the `filter` of `segCount`;
* `prefixMax acc xs`: the running maxima; **`kidIn_prefixMax`**: the first `c` with
  `e < xs[c]` is the first with `e < max(xs[0..c])`, one binary search on the monotone maxima
  (`kidOf`'s `find?`).
-/

namespace LeanVM.Guest.Fast

open LeanVM.Extraction.Fast

@[expose] public section

/-! ## Binary search -/

/-- **Binary search**: in an array sorted ascending, the first index in `[lo, hi)` whose entry is
at least `e` (`hi` if none). -/
def lowerBound (t : Array ℕ) (e lo hi : ℕ) : ℕ :=
  if lo < hi then
    if t.getD ((lo + hi) / 2) 0 < e then lowerBound t e ((lo + hi) / 2 + 1) hi
    else lowerBound t e lo ((lo + hi) / 2)
  else lo
termination_by hi - lo

/-- An array sorted ascending. -/
def Ascends (t : Array ℕ) : Prop := ∀ i j (hi : i < t.size) (hj : j < t.size), i ≤ j → t[i] ≤ t[j]

theorem lowerBound_spec (t : Array ℕ) (ht : Ascends t) (e : ℕ) :
    ∀ n lo hi, hi - lo = n → lo ≤ hi → hi ≤ t.size →
      (∀ i (h : i < t.size), i < lo → t[i] < e) → (∀ i (h : i < t.size), hi ≤ i → e ≤ t[i]) →
      lowerBound t e lo hi ≤ t.size ∧
        (∀ i (h : i < t.size), i < lowerBound t e lo hi → t[i] < e) ∧
        (∀ i (h : i < t.size), lowerBound t e lo hi ≤ i → e ≤ t[i]) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro lo hi hn hlh hhi hlo hhi'
  rw [lowerBound]
  by_cases hlt : lo < hi
  · simp only [hlt, ↓reduceIte]
    have hmid : (lo + hi) / 2 < t.size := by omega
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hmid, Option.getD_some]
    split
    · rename_i hc
      refine ih (hi - ((lo + hi) / 2 + 1)) (by omega) _ _ rfl (by omega) hhi (fun i hi' hil ↦ ?_)
        hhi'
      by_cases hil' : i < lo
      · exact hlo i hi' hil'
      · exact Nat.lt_of_le_of_lt (ht i _ hi' hmid (by omega)) hc
    · rename_i hc
      refine ih ((lo + hi) / 2 - lo) (by omega) _ _ rfl (by omega) (by omega) hlo
        (fun i hi' hil ↦ ?_)
      by_cases hil' : hi ≤ i
      · exact hhi' i hi' hil'
      · exact Nat.le_trans (by omega) (ht _ i hmid hi' hil)
  · simp only [hlt, ↓reduceIte]
    have : lo = hi := by omega
    subst this
    exact ⟨hhi, hlo, hhi'⟩

/-- The binary search over the whole array: the first index whose entry is at least `e`. -/
theorem lowerBound_full (t : Array ℕ) (ht : Ascends t) (e : ℕ) :
    lowerBound t e 0 t.size ≤ t.size ∧
      (∀ i (h : i < t.size), i < lowerBound t e 0 t.size → t[i] < e) ∧
      (∀ i (h : i < t.size), lowerBound t e 0 t.size ≤ i → e ≤ t[i]) :=
  lowerBound_spec t ht e _ 0 t.size rfl (Nat.zero_le _) (Nat.le_refl _)
    (fun _ _ h ↦ absurd h (Nat.not_lt_zero _)) (fun _ h h' ↦ absurd h (by omega))

/-- **The binary search counts the entries below `e`.** -/
theorem countP_lt_lowerBound (t : Array ℕ) (ht : Ascends t) (e : ℕ) :
    t.toList.countP (fun x ↦ decide (x < e)) = lowerBound t e 0 t.size := by
  obtain ⟨hr, hlt, hge⟩ := lowerBound_full t ht e
  set r := lowerBound t e 0 t.size
  rw [← List.take_append_drop r t.toList, List.countP_append,
    List.countP_eq_length.2 (fun x hx ↦ ?_), List.countP_eq_zero.2 (fun x hx ↦ ?_)]
  · simp only [List.length_take, Array.length_toList]; omega
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simp only [List.getElem_drop, Array.getElem_toList, decide_eq_true_eq, Nat.not_lt]
    exact hge _ (by simp at hi; omega) (by omega)
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simp only [List.getElem_take, Array.getElem_toList, decide_eq_true_eq]
    exact hlt _ _ (by simp at hi; omega)

/-- A list sorted ascending, as an array. -/
theorem monotone_toArray {l : List ℕ} (hl : l.Pairwise (· ≤ ·)) : Ascends l.toArray := by
  intro i j hi hj hij
  rcases Nat.eq_or_lt_of_le hij with rfl | hlt
  · exact Nat.le_refl _
  · simpa using List.pairwise_iff_getElem.1 hl i j (by simpa using hi) (by simpa using hj) hlt

/-- **Counting by two binary searches**: the entries in `[a, b)` are those below `b` less those
below `a`, on any list. -/
theorem countP_Ico (l : List ℕ) (a b : ℕ) :
    l.countP (fun x ↦ decide (a ≤ x ∧ x < b)) =
      l.countP (fun x ↦ decide (x < b)) - l.countP (fun x ↦ decide (x < a)) := by
  by_cases hab : a ≤ b
  · have : l.countP (fun x ↦ decide (x < b)) =
        l.countP (fun x ↦ decide (x < a)) + l.countP (fun x ↦ decide (a ≤ x ∧ x < b)) := by
      induction l with
      | nil => rfl
      | cons x l ih =>
        simp only [List.countP_cons, decide_eq_true_eq]
        split_ifs <;> omega
    omega
  · rw [List.countP_eq_zero.2 (fun x _ ↦ by simp; omega)]
    have := List.countP_mono_left (l := l) (p := fun x ↦ decide (x < b))
      (q := fun x ↦ decide (x < a)) (fun x _ h ↦ by simp at h ⊢; omega)
    omega

/-! ## The coverage table: the pairs `(mark, slot)` sorted -/

section Cover

attribute [local instance] lexOrd

theorem compare_pair_lt {a b : ℕ × ℕ} (h : compare a b = .lt) : a.1 ≤ b.1 ∧ (a.1 = b.1 → a.2 < b.2) := by
  rw [show compare a b = (compare a.1 b.1).then (compare a.2 b.2) from rfl,
    Ordering.then_eq_lt, Nat.compare_eq_lt, Nat.compare_eq_eq, Nat.compare_eq_lt] at h
  omega

/-- A key added with the value `0` (the key holds the slot). -/
def coverInsert (m : SortedMap (ℕ × ℕ) ℕ) (p : ℕ × ℕ) : SortedMap (ℕ × ℕ) ℕ := m.insert p 0

/-- A level merged into the newer entries. -/
def mergeLevel (acc : List ((ℕ × ℕ) × ℕ)) (l : Level (ℕ × ℕ) ℕ) : List ((ℕ × ℕ) × ℕ) :=
  mergeNewer acc l.entries.toList

/-- A map's levels merged into one list, sorted by key. -/
def flattenLevels (ls : List (Level (ℕ × ℕ) ℕ)) : List ((ℕ × ℕ) × ℕ) := ls.foldl mergeLevel []

/-- The keys of the pairs `ps` sorted: inserted into a sorted map, its levels merged. -/
def coverKeys (ps : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  (flattenLevels (ps.foldl coverInsert SortedMap.empty).levels).map Prod.fst

/-- **The coverage table** of the pairs `(mark, slot)`: the marks in ascending order and their
slots (ties by slot). -/
def coverTable (ps : List (ℕ × ℕ)) : Array ℕ × Array ℕ :=
  let ks := coverKeys ps
  ((ks.map Prod.fst).toArray, (ks.map Prod.snd).toArray)

/-- **The first slot holding the mark `e`**, `0` if none: one binary search among the marks. -/
def slotIn (tm ts : Array ℕ) (e : ℕ) : ℕ :=
  let i := lowerBound tm e 0 tm.size
  if tm.getD i 0 = e then ts.getD i 0 else 0

/-- **The number of slots whose marks lie in `[a, b)`**: two binary searches. -/
def countIn (tm : Array ℕ) (a b : ℕ) : ℕ := lowerBound tm b 0 tm.size - lowerBound tm a 0 tm.size

theorem get?_foldl_coverInsert (k : ℕ × ℕ) :
    ∀ (ps : List (ℕ × ℕ)) (m : SortedMap (ℕ × ℕ) ℕ),
      (ps.foldl coverInsert m).get? k = if k ∈ ps then some 0 else m.get? k := by
  intro ps
  induction ps with
  | nil => intro m; simp
  | cons p ps ih =>
    intro m
    rw [List.foldl_cons, ih, coverInsert, SortedMap.get?_insert]
    by_cases hk : k ∈ ps
    · simp [hk]
    · by_cases hp : p = k
      · subst hp; simp
      · have : k ∉ p :: ps := by simp [hk, Ne.symm hp]
        simp [hk, hp, this]

theorem foldl_mergeLevel (k : ℕ × ℕ) :
    ∀ (ls : List (Level (ℕ × ℕ) ℕ)) (acc : List ((ℕ × ℕ) × ℕ)), Ascending acc →
      Ascending (ls.foldl mergeLevel acc) ∧
        lookup (ls.foldl mergeLevel acc) k =
          (lookup acc k).or (ls.findSome? fun l ↦ lookup l.entries.toList k) := by
  intro ls
  induction ls with
  | nil => intro acc h; simp [h]
  | cons l ls ih =>
    intro acc h
    have hm : Ascending (mergeLevel acc l) := ascending_mergeNewer h l.sorted
    obtain ⟨h1, h2⟩ := ih _ hm
    refine ⟨h1, ?_⟩
    rw [List.foldl_cons, h2, mergeLevel, lookup_mergeNewer h, List.findSome?_cons]
    cases lookup acc k <;> cases lookup l.entries.toList k <;> rfl

theorem lookup_eq_none_iff {l : List ((ℕ × ℕ) × ℕ)} {k : ℕ × ℕ} :
    lookup l k = none ↔ ∀ e ∈ l, e.1 ≠ k := by
  simp only [lookup, Option.map_eq_none_iff, List.find?_eq_none, beq_iff_eq,
    Std.LawfulEqOrd.compare_eq_iff_eq]

/-- The flattened map: sorted by key, its keys those inserted. -/
theorem coverKeys_spec (ps : List (ℕ × ℕ)) :
    (coverKeys ps).Pairwise (fun a b ↦ compare a b = .lt) ∧ ∀ k, k ∈ coverKeys ps ↔ k ∈ ps := by
  have hasc := (foldl_mergeLevel (0, 0) (ps.foldl coverInsert SortedMap.empty).levels [] (by
    simp [Ascending])).1
  refine ⟨by simpa [coverKeys, flattenLevels, Ascending, List.pairwise_map] using hasc,
    fun k ↦ ?_⟩
  have h := (foldl_mergeLevel k (ps.foldl coverInsert SortedMap.empty).levels [] (by
    simp [Ascending])).2
  rw [lookup_nil, Option.none_or, ← SortedMap.get?_eq, get?_foldl_coverInsert,
    SortedMap.get?_empty] at h
  simp only [coverKeys, flattenLevels, List.mem_map]
  constructor
  · rintro ⟨e, he, rfl⟩
    by_contra hn
    rw [ite_eq_right_of_eq_false _ _ (eq_false hn), lookup_eq_none_iff] at h
    exact h e he rfl
  · intro hk
    rw [ite_eq_left_of_eq_true _ _ (eq_true hk)] at h
    by_contra hn
    have : lookup (List.foldl mergeLevel [] (ps.foldl coverInsert SortedMap.empty).levels) k =
        none := lookup_eq_none_iff.2 fun e he hek ↦ hn ⟨e, he, hek⟩
    rw [this] at h
    exact absurd h (by simp)

/-- The pairs `(mk s, s)` of a region of `len` slots. -/
def regionPairs (mk : ℕ → ℕ) (len : ℕ) : List (ℕ × ℕ) := (List.range len).map fun s ↦ (mk s, s)

theorem nodup_regionPairs (mk : ℕ → ℕ) (len : ℕ) : (regionPairs mk len).Nodup :=
  List.Nodup.map_on (fun a _ b _ h ↦ by simpa using congrArg Prod.snd h) List.nodup_range

/-- **The sorted keys are the region's pairs**, permuted. -/
theorem coverKeys_perm (mk : ℕ → ℕ) (len : ℕ) :
    (coverKeys (regionPairs mk len)).Perm (regionPairs mk len) := by
  obtain ⟨hs, hm⟩ := coverKeys_spec (regionPairs mk len)
  refine (List.perm_ext_iff_of_nodup ?_ (nodup_regionPairs mk len)).2 hm
  exact hs.imp fun {a b} h hab ↦ by subst hab; simp at h

theorem coverKeys_fst_sorted (ps : List (ℕ × ℕ)) :
    ((coverKeys ps).map Prod.fst).Pairwise (· ≤ ·) :=
  List.pairwise_map.2 ((coverKeys_spec ps).1.imp fun h ↦ (compare_pair_lt h).1)

/-- **Counting by the table**: `countIn` is the number of the region's slots whose marks lie in
`[a, b)`. -/
theorem countIn_coverTable (mk : ℕ → ℕ) (len a b : ℕ) :
    countIn (coverTable (regionPairs mk len)).1 a b =
      ((List.range len).filter fun s ↦ decide (a ≤ mk s ∧ mk s < b)).length := by
  have hmono := monotone_toArray (coverKeys_fst_sorted (regionPairs mk len))
  simp only [countIn, coverTable]
  rw [← countP_lt_lowerBound _ hmono, ← countP_lt_lowerBound _ hmono, List.toList_toArray,
    ← countP_Ico, List.countP_map, ← List.countP_eq_length_filter,
    (coverKeys_perm mk len).countP_eq, regionPairs, List.countP_map]
  rfl

/-- On keys sorted by mark, `slotIn` is the first key of mark `e`'s slot, `0` if none. -/
theorem slotIn_eq_find (K : List (ℕ × ℕ)) (hK : (K.map Prod.fst).Pairwise (· ≤ ·)) (e : ℕ) :
    slotIn (K.map Prod.fst).toArray (K.map Prod.snd).toArray e =
      ((K.find? fun p ↦ decide (p.1 = e)).map Prod.snd).getD 0 := by
  have hmono := monotone_toArray hK
  obtain ⟨hr, hlt, hge⟩ := lowerBound_full _ hmono e
  simp only [slotIn]
  generalize lowerBound (K.map Prod.fst).toArray e 0 (K.map Prod.fst).toArray.size = r at *
  simp only [List.size_toArray, List.length_map, List.getElem_toArray, List.getElem_map] at hr hlt hge
  have hKs : ∀ i j (hi : i < K.length) (hj : j < K.length), i ≤ j → K[i].1 ≤ K[j].1 := by
    intro i j hi hj hij
    have := hmono i j (by simpa using hi) (by simpa using hj) hij
    simp only [List.getElem_toArray, List.getElem_map] at this
    exact this
  have htake : (K.take r).find? (fun p ↦ decide (p.1 = e)) = none := by
    refine List.find?_eq_none.2 (fun x hx ↦ ?_)
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simp only [List.getElem_take, decide_eq_true_eq]
    have := hlt i (by simp at hi; omega) (by simp at hi; omega)
    omega
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map]
  conv_rhs => rw [← List.take_append_drop r K, List.find?_append, htake, Option.none_or]
  by_cases hrK : r < K.length
  · rw [List.getElem?_eq_getElem hrK, List.drop_eq_getElem_cons hrK, List.find?_cons]
    simp only [Option.map_some, Option.getD_some]
    by_cases hre : K[r].1 = e
    · simp [hre]
    · simp only [hre, decide_false]
      rw [List.find?_eq_none.2 (fun x hx ↦ ?_)]
      · rfl
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
        simp only [List.getElem_drop, decide_eq_true_eq]
        have h1 := hge r hrK (Nat.le_refl _)
        have h2 := hKs r (r + 1 + i) hrK (by simp at hi; omega) (by omega)
        omega
  · rw [List.drop_eq_nil_of_le (by omega), List.getElem?_eq_none (by omega)]
    simp

/-- **The first slot by the table**: `slotIn` is the first of the region's slots holding the
mark `e`, `0` if none. -/
theorem slotIn_coverTable (mk : ℕ → ℕ) (len e : ℕ) :
    slotIn (coverTable (regionPairs mk len)).1 (coverTable (regionPairs mk len)).2 e =
      ((List.range len).find? fun s ↦ decide (mk s = e)).getD 0 := by
  have hsort := (coverKeys_spec (regionPairs mk len)).1
  have hperm := coverKeys_perm mk len
  -- the first pair of mark `e` in the sorted keys is the region's first
  have hfind : (coverKeys (regionPairs mk len)).find? (fun p ↦ decide (p.1 = e)) =
      (regionPairs mk len).find? (fun p ↦ decide (p.1 = e)) := by
    rw [← List.head?_filter, ← List.head?_filter]
    congr 1
    refine List.Perm.eq_of_pairwise (le := fun p q ↦ p.2 < q.2) (fun _ _ _ _ h h' ↦ by omega)
      ?_ ?_ (hperm.filter _)
    · refine List.pairwise_filter.2 (hsort.imp fun {p q} h hp hq ↦ ?_)
      have := compare_pair_lt h
      simp at hp hq
      exact this.2 (by omega)
    · refine List.Pairwise.filter _ ?_
      simp only [regionPairs, List.pairwise_map]
      exact List.pairwise_lt_range
  have hrange : ((List.range len).find? fun s ↦ decide (mk s = e)) =
      ((regionPairs mk len).find? (fun p ↦ decide (p.1 = e))).map Prod.snd := by
    simp [regionPairs, List.find?_map, Option.map_map, Function.comp_def]
  rw [hrange, ← hfind]
  exact slotIn_eq_find _ (coverKeys_fst_sorted _) e

end Cover

/-! ## The first child whose running count passes a mark -/

/-- **The running maxima** of `xs`, from `acc`. -/
def prefixMax (acc : ℕ) : List ℕ → List ℕ
  | [] => []
  | x :: xs => let m := if acc < x then x else acc; m :: prefixMax m xs

theorem length_prefixMax : ∀ (acc : ℕ) (xs : List ℕ), (prefixMax acc xs).length = xs.length
  | _, [] => rfl
  | _, _ :: xs => by simp [prefixMax, length_prefixMax _ xs]

theorem prefixMax_sorted : ∀ (acc : ℕ) (xs : List ℕ),
    (prefixMax acc xs).Pairwise (· ≤ ·) ∧ ∀ y ∈ prefixMax acc xs, acc ≤ y
  | _, [] => by simp [prefixMax]
  | acc, x :: xs => by
    obtain ⟨h1, h2⟩ := prefixMax_sorted (if acc < x then x else acc) xs
    simp only [prefixMax, List.pairwise_cons, List.mem_cons, forall_eq_or_imp]
    refine ⟨⟨h2, h1⟩, by split <;> omega, fun y hy ↦ ?_⟩
    have := h2 y hy
    split at this <;> omega

/-- **A running maximum passes `e` iff an entry so far does** (or the start). -/
theorem lt_prefixMax_iff (e : ℕ) : ∀ (acc : ℕ) (xs : List ℕ) (c : ℕ) (hc : c < xs.length),
    e < (prefixMax acc xs)[c]'(by rw [length_prefixMax]; exact hc) ↔
      e < acc ∨ ∃ c', ∃ h : c' < xs.length, c' ≤ c ∧ e < xs[c']
  | _, [], _, hc => absurd hc (Nat.not_lt_zero _)
  | acc, x :: xs, 0, _ => by
    simp only [prefixMax, List.getElem_cons_zero]
    constructor
    · intro h
      split at h
      · exact .inr ⟨0, by simp, Nat.le_refl _, by simpa using h⟩
      · exact .inl h
    · rintro (h | ⟨c', hc', h0, h⟩)
      · split <;> omega
      · obtain rfl : c' = 0 := by omega
        simp only [List.getElem_cons_zero] at h
        split <;> omega
  | acc, x :: xs, c + 1, hc => by
    simp only [prefixMax, List.getElem_cons_succ]
    rw [lt_prefixMax_iff e _ xs c (by simpa using hc)]
    constructor
    · rintro (h | ⟨c', hc', h0, h⟩)
      · split at h
        · exact .inr ⟨0, by simp, by omega, by simpa using h⟩
        · exact .inl h
      · exact .inr ⟨c' + 1, by simpa using hc', by omega, by simpa using h⟩
    · rintro (h | ⟨c', hc', h0, h⟩)
      · left; split <;> omega
      · cases c' with
        | zero => left; simp only [List.getElem_cons_zero] at h; split <;> omega
        | succ c' =>
          exact .inr ⟨c', by simpa using hc', by omega, by simpa using h⟩

/-- **The first index whose running maximum passes `e`**, `0` if none: one binary search. -/
def kidIn (M : Array ℕ) (e : ℕ) : ℕ :=
  let i := lowerBound M (e + 1) 0 M.size
  if i < M.size then i else 0

/-- **The first child by the running maxima**: `kidIn` of the running maxima of the counts
`cnt (c + 1)` is the first `c < n` with `e < cnt (c + 1)`, `0` if none. -/
theorem kidIn_prefixMax (cnt : ℕ → ℕ) (n e : ℕ) :
    kidIn (prefixMax 0 ((List.range n).map fun c ↦ cnt (c + 1))).toArray e =
      ((List.range n).find? fun c ↦ decide (e < cnt (c + 1))).getD 0 := by
  set xs := (List.range n).map fun c ↦ cnt (c + 1)
  have hxs : xs.length = n := by simp [xs]
  have hxi : ∀ c (h : c < xs.length), xs[c] = cnt (c + 1) := by intro c h; simp [xs]
  set M := prefixMax 0 xs
  have hML : M.length = n := by rw [length_prefixMax, hxs]
  have hmono := monotone_toArray (prefixMax_sorted 0 xs).1
  obtain ⟨hr, hlt, hge⟩ := lowerBound_full M.toArray hmono (e + 1)
  simp only [kidIn]
  set r := lowerBound M.toArray (e + 1) 0 M.toArray.size
  simp only [List.size_toArray, hML] at hr
  have hiff : ∀ c (hc : c < n), e < M[c]'(by omega) ↔ ∃ c' < n, c' ≤ c ∧ e < cnt (c' + 1) := by
    intro c hc
    rw [lt_prefixMax_iff e 0 xs c (by omega)]
    constructor
    · rintro (h | ⟨c', hc', h0, h⟩)
      · omega
      · exact ⟨c', by omega, h0, by rwa [hxi] at h⟩
    · rintro ⟨c', hc', h0, h⟩
      exact .inr ⟨c', by omega, h0, by rwa [hxi]⟩
  -- below `r` the maxima are at most `e`
  have hnot : ∀ c (hc : c < n), c < r → ¬ e < cnt (c + 1) := by
    intro c hc hcr h
    have h1 := hlt c (by simp; omega) hcr
    simp only [List.getElem_toArray] at h1
    have := (hiff c hc).2 ⟨c, hc, Nat.le_refl _, h⟩
    omega
  by_cases hrn : r < n
  · simp only [List.size_toArray, hML, hrn, ↓reduceIte]
    have h1 := hge r (by simp; omega) (Nat.le_refl _)
    simp only [List.getElem_toArray] at h1
    obtain ⟨c', hc', h0, h⟩ := (hiff r hrn).1 (by omega)
    have hcr : c' = r := by
      by_contra hne
      exact hnot c' hc' (by omega) h
    subst hcr
    rw [(List.find?_range_eq_some).2 ⟨by simpa using h, List.mem_range.2 hc', fun j hj ↦ by
      simpa using hnot j (by omega) hj⟩]
    rfl
  · simp only [List.size_toArray, hML, hrn, ↓reduceIte]
    rw [(List.find?_range_eq_none).2 fun i hi ↦ by simpa using hnot i hi (by omega)]
    rfl

end

end LeanVM.Guest.Fast
