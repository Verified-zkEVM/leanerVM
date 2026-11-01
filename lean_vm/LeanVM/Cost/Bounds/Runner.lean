module

public import LeanVM.Cost.Bounds.Step

/-!
# Bounds: the candidate runner

The runner (`Cost/Extractor/Runner.lean`): its tables built once per layout (`runnerTablesC`),
then per candidate stack the public boundary, the memory vector and the halting loop
(`runWithTablesC`). With `κ ≤ 32` the memory's and `ℓ ≤ 32` the bytecode's log-size, at most six
tables of at most `2^32` rows (the layout's checks in `buildLayoutLite`), and the step cap
`stepCapLite ≤ 2^35`:

* **`mergeSortList_cost_le`**: Init's merge sort, `n log n`: `(B + 64)·n·⌈log₂ n⌉ + 89·n + 3`
  (`B` the comparison's price), for `n < 2^63`;
* **`powTable_cost`**: the address table of `2^κ` words, `(70κ + 374)·2^κ + 20`; `pcFinal_cost`
  (`553 + 535ℓ`), `stepCapLite_cost` (`206`);
* **`runnerTables_cost`**: `(70κ + 374)·2^κ + (70ℓ + 374)·2^ℓ + 535ℓ + 830`; at `κ = ℓ = 32`,
  `5228·2^32 + 17950 ≈ 2^44.35`;
* `boundaryOfStack_cost` (`1500`), `memoryVec_cost` (`44·2^κ + 208`), **`haltLoopVec_cost`**
  (`(S + 45)·n + 20` for fuel `n`, `S` a step's price);
* **`runWithTables_cost`**: one stack, `(runnerStepPrice κ ℓ + 45)·stepCapLite + 44·2^κ + 1796`, with
  `runnerStepPrice κ ℓ = 411697 + 42ℓ + 1092κ` (`stepVec_cost`, `Bounds/Step.lean`); at the worst shape
  **`runWithTables_cost_worst`**: `448030·2^35 + 44·2^32 + 1796 ≈ 2^53.77`;
* **`runner_cost`**: the tables and at most `1 + 2^18` stacks (the fast path's at most one,
  `FastInv`; the decoder's at most `2^18`, `decodeStacksDistinct_length_le_johnson`): at most
  `runnerBudget ≈ 2^71.77`.

Hypotheses: placements' offsets word-sized (`(layout.placement c).index < 2^64`) and the layout's
sizes above; `afterRootLite`'s layouts meet them (`afterRootLite_facts`, offsets below `2^48`) and
`runner_cost_afterRootLite` discharges them (`Bounds/Layout.lean`).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Cost.Library LeanVM.Parameters LeanVM.Semantics
open LeanVM.Extraction.Fast

public section

variable (P : LeanVM.Cost.Program)

section MergeSort
variable {α : Type} [Enc α]

/-- `List.take` (`take.c231`): `19` per element, `13` at the end. -/
theorem takeList_cost (hP : Includes P Auto.List.take.c231.costDeps) :
    ∀ (n : ℕ) (l : List α), n < 2 ^ 64 →
      machineCost P Auto.List.take.c231.costIdx [enc n, enc l] ≤ 19 * l.length + 13
  | 0, l, _ => by rw [Auto.List.take.c231.costEq_zero P hP]; omega
  | n + 1, [], h => by rw [Auto.List.take.c231.costEq_succ P hP, limbs_of_lt h]; simp
  | n + 1, x :: l, h => by
    rw [Auto.List.take.c231.costEq_succ P hP, limbs_of_lt h]
    have := takeList_cost hP n l (by omega)
    simp only [List.length_cons]
    omega

/-- `List.drop` (`drop.c232`): `15` per element, `13` at the end. -/
theorem dropList_cost (hP : Includes P Auto.List.drop.c232.costDeps) :
    ∀ (n : ℕ) (l : List α), n < 2 ^ 64 →
      machineCost P Auto.List.drop.c232.costIdx [enc n, enc l] ≤ 15 * l.length + 13
  | 0, l, _ => by rw [Auto.List.drop.c232.costEq_zero P hP]; omega
  | n + 1, [], h => by rw [Auto.List.drop.c232.costEq_succ P hP, limbs_of_lt h]; simp
  | n + 1, x :: l, h => by
    rw [Auto.List.drop.c232.costEq_succ P hP, limbs_of_lt h]
    have := dropList_cost hP n l (by omega)
    simp only [List.length_cons]
    omega

/-- The merge (`mergeList.c230`): `B + 21` per element, the comparisons on elements of `Q`. -/
theorem mergeList_cost_le (hP : Includes P Auto.LeanVM.Cost.InitLib.mergeList.c230.costDeps)
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
theorem length_mergeSortList_eq (l : List α) (le : α → α → Bool) :
    (InitLib.mergeSortList l le).length = l.length := by
  rw [← InitLib.mergeSort_eq_mergeSortList, List.length_mergeSort]

omit [Enc α] in
theorem mem_of_mem_mergeSortList {l : List α} {le : α → α → Bool} {a : α}
    (h : a ∈ InitLib.mergeSortList l le) : a ∈ l := by
  rw [← InitLib.mergeSort_eq_mergeSortList] at h
  exact List.mem_mergeSort.1 h

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
    have hlen := listLength_cost P (by includes) t (by omega)
    have htake := takeList_cost P (by includes) h1 (x :: y :: t) (by omega)
    have hdrop := dropList_cost P (by includes) h1 (x :: y :: t) (by omega)
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
    have hmerge := mergeList_cost_le P (by includes) le leVal hle B Q hB (h1 + (t.length + 2 - h1))
      (InitLib.mergeSortList (List.take h1 (x :: y :: t)) le)
      (InitLib.mergeSortList (List.drop h1 (x :: y :: t)) le)
      (by simp only [length_mergeSortList_eq]; omega)
      (fun a ha ↦ hmemT a (mem_of_mem_mergeSortList ha))
      (fun a ha ↦ hmemD a (mem_of_mem_mergeSortList ha))
    simp only [length_mergeSortList_eq, hlt, hld, List.length_cons] at ih1 ih2 hmerge htake hdrop
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
theorem mergeSortList_cost_le
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

end MergeSort

/-! ## The runner's tables -/

section Tables
open Auto.LeanVM.Extraction.Fast

theorem length_powPairs : ∀ (n i : ℕ) (x : K), (powPairs n i x).length = n
  | 0, _, _ => rfl
  | n + 1, i, x => by rw [powPairs, List.length_cons, length_powPairs n]

theorem mem_powPairs : ∀ (n i : ℕ) (x : K) (e : ℕ × ℕ), e ∈ powPairs n i x →
    e.1 < 2 ^ 64 ∧ e.2 < i + n
  | 0, _, _, e, h => by simp [powPairs] at h
  | n + 1, i, x, e, h => by
    rw [powPairs, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨UInt64.toNat_lt _, by dsimp only; omega⟩
    · have := mem_powPairs n (i + 1) (x * LeanVM.Parameters.g) e h
      omega

theorem powTable_size (κ : ℕ) : (powTable κ).size = 2 ^ κ := by
  rw [powTable, List.size_toArray, List.length_mergeSort, length_powPairs]

/-- The address table of `2^κ` words, `κ ≤ 62`, is a table of word-sized pairs. -/
theorem wordTable_powTable {κ : ℕ} (hκ : κ ≤ 62) : WordTable (powTable κ) := by
  refine ⟨by rw [powTable_size]; exact Nat.pow_lt_pow_right (by norm_num) (by omega), ?_⟩
  intro e he
  rw [powTable, List.toList_toArray, List.mem_mergeSort] at he
  have := mem_powPairs _ _ _ e he
  have : 2 ^ κ < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

/-- The pairs `(lane of g^i, i)` (`powPairs.c373`): `284` per pair, `6` at the end. -/
theorem powPairs_cost (hP : Includes P powPairs.c373.costDeps) :
    ∀ (n i : ℕ) (x : K), n + i < 2 ^ 64 →
      machineCost P powPairs.c373.costIdx [enc n, enc i, enc x] ≤ 284 * n + 6
  | 0, i, x, _ => by rw [powPairs.c373.costEq_zero P hP]
  | n + 1, i, x, h => by
    rw [powPairs.c373.costEq_succ P hP, limbs_of_lt (by omega : n + 1 < 2 ^ 64),
      limbs_of_lt (by omega : i < 2 ^ 64)]
    have := powPairs_cost hP n (i + 1) (x * LeanVM.Parameters.g) (by omega)
    omega

/-- **The address table** (`powTable.c371`) of `2^κ` words: `2^κ` powers and their merge sort, at
most `(70κ + 374)·2^κ + 20`. -/
theorem powTable_cost (hP : Includes P powTable.c371.costDeps) (κ : ℕ) (hκ : κ ≤ 62) :
    machineCost P powTable.c371.costIdx [enc κ] ≤ (70 * κ + 374) * 2 ^ κ + 20 := by
  rw [powTable.c371.costEq P hP, limbs_shift (by omega), limbs_of_lt (by omega : κ < 2 ^ 64),
    List.length_mergeSort, length_powPairs]
  have hN : 2 ^ κ < 2 ^ 63 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h1 := powPairs_cost P (by includes) (2 ^ κ) 0 1 (by omega)
  have h2 := mergeSortList_cost_le P (by includes) _ (.fn powTable.c371.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (powTable.c371.lam0.costSpec P (by includes) a b)) 6
    (fun e ↦ e.1 < 2 ^ 64)
    (fun a b ha hb ↦ by
      simp only [appCost_fn, List.nil_append]
      rw [powTable.c371.lam0.costEq P (by includes), limbs_of_lt ha, limbs_of_lt hb]
      omega)
    (powPairs (2 ^ κ) 0 1) (by rw [length_powPairs]; exact hN)
    (fun e he ↦ (mem_powPairs _ _ _ e he).1)
  rw [length_powPairs, Nat.clog_pow 2 κ (by norm_num)] at h2
  have : (70 * κ + 374) * 2 ^ κ = 70 * (2 ^ κ * κ) + 374 * 2 ^ κ := by ring
  omega

/-- The final `pc` (`pcFinal.c374`): `g^(2^ℓ − 1)` by squaring, at most `553 + 535·ℓ`. -/
theorem pcFinal_cost (hP : Includes P Auto.LeanVM.Semantics.Program.pcFinal.c374.costDeps)
    (prog : Semantics.Program) :
    machineCost P Auto.LeanVM.Semantics.Program.pcFinal.c374.costIdx [enc prog] ≤
      553 + 535 * prog.logSize := by
  have hls : prog.logSize ≤ 32 := prog.logSize_le
  rw [Auto.LeanVM.Semantics.Program.pcFinal.c374.costEq P hP, limbs_shift (by omega),
    limbs_of_lt (by omega : prog.logSize < 2 ^ 64), limbs_two_pow (by omega)]
  have h2 : 2 ^ prog.logSize ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hls
  have := powSq_cost P (by includes) LeanVM.Parameters.g (2 ^ prog.logSize - 1) (by omega)
  have hlog : Nat.log2 (2 ^ prog.logSize - 1) ≤ prog.logSize := by
    rcases Nat.eq_zero_or_pos prog.logSize with h0 | hpos
    · rw [h0]; simp
    · have := log2_lt_of hpos (by have := Nat.one_le_two_pow (n := prog.logSize); omega :
        2 ^ prog.logSize - 1 < 2 ^ prog.logSize)
      omega
  have := Nat.mul_le_mul_left 535 (Nat.add_le_add_right hlog 1)
  omega

theorem sum_pow_le (l : List ℕ) (hl : ∀ h ∈ l, h ≤ 32) :
    (l.map (2 ^ ·)).sum ≤ l.length * 2 ^ 32 := by
  induction l with
  | nil => simp
  | cons h l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := ih (fun x hx ↦ hl x (by simp [hx]))
    have : 2 ^ h ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (hl h (by simp))
    nlinarith

theorem foldr_add_eq (l : List ℕ) : List.foldr (fun x1 x2 ↦ x1 + x2) 0 l = l.sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.foldr_cons, ih, List.sum_cons]

/-- `List.sum` (`sum.c376`) of word-sized partial sums: `13` per element, `7` at the end. -/
theorem listSum_cost (hP : Includes P Auto.List.sum.c376.costDeps) (l : List ℕ)
    (hl : l.sum < 2 ^ 64) : machineCost P Auto.List.sum.c376.costIdx [enc l] ≤ 13 * l.length + 7 := by
  rw [Auto.List.sum.c376.costEq P hP]
  have hF : Includes P Auto.List.foldr.c86.costDeps := by includes
  have hf : ∀ a b : ℕ, RunsApp P (.fn Auto.List.sum.c376.lam0.costIdx []) [enc a, enc b] (enc (a + b)) :=
    fun a b ↦ RunsApp.of_spec (Auto.List.sum.c376.lam0.costSpec P (by includes) a b)
  suffices ∀ l : List ℕ, l.sum < 2 ^ 64 → machineCost P Auto.List.foldr.c86.costIdx
      [.fn Auto.List.sum.c376.lam0.costIdx [], enc 0, enc l] ≤ 13 * l.length + 3 by
    have := this l hl; omega
  intro l
  induction l with
  | nil => intro _; rw [Auto.List.foldr.c86.costEq_nil P hF _ _ hf]; omega
  | cons x l ih =>
    intro hs
    rw [Auto.List.foldr.c86.costEq_cons P hF _ _ hf, foldr_add_eq]
    simp only [List.sum_cons] at hs
    simp only [appCost_fn, List.nil_append]
    rw [Auto.List.sum.c376.lam0.costEq P (by includes), limbs_of_lt (by omega : x < 2 ^ 64),
      limbs_of_lt (by omega : l.sum < 2 ^ 64)]
    have := ih (by omega)
    simp only [List.length_cons, max_self]
    omega

/-- The step cap (`stepCapLite.c375`) of a layout of at most six tables of at most `2^32` rows, at
most `2^32` memory and bytecode words: at most `206`; the cap itself at most `2^35`. -/
theorem stepCapLite_cost (hP : Includes P stepCapLite.c375.costDeps) (layout : LayoutLite)
    (hm : layout.logMemory ≤ 32) (hb : layout.logBytecode ≤ 32)
    (hh : ∀ h ∈ layout.tableLogHeights, h ≤ 32) (hl : layout.tableLogHeights.length ≤ 6) :
    machineCost P stepCapLite.c375.costIdx [enc layout] ≤ 206 := by
  rw [stepCapLite.c375.costEq P hP]
  have hs := sum_pow_le _ hh
  have hm2 : 2 ^ layout.logMemory ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hm
  have hb2 : 2 ^ layout.logBytecode ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hb
  have h1 := map_cost P (by includes) _ (.fn stepCapLite.c375.lam0.costIdx [])
    (fun x ↦ RunsApp.of_spec (stepCapLite.c375.lam0.costSpec P (by includes) x)) 5
    layout.tableLogHeights (fun x hx ↦ by
      simp only [appCost_fn, List.nil_append]
      have := hh x hx
      rw [stepCapLite.c375.lam0.costEq P (by includes), limbs_shift (by omega),
        limbs_of_lt (by omega : x < 2 ^ 64)])
  have h2 := listSum_cost P (by includes) (layout.tableLogHeights.map (2 ^ ·)) (by nlinarith)
  rw [List.length_map] at h2
  rw [limbs_shift (by omega), limbs_of_lt (by omega : layout.logMemory < 2 ^ 64),
    limbs_shift (by omega), limbs_of_lt (by omega : layout.logBytecode < 2 ^ 64),
    limbs_of_lt (by nlinarith : (layout.tableLogHeights.map (2 ^ ·)).sum < 2 ^ 64),
    limbs_two_pow (by omega : layout.logMemory < 64), limbs_two_pow (by omega : layout.logBytecode < 64),
    limbs_of_lt (by nlinarith : (layout.tableLogHeights.map (2 ^ ·)).sum + 2 ^ layout.logMemory < 2 ^ 64)]
  simp only [max_self]
  omega

theorem stepCapLite_le (layout : LayoutLite) (hm : layout.logMemory ≤ 32) (hb : layout.logBytecode ≤ 32)
    (hh : ∀ h ∈ layout.tableLogHeights, h ≤ 32) (hl : layout.tableLogHeights.length ≤ 6) :
    stepCapLite layout ≤ 2 ^ 35 := by
  have hs := sum_pow_le _ hh
  have hm2 : 2 ^ layout.logMemory ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hm
  have hb2 : 2 ^ layout.logBytecode ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hb
  unfold stepCapLite
  nlinarith

end Tables

/-- **The runner's tables** (`runnerTablesC`): the memory's and the code's address tables, the
final `pc`, the step cap: at most `(70·κ + 374)·2^κ + (70·ℓ + 374)·2^ℓ + 535·ℓ + 830`, `κ` the
memory's and `ℓ` the bytecode's log-size. -/
theorem runnerTables_cost (hP : Includes P runnerTablesC.costDeps) (prog : Semantics.Program)
    (layout : LayoutLite) (hm : layout.logMemory ≤ 32) (hb : layout.logBytecode ≤ 32)
    (hh : ∀ h ∈ layout.tableLogHeights, h ≤ 32) (hl : layout.tableLogHeights.length ≤ 6) :
    machineCost P runnerTablesC.costIdx [enc prog, enc layout] ≤
      (70 * layout.logMemory + 374) * 2 ^ layout.logMemory +
        (70 * prog.logSize + 374) * 2 ^ prog.logSize + 535 * prog.logSize + 830 := by
  have hls : prog.logSize ≤ 32 := prog.logSize_le
  rw [runnerTablesC.costEq P hP, limbs_of_lt (by omega : layout.logMemory < 2 ^ 64)]
  have h1 := powTable_cost P (by includes) layout.logMemory (by omega)
  have h2 := powTable_cost P (by includes) prog.logSize (by omega)
  have h3 := pcFinal_cost P (by includes) prog
  have h4 := stepCapLite_cost P (by includes) layout hm hb hh hl
  split_ifs <;> omega

/-! ## A stack -/

section Stack
open Auto.LeanVM.Extraction.Fast

theorem placementGetD_cost (hP : Includes P Auto.List.getD.c274.costDeps) (layout : LayoutLite)
    (c : ℕ) (hc : c ≤ 2) :
    machineCost P Auto.List.getD.c274.costIdx
      [enc layout.placements, enc c, enc (none : Option LeanVM.Protocol.Verifier.Placement)] ≤ 45 := by
  have := getD_cost_idx P hP layout.placements c (by omega) none
  omega

/-- A word of the memory image (`memoryImageLite.c382`): three placements and three stack reads,
at most `199`. -/
theorem memoryImageLite_cost (hP : Includes P memoryImageLite.c382.costDeps) (layout : LayoutLite)
    (hm : layout.logMemory < 64) (hidx : ∀ c, (layout.placement c).index < 2 ^ 64) {μ : ℕ}
    (q : Vector K (2 ^ μ)) (a : Fin (2 ^ layout.logMemory)) :
    machineCost P memoryImageLite.c382.costIdx [enc layout, enc μ, enc q, enc a] ≤ 199 := by
  rw [memoryImageLite.c382.costEq P hP]
  have hD : Includes P Auto.List.getD.c274.costDeps := by includes
  have h0 := placementGetD_cost P hD layout LeanVM.Protocol.Verifier.memory0 (by decide)
  have h1 := placementGetD_cost P hD layout LeanVM.Protocol.Verifier.memory1 (by decide)
  have h2 := placementGetD_cost P hD layout LeanVM.Protocol.Verifier.memory2 (by decide)
  have ha : (a : ℕ) < 2 ^ 64 := lt_trans a.isLt (Nat.pow_lt_pow_right (by norm_num) hm)
  rw [limbs_of_lt ha, limbs_of_lt (hidx _), limbs_of_lt (hidx _), limbs_of_lt (hidx _)]
  simp only [max_self]
  generalize layout.placements.getD LeanVM.Protocol.Verifier.memory0 none = o0
  generalize layout.placements.getD LeanVM.Protocol.Verifier.memory1 none = o1
  generalize layout.placements.getD LeanVM.Protocol.Verifier.memory2 none = o2
  cases o0 <;> cases o1 <;> cases o2 <;> dsimp only <;> omega

theorem word01_cost (hP : Includes P Auto.LeanVM.Semantics.PublicInput.word0.c383.costDeps)
    (hP' : Includes P Auto.LeanVM.Semantics.PublicInput.word1.c385.costDeps) (input : PublicInput) :
    machineCost P Auto.LeanVM.Semantics.PublicInput.word0.c383.costIdx [enc input] = 25 ∧
      machineCost P Auto.LeanVM.Semantics.PublicInput.word1.c385.costIdx [enc input] = 25 := by
  have hF : Includes P Auto.Fin.ofNat.c384.costDeps := by includes
  rw [Auto.LeanVM.Semantics.PublicInput.word0.c383.costEq P hP,
    Auto.LeanVM.Semantics.PublicInput.word1.c385.costEq P hP']
  simp only [Auto.Fin.ofNat.c384.costEq P hF]
  constructor <;> cost_simp

/-- **The public boundary** (`boundaryOfStack.c381`): the memory's words `0` and `1` against the
public input, at most `1500`. -/
theorem boundaryOfStack_cost (hP : Includes P boundaryOfStack.c381.costDeps) (input : PublicInput)
    (layout : LayoutLite) (hm : layout.logMemory < 64) (hidx : ∀ c, (layout.placement c).index < 2 ^ 64)
    {μ : ℕ} (q : Vector K (2 ^ μ)) :
    machineCost P boundaryOfStack.c381.costIdx [enc input, enc layout, enc μ, enc q] ≤ 1500 := by
  rw [boundaryOfStack.c381.costEq P hP]
  obtain ⟨hw0, hw1⟩ := word01_cost P (by includes) (by includes) input
  rw [hw0, hw1, limbs_of_lt (by omega : layout.logMemory < 2 ^ 64),
    limbs_of_lt (show minLogMem < 2 ^ 64 by unfold minLogMem; norm_num),
    limbs_of_lt (show maxLogMem < 2 ^ 64 by unfold maxLogMem; norm_num)]
  have hall := memoryImageLite_cost P (by includes) layout hm hidx q
  have h0 := hall ⟨0, Nat.two_pow_pos _⟩
  by_cases hc : minLogMem ≤ layout.logMemory ∧ layout.logMemory ≤ maxLogMem
  · have h1 := hall ⟨1, Nat.one_lt_two_pow (by unfold minLogMem at hc; omega)⟩
    split_ifs <;> omega
  · split_ifs <;> omega

/-- **The memory vector** (`memoryVec.c386`): three placements, then `2^κ` words of three limbs:
at most `44·2^κ + 208`. -/
theorem memoryVec_cost (hP : Includes P memoryVec.c386.costDeps) (layout : LayoutLite)
    (hm : layout.logMemory < 64) (hidx : ∀ c, (layout.placement c).index < 2 ^ 64) {μ : ℕ}
    (q : Vector K (2 ^ μ)) :
    machineCost P memoryVec.c386.costIdx [enc layout, enc μ, enc q] ≤ 44 * 2 ^ layout.logMemory + 208 := by
  rw [memoryVec.c386.costEq P hP, ofFnFrom_length]
  have hD : Includes P Auto.List.getD.c274.costDeps := by includes
  have h0 := placementGetD_cost P hD layout LeanVM.Protocol.Verifier.memory0 (by decide)
  have h1 := placementGetD_cost P hD layout LeanVM.Protocol.Verifier.memory1 (by decide)
  have h2 := placementGetD_cost P hD layout LeanVM.Protocol.Verifier.memory2 (by decide)
  have hN : 2 ^ layout.logMemory < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hm
  have hof := ofFnFrom_cost P (by includes) hN _
    (.fn memoryVec.c386.lam0.costIdx [enc layout, enc μ, enc q,
      enc (layout.placement LeanVM.Protocol.Verifier.memory0).index,
      enc (layout.placement LeanVM.Protocol.Verifier.memory2).index,
      enc (layout.placement LeanVM.Protocol.Verifier.memory1).index])
    (fun i ↦ RunsApp.of_spec (memoryVec.c386.lam0.costSpec P (by includes) layout q _ _ _ i)) 25
    (fun i ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [memoryVec.c386.lam0.costEq P (by includes), limbs_of_lt (lt_trans i.isLt hN),
        limbs_of_lt (hidx _), limbs_of_lt (hidx _), limbs_of_lt (hidx _)]
      simp only [max_self]
      omega) 0 (Nat.zero_le _)
  rw [limbs_shift hm, limbs_of_lt (by omega : layout.logMemory < 2 ^ 64)]
  simp only [Nat.sub_zero] at hof
  generalize layout.placements.getD LeanVM.Protocol.Verifier.memory0 none = o0
  generalize layout.placements.getD LeanVM.Protocol.Verifier.memory1 none = o1
  generalize layout.placements.getD LeanVM.Protocol.Verifier.memory2 none = o2
  cases o0 <;> cases o1 <;> cases o2 <;> dsimp only <;> omega

end Stack


/-! ## The halting loop and a stack -/

section Loop
open Auto.LeanVM.Extraction.Fast

/-- **The halting loop** (`haltLoopVec.c389`): `n` steps at most, each one step's price (at most
`S`) and `45`; `20` at the end. The step counter `a` stays a word. -/
theorem haltLoopVec_cost (hP : Includes P haltLoopVec.c389.costDeps)
    (memT codeT : Array (ℕ × ℕ)) (prog : LeanVM.Semantics.Program) {κ : ℕ} (mem : Vector E (2 ^ κ))
    (fin : Registers K) (S : ℕ)
    (hS : ∀ r : Registers K, machineCost P Auto.LeanVM.Extraction.Fast.stepVec.c390.costIdx
      [enc memT, enc codeT, enc prog, enc κ, enc mem, enc r] ≤ S) :
    ∀ (n a : ℕ) (r : Registers K), n + a < 2 ^ 64 →
      machineCost P Auto.LeanVM.Extraction.Fast.haltLoopVec.c389.costIdx
        [enc memT, enc codeT, enc prog, enc κ, enc mem, enc fin, enc n, enc a, enc r] ≤
        (S + 45) * n + 20 := by
  intro n
  induction n with
  | zero =>
    intro a r _
    rw [Auto.LeanVM.Extraction.Fast.haltLoopVec.c389.costEq_zero P hP]
    split_ifs <;> omega
  | succ n ih =>
    intro a r hna
    rw [Auto.LeanVM.Extraction.Fast.haltLoopVec.c389.costEq_succ P hP,
      limbs_of_lt (by omega : n + 1 < 2 ^ 64)]
    have hs := hS r
    generalize hst : stepVec memT codeT prog mem r = o
    cases o with
    | none => split_ifs <;> (try dsimp only) <;> nlinarith
    | some r' =>
      have := ih (a + 1) r' (by omega)
      rw [limbs_of_lt (by omega : a < 2 ^ 64)]
      split_ifs <;> (try dsimp only) <;> nlinarith


/-- **A stack's execution** (`candidateExecutionVec.c380`): the boundary, then the memory vector
and the halting loop of fuel `cap`: at most `(S + 45)·cap + 44·2^κ + 1777`. -/
theorem candidateExecutionVec_cost (hP : Includes P candidateExecutionVec.c380.costDeps)
    (memT codeT : Array (ℕ × ℕ)) (prog : Semantics.Program) (input : PublicInput) (layout : LayoutLite)
    (hm : layout.logMemory < 64) (hidx : ∀ c, (layout.placement c).index < 2 ^ 64)
    (fin : Registers K) (cap : ℕ) (hcap : cap < 2 ^ 64) {μ : ℕ} (q : Vector K (2 ^ μ)) (S : ℕ)
    (hS : ∀ r : Registers K, machineCost P stepVec.c390.costIdx
      [enc memT, enc codeT, enc prog, enc layout.logMemory, enc (memoryVec layout q), enc r] ≤ S) :
    machineCost P candidateExecutionVec.c380.costIdx
        [enc memT, enc codeT, enc prog, enc input, enc layout, enc fin, enc cap, enc μ, enc q] ≤
      (S + 45) * cap + 44 * 2 ^ layout.logMemory + 1777 := by
  rw [candidateExecutionVec.c380.costEq P hP]
  have h1 := boundaryOfStack_cost P (by includes) input layout hm hidx q
  have h2 := memoryVec_cost P (by includes) layout hm hidx q
  have h3 := haltLoopVec_cost P (by includes) memT codeT prog (memoryVec layout q) fin S hS cap 0
    Registers.initial (by omega)
  have h4 := optionMap_cost P (by includes) _
    (.fn candidateExecutionVec.c380.lam0.costIdx [enc prog, enc layout, enc (memoryVec layout q)])
    (fun n ↦ RunsApp.of_spec (candidateExecutionVec.c380.lam0.costSpec P (by includes) prog layout _ n)) 8
    (fun n ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [candidateExecutionVec.c380.lam0.costEq P (by includes)])
    (haltLoopVec memT codeT prog (memoryVec layout q) fin cap 0 Registers.initial)
  split_ifs <;> omega

/-- **One stack, from the runner's tables** (`runWithTablesC`): at most
`(runnerStepPrice κ ℓ + 45)·stepCapLite + 44·2^κ + 1796`. -/
theorem runWithTables_cost (hP : Includes P runWithTablesC.costDeps) (prog : Semantics.Program)
    (input : PublicInput) (layout : LayoutLite) (hm : layout.logMemory ≤ 32)
    (hb : layout.logBytecode ≤ 32) (hh : ∀ h ∈ layout.tableLogHeights, h ≤ 32)
    (hl : layout.tableLogHeights.length ≤ 6) (hidx : ∀ c, (layout.placement c).index < 2 ^ 64)
    (q : Vector K (2 ^ layout.stackLog)) :
    machineCost P runWithTablesC.costIdx
        [enc (runnerTables prog layout), enc prog, enc input, enc layout, enc q] ≤
      (runnerStepPrice layout.logMemory prog.logSize + 45) * stepCapLite layout +
        44 * 2 ^ layout.logMemory + 1796 := by
  have hls : prog.logSize ≤ 32 := prog.logSize_le
  have hcap := stepCapLite_le layout hm hb hh hl
  unfold runnerTables
  simp only [show layout.logMemory < 64 by omega, ↓reduceIte]
  rw [runWithTablesC.costEq_some P hP]
  dsimp only
  have := candidateExecutionVec_cost P (by includes) (powTable layout.logMemory) (powTable prog.logSize)
    prog input layout (by omega) hidx (Registers.final prog) (stepCapLite layout)
    (lt_of_le_of_lt hcap (by norm_num)) q (runnerStepPrice layout.logMemory prog.logSize)
    (fun r ↦ by
      have := stepVec_cost P (by includes) (powTable layout.logMemory) (powTable prog.logSize)
        (wordTable_powTable (by omega)) (wordTable_powTable (by omega)) prog (by omega)
        (memoryVec layout q) r
      rw [powTable_size, powTable_size, Nat.log2_two_pow, Nat.log2_two_pow] at this
      unfold runnerStepPrice
      omega)
  omega

/-- **One stack at the worst shape** (`κ, ℓ ≤ 32`, at most six tables of at most `2^32` rows):
at most `448030·2^35 + 44·2^32 + 1796` (`≈ 2^53.77`). -/
theorem runWithTables_cost_worst (hP : Includes P runWithTablesC.costDeps) (prog : Semantics.Program)
    (input : PublicInput) (layout : LayoutLite) (hm : layout.logMemory ≤ 32)
    (hb : layout.logBytecode ≤ 32) (hh : ∀ h ∈ layout.tableLogHeights, h ≤ 32)
    (hl : layout.tableLogHeights.length ≤ 6) (hidx : ∀ c, (layout.placement c).index < 2 ^ 64)
    (q : Vector K (2 ^ layout.stackLog)) :
    machineCost P runWithTablesC.costIdx
        [enc (runnerTables prog layout), enc prog, enc input, enc layout, enc q] ≤
      448030 * 2 ^ 35 + 44 * 2 ^ 32 + 1796 := by
  have hls : prog.logSize ≤ 32 := prog.logSize_le
  have h := runWithTables_cost P hP prog input layout hm hb hh hl hidx q
  have hcap := stepCapLite_le layout hm hb hh hl
  have hS : runnerStepPrice layout.logMemory prog.logSize + 45 ≤ 448030 := by unfold runnerStepPrice; omega
  have h2 : 2 ^ layout.logMemory ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hm
  have := Nat.mul_le_mul hS hcap
  omega

end Loop

/-! ## The runner -/

/-- The runner's budget at the worst shape: the tables, and `1 + 2^18` stacks. -/
@[expose] def runnerBudget : ℕ :=
  (5228 * 2 ^ 32 + 17950) + (2 ^ 18 + 1) * (448030 * 2 ^ 35 + 44 * 2 ^ 32 + 1796)

theorem runnerBudget_lt : runnerBudget < 2 ^ 72 := by unfold runnerBudget; norm_num

/-- **The runner** at the worst shape: its tables once, and at most `1 + 2^18` candidate stacks
(at most one from the fast path, at most `2^18` from the decoder): at most `runnerBudget`
(`≈ 2^71.77`). -/
theorem runner_cost (hT : Includes P runnerTablesC.costDeps) (hW : Includes P runWithTablesC.costDeps)
    (prog : Semantics.Program) (input : PublicInput) (layout : LayoutLite)
    (hm : layout.logMemory ≤ 32) (hb : layout.logBytecode ≤ 32)
    (hh : ∀ h ∈ layout.tableLogHeights, h ≤ 32) (hl : layout.tableLogHeights.length ≤ 6)
    (hidx : ∀ c, (layout.placement c).index < 2 ^ 64) (qs : List (Vector K (2 ^ layout.stackLog)))
    (hqs : qs.length ≤ 2 ^ 18 + 1) :
    machineCost P runnerTablesC.costIdx [enc prog, enc layout] +
        (qs.map fun q ↦ machineCost P runWithTablesC.costIdx
          [enc (runnerTables prog layout), enc prog, enc input, enc layout, enc q]).sum ≤
      runnerBudget := by
  have hls : prog.logSize ≤ 32 := prog.logSize_le
  have h1 := runnerTables_cost P hT prog layout hm hb hh hl
  have hm2 : (70 * layout.logMemory + 374) * 2 ^ layout.logMemory ≤ (70 * 32 + 374) * 2 ^ 32 :=
    Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by norm_num) hm)
  have hl2 : (70 * prog.logSize + 374) * 2 ^ prog.logSize ≤ (70 * 32 + 374) * 2 ^ 32 :=
    Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by norm_num) hls)
  have h2 : (qs.map fun q ↦ machineCost P runWithTablesC.costIdx
      [enc (runnerTables prog layout), enc prog, enc input, enc layout, enc q]).sum ≤
      qs.length * (448030 * 2 ^ 35 + 44 * 2 ^ 32 + 1796) := by
    have := List.sum_le_length_nsmul (qs.map fun q ↦ machineCost P runWithTablesC.costIdx
      [enc (runnerTables prog layout), enc prog, enc input, enc layout, enc q])
      (448030 * 2 ^ 35 + 44 * 2 ^ 32 + 1796) (fun x hx ↦ by
        obtain ⟨q, _, rfl⟩ := List.mem_map.1 hx
        exact runWithTables_cost_worst P hW prog input layout hm hb hh hl hidx q)
    simpa using this
  have h3 := Nat.mul_le_mul_right (448030 * 2 ^ 35 + 44 * 2 ^ 32 + 1796) hqs
  unfold runnerBudget
  omega

end

end LeanVM.Cost.Bounds
