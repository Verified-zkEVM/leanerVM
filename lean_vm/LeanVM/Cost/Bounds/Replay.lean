module

public import LeanVM.Cost.Bounds.Basic
public import LeanVM.Cost.Extractor.Replay

/-!
# Bounds: the verifier's replay up to the stack's root

`afterRootLite bytecode π` (`Cost/Extractor/Replay.lean`) reads eight scalars, builds the
layout's fields the extractor reads (about `163` columns: their log-sizes, their placements on the
stack, sorted by size) and reads the stack's root at the ladder's first level. Its price does not
depend on the proof beyond those ten scalars, and depends on the bytecode only through its length.

The list functions it calls, bounded on lists of word-sized lengths (`W = 2^64`):
* `length_cost`, `rangeLoop_cost`, `getD_cost`, `filter_cost`, `elem_cost`, `take_cost`,
  `drop_cost`, `set_cost`, `zipIdx_cost`, `findIdxGo_cost`, `findIdxOptGo_cost`,
  `replicate_cost'`, `append_cost`, `all_cost`, `reverseAux_cost`;
* `mergeList_cost`, `mergeSortList_cost` (quadratic: here on `163` entries).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Extraction LeanVM.Extraction.Fast

public section

variable (P : Program)

/-! ## Lists -/

section Lists

variable {α : Type} [Enc α]

theorem length_cost (hP : Includes P Auto.List.length.c31.costDeps) :
    ∀ l : List α, l.length < 2 ^ 64 →
      machineCost P Auto.List.length.c31.costIdx [enc l] ≤ 9 * l.length + 3
  | [], _ => by rw [Auto.List.length.c31.costEq_nil P hP]; omega
  | x :: l, h => by
    rw [Auto.List.length.c31.costEq_cons P hP, limbs_of_lt (by simp at h; omega)]
    have := length_cost hP l (by simp at h; omega)
    simp only [List.length_cons]
    omega

theorem rangeLoop_cost (hP : Includes P Auto.List.range.loop.c21.costDeps) :
    ∀ (n : ℕ) (acc : List ℕ), n < 2 ^ 64 →
      machineCost P Auto.List.range.loop.c21.costIdx [enc n, enc acc] ≤ 17 * n + 6
  | 0, acc, _ => by rw [Auto.List.range.loop.c21.costEq_zero P hP]
  | n + 1, acc, h => by
    rw [Auto.List.range.loop.c21.costEq_succ P hP, limbs_of_lt h]
    have := rangeLoop_cost hP n (n :: acc) (by omega)
    omega

theorem getInternal_cost (hP : Includes P Auto.List.get?Internal.c40.costDeps) :
    ∀ (l : List α) (i : ℕ), i < 2 ^ 64 →
      machineCost P Auto.List.get?Internal.c40.costIdx [enc l, enc i] ≤ 15 * l.length + 10
  | [], i, _ => by rw [Auto.List.get?Internal.c40.costEq_nil P hP]; omega
  | x :: l, 0, _ => by rw [Auto.List.get?Internal.c40.costEq_cons P hP]; simp
  | x :: l, i + 1, h => by
    rw [Auto.List.get?Internal.c40.costEq_cons P hP, limbs_of_lt h]
    have := getInternal_cost hP l i (by omega)
    simp only [List.length_cons]
    omega

theorem getD_cost (hP : Includes P Auto.List.getD.c39.costDeps) (l : List α) (i : ℕ) (d : α)
    (hi : i < 2 ^ 64) :
    machineCost P Auto.List.getD.c39.costIdx [enc l, enc i, enc d] ≤ 15 * l.length + 15 := by
  rw [Auto.List.getD.c39.costEq P hP]
  have := getInternal_cost P (by includes) l i hi
  cases l[i]? <;> simp <;> omega

theorem filter_cost (hP : Includes P Auto.List.filter.c29.costDeps) (p : α → Bool) (pVal : Val)
    (hp : ∀ a, RunsApp P pVal [enc a] (enc (p a))) (B : ℕ) :
    ∀ l : List α, (∀ a ∈ l, appCost P pVal [enc a] ≤ B) →
      machineCost P Auto.List.filter.c29.costIdx [pVal, enc l] ≤ (B + 13) * l.length + 3
  | [], _ => by rw [Auto.List.filter.c29.costEq_nil P hP p pVal hp]; omega
  | x :: l, hB => by
    rw [Auto.List.filter.c29.costEq_cons P hP p pVal hp]
    have h1 := filter_cost hP p pVal hp B l fun a ha ↦ hB a (by simp [ha])
    have h2 := hB x (by simp)
    simp only [List.length_cons]
    cases p x <;> simp <;> nlinarith

theorem elem_cost (hP : Includes P Auto.List.elem.c80.costDeps) (a : ℕ) (ha : a < 2 ^ 64) :
    ∀ l : List ℕ, (∀ b ∈ l, b < 2 ^ 64) →
      machineCost P Auto.List.elem.c80.costIdx [enc a, enc l] ≤ 10 * l.length + 3
  | [], _ => by rw [Auto.List.elem.c80.costEq_nil P hP]; omega
  | b :: l, hb => by
    rw [Auto.List.elem.c80.costEq_cons P hP, limbs_of_lt ha, limbs_of_lt (hb b (by simp))]
    have := elem_cost hP a ha l fun c hc ↦ hb c (by simp [hc])
    simp only [List.length_cons]
    cases a == b <;> dsimp only <;> omega

theorem take_cost (hP : Includes P Auto.List.take.c73.costDeps) :
    ∀ (n : ℕ) (l : List α), n < 2 ^ 64 →
      machineCost P Auto.List.take.c73.costIdx [enc n, enc l] ≤ 19 * l.length + 13
  | 0, l, _ => by rw [Auto.List.take.c73.costEq_zero P hP]; omega
  | n + 1, [], h => by rw [Auto.List.take.c73.costEq_succ P hP, limbs_of_lt h]; simp
  | n + 1, x :: l, h => by
    rw [Auto.List.take.c73.costEq_succ P hP, limbs_of_lt h]
    have := take_cost hP n l (by omega)
    simp only [List.length_cons]
    omega

theorem drop_cost (hP : Includes P Auto.List.drop.c74.costDeps) :
    ∀ (n : ℕ) (l : List α), n < 2 ^ 64 →
      machineCost P Auto.List.drop.c74.costIdx [enc n, enc l] ≤ 15 * l.length + 13
  | 0, l, _ => by rw [Auto.List.drop.c74.costEq_zero P hP]; omega
  | n + 1, [], h => by rw [Auto.List.drop.c74.costEq_succ P hP, limbs_of_lt h]; simp
  | n + 1, x :: l, h => by
    rw [Auto.List.drop.c74.costEq_succ P hP, limbs_of_lt h]
    have := drop_cost hP n l (by omega)
    simp only [List.length_cons]
    omega

theorem set_cost (hP : Includes P Auto.List.set.c77.costDeps) (a : α) :
    ∀ (l : List α) (n : ℕ), n < 2 ^ 64 →
      machineCost P Auto.List.set.c77.costIdx [enc l, enc n, enc a] ≤ 20 * l.length + 3
  | [], n, _ => by rw [Auto.List.set.c77.costEq_nil P hP]; omega
  | x :: l, 0, _ => by
    rw [Auto.List.set.c77.costEq_cons P hP]
    simp only [limbs_zero, List.length_cons, Nat.rec_zero]
    omega
  | x :: l, n + 1, h => by
    rw [Auto.List.set.c77.costEq_cons P hP, limbs_of_lt h]
    have := set_cost hP a l n (by omega)
    simp only [List.length_cons]
    omega

theorem zipIdx_cost (hP : Includes P Auto.List.zipIdx.c87.costDeps) :
    ∀ (l : List α) (n : ℕ), n + l.length < 2 ^ 64 →
      machineCost P Auto.List.zipIdx.c87.costIdx [enc l, enc n] ≤ 16 * l.length + 3
  | [], n, _ => by rw [Auto.List.zipIdx.c87.costEq_nil P hP n]; omega
  | x :: l, n, h => by
    rw [Auto.List.zipIdx.c87.costEq_cons P hP x l n, limbs_of_lt (by simp at h; omega)]
    have := zipIdx_cost hP l (n + 1) (by simp at h; omega)
    simp only [List.length_cons]
    omega

theorem findIdxGo_cost (hP : Includes P Auto.List.findIdx.go.c84.costDeps) (p : α → Bool)
    (pVal : Val) (hp : ∀ a, RunsApp P pVal [enc a] (enc (p a))) (B : ℕ) :
    ∀ (l : List α) (n : ℕ), n + l.length < 2 ^ 64 → (∀ a ∈ l, appCost P pVal [enc a] ≤ B) →
      machineCost P Auto.List.findIdx.go.c84.costIdx [pVal, enc l, enc n] ≤
        (B + 13) * l.length + 3
  | [], n, _, _ => by rw [Auto.List.findIdx.go.c84.costEq_nil P hP p pVal hp]; omega
  | x :: l, n, h, hB => by
    rw [Auto.List.findIdx.go.c84.costEq_cons P hP p pVal hp, limbs_of_lt (by simp at h; omega)]
    have h1 := findIdxGo_cost hP p pVal hp B l (n + 1) (by simp at h; omega)
      fun a ha ↦ hB a (by simp [ha])
    have h2 := hB x (by simp)
    simp only [List.length_cons]
    split <;> nlinarith

theorem findIdxOptGo_cost (hP : Includes P Auto.List.findIdx?.go.c68.costDeps) (p : α → Bool)
    (pVal : Val) (hp : ∀ a, RunsApp P pVal [enc a] (enc (p a))) (B : ℕ) :
    ∀ (l : List α) (n : ℕ), n + l.length < 2 ^ 64 → (∀ a ∈ l, appCost P pVal [enc a] ≤ B) →
      machineCost P Auto.List.findIdx?.go.c68.costIdx [pVal, enc l, enc n] ≤
        (B + 13) * l.length + 3
  | [], n, _, _ => by rw [Auto.List.findIdx?.go.c68.costEq_nil P hP p pVal hp]; omega
  | x :: l, n, h, hB => by
    rw [Auto.List.findIdx?.go.c68.costEq_cons P hP p pVal hp, limbs_of_lt (by simp at h; omega)]
    have h1 := findIdxOptGo_cost hP p pVal hp B l (n + 1) (by simp at h; omega)
      fun a ha ↦ hB a (by simp [ha])
    have h2 := hB x (by simp)
    simp only [List.length_cons]
    split <;> nlinarith

theorem replicate_cost' (hP : Includes P Auto.List.replicate.c54.costDeps) (a : α) :
    ∀ n, n < 2 ^ 64 → machineCost P Auto.List.replicate.c54.costIdx [enc n, enc a] ≤ 17 * n + 6
  | 0, _ => by rw [Auto.List.replicate.c54.costEq_zero P hP]
  | n + 1, h => by
    rw [Auto.List.replicate.c54.costEq_succ P hP, limbs_of_lt h]
    have := replicate_cost' hP a n (by omega)
    omega

theorem append_cost (hP : Includes P Auto.List.append.c24.costDeps) (ys : List α) :
    ∀ xs : List α, machineCost P Auto.List.append.c24.costIdx [enc xs, enc ys] ≤ 9 * xs.length + 3
  | [] => by rw [Auto.List.append.c24.costEq_nil P hP]; omega
  | x :: xs => by
    rw [Auto.List.append.c24.costEq_cons P hP]
    have := append_cost hP ys xs
    simp only [List.length_cons]
    omega

theorem flatten_cost (hP : Includes P Auto.List.flatten.c23.costDeps) :
    ∀ xss : List (List α),
      machineCost P Auto.List.flatten.c23.costIdx [enc xss] ≤ 9 * xss.flatten.length + 18 * xss.length + 3
  | [] => by rw [Auto.List.flatten.c23.costEq_nil P hP]; omega
  | xs :: xss => by
    rw [Auto.List.flatten.c23.costEq_cons P hP]
    have h1 := flatten_cost hP xss
    have h2 := append_cost P (by includes) xss.flatten xs
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    omega

theorem all_cost (hP : Includes P Auto.List.all.c95.costDeps) (p : α → Bool) (pVal : Val)
    (hp : ∀ a, RunsApp P pVal [enc a] (enc (p a))) (B : ℕ) :
    ∀ l : List α, (∀ a ∈ l, appCost P pVal [enc a] ≤ B) →
      machineCost P Auto.List.all.c95.costIdx [enc l, pVal] ≤ (B + 9) * l.length + 3
  | [], _ => by rw [Auto.List.all.c95.costEq_nil P hP p pVal hp]; omega
  | x :: l, hB => by
    rw [Auto.List.all.c95.costEq_cons P hP x l p pVal hp]
    have h1 := all_cost hP p pVal hp B l fun a ha ↦ hB a (by simp [ha])
    have h2 := hB x (by simp)
    simp only [List.length_cons]
    split <;> nlinarith

theorem reverseAux_cost (hP : Includes P Auto.List.reverseAux.c6.costDeps) :
    ∀ (xs acc : List α), machineCost P Auto.List.reverseAux.c6.costIdx [enc xs, enc acc] ≤
      9 * xs.length + 3
  | [], acc => by rw [Auto.List.reverseAux.c6.costEq_nil P hP]; omega
  | x :: xs, acc => by
    rw [Auto.List.reverseAux.c6.costEq_cons P hP]
    have := reverseAux_cost hP xs (x :: acc)
    simp only [List.length_cons]
    omega

/-! ## Merge sort -/

theorem mergeList_cost (hP : Includes P Auto.LeanVM.Cost.InitLib.mergeList.c72.costDeps)
    (le : α → α → Bool) (leVal : Val) (hle : ∀ a b, RunsApp P leVal [enc a, enc b] (enc (le a b)))
    (B : ℕ) (S : List α) (hB : ∀ a ∈ S, ∀ b ∈ S, appCost P leVal [enc a, enc b] ≤ B) :
    ∀ (n : ℕ) (xs ys : List α), xs.length + ys.length ≤ n → (∀ a ∈ xs, a ∈ S) →
      (∀ b ∈ ys, b ∈ S) →
      machineCost P Auto.LeanVM.Cost.InitLib.mergeList.c72.costIdx [enc xs, enc ys, leVal] ≤
        (B + 21) * (xs.length + ys.length) + 5 := by
  intro n
  induction n with
  | zero =>
    intro xs ys hn _ _
    cases xs with
    | nil => rw [Auto.LeanVM.Cost.InitLib.mergeList.c72.costEq_nil P hP _ le leVal hle]; omega
    | cons => simp at hn
  | succ n ih =>
    intro xs ys hn hxs hys
    cases xs with
    | nil => rw [Auto.LeanVM.Cost.InitLib.mergeList.c72.costEq_nil P hP _ le leVal hle]; omega
    | cons x xs =>
      rw [Auto.LeanVM.Cost.InitLib.mergeList.c72.costEq_cons P hP x xs ys le leVal hle]
      cases ys with
      | nil =>
        dsimp only
        simp only [List.length_cons, List.length_nil]
        nlinarith
      | cons y ys =>
        have hxy := hB x (hxs x (by simp)) y (hys y (by simp))
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
  exact List.mem_mergeSort.1 h

/-- The merge sort's recurrence closed: two halves `a + b = m` of quadratic price, and linear work. -/
theorem quadratic_halves (B a b T1 T2 M X : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h1 : T1 ≤ (B + 147) * a ^ 2 + 5) (h2 : T2 ≤ (B + 147) * b ^ 2 + 5)
    (hM : M ≤ (B + 21) * (a + b) + 5) (hX : X ≤ 43 * (a + b) + 75) :
    T1 + T2 + M + X ≤ (B + 147) * (a + b) ^ 2 + 5 := by
  have hab : a + b ≤ 2 * (a * b) := by nlinarith
  have hsq : (B + 147) * (a + b) ^ 2 =
      (B + 147) * a ^ 2 + (B + 147) * b ^ 2 + 2 * ((B + 147) * (a * b)) := by ring
  have hK : (B + 147) * (a + b) ≤ 2 * ((B + 147) * (a * b)) := by
    have := Nat.mul_le_mul_left (B + 147) hab
    linarith
  have hBm : (B + 21) * (a + b) + 43 * (a + b) + 85 ≤ (B + 147) * (a + b) := by nlinarith
  omega

/-- **Merge sort** (`mergeSortList`), quadratic: `(B + 147)·n² + 5`, `B` the comparison's price. -/
theorem mergeSortList_cost
    (hP : Includes P Auto.LeanVM.Cost.InitLib.mergeSortList.c71.costDeps)
    (le : α → α → Bool) (leVal : Val) (hle : ∀ a b, RunsApp P leVal [enc a, enc b] (enc (le a b)))
    (B : ℕ) (S : List α) (hB : ∀ a ∈ S, ∀ b ∈ S, appCost P leVal [enc a, enc b] ≤ B) :
    ∀ (n : ℕ) (l : List α), l.length ≤ n → l.length < 2 ^ 63 → (∀ a ∈ l, a ∈ S) →
      machineCost P Auto.LeanVM.Cost.InitLib.mergeSortList.c71.costIdx [enc l, leVal] ≤
        (B + 147) * l.length ^ 2 + 5 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro l hn hw hS
  rcases l with _ | ⟨x, _ | ⟨y, t⟩⟩
  · rw [Auto.LeanVM.Cost.InitLib.mergeSortList.c71.costEq_nil P hP le leVal hle]; omega
  · rw [Auto.LeanVM.Cost.InitLib.mergeSortList.c71.costEq_cons P hP x [] le leVal hle]
    simp only [List.length_cons, List.length_nil]
    nlinarith
  · rw [Auto.LeanVM.Cost.InitLib.mergeSortList.c71.costEq_cons P hP x (y :: t) le leVal hle]
    dsimp only
    simp only [List.length_cons] at hn hw ⊢
    have hw' : t.length + 2 + 1 < 2 ^ 64 := by omega
    set h1 := (t.length + 2 + 1) / 2 with hh1
    rw [limbs_of_lt (by omega : t.length < 2 ^ 64), limbs_of_lt (by omega : t.length + 2 < 2 ^ 64),
      limbs_of_lt hw']
    have hlen := length_cost P (by includes) t (by omega)
    have htake := take_cost P (by includes) h1 (x :: y :: t) (by omega)
    have hdrop := drop_cost P (by includes) h1 (x :: y :: t) (by omega)
    have hlt : (List.take h1 (x :: y :: t)).length = h1 := by simp; omega
    have hld : (List.drop h1 (x :: y :: t)).length = t.length + 2 - h1 := by simp
    have hmemT : ∀ a ∈ List.take h1 (x :: y :: t), a ∈ S :=
      fun a ha ↦ hS a (List.mem_of_mem_take ha)
    have hmemD : ∀ a ∈ List.drop h1 (x :: y :: t), a ∈ S :=
      fun a ha ↦ hS a (List.mem_of_mem_drop ha)
    have ih1 := ih h1 (by omega) (List.take h1 (x :: y :: t)) (by omega) (by omega) hmemT
    have ih2 := ih (t.length + 2 - h1) (by omega) (List.drop h1 (x :: y :: t)) (by omega)
      (by omega) hmemD
    have hmerge := mergeList_cost P (by includes) le leVal hle B S hB (h1 + (t.length + 2 - h1))
      (InitLib.mergeSortList (List.take h1 (x :: y :: t)) le)
      (InitLib.mergeSortList (List.drop h1 (x :: y :: t)) le)
      (by simp only [length_mergeSortList]; omega)
      (fun a ha ↦ hmemT a (mem_mergeSortList ha)) (fun a ha ↦ hmemD a (mem_mergeSortList ha))
    simp only [length_mergeSortList, hlt, hld, List.length_cons] at ih1 ih2 hmerge htake hdrop
    have hsum : h1 + (t.length + 2 - h1) = t.length + 2 := by omega
    have := quadratic_halves B h1 (t.length + 2 - h1) _ _ _
      (machineCost P Auto.List.length.c31.costIdx [enc t] + 3 +
        machineCost P Auto.List.take.c73.costIdx [enc h1, enc (x :: y :: t)] +
        machineCost P Auto.List.drop.c74.costIdx [enc h1, enc (x :: y :: t)] + 41)
      (by omega) (by omega) ih1 ih2 (hmerge.trans (le_of_eq (by rw [hsum]))) (by rw [hsum]; omega)
    rw [hsum] at this
    rw [show t.length + 1 + 1 = t.length + 2 by omega]
    omega

end Lists

end

end LeanVM.Cost.Bounds
