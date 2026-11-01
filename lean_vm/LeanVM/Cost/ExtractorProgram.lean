module

public import LeanVM.Cost.Extractor.Top

/-!
# The extractor's program

`extractorProgram`, the cost-machine program `LeanVM.ExtractorEfficient`
(`Statement/CostMachine.lean`) is proved of: function `0` is the entry `entryBody j`, which
destructures the input `encode prog input T proof` (a constructor of four fields), calls function
`j = extractorC.costIdx` (the compiled `extractorTop`, `Cost/Extractor/Top.lean`) on them and
unwraps its optional output; the other functions are the bodies the compiled extractor's spec
needs (`extractorC.costDeps`, sorted by index, all past `0`: the compiler allocates indices from
`1`).

* `includes_ofList`: a program built by `Program.ofList` holds its bodies if their indices are
  distinct; `nodup_of_increasing`: they are if they increase (a linear check, by evaluation);
* `size_ofList_le`: its size is at most its bodies' sizes plus two per index, a sum to evaluate,
  not an array to build. The evaluation for `extractorProgram` is in
  `Cost/ExtractorSize.lean`, a module of its own (it is slow).
-/

namespace LeanVM.Cost

open LeanVM.Cost.Extractor

public section

/-- **The entry body**: the input's four fields passed to function `j`, its optional output
unwrapped. -/
@[expose] def entryBody (j : ℕ) : Term :=
  .case (.var 0) [.case (.call j [.var 0, .var 1, .var 2, .var 3]) [.ctor 0 [], .var 0]]

/-- The extractor program's bodies: the entry at `0`, then the compiled extractor's. -/
@[expose] def extractorProgramBodies : List (ℕ × Term) :=
  (0, entryBody extractorC.costIdx) :: extractorC.costDeps

theorem extractorProgramBodies_eq :
    extractorProgramBodies = (0, entryBody extractorC.costIdx) :: extractorC.costDeps := by
  unfold extractorProgramBodies; rfl

/-- **The extractor's program.** -/
@[expose] def extractorProgram : Program := Program.ofList extractorProgramBodies

/-! ## Programs from lists of bodies -/

theorem getElem?_foldl_set_of_not_mem (l : List (ℕ × Term)) (A : Program) {i : ℕ}
    (hi : i ∉ l.map (·.1)) :
    (l.foldl (fun P p ↦ P.setIfInBounds p.1 p.2) A)[i]? = A[i]? := by
  induction l generalizing A with
  | nil => rfl
  | cons q l ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hi
    rw [List.foldl_cons, ih _ hi.2, Array.getElem?_setIfInBounds_ne (Ne.symm hi.1)]

theorem getElem?_foldl_set (l : List (ℕ × Term)) (hl : (l.map (·.1)).Nodup) :
    ∀ (A : Program), (∀ p ∈ l, p.1 < Array.size A) → ∀ p ∈ l,
      (l.foldl (fun P p ↦ P.setIfInBounds p.1 p.2) A)[p.1]? = some p.2 := by
  induction l with
  | nil => intro A _ p hp; simp at hp
  | cons q l ih =>
    intro A hA p hp
    simp only [List.map_cons, List.nodup_cons] at hl
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hp with rfl | hp
    · rw [getElem?_foldl_set_of_not_mem l _ hl.1,
        Array.getElem?_setIfInBounds_self_of_lt (hA _ List.mem_cons_self)]
    · exact ih hl.2 _ (fun r hr ↦ by
        rw [Array.size_setIfInBounds]; exact hA r (List.mem_cons_of_mem _ hr)) p hp

theorem lt_foldr_max_succ {l : List ℕ} {i : ℕ} (h : i ∈ l) : i < l.foldr max 0 + 1 := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp only [List.foldr_cons]; omega
    · have := ih h; simp only [List.foldr_cons]; omega

/-- **A program built from distinct indices holds its bodies.** -/
theorem includes_ofList (l : List (ℕ × Term)) (hl : (l.map (·.1)).Nodup) :
    Includes (Program.ofList l) l := by
  intro p hp
  refine getElem?_foldl_set l hl _ (fun r hr ↦ ?_) p hp
  rw [Array.size_replicate]
  exact lt_foldr_max_succ (List.mem_map_of_mem hr)

theorem sum_map_set_le (f : Term → ℕ) :
    ∀ (l : List Term) (i : ℕ) (t : Term), ((l.set i t).map f).sum ≤ (l.map f).sum + f t
  | [], _, _ => by simp
  | _ :: _, 0, _ => by simp; omega
  | a :: l, i + 1, t => by
    have := sum_map_set_le f l i t
    simp only [List.set_cons_succ, List.map_cons, List.sum_cons]
    omega

theorem size_setIfInBounds_le (A : Program) (i : ℕ) (t : Term) :
    Program.size (A.setIfInBounds i t) ≤ Program.size A + t.size := by
  unfold Program.size
  rw [Array.setIfInBounds_def]
  split
  · rw [Array.toList_set]; exact sum_map_set_le _ _ _ _
  · omega

/-- **A program's size from its bodies**: at most their sizes plus two per index (the literal
`0` of an index without a body). -/
theorem size_ofList_le (l : List (ℕ × Term)) :
    (Program.ofList l).size ≤
      (l.map fun p ↦ p.2.size).sum + 2 * ((l.map (·.1)).foldr max 0 + 1) := by
  have key : ∀ (l : List (ℕ × Term)) (A : Program),
      Program.size (l.foldl (fun P p ↦ P.setIfInBounds p.1 p.2) A) ≤
        Program.size A + (l.map fun p ↦ p.2.size).sum := by
    intro l
    induction l with
    | nil => intro A; simp
    | cons q l ih =>
      intro A
      have := ih (A.setIfInBounds q.1 q.2)
      have := size_setIfInBounds_le A q.1 q.2
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      omega
  have hrep : ∀ n, Program.size (Array.replicate n (Term.val (.nat 0))) = 2 * n := by
    intro n
    simp only [Program.size, Array.toList_replicate, List.map_replicate, List.sum_replicate,
      Term.size, Val.size, smul_eq_mul]
    omega
  have := key l (Array.replicate ((l.map (·.1)).foldr max 0 + 1) (.val (.nat 0)))
  rw [hrep] at this
  unfold Program.ofList
  dsimp only
  omega

/-- The indices increase from `a` on (a linear check). -/
@[expose] def increasingFrom : ℕ → List ℕ → Bool
  | _, [] => true
  | a, b :: l => decide (a < b) && increasingFrom b l

theorem nodup_of_increasingFrom :
    ∀ (a : ℕ) (l : List ℕ), increasingFrom a l = true → (∀ x ∈ l, a < x) ∧ l.Nodup
  | _, [], _ => by simp
  | a, b :: l, h => by
    simp only [increasingFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hl, hn⟩ := nodup_of_increasingFrom b l h.2
    refine ⟨fun x hx ↦ ?_, List.nodup_cons.2 ⟨fun hb ↦ absurd (hl b hb) (lt_irrefl b), hn⟩⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact h.1.trans (hl x hx)

/-- **Increasing indices are distinct.** -/
theorem nodup_of_increasing {a : ℕ} {l : List ℕ} (h : increasingFrom a l = true) :
    (a :: l).Nodup := by
  obtain ⟨hl, hn⟩ := nodup_of_increasingFrom a l h
  exact List.nodup_cons.2 ⟨fun ha ↦ absurd (hl a ha) (lt_irrefl a), hn⟩

end

end LeanVM.Cost
