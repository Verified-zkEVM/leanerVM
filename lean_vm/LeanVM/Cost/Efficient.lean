module

public import LeanVM.Cost.Rules
public import LeanVM.Protocol.Extraction.Fast.Compiled

/-!
# The extractor's efficiency from the compiled extractor's spec

`LeanVM.ExtractorEfficient` (`Statement/CostMachine.lean`) runs a program's function `0` on one
value, `encode prog input T proof = .ctor 0 [enc prog, enc input, enc qs, enc proof]` with
`qs = permutationQueries T`, and decodes its output with `decodeExecution prog`, which parses an
execution's encoding. The compiled extractor (`extractorTop`, `Fast/Compiled.lean`) is a function
of four encoded arguments whose output encodes an `Option (Execution prog)`. The glue is the entry
body `entryBody j`: it destructures the input, calls function `j` on its four fields and unwraps
the option (`none` to `.ctor 0 []`, which no execution decodes from; `some t` to `t`'s encoding),
at `9` steps more than the call (`runsBody_entry`).

* **`extractorTop_output`**: in a program whose function `0` is `entryBody j`, if function `j`
  computes `extractorTop` at a price `cost` that is within `extractorBudgetAt` at the announced
  shape whenever the extraction succeeds, the decoded output within `extractorBudget` is
  `transcriptExtractor`'s, on every input;
* **`extractorEfficient_of_spec`**: with the program's size within `extractorSizeBound`,
  `ExtractorEfficient`;
* `includes_ofList`: a program built by `Program.ofList` holds its bodies if their indices are
  distinct; `size_ofList_le`: its size is at most its bodies' sizes plus two per index, a sum to
  evaluate (`decide`), not an array to build.
-/

namespace LeanVM.Cost

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Extraction LeanVM.Extraction.Fast Common

public section

/-! ## The entry -/

/-- **The entry body**: the input's four fields passed to function `j`, its optional output
unwrapped. -/
@[expose] def entryBody (j : ℕ) : Term :=
  .case (.var 0) [.case (.call j [.var 0, .var 1, .var 2, .var 3]) [.ctor 0 [], .var 0]]

/-- The value the entry returns for an optional output. -/
@[expose] def unwrapOption {α : Type} [Enc α] : Option α → Val
  | none => .ctor 0 []
  | some a => enc a

theorem runsBody_entry {P : Program} {j : ℕ} (hentry : P[0]? = some (entryBody j))
    {α : Type} [Enc α] {a b c d : Val} {o : Option α} {e : ℕ}
    (h : RunsBody P j [a, b, c, d] (enc o) e) :
    RunsBody P 0 [.ctor 0 [a, b, c, d]] (unwrapOption o) (e + 9) := by
  have hargs : RunsList P [a, b, c, d, .ctor 0 [a, b, c, d]] [.var 0, .var 1, .var 2, .var 3]
      [a, b, c, d] 4 :=
    RunsList.cons (Runs.var rfl) (RunsList.cons (Runs.var rfl) (RunsList.cons (Runs.var rfl)
      (RunsList.cons (Runs.var rfl) RunsList.nil)))
  have hcall := Runs.call hargs h
  refine RunsBody.intro hentry ?_
  cases o with
  | none =>
    have hcall' : Runs P [a, b, c, d, .ctor 0 [a, b, c, d]]
        (.call j [.var 0, .var 1, .var 2, .var 3]) (.ctor 0 []) (4 + e + 1) := hcall
    have halt : Runs P ([] ++ [a, b, c, d, .ctor 0 [a, b, c, d]]) (.ctor 0 []) (.ctor 0 []) 1 :=
      (Runs.ctor RunsList.nil).cost_eq (by simp)
    have hinner := Runs.case (alts := [.ctor 0 [], .var 0]) hcall' rfl halt
    exact (Runs.case (Runs.var rfl) rfl hinner).cost_eq (by omega)
  | some t =>
    have hcall' : Runs P [a, b, c, d, .ctor 0 [a, b, c, d]]
        (.call j [.var 0, .var 1, .var 2, .var 3]) (.ctor 1 [enc t]) (4 + e + 1) := hcall
    have halt : Runs P ([enc t] ++ [a, b, c, d, .ctor 0 [a, b, c, d]]) (.var 0) (enc t) 1 :=
      Runs.var rfl
    have hinner := Runs.case (alts := [.ctor 0 [], .var 0]) hcall' rfl halt
    exact (Runs.case (Runs.var rfl) rfl hinner).cost_eq (by omega)

theorem decodeExecution_unwrap (prog : Semantics.Program) (o : Option (Execution prog)) :
    decodeExecution prog (unwrapOption o) = o := by
  cases o with
  | none => rfl
  | some t => exact decodeExecution_enc prog t

/-- An output within a budget is the value of a run. -/
theorem runsBody_of_outputWithin {P : Program} {x v : Val} {b : ℕ}
    (h : outputWithin P x b = some v) : ∃ c, RunsBody P 0 [x] v c := by
  unfold outputWithin run at h
  split at h
  · rename_i v' c hr
    split at h
    · obtain rfl : v' = v := Option.some.inj h
      exact ⟨c, b + 1, hr⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-! ## The extractor's output -/

/-- Where the proof announces no shape, the statement's extractor returns nothing. -/
theorem transcriptExtractor_eq_none {prog : Semantics.Program} {π : Proof}
    (h : afterRoot (bytecodeWords prog) π = none) (input : PublicInput) (T : OracleQueryLog) :
    transcriptExtractor prog input T π = none := by
  unfold transcriptExtractor extract
  simp only [h]
  rfl

/-- **The glue**: in a program whose function `0` is `entryBody j`, if function `j` computes
`extractorTop` at the price `cost`, within `extractorBudgetAt` at the announced shape (less the
entry's `9`) wherever the extraction succeeds, the output within `extractorBudget`, decoded, is
`transcriptExtractor`'s. -/
theorem extractorTop_output (P : Program) (j : ℕ) (hentry : P[0]? = some (entryBody j))
    (cost : Semantics.Program → PublicInput →
      List (PermutationQuery KeccakState × KeccakState) → Proof → ℕ)
    (hrun : ∀ prog input qs π, RunsBody P j [enc prog, enc input, enc qs, enc π]
      (enc (extractorTop prog input qs π)) (cost prog input qs π))
    (hcost : ∀ prog input T π layout logInverseRate st t,
      afterRoot (bytecodeWords prog) π = some ((layout, logInverseRate), st) →
      extractorTop prog input (permutationQueries T) π = some t →
      cost prog input (permutationQueries T) π + 9 ≤
        extractorBudgetAt prog layout logInverseRate (permutationQueries T).length)
    (prog : Semantics.Program) (input : PublicInput) (T : OracleQueryLog) (proof : Proof) :
    (outputWithin P (encode prog input T proof) (extractorBudget prog T proof)).bind
        (decodeExecution prog) =
      transcriptExtractor prog input T proof := by
  have hentryRun := runsBody_entry hentry (hrun prog input (permutationQueries T) proof)
  rw [← extractorTop_eq]
  cases ht : extractorTop prog input (permutationQueries T) proof with
  | none =>
    rw [ht] at hentryRun
    cases ho : outputWithin P (encode prog input T proof) (extractorBudget prog T proof) with
    | none => rfl
    | some v =>
      obtain ⟨c, hv⟩ := runsBody_of_outputWithin ho
      obtain ⟨rfl, -⟩ := RunsBody.unique hv hentryRun
      exact decodeExecution_unwrap prog none
  | some t =>
    rw [ht] at hentryRun
    cases ha : afterRoot (bytecodeWords prog) proof with
    | none =>
      have := transcriptExtractor_eq_none ha input T
      rw [← extractorTop_eq, ht] at this
      exact absurd this (by simp)
    | some r =>
      obtain ⟨⟨layout, R⟩, st⟩ := r
      have hb : extractorBudget prog T proof =
          extractorBudgetAt prog layout R (permutationQueries T).length := by
        simp only [extractorBudget, ha]
      have hc := hcost prog input T proof layout R st t ha ht
      have hx : encode prog input T proof =
          .ctor 0 [enc prog, enc input, enc (permutationQueries T), enc proof] := rfl
      rw [hx, outputWithin_of_runs (b := extractorBudget prog T proof) hentryRun
        (by rw [hb]; exact hc)]
      exact decodeExecution_unwrap prog (some t)

/-- **`ExtractorEfficient` from the compiled extractor's spec** and the program's size. -/
theorem extractorEfficient_of_spec (P : Program) (hsize : P.size ≤ extractorSizeBound) (j : ℕ)
    (hentry : P[0]? = some (entryBody j))
    (cost : Semantics.Program → PublicInput →
      List (PermutationQuery KeccakState × KeccakState) → Proof → ℕ)
    (hrun : ∀ prog input qs π, RunsBody P j [enc prog, enc input, enc qs, enc π]
      (enc (extractorTop prog input qs π)) (cost prog input qs π))
    (hcost : ∀ prog input T π layout logInverseRate st t,
      afterRoot (bytecodeWords prog) π = some ((layout, logInverseRate), st) →
      extractorTop prog input (permutationQueries T) π = some t →
      cost prog input (permutationQueries T) π + 9 ≤
        extractorBudgetAt prog layout logInverseRate (permutationQueries T).length) :
    LeanVM.ExtractorEfficient :=
  ⟨P, hsize, extractorTop_output P j hentry cost hrun hcost⟩

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

end

end LeanVM.Cost
