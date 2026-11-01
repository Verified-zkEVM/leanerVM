module

public import LeanVM.Cost.ExtractorSize
public import LeanVM.Cost.Bounds.Top

/-!
# The extractor the compiled program computes

`LeanVM.extractorOf P` (`Statement/CostMachine.lean`), the extractor of the end statement, runs
the program's function `0` on one value, `encode prog input T proof = .ctor 0 [enc prog, enc input, enc qs, enc proof]` with
`qs = permutationQueries T`, and decodes its output with `decodeExecution prog`, which parses an
execution's encoding. The compiled extractor (`extractorC`, `Cost/Extractor/Top.lean`, computing
`extractorTop`, `Fast/Compiled.lean`) is a function of four encoded arguments whose output encodes
an `Option (Execution prog)`. The glue is the entry body `entryBody j` (`Cost/ExtractorProgram.lean`):
it destructures the input, calls function `j` on its four fields and unwraps the option (`none` to
`.ctor 0 []`, which no execution decodes from; `some t` to `t`'s encoding), at `9` steps more than
the call (`runsBody_entry`).

* **`extractorTop_output`**: in a program whose function `0` is `entryBody j`, if function `j`
  computes `extractorTop` at a price `cost` that is within `extractorBudgetAt` at the announced
  shape whenever the extraction succeeds, the decoded output within `extractorBudget` is
  `transcriptExtractor`'s, on every input; **`extractorOf_eq_of_spec`**: `extractorOf P =
  transcriptExtractor`;
* `extractorProgram_size_le`: `extractorProgram`'s size is within `extractorSizeBound`
  (`Cost/ExtractorSize.lean`);
* **`extractorOf_extractorProgram`**: for `extractorProgram` (its entry at `0`, its bodies held),
  the compiled extractor's spec (`extractorC.costSpec`) and its price within the budget
  (`extractorC_within`, `Cost/Bounds/Top.lean`), `extractorOf extractorProgram =
  transcriptExtractor`.
-/

namespace LeanVM.Cost

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Cost.Extractor Common

public section

/-! ## The entry -/

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

/-- Where the proof announces no shape, `transcriptExtractor` returns nothing. -/
theorem transcriptExtractor_eq_none {prog : Semantics.Program} {π : Proof}
    (h : afterRoot (bytecodeWords prog) π = none) (input : PublicInput) (T : OracleQueryLog) :
    transcriptExtractor prog input T π = none := by
  unfold transcriptExtractor extract
  simp only [h]
  rfl

/-- **The glue**: in a program whose function `0` is `entryBody j`, if function `j` computes
`extractorTop` at the price `cost`, within the budget at the announced shape (less the entry's
`9`) wherever the extraction succeeds, the output within `extractorBudget`, decoded, is
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

/-- **The extractor a program computes is `transcriptExtractor`**, from the compiled extractor's
spec at function `j` and its price within the budget. -/
theorem extractorOf_eq_of_spec (P : Program) (j : ℕ) (hentry : P[0]? = some (entryBody j))
    (cost : Semantics.Program → PublicInput →
      List (PermutationQuery KeccakState × KeccakState) → Proof → ℕ)
    (hrun : ∀ prog input qs π, RunsBody P j [enc prog, enc input, enc qs, enc π]
      (enc (extractorTop prog input qs π)) (cost prog input qs π))
    (hcost : ∀ prog input T π layout logInverseRate st t,
      afterRoot (bytecodeWords prog) π = some ((layout, logInverseRate), st) →
      extractorTop prog input (permutationQueries T) π = some t →
      cost prog input (permutationQueries T) π + 9 ≤
        extractorBudgetAt prog layout logInverseRate (permutationQueries T).length) :
    LeanVM.extractorOf P = transcriptExtractor := by
  funext prog input T proof
  exact extractorTop_output P j hentry cost hrun hcost prog input T proof

/-! ## The extractor's program -/

/-- The extractor's program holds its bodies: their indices are distinct
(`Cost/ExtractorSize.lean`). -/
theorem extractorProgram_includes_all : Includes extractorProgram extractorProgramBodies := by
  have h := nodup_of_increasing extractorProgram_indices_increasing
  refine includes_ofList _ ?_
  rw [extractorProgramBodies_eq, List.map_cons]
  exact h

/-- **The program's size is within `extractorSizeBound`** (`2^15`): at most `11515`
(`Cost/ExtractorSize.lean`). -/
theorem extractorProgram_size_le : extractorProgram.size ≤ extractorSizeBound :=
  extractorProgram_size_le_measured.trans (by decide)

/-- The extractor's program holds the compiled extractor's bodies. -/
theorem extractorProgram_includes : Includes extractorProgram extractorC.costDeps :=
  extractorProgram_includes_all.mono fun _ hp ↦ by
    rw [extractorProgramBodies_eq]; exact List.mem_cons_of_mem _ hp

/-- Its function `0` is the entry calling the compiled extractor. -/
theorem extractorProgram_entry : extractorProgram[0]? = some (entryBody extractorC.costIdx) :=
  extractorProgram_includes_all.get (by rw [extractorProgramBodies_eq]; exact List.mem_cons_self)

/-- **The compiled extractor's price is within the budget** (`extractorC_within`,
`Cost/Bounds/Top.lean`): wherever the proof announces a shape, the price in `extractorProgram` and
the entry's `9` are within `extractorBudgetAt`. -/
theorem extractorPrice_within_budget : ∀ prog input T π layout logInverseRate st (t : Execution prog),
    afterRoot (bytecodeWords prog) π = some ((layout, logInverseRate), st) →
    extractorTop prog input (permutationQueries T) π = some t →
    machineCost extractorProgram extractorC.costIdx
        [enc prog, enc input, enc (permutationQueries T), enc π] + 9 ≤
      extractorBudgetAt prog layout logInverseRate (permutationQueries T).length :=
  fun prog input T π layout logInverseRate st _ ha _ ↦
    Bounds.extractorC_within extractorProgram extractorProgram_includes prog input T π layout
      logInverseRate st ha

/-- **The extractor `extractorProgram` computes is `transcriptExtractor`**: its spec and its price
within the budget. -/
theorem extractorOf_extractorProgram : LeanVM.extractorOf extractorProgram = transcriptExtractor :=
  extractorOf_eq_of_spec extractorProgram extractorC.costIdx extractorProgram_entry
    (fun prog input qs π ↦ machineCost extractorProgram extractorC.costIdx
      [enc prog, enc input, enc qs, enc π])
    (fun prog input qs π ↦ extractorC.costSpec extractorProgram extractorProgram_includes
      prog input qs π)
    extractorPrice_within_budget

end

end LeanVM.Cost
