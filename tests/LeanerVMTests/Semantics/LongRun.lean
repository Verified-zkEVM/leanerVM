import LeanerVM.Semantics.FillCycle
import LeanerVM.Semantics.FillSteps

/-!
# Layer 10 tests: a valid run no fitting trace can have

`Trace.Fits.rows` and `Trace.Fits.jump` bound every table's padded height by `2^32`, while a valid
execution is unbounded: its steps are limited only by the memory `κ ≤ 32`, and `JUMP` loads the
frame pointer from memory, so frames `g^(4 j)` can fill all `2^32` cells. For every program that
starts with thirty-three `SET_CONSTANT [g^0] g` and a `JUMP [g^1, g^2, g^3]` and has a sentinel
slot, the run that loops over `2^30` frames, thirty-three steps each, is a valid execution of
`33 * 2^30 + 1` steps. A trace that fits has at most `6 * 2^32` steps (`Trace.Fits.steps_le`), so
this one does not: the size conditions cannot be dropped. Its memory is also at the cap
(`Fits.room` fails too), so the statement of `long_run_exceeds_sizes` is about the two size fields
alone.

This is the `Semantics` half of the size refutation of the blueprint's completeness statement. That
no witness satisfies `Caps` and represents this trace needs `Caps` and `AssignmentRepresents`, and
is checked with the completeness theorem.
-/

namespace LeanerVMTests.Semantics.LongRun

open LeanerVM.Parameters LeanerVM.Semantics

/-- The number of frames. -/
def J : ℕ := 2 ^ 30

/-- The image, at `κ = 32`, for the sentinel counter `fin`. -/
def img (fin : K) : MemImage 32 := fun n ↦
  if (n : ℕ) % 4 = 2 then (if (n : ℕ) / 4 = J - 1 then ofK fin else ofK g)
  else if (n : ℕ) % 4 = 3 then
    (if (n : ℕ) / 4 = J - 1 then ofK 1 else ofK (gpow (4 * ((n : ℕ) / 4 + 1))))
  else ofK g

/-- The memory of `2^32` cells holds `4 J` cells, `J` frames of four. -/
theorem two_pow_32 : (2 : ℕ) ^ 32 = 4 * J := by norm_num [J]

/-- Reading the address of a cell of the image gives the cell. -/
theorem read_img (fin : K) (n : ℕ) (hn : n < 2 ^ 32) :
    (img fin).read (gpow n) = some (img fin ⟨n, hn⟩) :=
  MemImage.read_gpow (by decide) (img fin) ⟨n, hn⟩

/-- Cell `4 j` of the image holds `g`: the operand of the `SET_CONSTANT`. -/
theorem img_cell0 (fin : K) (j : ℕ) (hj : j < J) :
    img fin ⟨4 * j, by have := two_pow_32; omega⟩ = ofK g := by
  unfold img
  simp

/-- Cell `4 j + 1` holds `g`: the `JUMP` condition, nonzero. -/
theorem img_cell1 (fin : K) (j : ℕ) (hj : j < J) :
    img fin ⟨4 * j + 1, by have := two_pow_32; omega⟩ = ofK g := by
  unfold img
  simp

/-- Cell `4 j + 2` holds `g`, the `JUMP` destination (slot `1`), except in the last frame. -/
theorem img_cell2 (fin : K) (j : ℕ) (hj : j < J) (hne : j ≠ J - 1) :
    img fin ⟨4 * j + 2, by have := two_pow_32; omega⟩ = ofK g := by
  unfold img
  have h1 : (4 * j + 2) % 4 = 2 := by omega
  have h2 : (4 * j + 2) / 4 ≠ J - 1 := by omega
  simp [h1, h2]

/-- In the last frame that cell holds the sentinel counter. -/
theorem img_cell2_last (fin : K) :
    img fin ⟨4 * (J - 1) + 2, by have := two_pow_32; unfold J at *; omega⟩ = ofK fin := by
  unfold img
  have h1 : (4 * (J - 1) + 2) % 4 = 2 := by unfold J; omega
  have h2 : (4 * (J - 1) + 2) / 4 = J - 1 := by unfold J; omega
  simp [h1, h2]

/-- Cell `4 j + 3` holds the next frame pointer `g^(4 (j + 1))`, except in the last frame. -/
theorem img_cell3 (fin : K) (j : ℕ) (hj : j < J) (hne : j ≠ J - 1) :
    img fin ⟨4 * j + 3, by have := two_pow_32; omega⟩ = ofK (gpow (4 * (j + 1))) := by
  unfold img
  have h1 : (4 * j + 3) % 4 ≠ 2 := by omega
  have h2 : (4 * j + 3) % 4 = 3 := by omega
  have h3 : (4 * j + 3) / 4 ≠ J - 1 := by omega
  have h4 : (4 * j + 3) / 4 = j := by omega
  simp [h2, h4, hne]

/-- In the last frame that cell holds `1`, the final frame pointer. -/
theorem img_cell3_last (fin : K) :
    img fin ⟨4 * (J - 1) + 3, by have := two_pow_32; unfold J at *; omega⟩ = ofK 1 := by
  unfold img
  have h2 : (4 * (J - 1) + 3) % 4 = 3 := by unfold J; omega
  have h3 : (4 * (J - 1) + 3) / 4 = J - 1 := by unfold J; omega
  simp [h2, h3]

/-- Slots `0 … 32` are `SET_CONSTANT [g^0] g`, slot `33` is `JUMP [g^1, g^2, g^3]`, and the
sentinel slot lies beyond them. -/
structure Shape (prog : Program) : Prop where
  /-- The first thirty-three slots set the cell at the frame pointer to `g`. -/
  sets : ∀ s, s ≤ 32 → prog.fetch (gpow s) = some (.setConstant (gpow 0) (ofK g))
  /-- Slot `33` jumps to slot `1` in the frame its third cell names. -/
  jump : prog.fetch (gpow 33) = some (.jump (gpow 1) (gpow 2) (gpow 3))
  /-- The program has at least `2^6` slots, so the sentinel is past slot `33`. -/
  big : 6 ≤ prog.logSize

/-- The sentinel counter is none of the slots `0 … 33`. -/
theorem Shape.finalPc_ne {prog : Program} (h : Shape prog) {s : ℕ} (hs : s ≤ 33) :
    prog.finalPc ≠ gpow s := fun heq ↦
  gpow_ne_finalPc prog (n := s) (by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h.big
    omega) heq.symm

/-! ## Steps -/

theorem set_step (prog : Program) (fin : K) {s j : ℕ}
    (hs : prog.fetch (gpow s) = some (.setConstant (gpow 0) (ofK g))) (hj : j < J) :
    step prog (img fin) ⟨gpow s, gpow (4 * j)⟩ = some ⟨gpow (s + 1), gpow (4 * j)⟩ := by
  have hlt : 4 * j < 2 ^ 32 := by have := two_pow_32; omega
  have hr : (img fin).read (gpow (4 * j)) = some (ofK g) := by
    rw [read_img fin (4 * j) hlt, img_cell0 fin j hj]
  have hmul : gpow (4 * j) * gpow 0 = gpow (4 * j) := by
    show g ^ (4 * j) * g ^ 0 = g ^ (4 * j)
    rw [pow_zero, mul_one]
  rw [step_of_fetch_eq_some (r := ⟨gpow s, gpow (4 * j)⟩) hs]
  have hex := executeWith_set_of_read (read := (img fin).read) (r := ⟨gpow s, gpow (4 * j)⟩) (o := gpow 0)
    (k := ofK g) (by show (img fin).read (gpow (4 * j) * gpow 0) = _; rw [hmul]; exact hr)
  show executeWith (img fin).read ⟨gpow s, gpow (4 * j)⟩ (.setConstant (gpow 0) (ofK g)) = _
  rw [hex, gpow_succ]
  rfl

/-- The `JUMP` in frame `4 j` goes to slot `1` in frame `4 (j + 1)`. -/
theorem jump_loop (prog : Program) (fin : K) {j : ℕ} (hj : j < J) (hne : j ≠ J - 1)
    (h33 : prog.fetch (gpow 33) = some (.jump (gpow 1) (gpow 2) (gpow 3))) :
    step prog (img fin) ⟨gpow 33, gpow (4 * j)⟩ = some ⟨gpow 1, gpow (4 * (j + 1))⟩ := by
  have hlt : ∀ o, o ≤ 3 → 4 * j + o < 2 ^ 32 := by intro o ho; have := two_pow_32; omega
  have m1 : gpow (4 * j) * gpow 1 = gpow (4 * j + 1) := (pow_add g (4 * j) 1).symm
  have m2 : gpow (4 * j) * gpow 2 = gpow (4 * j + 2) := (pow_add g (4 * j) 2).symm
  have m3 : gpow (4 * j) * gpow 3 = gpow (4 * j + 3) := (pow_add g (4 * j) 3).symm
  have hc : (img fin).read (gpow (4 * j) * gpow 1) = some (ofK g) := by
    rw [m1, read_img fin _ (hlt 1 (by norm_num)), img_cell1 fin j hj]
  have hd : (img fin).read (gpow (4 * j) * gpow 2) = some (ofK g) := by
    rw [m2, read_img fin _ (hlt 2 (by norm_num)), img_cell2 fin j hj hne]
  have hf : (img fin).read (gpow (4 * j) * gpow 3) = some (ofK (gpow (4 * (j + 1)))) := by
    rw [m3, read_img fin _ (hlt 3 (by norm_num)), img_cell3 fin j hj hne]
  have hex := executeWith_jump_taken (read := (img fin).read) (r := ⟨gpow 33, gpow (4 * j)⟩)
    (oc := gpow 1) (od := gpow 2) (of := gpow 3) (c := g) (d := g) (f := gpow (4 * (j + 1)))
    hc hd hf g_ne_zero
  rw [step_of_fetch_eq_some (r := ⟨gpow 33, gpow (4 * j)⟩) h33]
  show executeWith (img fin).read ⟨gpow 33, gpow (4 * j)⟩ (.jump (gpow 1) (gpow 2) (gpow 3)) = _
  rw [hex, show gpow 1 = g from pow_one g]

/-- The `JUMP` in the last frame goes to the sentinel with frame pointer `1`. -/
theorem jump_last (prog : Program) (fin : K)
    (h33 : prog.fetch (gpow 33) = some (.jump (gpow 1) (gpow 2) (gpow 3))) :
    step prog (img fin) ⟨gpow 33, gpow (4 * (J - 1))⟩ = some ⟨fin, 1⟩ := by
  have hlt : ∀ o, o ≤ 3 → 4 * (J - 1) + o < 2 ^ 32 := by
    intro o ho; have := two_pow_32; unfold J at *; omega
  have m1 : gpow (4 * (J - 1)) * gpow 1 = gpow (4 * (J - 1) + 1) :=
    (pow_add g (4 * (J - 1)) 1).symm
  have m2 : gpow (4 * (J - 1)) * gpow 2 = gpow (4 * (J - 1) + 2) :=
    (pow_add g (4 * (J - 1)) 2).symm
  have m3 : gpow (4 * (J - 1)) * gpow 3 = gpow (4 * (J - 1) + 3) :=
    (pow_add g (4 * (J - 1)) 3).symm
  have hJ : J - 1 < J := by unfold J; omega
  have hc : (img fin).read (gpow (4 * (J - 1)) * gpow 1) = some (ofK g) := by
    rw [m1, read_img fin _ (hlt 1 (by norm_num)), img_cell1 fin (J - 1) hJ]
  have hd : (img fin).read (gpow (4 * (J - 1)) * gpow 2) = some (ofK fin) := by
    rw [m2, read_img fin _ (hlt 2 (by norm_num)), img_cell2_last fin]
  have hf : (img fin).read (gpow (4 * (J - 1)) * gpow 3) = some (ofK (1 : K)) := by
    rw [m3, read_img fin _ (hlt 3 (by norm_num)), img_cell3_last fin]
  have hex := executeWith_jump_taken (read := (img fin).read) (r := ⟨gpow 33, gpow (4 * (J - 1))⟩)
    (oc := gpow 1) (od := gpow 2) (of := gpow 3) (c := g) (d := fin) (f := 1) hc hd hf g_ne_zero
  rw [step_of_fetch_eq_some (r := ⟨gpow 33, gpow (4 * (J - 1))⟩) h33]
  exact hex

/-! ## Runs -/

theorem run_sets (prog : Program) (fin : K) (sh : Shape prog) {j : ℕ} (hj : j < J) :
    ∀ m s, s + m ≤ 33 →
      run prog (img fin) m ⟨gpow s, gpow (4 * j)⟩ = some ⟨gpow (s + m), gpow (4 * j)⟩ := by
  intro m
  induction m with
  | zero => intro s _; rfl
  | succ m ih =>
    intro s hs
    have hpc : (⟨gpow s, gpow (4 * j)⟩ : Regs K).pc ≠ prog.finalPc :=
      fun h ↦ sh.finalPc_ne (by omega) h.symm
    have h1 := run_one hpc (set_step prog fin (sh.sets s (by omega)) hj)
    have h2 := ih (s + 1) (by omega)
    have := run_trans h1 h2
    rw [show 1 + m = m + 1 by omega, show s + 1 + m = s + (m + 1) by omega] at this
    exact this

/-- The 32 `SET_CONSTANT`s of an iteration. -/
theorem run_body (prog : Program) (fin : K) (sh : Shape prog) {j : ℕ} (hj : j < J) :
    run prog (img fin) 32 ⟨gpow 1, gpow (4 * j)⟩ = some ⟨gpow 33, gpow (4 * j)⟩ :=
  run_sets prog fin sh hj 32 1 (by norm_num)

/-- Slot `33` is not the sentinel. -/
theorem pc33_ne (prog : Program) (sh : Shape prog) (j : ℕ) :
    (⟨gpow 33, gpow (4 * j)⟩ : Regs K).pc ≠ prog.finalPc :=
  fun h ↦ sh.finalPc_ne (le_refl 33) h.symm

/-- One iteration that loops. -/
theorem run_iter (prog : Program) (fin : K) (sh : Shape prog) {j : ℕ} (hj : j < J)
    (hne : j ≠ J - 1) :
    run prog (img fin) 33 ⟨gpow 1, gpow (4 * j)⟩ = some ⟨gpow 1, gpow (4 * (j + 1))⟩ :=
  run_trans (run_body prog fin sh hj)
    (run_one (pc33_ne prog sh j) (jump_loop prog fin hj hne sh.jump))

/-- The last iteration, which jumps to the sentinel. -/
theorem run_last (prog : Program) (fin : K) (sh : Shape prog) :
    run prog (img fin) 33 ⟨gpow 1, gpow (4 * (J - 1))⟩ = some ⟨fin, 1⟩ := by
  have hJ : J - 1 < J := by unfold J; omega
  exact run_trans (run_body prog fin sh hJ)
    (run_one (pc33_ne prog sh (J - 1)) (jump_last prog fin sh.jump))

/-- `m` looping iterations from slot `1` in frame `0` end at slot `1` in frame `4 m`. -/
theorem run_iters (prog : Program) (fin : K) (sh : Shape prog) :
    ∀ m, m ≤ J - 1 →
      run prog (img fin) (33 * m) ⟨gpow 1, gpow (4 * 0)⟩ = some ⟨gpow 1, gpow (4 * m)⟩ := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    have hJ : m < J := by omega
    have := run_trans (ih (by omega)) (run_iter prog fin sh hJ (by omega))
    rw [show 33 * m + 33 = 33 * (m + 1) by ring] at this
    exact this

/-- The whole run: slot `0`, then `J - 1` looping iterations, then the last one. -/
theorem run_full (prog : Program) (sh : Shape prog) :
    run prog (img prog.finalPc) (33 * J + 1) Regs.initial = some (Regs.final prog) := by
  have hJ : 0 < J := by unfold J; omega
  have e : (Regs.initial : Regs K) = ⟨gpow 0, gpow (4 * 0)⟩ := by
    unfold Regs.initial
    rw [Nat.mul_zero]
    simp [gpow]
  have hpc : (⟨gpow 0, gpow (4 * 0)⟩ : Regs K).pc ≠ prog.finalPc :=
    fun h ↦ sh.finalPc_ne (by norm_num : 0 ≤ 33) h.symm
  have h0 := run_one hpc (set_step prog prog.finalPc (sh.sets 0 (by norm_num)) hJ)
  have h1 := run_trans h0 (run_iters prog prog.finalPc sh (J - 1) le_rfl)
  have h2 := run_trans h1 (run_last prog prog.finalPc sh)
  rw [e, show 33 * J + 1 = 1 + 33 * (J - 1) + 33 by omega]
  exact h2

/-- **The long valid execution.**  For every program of the shape, a valid execution with more
than `2^35 = 8 * 2^32` steps. -/
theorem long_run_valid (prog : Program) (sh : Shape prog) :
    ∃ (input : PublicInput) (t : Trace prog), ValidExecution prog input t ∧ 2 ^ 35 < t.steps := by
  have hJ : 0 < J := by unfold J; omega
  refine ⟨⟨![g, 0, g, 0]⟩, ⟨32, img prog.finalPc, 33 * J + 1⟩, ⟨?_, run_full prog sh⟩, ?_⟩
  · refine ⟨by show minLogMem ≤ 32; decide, by show 32 ≤ maxLogMem; decide, ?_, ?_⟩
    · show (img prog.finalPc).read (gpow 0) = some (E.ofLimbs g 0 0)
      have hc : img prog.finalPc ⟨0, by norm_num⟩ = ofK g := img_cell0 prog.finalPc 0 hJ
      rw [read_img prog.finalPc 0 (by norm_num), hc, ofK_eq_ofLimbs]
    · show (img prog.finalPc).read (gpow 1) = some (E.ofLimbs g 0 0)
      have hc : img prog.finalPc ⟨1, by norm_num⟩ = ofK g := img_cell1 prog.finalPc 0 hJ
      rw [read_img prog.finalPc 1 (by norm_num), hc, ofK_eq_ofLimbs]
  · show 2 ^ 35 < 33 * J + 1
    unfold J
    norm_num



/-! ## The size conditions fail -/

/-- No trace of this run fits the row cap: it has more than `6 * 2^32` steps, the most a trace
whose tables are all within the cap can have. -/
theorem long_run_exceeds_sizes (prog : Program) (sh : Shape prog) :
    ∃ (input : PublicInput) (t : Trace prog), ValidExecution prog input t ∧
      ¬ ((∀ op, op ≠ .jump → fillTarget (t.runRows op) (minRows op) ≤ 2 ^ maxLogRows) ∧
        JumpFeasible t.owed) := by
  obtain ⟨input, t, hv, hbig⟩ := long_run_valid prog sh
  refine ⟨input, t, hv, fun ⟨hrows, hjump⟩ ↦ ?_⟩
  obtain ⟨rf, hrf⟩ : ∃ rf, run prog t.image t.steps Regs.initial = some rf := ⟨_, hv.2⟩
  have := Trace.steps_le_of_sizes hrf hrows hjump
  have h35 : (2 : ℕ) ^ 35 = 8 * 2 ^ 32 := by norm_num
  have hcap : maxLogRows = 32 := rfl
  rw [hcap] at this
  omega

/-- So the long valid execution is not a fitting trace. -/
theorem long_run_not_fits (prog : Program) (sh : Shape prog) :
    ∃ (input : PublicInput) (t : Trace prog), ValidExecution prog input t ∧ ¬ t.Fits := by
  obtain ⟨input, t, hv, h⟩ := long_run_exceeds_sizes prog sh
  exact ⟨input, t, hv, fun hf ↦ h ⟨hf.rows, hf.jump⟩⟩

/-- A program of `2^11` slots with the shape: `SET_CONSTANT [g^0] g` in slots `0 … 32`, the `JUMP`
in slot `33`, and `SET_CONSTANT` elsewhere, the sentinel included. -/
def shapeProg : Program :=
  ⟨11, by decide, fun i ↦
    if (i : ℕ) = 33 then .jump (gpow 1) (gpow 2) (gpow 3) else .setConstant (gpow 0) (ofK g)⟩

/-- It has the shape. -/
theorem shapeProg_shape : Shape shapeProg where
  sets := fun s hs ↦ by
    have h := shapeProg.fetch_gpow ⟨s, by show s < 2 ^ 11; omega⟩
    rw [h]
    simp only [shapeProg]
    simp [show s ≠ 33 by omega]
  jump := by
    have h := shapeProg.fetch_gpow ⟨33, by show 33 < 2 ^ 11; norm_num⟩
    rw [h]
    simp [shapeProg]
  big := by decide

/-- The sentinel slot is not a `JUMP`. -/
theorem shapeProg_sentinelSafe : SentinelSafe shapeProg := by decide

/-- On the concrete program: a valid execution that no fitting trace can be. -/
example : ∃ (input : PublicInput) (t : Trace shapeProg), ValidExecution shapeProg input t ∧
    ¬ t.Fits :=
  long_run_not_fits shapeProg shapeProg_shape

end LeanerVMTests.Semantics.LongRun
