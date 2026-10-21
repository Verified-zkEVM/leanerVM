/-
  LeanVM.Arithmetization.CompletenessB.Theorem

  Constraint completeness under a semantics of canonical `BLAKE2S` rows: an execution valid under
  it whose tables fit the row cap has a witness satisfying the constraint statement without the
  compression, over the execution's image.
-/

module

public import LeanVM.Arithmetization.CompletenessB.Satisfied
public import LeanVM.Arithmetization.Completeness.Theorem
public import LeanVM.Arithmetization.Soundness.Walk
public import LeanVM.Arithmetization.CompletenessB.Count

@[expose] public section

/-!
# Constraint completeness under a semantics of `BLAKE2S`

`Completeness/Theorem.lean` with the run under a semantics `Sm` whose `BLAKE2S` rows are
canonical: the run's register sequence (`regsB`), skeletons (`runSkelsB`) and rows (`runRowsB`),
the states and skeletons of the run (`stateAtB`, `skAtB`), their soundness (`skAtB_ok`) and the
state pair's rotation (`runSkelsB_state_perm`). `constraintCompletenessB_rows`: a valid execution
under `Sm` whose run has at most `2^maxLogRows` rows of every opcode has a witness satisfying
`SatisfiedByB` whose image is the execution's (`ImageOf`), its six tables holding the run's rows.
`countB_eq_runRowsB`: the counts the committed size reads (`Trace.countB`) are those rows.
-/

open scoped List

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics
open Air.Flat (Component EnsembleWitness)

variable {Sm : BlakeSem}

/-! ## Runs under a semantics -/

section Runs

variable {κ : ℕ} {prog : Program} {L : MemImage κ}

theorem runB_succ_of_eq' {r : Regs K} (h : r.pc = prog.finalPc) (n : ℕ) :
    runB Sm prog L (n + 1) r = none := by
  simp [runB, h]

theorem runB_add' (m n : ℕ) (r : Regs K) :
    runB Sm prog L (m + n) r = runB Sm prog L m r >>= runB Sm prog L n := by
  induction m generalizing r with
  | zero => simp [runB]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega]
    by_cases hpc : r.pc = prog.finalPc
    · simp [runB, hpc]
    · rw [runB_succ_of_ne Sm hpc, runB_succ_of_ne Sm hpc, bind_assoc]
      congr 1
      funext r'
      exact ih r'

theorem runB_prefix {m n : ℕ} {r r'' : Regs K} (h : runB Sm prog L (m + n) r = some r'') :
    ∃ r', runB Sm prog L m r = some r' ∧ runB Sm prog L n r' = some r'' := by
  rw [runB_add'] at h
  exact Option.bind_eq_some_iff.mp h

theorem pc_ne_finalPc_of_runB_succ {n : ℕ} {r r' : Regs K}
    (h : runB Sm prog L (n + 1) r = some r') : r.pc ≠ prog.finalPc :=
  fun hpc ↦ by rw [runB_succ_of_eq' hpc] at h; exact Option.some_ne_none r' h.symm

theorem runB_intermediate {n : ℕ} {r r' : Regs K} (h : runB Sm prog L n r = some r') {m : ℕ}
    (hm : m < n) : ∃ r₁, runB Sm prog L m r = some r₁ ∧ r₁.pc ≠ prog.finalPc := by
  obtain ⟨k, rfl⟩ : ∃ k, n = m + (k + 1) := ⟨n - m - 1, by omega⟩
  obtain ⟨r₁, h₁, h₂⟩ := runB_prefix h
  exact ⟨r₁, h₁, pc_ne_finalPc_of_runB_succ h₂⟩

end Runs

/-- The register sequence of a trace's run under `Sm` (`Trace.regs`). -/
noncomputable def regsB (Sm : BlakeSem) {prog : Program} (t : Trace prog) : List (Regs K) :=
  (List.range (t.steps + 1)).filterMap fun n ↦ runB Sm prog t.image n Regs.initial

/-- The skeletons of the run under `Sm` (`Trace.runSkels`). -/
noncomputable def runSkelsB (Sm : BlakeSem) {prog : Program} (t : Trace prog) : List Skel :=
  (regsB Sm t).dropLast.filterMap fun r ↦ (prog.fetch r.pc).map fun ins ↦ ⟨r.pc, r.fp, ins⟩

/-- The rows of opcode `op` of the run under `Sm` (`Trace.runRows`). -/
noncomputable def runRowsB (Sm : BlakeSem) {prog : Program} (t : Trace prog) (op : Opcode) : ℕ :=
  ((regsB Sm t).dropLast.filter fun r ↦ (prog.fetch r.pc).map Instr.opcode = some op).length

theorem regsB_length {prog : Program} {t : Trace prog} {r : Regs K}
    (h : runB Sm prog t.image t.steps Regs.initial = some r) : (regsB Sm t).length = t.steps + 1 := by
  rw [regsB]
  refine (List.filterMap_length_eq_length.mpr ?_).trans List.length_range
  intro n hn
  rcases Nat.lt_succ_iff_lt_or_eq.mp (List.mem_range.mp hn) with hlt | rfl
  · obtain ⟨r₁, h₁, -⟩ := runB_intermediate h hlt
    simp [h₁]
  · simp [h]

theorem count_runSkelsB {prog : Program} (t : Trace prog) (op : Opcode) :
    Skel.count op (runSkelsB Sm t) = runRowsB Sm t op := by
  unfold Skel.count Skel.onTable runSkelsB runRowsB
  generalize (regsB Sm t).dropLast = l
  induction l with
  | nil => rfl
  | cons r l ih =>
    cases hf : prog.fetch r.pc with
    | none => simpa [List.filterMap_cons, List.filter_cons, hf] using ih
    | some ins =>
      by_cases ho : ins.opcode = op <;> simp [hf, ho, ih]

/-- Along a run under `Sm` that succeeds, `runCountB` counts the states stepped from whose
fetched instruction has opcode `op`. -/
theorem runCountB_eq_length {κ : ℕ} {prog : Program} {L : MemImage κ} (op : Opcode) {n : ℕ}
    {r rf : Regs K} (h : runB Sm prog L n r = some rf) :
    runCountB Sm prog L op n r = (((List.range n).filterMap fun m ↦
      runB Sm prog L m r).filter fun r₁ ↦ (prog.fetch r₁.pc).map Instr.opcode = some op).length := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    have hpc := pc_ne_finalPc_of_runB_succ h
    rw [runB_succ_of_ne Sm hpc] at h
    obtain ⟨r', hs, hr'⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ins, hf⟩ : ∃ ins, prog.fetch r.pc = some ins := by
      cases hf : prog.fetch r.pc with
      | none => simp [stepB, hf] at hs
      | some ins => exact ⟨ins, rfl⟩
    have htail : ((List.range n).map Nat.succ).filterMap (fun m ↦ runB Sm prog L m r) =
        (List.range n).filterMap fun m ↦ runB Sm prog L m r' := by
      rw [List.filterMap_map]
      congr 1
      funext m
      simp only [Function.comp, runB_succ_of_ne Sm hpc, hs, Option.bind_eq_bind, Option.bind_some]
    rw [List.range_succ_eq_map, List.filterMap_cons, htail]
    simp only [runCountB, hf, hs, ih hr', runB]
    by_cases ho : ins.opcode = op <;> simp [hf, ho, Nat.add_comm]

/-- **The counts under `Sm` are the run's rows.** -/
theorem countB_eq_runRowsB {prog : Program} {t : Trace prog} {rf : Regs K}
    (h : runB Sm prog t.image t.steps Regs.initial = some rf) (op : Opcode) :
    t.countB Sm op = runRowsB Sm t op := by
  unfold Trace.countB runRowsB regsB
  rw [List.range_succ, List.filterMap_append]
  simp only [List.filterMap_cons, List.filterMap_nil, h, List.dropLast_concat]
  exact runCountB_eq_length op h

/-! ## The run's states and skeletons -/

section Run

variable {prog : Program} {t : Trace prog}

/-- The state after `k` steps of the run under `Sm`. -/
noncomputable def stateAtB (Sm : BlakeSem) (t : Trace prog) (k : ℕ) : Regs K :=
  (runB Sm prog t.image k Regs.initial).getD Regs.initial

/-- The skeleton stepped from at step `k`. -/
noncomputable def skAtB (Sm : BlakeSem) (t : Trace prog) (k : ℕ) : Skel :=
  ⟨(stateAtB Sm t k).pc, (stateAtB Sm t k).fp,
    (prog.fetch (stateAtB Sm t k).pc).getD (.setConstant 0 0)⟩

theorem run_stateAtB (hv : runB Sm prog t.image t.steps Regs.initial = some (Regs.final prog))
    {k : ℕ} (hk : k ≤ t.steps) : runB Sm prog t.image k Regs.initial = some (stateAtB Sm t k) := by
  obtain ⟨r, hr, -⟩ := runB_prefix (m := k) (n := t.steps - k)
    (by rwa [Nat.add_sub_cancel' hk])
  simp [stateAtB, hr]

theorem stateAtB_step (hv : runB Sm prog t.image t.steps Regs.initial = some (Regs.final prog))
    {k : ℕ} (hk : k < t.steps) :
    (stateAtB Sm t k).pc ≠ prog.finalPc ∧
      stepB Sm prog t.image (stateAtB Sm t k) = some (stateAtB Sm t (k + 1)) := by
  have h1 := run_stateAtB hv (show k + 1 ≤ t.steps by omega)
  have h0 := run_stateAtB hv hk.le
  rw [runB_add', h0] at h1
  have h1' : runB Sm prog t.image 1 (stateAtB Sm t k) = some (stateAtB Sm t (k + 1)) := h1
  have hpc := pc_ne_finalPc_of_runB_succ h1'
  refine ⟨hpc, ?_⟩
  rw [runB_succ_of_ne Sm hpc] at h1'
  generalize stepB Sm prog t.image (stateAtB Sm t k) = s at h1' ⊢
  cases s with
  | none => simp at h1'
  | some r => simpa [runB] using h1'

theorem regsB_eq_map (hv : runB Sm prog t.image t.steps Regs.initial = some (Regs.final prog)) :
    regsB Sm t = (List.range (t.steps + 1)).map (stateAtB Sm t) := by
  unfold regsB
  exact filterMap_eq_map_of _ _ _ fun k hk ↦ by
    simp only [run_stateAtB hv (Nat.lt_succ_iff.mp (List.mem_range.mp hk))]

theorem stateAtB_exec (hv : runB Sm prog t.image t.steps Regs.initial = some (Regs.final prog))
    {k : ℕ} (hk : k < t.steps) :
    ∃ ins, prog.fetch (stateAtB Sm t k).pc = some ins ∧
      executeWithB Sm t.image.read (stateAtB Sm t k) ins = some (stateAtB Sm t (k + 1)) := by
  obtain ⟨-, hs⟩ := stateAtB_step hv hk
  unfold stepB at hs
  obtain ⟨ins, hf, hex⟩ := Option.bind_eq_some_iff.mp hs
  exact ⟨ins, hf, hex⟩

theorem skAtB_ins {k : ℕ} {ins : Instr} (hf : prog.fetch (stateAtB Sm t k).pc = some ins) :
    (skAtB Sm t k).ins = ins := by
  simp only [skAtB, hf, Option.getD_some]

theorem runSkelsB_eq (hv : runB Sm prog t.image t.steps Regs.initial = some (Regs.final prog)) :
    runSkelsB Sm t = (List.range t.steps).map (skAtB Sm t) := by
  unfold runSkelsB
  rw [regsB_eq_map hv, List.range_succ, List.map_append, List.map_singleton, List.dropLast_concat,
    List.filterMap_map]
  refine filterMap_eq_map_of _ _ _ fun k hk ↦ ?_
  obtain ⟨ins, hf, -⟩ := stateAtB_exec hv (List.mem_range.mp hk)
  simp only [Function.comp_apply, hf, Option.map_some, skAtB, Option.getD_some]

theorem skAtB_ok (hv : runB Sm prog t.image t.steps Regs.initial = some (Regs.final prog))
    {k : ℕ} (hk : k < t.steps) : SkelOkB Sm prog t.image (skAtB Sm t k) := by
  obtain ⟨ins, hf, hex⟩ := stateAtB_exec hv hk
  refine ⟨?_, stateAtB Sm t (k + 1), ?_⟩
  · show prog.fetch (stateAtB Sm t k).pc = some (skAtB Sm t k).ins
    rw [skAtB_ins hf]
    exact hf
  · show executeWithB Sm t.image.read (stateAtB Sm t k) (skAtB Sm t k).ins = _
    rw [skAtB_ins hf]
    exact hex

theorem nextOfB_skAtB (hv : runB Sm prog t.image t.steps Regs.initial = some (Regs.final prog))
    {k : ℕ} (hk : k < t.steps) : nextOfB Sm t.image (skAtB Sm t k) = stateAtB Sm t (k + 1) := by
  obtain ⟨ins, hf, hex⟩ := stateAtB_exec hv hk
  show (executeWithB Sm t.image.read (stateAtB Sm t k) (skAtB Sm t k).ins).getD (stateAtB Sm t k) = _
  rw [skAtB_ins hf, hex]
  rfl

theorem runSkelsB_state_perm (hv : runB Sm prog t.image t.steps Regs.initial = some (Regs.final prog)) :
    (#[1, 1] :: (runSkelsB Sm t).map fun sk ↦
        #[(nextOfB Sm t.image sk).pc, (nextOfB Sm t.image sk).fp]).Perm
      (#[prog.finalPc, 1] :: (runSkelsB Sm t).map fun sk ↦ #[sk.pc, sk.fp]) := by
  obtain ⟨f, hf⟩ : ∃ f : ℕ → Array K, f = fun k ↦ #[(stateAtB Sm t k).pc, (stateAtB Sm t k).fp] :=
    ⟨_, rfl⟩
  have hlast : stateAtB Sm t t.steps = Regs.final prog := by
    have := run_stateAtB hv le_rfl
    rw [hv] at this
    exact (Option.some.inj this).symm
  have h0 : f 0 = #[1, 1] := by rw [hf]; rfl
  have hn : f t.steps = #[prog.finalPc, 1] := by
    rw [hf]
    show #[(stateAtB Sm t t.steps).pc, (stateAtB Sm t t.steps).fp] = _
    rw [hlast]
    rfl
  have hstate : (List.range t.steps).map (fun k ↦ #[(skAtB Sm t k).pc, (skAtB Sm t k).fp]) =
      (List.range t.steps).map f := by rw [hf]; rfl
  have hnext : (List.range t.steps).map
      (fun k ↦ #[(nextOfB Sm t.image (skAtB Sm t k)).pc, (nextOfB Sm t.image (skAtB Sm t k)).fp]) =
      (List.range t.steps).map fun k ↦ f (k + 1) :=
    List.map_congr_left fun k hk ↦ by rw [nextOfB_skAtB hv (List.mem_range.mp hk), hf]
  rw [runSkelsB_eq hv, List.map_map, List.map_map]
  simp only [Function.comp_def]
  rw [hstate, hnext, ← h0, ← hn]
  exact shift_perm f t.steps

end Run

/-! ## The theorem -/

/-- **The witness's image is the trace's.** -/
structure ImageOf {prog : Program} (w : EnsembleWitness (leanIsaEnsemble prog)) (t : Trace prog) :
    Prop where
  /-- The memory log-size is the trace's. -/
  κ_eq : (imageOf w.data).1 = t.κ
  /-- Every word of the image is the trace's. -/
  image_eq : ∀ i (hi : i < 2 ^ t.κ), (imageOf w.data).2 ⟨i, κ_eq ▸ hi⟩ = t.image ⟨i, hi⟩

/-- **Constraint completeness under a semantics of canonical `BLAKE2S` rows, with the row
counts.** A valid execution under `Sm` whose run has at most `2^maxLogRows` rows of every opcode
has a witness satisfying the constraint statement without the compression, over the execution's
image, whose six opcode tables hold exactly the run's rows. -/
theorem constraintCompletenessB_rows [Fact (Canonical Sm)] {prog : Program} {input : PublicInput}
    {t : Trace prog} (h : ValidExecutionB Sm prog input t)
    (hrows : ∀ op, runRowsB Sm t op ≤ 2 ^ maxLogRows) :
    ∃ w, SatisfiedByB prog input w ∧ ImageOf w t ∧
      ∀ j : Fin 6, (tableAt w ⟨j, by omega⟩).table.length = runRowsB Sm t (tableOpcode j) := by
  obtain ⟨⟨hmin, hcap, hw0, hw1⟩, hrun⟩ := h
  have hS : ∀ sk ∈ runSkelsB Sm t, SkelOkB Sm prog t.image sk := by
    intro sk hsk
    rw [runSkelsB_eq hrun] at hsk
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hsk
    exact skAtB_ok hrun (List.mem_range.mp hk)
  have hlen : ∀ op, List.length
      (opTable t.image (imageData t.image) (skelRows t.image (runSkelsB Sm t)) op).table =
        runRowsB Sm t op := by
    intro op
    show (List.map _ (List.filter _ _)).length = _
    rw [List.length_map, skelRows, length_filter_mkRows, count_runSkelsB]
  refine ⟨skelWitness prog input t.image (runSkelsB Sm t), ?_, ⟨imageData_logSize t.image hcap,
    fun i hi ↦ imageData_apply' t.image hcap i _⟩, ?_⟩
  · exact skelWitness_satisfiedByB prog input t.image _ hmin hcap hS (runSkelsB_state_perm hrun)
      (fun op ↦ (count_runSkelsB t op).trans_le (hrows op)) hw0 hw1
  · intro j
    fin_cases j
    exacts [hlen .xor, hlen .mulNative, hlen .setConstant, hlen .deref, hlen .jump, hlen .blake2s]

end LeanVM.Arithmetization
