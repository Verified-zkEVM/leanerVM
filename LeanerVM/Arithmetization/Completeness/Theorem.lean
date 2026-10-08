/-
  LeanerVM.Arithmetization.Completeness.Theorem

  Constraint completeness for a padded trace: a valid, fitting execution has a padded trace and a
  witness that satisfies the constraint statement and represents it.
-/

module

public import LeanerVM.Arithmetization.Completeness.Satisfied

@[expose] public section

/-!
# Constraint completeness

leanISA roadmap Layer 10 (`docs/roadmap/leanisa-blueprint.md`), at leanVM pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2`. Category A, completeness direction of `T1`, for the
proof system's constraint statement (`SatisfiedBy`). `constraintCompleteness` is the roadmap's
statement for a padded trace, as the Semantics half of this slice (`Semantics.PaddedTrace`)
restated it: a valid execution of well-formed bytecode that `Fits` has a padded trace `t'` (valid,
its words those of `t`) and a witness satisfying `SatisfiedBy prog input` and representing `t'`.

**The witness.** Take the fill blocks the bytecode has (`HasFillBlocks.exists_starts`), the
traversal counts of the plan for a power of two `2^τ` of `JUMP` rows (`planCount`), and the padded
trace `padTrace t pcs`. The skeletons `S` are the run's (`Trace.runSkels`: the states stepped from
and the instructions fetched there) followed by the fill's (`padSkels`). `padWitness`
(`Completeness.Witness`) writes one row per skeleton in the table of its opcode, the image as the
memory block and the program as the bytecode block, with the read counts that make the three
channel pairs balance (`Completeness.Bus`, `Completeness.Balance`). `padWitness_satisfiedBy`
(`Completeness.Satisfied`) reduces `SatisfiedBy` to facts about `S` and the image, which this file proves:

* the skeletons are sound: the run's from the valid run (`skAt_ok`), the fill's from the fill
  blocks (`padSkels_ok`);
* the state pair balances: the run's pushes and pulls rotate (`runSkels_state_perm`, from
  `shift_perm`), the fill's are the closed walks (`perm_of_skelsValid`, from the fill-block lemma);
* the heights (`Trace.count_rows`, `tableHeight_pow`) and the `BLAKE2S` floor;
* the memory window and the two public words (`PaddedFrom.valid`).

`AssignmentRepresents` follows from `padWitness_rowSteps`: every skeleton is a row whose state
pull is its state and push its successor, and the run's register sequence is the run's skeletons.

## Wrong readings excluded

* The witness does not represent `t` itself: the committed memory has no room for the fill
  frames, so the witness represents the padded trace, which is `t` with frames above it
  (`Semantics.PaddedImage`, and the refutation in `tests/LeanerVMTests/Semantics`).
* `Fits` is not part of validity: a valid execution too long to fill within the row caps has no
  witness at all (`Caps`), which is why the theorem takes `hfit`.
* The skeletons are not the trace's registers: a fill row is a state in the frame of its cycle,
  and its successor is another fill row (`perm_of_skelsValid`), not a step of the run.
-/

open scoped List

namespace LeanerVM.Arithmetization

open LeanerVM.Parameters LeanerVM.Semantics
open Air.Flat (Component EnsembleWitness)

section Run

variable {prog : Program}

/-- The state after `k` steps of the run of `t`, the initial state if the run fails. -/
noncomputable def stateAt (t : Trace prog) (k : ℕ) : Regs K :=
  (run prog t.image k Regs.initial).getD Regs.initial

/-- The skeleton stepped from at step `k`: the state and the instruction fetched there. -/
noncomputable def skAt (t : Trace prog) (k : ℕ) : Skel :=
  ⟨(stateAt t k).pc, (stateAt t k).fp, (prog.fetch (stateAt t k).pc).getD fillClose⟩

/-- A list all of whose entries map to `some` is the `filterMap` of the entries' values. -/
theorem filterMap_eq_map_of {α β : Type} (p : α → Option β) (f : α → β) (l : List α)
    (h : ∀ x ∈ l, p x = some (f x)) : l.filterMap p = l.map f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.filterMap_cons, h x List.mem_cons_self, List.map_cons, ih fun y hy ↦
      h y (List.mem_cons_of_mem _ hy)]

variable {t : Trace prog}

/-- The run to step `k ≤ steps` reaches `stateAt t k`. -/
theorem run_stateAt (hv : run prog t.image t.steps Regs.initial = some (Regs.final prog)) {k : ℕ}
    (hk : k ≤ t.steps) : run prog t.image k Regs.initial = some (stateAt t k) := by
  obtain ⟨r, hr, -⟩ := run_prefix (m := k) (n := t.steps - k)
    (by rwa [Nat.add_sub_cancel' hk])
  simp [stateAt, hr]

/-- Every step of a valid run is taken away from the sentinel, fetches and executes. -/
theorem stateAt_step (hv : run prog t.image t.steps Regs.initial = some (Regs.final prog))
    {k : ℕ} (hk : k < t.steps) :
    (stateAt t k).pc ≠ prog.finalPc ∧ step prog t.image (stateAt t k) = some (stateAt t (k + 1)) := by
  have h1 := run_stateAt hv (show k + 1 ≤ t.steps by omega)
  have h0 := run_stateAt hv hk.le
  rw [run_add, h0] at h1
  have h1' : run prog t.image 1 (stateAt t k) = some (stateAt t (k + 1)) := h1
  have hpc := pc_ne_finalPc_of_run_succ h1'
  refine ⟨hpc, ?_⟩
  rw [run_succ_of_ne hpc] at h1'
  generalize step prog t.image (stateAt t k) = s at h1' ⊢
  cases s with
  | none => simp at h1'
  | some r => simpa using h1'

end Run

section Run

variable {prog : Program} {t : Trace prog}

/-- The register sequence of a valid run is the states `stateAt t 0, …, stateAt t steps`. -/
theorem regs_eq_map (hv : run prog t.image t.steps Regs.initial = some (Regs.final prog)) :
    t.regs = (List.range (t.steps + 1)).map (stateAt t) := by
  unfold Trace.regs
  exact filterMap_eq_map_of _ _ _ fun k hk ↦ by
    simp only [run_stateAt hv (Nat.lt_succ_iff.mp (List.mem_range.mp hk))]

/-- Every state stepped from fetches an instruction that executes to the next state. -/
theorem stateAt_exec (hv : run prog t.image t.steps Regs.initial = some (Regs.final prog))
    {k : ℕ} (hk : k < t.steps) :
    ∃ ins, prog.fetch (stateAt t k).pc = some ins ∧
      execute t.image (stateAt t k) ins = some (stateAt t (k + 1)) := by
  obtain ⟨-, hs⟩ := stateAt_step hv hk
  unfold step at hs
  obtain ⟨ins, hf, hex⟩ := Option.bind_eq_some_iff.mp hs
  exact ⟨ins, hf, hex⟩

/-- The instruction of a skeleton of the run is the one fetched. -/
theorem skAt_ins {k : ℕ} {ins : Instr} (hf : prog.fetch (stateAt t k).pc = some ins) :
    (skAt t k).ins = ins := by
  simp only [skAt, hf, Option.getD_some]

/-- The skeletons of a valid run are those stepped from, one per step. -/
theorem runSkels_eq (hv : run prog t.image t.steps Regs.initial = some (Regs.final prog)) :
    t.runSkels = (List.range t.steps).map (skAt t) := by
  unfold Trace.runSkels
  rw [regs_eq_map hv, List.range_succ, List.map_append, List.map_singleton, List.dropLast_concat,
    List.filterMap_map]
  refine filterMap_eq_map_of _ _ _ fun k hk ↦ ?_
  obtain ⟨ins, hf, -⟩ := stateAt_exec hv (List.mem_range.mp hk)
  simp only [Function.comp_apply, hf, Option.map_some, skAt, Option.getD_some]

/-- Every skeleton of a valid run is sound over the run's image. -/
theorem skAt_ok (hv : run prog t.image t.steps Regs.initial = some (Regs.final prog))
    {k : ℕ} (hk : k < t.steps) : SkelOk prog t.image (skAt t k) := by
  obtain ⟨ins, hf, hex⟩ := stateAt_exec hv hk
  refine ⟨?_, stateAt t (k + 1), ?_⟩
  · show prog.fetch (stateAt t k).pc = some (skAt t k).ins
    rw [skAt_ins hf]
    exact hf
  · show execute t.image (stateAt t k) (skAt t k).ins = _
    rw [skAt_ins hf]
    exact hex

/-- The successor of a skeleton of the run is the next state. -/
theorem nextOf_skAt (hv : run prog t.image t.steps Regs.initial = some (Regs.final prog))
    {k : ℕ} (hk : k < t.steps) : nextOf t.image (skAt t k) = stateAt t (k + 1) := by
  obtain ⟨ins, hf, hex⟩ := stateAt_exec hv hk
  show (execute t.image (stateAt t k) (skAt t k).ins).getD (stateAt t k) = _
  rw [skAt_ins hf, hex]
  rfl

/-- **The run's state pulls and pushes balance with the boundary**: the initial state is pushed,
the final one pulled, and each state stepped to is stepped from. -/
theorem runSkels_state_perm (hv : run prog t.image t.steps Regs.initial = some (Regs.final prog)) :
    (#[1, 1] :: t.runSkels.map fun sk ↦ #[(nextOf t.image sk).pc, (nextOf t.image sk).fp]).Perm
      (#[prog.finalPc, 1] :: t.runSkels.map fun sk ↦ #[sk.pc, sk.fp]) := by
  obtain ⟨f, hf⟩ : ∃ f : ℕ → Array K, f = fun k ↦ #[(stateAt t k).pc, (stateAt t k).fp] :=
    ⟨_, rfl⟩
  have hlast : stateAt t t.steps = Regs.final prog := by
    have := run_stateAt hv le_rfl
    rw [hv] at this
    exact (Option.some.inj this).symm
  have h0 : f 0 = #[1, 1] := by rw [hf]; rfl
  have hn : f t.steps = #[prog.finalPc, 1] := by
    rw [hf]
    show #[(stateAt t t.steps).pc, (stateAt t t.steps).fp] = _
    rw [hlast]
    rfl
  have hstate : (List.range t.steps).map (fun k ↦ #[(skAt t k).pc, (skAt t k).fp]) =
      (List.range t.steps).map f := by rw [hf]; rfl
  have hnext : (List.range t.steps).map
      (fun k ↦ #[(nextOf t.image (skAt t k)).pc, (nextOf t.image (skAt t k)).fp]) =
      (List.range t.steps).map fun k ↦ f (k + 1) :=
    List.map_congr_left fun k hk ↦ by rw [nextOf_skAt hv (List.mem_range.mp hk), hf]
  rw [runSkels_eq hv, List.map_map, List.map_map]
  simp only [Function.comp_def]
  rw [hstate, hnext, ← h0, ← hn]
  exact shift_perm f t.steps

end Run

/-! ## The skeletons of the fill -/

section Fill

variable {prog : Program}

/-- A skeleton of a fill is a skeleton of one traversal of one cycle. -/
theorem mem_padSkels {κ : ℕ} {pcs : Opcode → ℕ → ℕ} {count : Opcode → ℕ → ℕ} {sk : Skel}
    (h : sk ∈ padSkels κ pcs count) : ∃ t, ∃ k < 8, sk ∈ cycleSkels κ pcs t k := by
  unfold padSkels at h
  obtain ⟨t, -, h⟩ := List.mem_flatMap.mp h
  obtain ⟨k, hk, h⟩ := List.mem_flatMap.mp h
  obtain ⟨l, hl, h⟩ := List.mem_flatten.mp h
  rw [List.eq_of_mem_replicate hl] at h
  exact ⟨t, k, List.mem_range.mp hk, h⟩

/-- A skeleton of a traversal of a block is the instruction fetched at its counter. -/
theorem cycleSkels_fetch {κ : ℕ} {pcs : Opcode → ℕ → ℕ} {t : Opcode} {k : ℕ}
    (hb : IsFillBlock prog t (sizeAt k) (pcs t (sizeAt k))) {sk : Skel}
    (h : sk ∈ cycleSkels κ pcs t k) : prog.fetch sk.pc = some sk.ins := by
  unfold cycleSkels at h
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
  have hi' := List.mem_range.mp hi
  by_cases hlt : i < sizeAt k
  · simpa [hlt] using hb.dummies i hlt
  · obtain rfl : i = sizeAt k := by omega
    simpa using hb.close

/-- **The skeletons of a fill are sound**: fetched, and they execute over the padded image. -/
theorem padSkels_ok {κ : ℕ} (hκ : 10 ≤ κ) (hκ' : κ < 63) (img : MemImage κ)
    (pcs : Opcode → ℕ → ℕ)
    (hpcs : ∀ t, ∀ k < 8, IsFillBlock prog t (sizeAt k) (pcs t (sizeAt k)))
    (count : Opcode → ℕ → ℕ) :
    ∀ sk ∈ padSkels κ pcs count, SkelOk prog (padImage img pcs) sk := by
  intro sk hsk
  obtain ⟨t, k, hk, hmem⟩ := mem_padSkels hsk
  have hfetch := cycleSkels_fetch (hpcs t k hk) hmem
  obtain ⟨next, -, hstep⟩ := FillerRowsValid.step_mem
    (padSkels_valid hκ hκ' img pcs hpcs count) (List.mem_map_of_mem (f := Skel.regs) hsk)
  exact ⟨hfetch, next, execute_of_step hfetch hstep⟩

/-- Skeletons that are valid fillers and sound have the states pushed that they pull. -/
theorem perm_of_skelsValid {κ : ℕ} {img : MemImage κ} {S : List Skel}
    (hv : SkelsValid prog img S) (hok : ∀ sk ∈ S, SkelOk prog img sk) :
    (S.map fun sk ↦ #[(nextOf img sk).pc, (nextOf img sk).fp]).Perm
      (S.map fun sk ↦ #[sk.pc, sk.fp]) := by
  let m : Option (Regs K) → Array K := fun o ↦
    match o with
    | some r => #[r.pc, r.fp]
    | none => #[]
  have h := hv.2.map m
  simp only [List.map_map] at h
  have hl : (fun sk : Skel ↦ #[sk.pc, sk.fp]) = m ∘ some ∘ Skel.regs := rfl
  have hr : S.map (m ∘ step prog img ∘ Skel.regs) =
      S.map fun sk ↦ #[(nextOf img sk).pc, (nextOf img sk).fp] := by
    refine List.map_congr_left fun sk hsk ↦ ?_
    obtain ⟨hf, next, hex⟩ := hok sk hsk
    have hs : step prog img sk.regs = some next := by
      rw [step_of_fetch_eq_some hf]
      exact hex
    simp only [Function.comp_apply, hs]
    simp [nextOf, hex, m]
  rw [hl]
  rw [← hr]
  exact h.symm

end Fill

/-! ## The witness represents the trace -/

/-- **A skeleton's row steps.** Every skeleton of the list the witness is built from is a row
whose one state pull is its state and one state push its successor. -/
theorem padWitness_rowSteps (prog : Program) (input : PublicInput) {κ : ℕ} (img : MemImage κ)
    (S : List Skel) (hS : ∀ sk ∈ S, ∃ next, execute img sk.regs sk.ins = some next) {sk : Skel}
    (hsk : sk ∈ S) : RowSteps (padWitness prog input img S) sk.regs (nextOf img sk) := by
  have hR : ∀ r ∈ padRows img S, ∃ next, execute img r.sk.regs r.sk.ins = some next :=
    fun r hr ↦ hS _ (mem_mkRows_sk hr)
  obtain ⟨r, hr, rfl⟩ : ∃ r ∈ padRows img S, r.sk = sk := by
    have h := hsk
    rw [← mkRows_sk img (fun _ ↦ 0) (fun _ ↦ 0) S] at h
    obtain ⟨r, hr, h⟩ := List.mem_map.mp h
    exact ⟨r, hr, h⟩
  have hmemT : ∀ op, opTable img (imageData img) (padRows img S) op ∈
      (padWitness prog input img S).tables := by
    intro op
    cases op <;> simp [padWitness]
  refine ⟨opTable img (imageData img) (padRows img S) r.sk.ins.opcode, hmemT _, PRow.raw img r,
    List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨hr, by simp⟩, rfl⟩, ?_, ?_⟩
  · rw [rowMessagesOn_eq_rowSends]
    show ((rowSends (opComponent r.sk.ins.opcode)
      (Environment.fromArray (r.raw img) (imageData img))).filter _).map _ = _
    rw [PRow.rowSends_raw (hR r hr) (imageData img)]
    exact sendsOf_statePull _ _ _ _ _ _
  · rw [rowMessagesOn_eq_rowSends]
    show ((rowSends (opComponent r.sk.ins.opcode)
      (Environment.fromArray (r.raw img) (imageData img))).filter _).map _ = _
    rw [PRow.rowSends_raw (hR r hr) (imageData img)]
    exact sendsOf_statePush _ _ _ _ _ _

/-- **The witness of a padded execution represents the trace**: the image the data names is the
trace's, and every step of the trace's register sequence is a row. -/
theorem padWitness_represents (prog : Program) (input : PublicInput) {T : Trace prog}
    (hκ : T.κ ≤ maxLogMem)
    (hv : run prog T.image T.steps Regs.initial = some (Regs.final prog)) (S : List Skel)
    (hS : ∀ sk ∈ S, ∃ next, execute T.image sk.regs sk.ins = some next)
    (hrun : ∀ k < T.steps, skAt T k ∈ S) :
    AssignmentRepresents (padWitness prog input T.image S) T where
  κ_eq := imageData_logSize T.image hκ
  image_eq := fun i hi ↦ imageData_apply' T.image hκ i _
  regs_embed := by
    intro k hk
    have hlen : T.regs.length = T.steps + 1 := Trace.regs_length hv
    have e : ∀ j (hj : j < T.regs.length), T.regs[j] = stateAt T j := fun j hj ↦ by
      rw [List.getElem_of_eq (regs_eq_map hv) hj]
      simp
    have hk' : k < T.steps := by omega
    rw [e k (by omega), e (k + 1) hk]
    have := padWitness_rowSteps prog input T.image S hS (hrun k hk')
    rwa [nextOf_skAt hv hk'] at this

/-! ## The theorem -/

/-- **Constraint completeness for a padded trace** (leanISA roadmap Layer 10, `T1`, Category A).
A valid execution of well-formed bytecode that fits has a padded trace `t'`, valid, and a witness
satisfying the constraint statement and representing `t'`. The witness is the rows of the run and
the closed walks of the fill, in the six tables, the image as the memory block and the program as
the bytecode block, with the counts that balance the buses. -/
theorem constraintCompleteness {prog : Program} {input : PublicInput} {t : Trace prog}
    (hwf : WellFormedBytecode prog) (h : ValidExecution prog input t) (hfit : t.Fits) :
    ∃ t', t'.PaddedFrom t ∧ ValidExecution prog input t' ∧
      ∃ w, SatisfiedBy prog input w ∧ AssignmentRepresents w t' := by
  obtain ⟨pcs, hpcs⟩ := hwf.hasFillBlocks.exists_starts
  obtain ⟨τ, hτ, h1, h2⟩ := hfit.jump
  have hcap : (padTrace t pcs).κ ≤ maxLogMem := hfit.room
  have hp := padTrace_from t pcs
  have hT : ValidExecution prog input (padTrace t pcs) := hp.valid hcap h
  obtain ⟨⟨hmin, -, hw0, hw1⟩, hrunT⟩ := hT
  have hκ10 : 10 ≤ t.κ := by
    have := h.1.1
    unfold minLogMem at this
    omega
  have hκ63 : t.κ < 63 := by
    have := hfit.room
    unfold maxLogMem at this
    omega
  have hrs : (padTrace t pcs).runSkels = t.runSkels := by
    unfold Trace.runSkels
    rw [hp.regs_eq hcap h]
  have hF := padSkels_valid hκ10 hκ63 t.image pcs hpcs (planCount t.runRows τ)
  have hFok := padSkels_ok hκ10 hκ63 t.image pcs hpcs (planCount t.runRows τ)
  have hrunok : ∀ sk ∈ (padTrace t pcs).runSkels, SkelOk prog (padTrace t pcs).image sk := by
    intro sk hsk
    rw [runSkels_eq hrunT] at hsk
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hsk
    exact skAt_ok hrunT (List.mem_range.mp hk)
  have hS : ∀ sk ∈ (padTrace t pcs).runSkels ++ padSkels t.κ pcs (planCount t.runRows τ),
      SkelOk prog (padTrace t pcs).image sk := by
    intro sk hsk
    rcases List.mem_append.mp hsk with hsk | hsk
    · exact hrunok sk hsk
    · exact hFok sk hsk
  have hcount := fun op ↦ Trace.count_rows t t.κ pcs h1 h2 op
  rw [← hrs] at hcount
  refine ⟨padTrace t pcs, hp, ⟨⟨hmin, hcap, hw0, hw1⟩, hrunT⟩,
    padWitness prog input (padTrace t pcs).image
      ((padTrace t pcs).runSkels ++ padSkels t.κ pcs (planCount t.runRows τ)), ?_, ?_⟩
  · refine padWitness_satisfiedBy prog input (padTrace t pcs).image _ hmin hcap hS ?_ ?_ ?_ hw0 hw1
    · simp only [List.map_append, ← List.cons_append]
      exact (runSkels_state_perm hrunT).append (perm_of_skelsValid hF hFok)
    · intro op
      rw [hcount op]
      exact tableHeight_pow hτ hfit.rows op
    · rw [hcount .blake2s]
      have := floor_le_fillTarget (t.runRows .blake2s) (minRows .blake2s)
      simp only [tableHeight, reduceCtorEq, ↓reduceIte]
      refine le_trans ?_ this
      decide
  · refine padWitness_represents prog input hcap hrunT _ (fun sk hsk ↦ (hS sk hsk).2) ?_
    intro k hk
    refine List.mem_append_left _ ?_
    rw [runSkels_eq hrunT]
    exact List.mem_map_of_mem (List.mem_range.mpr hk)

end LeanerVM.Arithmetization
