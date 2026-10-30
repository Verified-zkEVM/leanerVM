/-
  LeanerVM.Semantics.PaddedRun

  A run on a padded image is the run on the original: reading is monotone under extension.
-/

module

public import LeanerVM.Semantics.PaddedTrace

/-!
# Padding keeps the run

leanISA roadmap Layer 10 (`docs/roadmap/leanisa-blueprint.md`). Category A. A padded trace adds
cells above the committed image and changes none below it, and a valid run reads only cells below
it, so the run is the same run. The chain is: a read that succeeds on the original image succeeds,
to the same word, on the extension (`MemImage.read_mono`); the six arms of `executeWith` only read
and compare, so a successful execution stays successful over a reader that reads more
(`executeWith_mono`); hence a step (`step_mono`), a run (`run_mono`), a valid execution
(`PaddedFrom.valid`) and the register sequence (`PaddedFrom.regs_eq`).

`PaddedFrom.valid` takes the cap `t'.κ ≤ maxLogMem` as a hypothesis: padding says only that the
memory grows, not that it stays within what the verifier accepts.

## Wrong readings excluded

* The extension may not change a word below `2^t.κ`: `image_ext` is what the run's reads need, and
  a trace that changes a cell the run reads is not a padding and is not valid
  (`tests/LeanerVMTests/Semantics/PaddedRun.lean`).
* Monotonicity is for success only: an unsuccessful read on the original (an address past the end)
  may succeed on the extension, so the extension can make more runs valid, never fewer.
-/

namespace LeanerVM.Semantics

open LeanerVM.Parameters

@[expose] public section

/-- Reading is monotone under extending the memory: a word read from `L` is read from an `L'`
holding the same words at the same indices, at the same address. -/
theorem MemImage.read_mono {κ κ' : ℕ} (hκ : κ ≤ κ') (hκ' : κ' < 64) {L : MemImage κ}
    {L' : MemImage κ'} (h : ∀ i (hi : i < 2 ^ κ) (hi' : i < 2 ^ κ'), L' ⟨i, hi'⟩ = L ⟨i, hi⟩)
    {a : K} {v : E} (hr : L.read a = some v) : L'.read a = some v := by
  obtain ⟨i, rfl, rfl⟩ := (MemImage.read_eq_some_iff (lt_of_le_of_lt hκ hκ') L).mp hr
  have hi' : (i : ℕ) < 2 ^ κ' := lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right (by norm_num) hκ)
  exact (MemImage.read_gpow hκ' L' ⟨i, hi'⟩).trans (congrArg some (h i i.isLt hi'))

/-- An instruction that executes over a reader executes to the same registers over a reader that
reads everything the first reads, to the same words: the arms only read and compare. -/
theorem executeWith_mono {read read' : K → Option E}
    (h : ∀ a v, read a = some v → read' a = some v) {r r' : Regs K} {ins : Instr}
    (he : executeWith read r ins = some r') : executeWith read' r ins = some r' := by
  cases ins <;>
    simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at he ⊢ <;>
    aesop

/-- A step over `L` is the same step over an extension `L'`. -/
theorem step_mono {κ κ' : ℕ} (hκ : κ ≤ κ') (hκ' : κ' < 64) {prog : Program} {L : MemImage κ}
    {L' : MemImage κ'} (h : ∀ i (hi : i < 2 ^ κ) (hi' : i < 2 ^ κ'), L' ⟨i, hi'⟩ = L ⟨i, hi⟩)
    {r r' : Regs K} (hs : step prog L r = some r') : step prog L' r = some r' := by
  unfold step at hs ⊢
  obtain ⟨ins, hf, hex⟩ := Option.bind_eq_some_iff.mp hs
  exact Option.bind_eq_some_iff.mpr
    ⟨ins, hf, executeWith_mono (fun _ _ hr ↦ MemImage.read_mono hκ hκ' h hr) hex⟩

/-- A run over `L` is the same run over an extension `L'`. -/
theorem run_mono {κ κ' : ℕ} (hκ : κ ≤ κ') (hκ' : κ' < 64) {prog : Program} {L : MemImage κ}
    {L' : MemImage κ'} (h : ∀ i (hi : i < 2 ^ κ) (hi' : i < 2 ^ κ'), L' ⟨i, hi'⟩ = L ⟨i, hi⟩)
    {n : ℕ} {r r' : Regs K} (hr : run prog L n r = some r') : run prog L' n r = some r' := by
  induction n generalizing r with
  | zero => exact hr
  | succ n ih =>
    rw [run_succ] at hr ⊢
    split_ifs at hr ⊢
    obtain ⟨r₁, hs, hrest⟩ := Option.bind_eq_some_iff.mp hr
    exact Option.bind_eq_some_iff.mpr ⟨r₁, step_mono hκ hκ' h hs, ih hrest⟩

/-- A valid execution stays valid on a padded trace within the memory cap: the public words are
below `2^t.κ`, and the run reads only cells below it. -/
theorem Trace.PaddedFrom.valid {prog : Program} {input : PublicInput} {t' t : Trace prog}
    (hp : t'.PaddedFrom t) (hcap : t'.κ ≤ maxLogMem) (hv : ValidExecution prog input t) :
    ValidExecution prog input t' := by
  obtain ⟨⟨hmin, -, hw0, hw1⟩, hrun⟩ := hv
  have hκ' : t'.κ < 64 := lt_of_le_of_lt hcap (by decide)
  refine ⟨⟨le_trans hmin hp.κ_le, hcap, ?_, ?_⟩, ?_⟩
  · exact MemImage.read_mono hp.κ_le hκ' hp.image_ext hw0
  · exact MemImage.read_mono hp.κ_le hκ' hp.image_ext hw1
  · rw [hp.steps_eq]
    exact run_mono hp.κ_le hκ' hp.image_ext hrun

/-- A padded trace has the same register sequence as the trace it pads: padding changes no state
of the run. -/
theorem Trace.PaddedFrom.regs_eq {prog : Program} {input : PublicInput} {t' t : Trace prog}
    (hp : t'.PaddedFrom t) (hcap : t'.κ ≤ maxLogMem) (hv : ValidExecution prog input t) :
    t'.regs = t.regs := by
  have hκ' : t'.κ < 64 := lt_of_le_of_lt hcap (by decide)
  unfold Trace.regs
  rw [hp.steps_eq]
  refine List.filterMap_congr fun n hn ↦ ?_
  have hn' : n < t.steps + 1 := List.mem_range.mp hn
  obtain ⟨r, hr⟩ : ∃ r, run prog t.image n Regs.initial = some r := by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn' with hlt | rfl
    · obtain ⟨r₁, h₁, -⟩ := run_intermediate hv.2 hlt
      exact ⟨r₁, h₁⟩
    · exact ⟨_, hv.2⟩
  rw [hr, run_mono hp.κ_le hκ' hp.image_ext hr]

end
end LeanerVM.Semantics
