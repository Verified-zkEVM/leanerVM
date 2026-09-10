/-
  LeanerVM.Semantics.Execution

  The execution loop with its halting test, traces, and valid executions.
-/

module

public import LeanerVM.Semantics.Step

/-!
# Valid executions

leanISA roadmap Layer 3 (`docs/roadmap/leanisa-blueprint.md`), at leanVM pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2`. Category A: written from specification §2
(`doc/leanvm/body/02-vm-specification.tex`; the initial registers `:16-20`, the public input
`:24`, the execution loop `:26-35`, nondeterminism `:43-47`) and the boundary tuples of §6.1
(`06-bus-interactions.tex`), before the Rust executor was opened; the diff is recorded in
`docs/roadmap/leanisa-status.md`.

**The loop.** `run prog L n r` takes `n` steps from `r` over the image `L`, testing for the
sentinel before each fetch: a state whose counter is `Program.finalPc prog = g^(N_prog - 1)`,
the last bytecode slot, halts the machine, and stepping from it is `none`. So
`run prog L n Regs.initial = some (Regs.final prog)` says exactly that the machine starts at
`(1, 1)`, executes `n` instructions none of which sits in the sentinel slot, and arrives at
`(g^(N_prog - 1), 1)`: the halting test precedes the fetch (roadmap acceptance test 5; §2
places it after the execute step, status finding S1) and the final frame pointer is `1` (§6.1,
the boundary pull `(g^(N_prog - 1), g^0)`; acceptance test 4, finding S2).

**Traces and valid executions.** A `Trace prog` is what the prover chooses: the memory
log-size `κ`, the committed image, and the step count; all nondeterminism is the image (§2,
"Non determinism"). `HasPublicBoundary input t` is the verifier's boundary: `κ` within the caps
`16 ≤ κ ≤ 32`, and the two public words at `g^0` and `g^1`. `ValidExecution prog input t` is
the boundary together with the run. `Trace.regs` is the register sequence
`r_0 = (1, 1), r_1, …, r_steps` the state bus of Layer 8 embeds.

`ValidExecution` is a specification, not a program: `Program.fetch` and `MemImage.read` are
noncomputable, so a concrete execution is a proof that peels `run` one step at a time
(`run_succ_of_ne`), fetches and reads through `Program.fetch_gpow` and `MemImage.read_gpow`,
and decides each instruction's relation on literal words in the kernel.

## Wrong readings excluded

* The final frame pointer is required: a run reaching the sentinel with `fp ≠ 1` is not a
  `ValidExecution` (acceptance test 4).
* The sentinel is never executed: `run` is `none` from a state at `finalPc`, whatever fuel
  remains, so the step count of a valid execution is the first arrival at the sentinel
  (`run_intermediate`), and the program with `N_prog = 1` has the empty execution
  (acceptance test 5).
* The boundary words sit at `g^0` and `g^1`, two lanes each (acceptance test 17).
-/

namespace LeanerVM.Semantics

open LeanerVM.Parameters

@[expose] public section

/-! ## Boundary registers -/

/-- The initial registers `(1, 1)`, that is `(g^0, g^0)` (specification §2). -/
def Regs.initial : Regs := ⟨1, 1⟩

/-- The sentinel counter `g^(N_prog - 1)`, the last bytecode slot: reaching it halts the
machine, and it is never executed (§2, execution loop step 3; acceptance test 5). -/
def Program.finalPc (prog : Program) : K := gpow (2 ^ prog.logSize - 1)

/-- The final registers `(g^(N_prog - 1), 1)`: the sentinel counter with the frame pointer back
at `1` (§6.1, the boundary pull; acceptance test 4). -/
def Regs.final (prog : Program) : Regs := ⟨prog.finalPc, 1⟩

/-! ## The loop -/

/-- `n` steps from `r`, halting before each fetch: `some` the registers after `n` steps when
none of the `n` states stepped from is at the sentinel, `none` otherwise (§2, execution loop). -/
noncomputable def run {κ : ℕ} (prog : Program) (L : MemImage κ) : ℕ → Regs → Option Regs
  | 0, r => some r
  | n + 1, r => if r.pc = prog.finalPc then none else step prog L r >>= run prog L n

/-! ## Traces and valid executions -/

/-- What the prover chooses for a run of `prog`: the memory log-size, the committed image, and
the number of steps (§2, "Non determinism"). -/
structure Trace (prog : Program) where
  /-- The memory log-size `κ_mem`. -/
  κ : ℕ
  /-- The committed memory image. -/
  image : MemImage κ
  /-- The number of instructions executed. -/
  steps : ℕ

/-- The verifier's boundary on a trace: `16 ≤ κ ≤ 32`, and the two public words at `g^0` and
`g^1` (§2; §6.1). -/
def HasPublicBoundary {prog : Program} (input : PublicInput) (t : Trace prog) : Prop :=
  minLogMem ≤ t.κ ∧ t.κ ≤ maxLogMem ∧
    t.image.read (gpow 0) = some input.word0 ∧ t.image.read (gpow 1) = some input.word1

/-- A valid execution of `prog` on `input`: the boundary holds and `t.steps` steps from `(1, 1)`
halt at `(g^(N_prog - 1), 1)` (§2). -/
def ValidExecution (prog : Program) (input : PublicInput) (t : Trace prog) : Prop :=
  HasPublicBoundary input t ∧ run prog t.image t.steps Regs.initial = some (Regs.final prog)

/-- The register sequence `r_0 = (1, 1), r_1, …, r_steps` of a trace; a prefix that fails to
run is dropped, so a valid trace has exactly `steps + 1` entries (`Trace.regs_length`). -/
noncomputable def Trace.regs {prog : Program} (t : Trace prog) : List Regs :=
  (List.range (t.steps + 1)).filterMap fun n ↦ run prog t.image n Regs.initial

/-! ## Load-bearing lemmas -/

section

variable {κ : ℕ} {prog : Program} {L : MemImage κ}

/-- Zero steps go nowhere. -/
@[simp] theorem run_zero (r : Regs) : run prog L 0 r = some r := rfl

/-- The loop: test for the sentinel, then fetch, execute, and continue. -/
theorem run_succ (n : ℕ) (r : Regs) :
    run prog L (n + 1) r = if r.pc = prog.finalPc then none else step prog L r >>= run prog L n :=
  rfl

/-- Away from the sentinel, a step is taken. -/
theorem run_succ_of_ne {r : Regs} (h : r.pc ≠ prog.finalPc) (n : ℕ) :
    run prog L (n + 1) r = step prog L r >>= run prog L n := by
  rw [run_succ, if_neg h]

/-- At the sentinel, no step is taken (acceptance test 5). -/
theorem run_succ_of_eq {r : Regs} (h : r.pc = prog.finalPc) (n : ℕ) :
    run prog L (n + 1) r = none := by
  rw [run_succ, if_pos h]

/-- Runs compose. -/
theorem run_add (m n : ℕ) (r : Regs) :
    run prog L (m + n) r = run prog L m r >>= run prog L n := by
  induction m generalizing r with
  | zero => simp
  | succ m ih =>
    rw [show m + 1 + n = m + n + 1 by omega, run_succ, run_succ]
    split_ifs
    · rfl
    · rw [bind_assoc]
      exact bind_congr fun r' ↦ ih r'

/-- A run of `m + n` steps passes through the registers after `m`. -/
theorem run_prefix {m n : ℕ} {r r'' : Regs} (h : run prog L (m + n) r = some r'') :
    ∃ r', run prog L m r = some r' ∧ run prog L n r' = some r'' := by
  rw [run_add] at h
  exact Option.bind_eq_some_iff.mp h

/-- A state that is stepped from is not at the sentinel. -/
theorem pc_ne_finalPc_of_run_succ {n : ℕ} {r r' : Regs} (h : run prog L (n + 1) r = some r') :
    r.pc ≠ prog.finalPc :=
  fun hpc ↦ by rw [run_succ_of_eq hpc] at h; exact Option.some_ne_none r' h.symm

/-- Along a run, every state before the last is away from the sentinel: the halting test
precedes every fetch (acceptance test 5). -/
theorem run_intermediate {n : ℕ} {r r' : Regs} (h : run prog L n r = some r') {m : ℕ}
    (hm : m < n) : ∃ r₁, run prog L m r = some r₁ ∧ r₁.pc ≠ prog.finalPc := by
  obtain ⟨k, rfl⟩ : ∃ k, n = m + (k + 1) := ⟨n - m - 1, by omega⟩
  obtain ⟨r₁, h₁, h₂⟩ := run_prefix h
  exact ⟨r₁, h₁, pc_ne_finalPc_of_run_succ h₂⟩

end

/-- A trace that runs has `steps + 1` register states. -/
theorem Trace.regs_length {prog : Program} {t : Trace prog} {r : Regs}
    (h : run prog t.image t.steps Regs.initial = some r) : t.regs.length = t.steps + 1 := by
  rw [Trace.regs]
  refine (List.filterMap_length_eq_length.mpr ?_).trans List.length_range
  intro n hn
  rcases Nat.lt_succ_iff_lt_or_eq.mp (List.mem_range.mp hn) with hlt | rfl
  · obtain ⟨r₁, h₁, -⟩ := run_intermediate h hlt
    simp [h₁]
  · simp [h]

end
end LeanerVM.Semantics
