/-
  LeanVM.Arithmetization.CompletenessB.Count

  The instruction counts and the committed size of an execution stepping under a semantics of
  `BLAKE2S`.
-/

module

public import LeanVM.Spec.Statement
public import LeanVM.Spec.IsaWith

@[expose] public section

/-!
# Counts under a semantics

`runCount`, `Trace.count` and `Trace.committedSize` (`Spec/Isa.lean`, `Spec/Statement.lean`) with
the steps under a semantics `S` (`stepB`): the deployed count stops at a `BLAKE2S` step that is no
compression, so an execution under another semantics is counted by these. At the deployed
semantics they are the deployed ones (`committedSizeB_deployed`).
-/

namespace LeanVM.Semantics

open LeanVM.Parameters

/-- The number of instructions of opcode `op` executed in `n` steps from `r` under `S`
(`runCount` under `S`). -/
noncomputable def runCountB (S : BlakeSem) {κ : ℕ} (prog : Program) (L : MemImage κ)
    (op : Opcode) : ℕ → Regs K → ℕ
  | 0, _ => 0
  | n + 1, r =>
    match prog.fetch r.pc, stepB S prog L r with
    | some ins, some r' => (if ins.opcode = op then 1 else 0) + runCountB S prog L op n r'
    | _, _ => 0

/-- The number of instructions of opcode `op` an execution executes under `S`. -/
noncomputable def Trace.countB (S : BlakeSem) {prog : Program} (t : Trace prog) (op : Opcode) : ℕ :=
  runCountB S prog t.image op t.steps Regs.initial

/-- **The committed size of an execution under `S`** (`Trace.committedSize` with `countB S`). -/
noncomputable def Trace.committedSizeB (S : BlakeSem) {prog : Program} (t : Trace prog) : ℕ :=
  let height (op : Opcode) : ℕ := 2 ^ Nat.clog 2 (t.countB S op)
  4 * 2 ^ t.κ + 2 ^ prog.logSize +
    15 * height .xor + 15 * height .mulNative + 8 * height .setConstant + 15 * height .deref +
    14 * height .jump + 19 * height .blake2s + 2 ^ 8 * height .blake2s

theorem runCountB_deployed {κ : ℕ} (prog : Program) (L : MemImage κ) (op : Opcode) :
    ∀ (n : ℕ) (r : Regs K), runCountB blakeDeployed prog L op n r = runCount prog L op n r
  | 0, _ => rfl
  | n + 1, r => by
    unfold runCountB runCount
    rw [stepB_deployed]
    rcases prog.fetch r.pc with _ | i <;> rcases step prog L r with _ | r' <;>
      simp only [runCountB_deployed prog L op n]

/-- At the deployed semantics the committed size is the deployed one. -/
theorem committedSizeB_deployed {prog : Program} (t : Trace prog) :
    t.committedSizeB blakeDeployed = t.committedSize := by
  have h : ∀ op, t.countB blakeDeployed op = t.count op := fun op ↦
    runCountB_deployed prog t.image op t.steps Regs.initial
  simp only [Trace.committedSizeB, Trace.committedSize, h]

end LeanVM.Semantics
