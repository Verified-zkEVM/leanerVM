/-
  LeanVM.Facts.IsaWith

  leanISA under the deployed `KECCAK` semantics is leanISA (`Statement/LeanIsa.lean`):
  `executeWithB_deployed`, `stepB_deployed`, `runB_deployed`, `validExecutionB_deployed`.
  The definitions are the statement's; these are proofs.
-/

module

public import Statement.LeanIsa
public import LeanVM.Fast.CubicExt
public import LeanVM.Fast.FieldWords

namespace LeanVM.Semantics

open LeanVM.Parameters

@[expose] public section

theorem executeWithB_deployed (read : K → Option E) (r : Regs K) (i : Instr) :
    executeWithB keccakDeployed read r i = executeWith read r i := by
  cases i <;> rfl

theorem stepB_deployed {κ : ℕ} (prog : Program) (L : MemImage κ) (r : Regs K) :
    stepB keccakDeployed prog L r = step prog L r := by
  have : executeWithB keccakDeployed L.read r = executeWith L.read r :=
    funext (executeWithB_deployed L.read r)
  simp only [stepB, step, execute, this]

theorem runB_deployed {κ : ℕ} (prog : Program) (L : MemImage κ) :
    ∀ (n : ℕ) (r : Regs K), runB keccakDeployed prog L n r = run prog L n r
  | 0, _ => rfl
  | n + 1, r => by
    have : runB keccakDeployed prog L n = run prog L n := funext (runB_deployed prog L n)
    simp only [runB, run, stepB_deployed, this]

/-- **The deployed semantics gives the deployed valid executions.** -/
theorem validExecutionB_deployed (prog : Program) (input : PublicInput) (t : Trace prog) :
    ValidExecutionB keccakDeployed prog input t ↔ ValidExecution prog input t := by
  simp only [ValidExecutionB, ValidExecution, runB_deployed]

end
end LeanVM.Semantics
