import LeanerVM.Arithmetization.Steps
import LeanerVMTests.Arithmetization.Statement

/-!
# Tests: rows are steps

A classic test for kernel evaluation, on the hand-built witness of the constraint-statement
tests (`LeanerVMTests.Arithmetization.Statement`).

**The theorems applied.** From `fill_satisfiedBy` alone, `rowSteps_of_satisfiedBy` makes the
`JUMP` row to the sentinel the step `(g^3, 1) → (g^31, 1)` of the fixture's program over its
image, the step the semantic tests compute directly (`fill_step3`); and the `XOR` fill row
the step `(g^4, g^5) → (g^5, g^5)`, which is not on the run: the fill blocks are closed walks
of steps. `no_row_at_sentinel` applies, the fixture's sentinel slot being an `XOR`.

**The sentinel hypothesis.** A program whose sentinel slot holds a `JUMP` is not
`SentinelSafe`; there a row may pull the sentinel counter and jump on. The counter-witness, a
satisfying witness of such a program that represents no valid execution, is
`LeanerVMTests.Arithmetization.Sentinel`.
-/

namespace LeanerVMTests.Arithmetization.Steps

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization
open LeanerVMTests.Arithmetization.Statement

/-- The fixture's sentinel slot is not a `JUMP`. -/
theorem fill_sentinelSafe : SentinelSafe fillProg := by decide

/-- The fixture's program with a `JUMP` in its sentinel slot. -/
def jumpSentinelProg : Program :=
  ⟨fillProg.logSize, fillProg.logSize_le, fun i ↦
    if (i : ℕ) = 31 then .jump (gpow 26) (gpow 27) (gpow 28) else fillProg.code i⟩

/-- It is not sentinel-safe. -/
example : ¬ SentinelSafe jumpSentinelProg := by decide

/-- The `JUMP` table of the witness has the fixture's rows. -/
theorem tableAt_four : (tableAt (fillW 1 g memCnt) 4).table = jumpT.table := by
  simp only [tableAt, fillW, mkW, witnessOfTables, Air.Flat.withDerivedData, List.getElem_map,
    List.getElem_attach]
  rfl

/-- The `XOR` table of the witness has the fixture's row. -/
theorem tableAt_zero : (tableAt (fillW 1 g memCnt) 0).table = xorT.table := by
  simp only [tableAt, fillW, mkW, witnessOfTables, Air.Flat.withDerivedData, List.getElem_map,
    List.getElem_attach]
  rfl

/-- The `JUMP` row to the sentinel is a step of the program, from the statement alone. -/
example : step fillProg fillImage ⟨gpow 3, 1⟩ = some ⟨gpow 31, 1⟩ := by
  have h := rowSteps_of_satisfiedBy fill_satisfiedBy (tableAt (fillW 1 g memCnt) 4)
    (List.getElem_mem _) (jumpRaw jumpRow3) (by rw [tableAt_four]; exact List.mem_cons_self)
    ⟨gpow 3, 1⟩ ⟨gpow 31, 1⟩
    (by rw [rowMessagesOn_eq, activeMessages_of_mults ?_] <;> decide +kernel)
    (by rw [rowMessagesOn_eq, activeMessages_of_mults ?_] <;> decide +kernel)
  rw [fill_imageOf] at h
  exact h

/-- The `XOR` fill row is a step too, off the run. -/
example : step fillProg fillImage ⟨gpow 4, gpow 5⟩ = some ⟨gpow 5, gpow 5⟩ := by
  have h := rowSteps_of_satisfiedBy fill_satisfiedBy (tableAt (fillW 1 g memCnt) 0)
    (List.getElem_mem _) (rawRow xorRow) (by rw [tableAt_zero]; exact List.mem_cons_self)
    ⟨gpow 4, gpow 5⟩ ⟨gpow 5, gpow 5⟩
    (by rw [rowMessagesOn_eq, activeMessages_of_mults ?_] <;> decide +kernel)
    (by rw [rowMessagesOn_eq, activeMessages_of_mults ?_] <;> decide +kernel)
  rw [fill_imageOf] at h
  exact h

/-- No row of the fixture pulls the sentinel counter `g^31`. -/
example : ∀ t ∈ (fillW 1 g memCnt).tables, ∀ row ∈ t.table, ∀ pc fp : K,
    #[pc, fp] ∈ rowMessagesOn t row StateChannel.toRaw .pull → pc ≠ fillProg.finalPc :=
  no_row_at_sentinel fill_sentinelSafe fill_satisfiedBy

end LeanerVMTests.Arithmetization.Steps
