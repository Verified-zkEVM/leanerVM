import LeanerVM.Semantics.TraceInput
import LeanerVM.Semantics.ReadHints

/-!
# Rust export diagnostic harness

The optional pinned Rust lane generates data that imports this test helper. It checks the
actual exported image, typed program, per-opcode row starts, main/filler partition, natural
state multiplicities and count accounting. It does not import or prove Rust source, and it
does not validate access-count columns, a complete assignment, or verifier acceptance.
-/

namespace LeanerVMTests.Semantics.RustExport

open LeanerVM.Parameters LeanerVM.Semantics

/-- Opcode order of Rust's six trace tables at revision `48a904208d682848dac0e18ef8b01ebfc40df9ad`. -/
def opcodeOrder : Vector Opcode 6 := #v[.xor, .mulNative, .setConstant, .deref, .jump, .blake2s]

/-- Replay an exported main run and separately check all rows attributed to filler. This is
an executable differential-test helper, not a theorem about the Rust implementation. -/
def checkExport (prog : Program) (publicInput : PublicInput) (input : TraceInput)
    (rows : Vector (Array (Regs K)) 6) (hints : List ℕ := []) : Bool :=
  match input.adapt prog with
  | none => false
  | some t =>
    let mainStarts := (List.finRange 6).flatMap fun i ↦ (rows[i].toList.take input.mainCounts[i])
    let fillerStarts := (List.finRange 6).flatMap fun i ↦ (rows[i].toList.drop input.mainCounts[i])
    checkTrace prog publicInput t &&
      decide (∀ i : Fin 6, rows[i].size = input.rowCounts[i]) &&
      (List.finRange 6).all (fun i ↦ rows[i].all fun r ↦
        decide ((addressIndexWithHints prog.logSize (hintIndices prog.logSize hints) r.pc).map
          (fun j ↦ (prog.code j).opcode) = some opcodeOrder[i])) &&
      decide ((mainStarts.map some).Perm
        ((List.range t.steps).map fun i ↦ runChecked prog t.image i Regs.initial)) &&
      checkFillerRowsWithHints prog t.image (hintIndices t.κ hints) fillerStarts

end LeanerVMTests.Semantics.RustExport
