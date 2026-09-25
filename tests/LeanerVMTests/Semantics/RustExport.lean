import LeanerVM.Semantics.TraceInput
import LeanerVM.Semantics.FillerRows

/-!
# Rust export diagnostic harness

The optional pinned Rust lane generates data that imports this test helper. It checks the
actual exported image, typed program, per-opcode row starts, main/filler partition, natural
state multiplicities and count accounting. It does not import or prove Rust source, and it
does not validate access-count columns, a complete assignment, or verifier acceptance. The
hint list is passed to the carrier for speed only (`LeanerVM.Semantics.Executable`).
-/

namespace LeanerVMTests.Semantics.RustExport

open LeanerVM.Parameters LeanerVM.Semantics

/-- Opcode order of Rust's six trace tables at revision `48a904208d682848dac0e18ef8b01ebfc40df9ad`. -/
def opcodeOrder : Vector Opcode 6 := #v[.xor, .mulNative, .setConstant, .deref, .jump, .blake2s]

/-- The states `r_0, …, r_{n-1}` of `n` checked steps from `r`, `none` from a failed step on.
A test helper for the main-row multiset; the accepted run was already checked by `checkTrace`. -/
def mainStates {κ : ℕ} (prog : Program) (image : MemImage κ) (hints : List ℕ) :
    ℕ → Option (Regs K) → List (Option (Regs K))
  | 0, _ => []
  | n + 1, r => r :: mainStates prog image hints n (r >>= stepChecked prog image hints)

/-- Replay an exported main run and separately check all rows attributed to filler. This is
an executable differential-test helper, not a theorem about the Rust implementation. -/
def checkExport (prog : Program) (publicInput : PublicInput) (input : TraceInput)
    (rows : Vector (Array (Regs K)) 6) (hints : List ℕ := []) : Bool :=
  match input.adapt prog with
  | none => false
  | some t =>
    let mainStarts := (List.finRange 6).flatMap fun i ↦ (rows[i].toList.take input.mainCounts[i])
    let fillerStarts := (List.finRange 6).flatMap fun i ↦ (rows[i].toList.drop input.mainCounts[i])
    checkTrace prog publicInput t hints &&
      decide (∀ i : Fin 6, rows[i].size = input.rowCounts[i]) &&
      (List.finRange 6).all (fun i ↦ rows[i].all fun r ↦
        decide ((fetchInstruction prog hints r.pc).map Instr.opcode = some opcodeOrder[i])) &&
      decide ((mainStarts.map some).Perm
        (mainStates prog t.image hints t.steps (some Regs.initial))) &&
      checkFillerRows prog t.image hints fillerStarts

end LeanerVMTests.Semantics.RustExport
