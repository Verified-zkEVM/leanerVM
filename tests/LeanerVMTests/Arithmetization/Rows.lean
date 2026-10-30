import LeanerVM.Arithmetization.Rows
import LeanerVMTests.Arithmetization.Statement

/-!
# Tests: what a row sends

A classic test for kernel evaluation. The closed forms of `LeanerVM.Arithmetization.Rows` are
evaluated on the rows of the hand-built witness of the constraint-statement tests
(`LeanerVMTests.Arithmetization.Statement`) and compared, channel by channel and in the
kernel, with Clean's own evaluation of each row circuit (through `Component.rowOperations`,
each channel and direction filtered by name and tag), which is independent of the theorems; the
theorems are then applied to the same rows. Every interaction of a row has multiplicity `1`. The
memory block's closed form is tested on one row, never on the witness's `2^16` rows.

Concrete readings: the `XOR` fill row reads the zero cell `g^5` three times with counts
`1, g, g²` and pushes `g, g², g³`; the product row's third read carries the executor's product
`x · y`; the `JUMP` row to the sentinel pushes `(g^31, 1)` with its indicator `b = 1`, and the
same row read without its two witness cells (`b = 0`) pushes the fall-through `(g^4, 1)`, so
the indicator is load-bearing; the verifier pulls `(g^31, 1)`, the program's sentinel.
-/

namespace LeanerVMTests.Arithmetization.Rows

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization
open LeanerVMTests.Arithmetization.Statement
open Air.Flat (Component EnsembleWitness)

/-! ## The three channels of a row in both directions, by Clean's evaluation -/

/-- A row's interactions, through Clean's row circuit. -/
def rowInts (t : Air.Flat.Table K) (row : Array K) : List (Interaction K) :=
  t.component.rowOperations.interactions.map (·.eval (t.environment row))

/-- A row's messages on the three channels in both directions, through Clean's row circuit: the
state pull and push, the bytecode pull and push, the memory pulls and pushes. -/
def viaClean (t : Air.Flat.Table K) (row : Array K) : List (List (Array K)) :=
  [(StateChannel.toRaw, (.pull : BusDir)), (StateChannel.toRaw, .push),
    (BytecodeChannel.toRaw, .pull), (BytecodeChannel.toRaw, .push), (MemChannel.toRaw, .pull),
    (MemChannel.toRaw, .push)].map fun (c, d) ↦
      (((rowInts t row).filter (·.channel.name = c.name)).filter (·.direction = d)).map (·.msg)

/-- The same six lists from an `OpcodeSends`. -/
def viaSends (s : OpcodeSends) : List (List (Array K)) :=
  [[#[s.pull.pc, s.pull.fp]], [#[s.push.pc, s.push.fp]], [(toElements s.bc).toArray],
    [(toElements s.bc.bump).toArray], s.mem.map fun m ↦ (toElements m).toArray,
    s.mem.map fun m ↦ (toElements m.bump).toArray]

/-! ## The closed forms against Clean, on the fixture's rows -/

example : viaClean xorT (rawRow xorRow) = viaSends (xorSends xorRow) := by decide +kernel
example : viaClean (mulT g) (rawRow (mulRow g)) = viaSends (mulSends (mulRow g)) := by
  decide +kernel
example : viaClean (setT 1) (rawRow (setRow0 1)) = viaSends (setSends (setRow0 1)) := by
  decide +kernel
example : viaClean (setT 1) (rawRow setRow1) = viaSends (setSends setRow1) := by decide +kernel
example : viaClean derefT (rawRow derefRow) = viaSends (derefSends derefRow) := by
  decide +kernel
example : viaClean jumpT (jumpRaw jumpRow3) = viaSends (jumpSends jumpRow3 1) := by
  decide +kernel
example : viaClean jumpT (jumpRaw jumpRow16) = viaSends (jumpSends jumpRow16 1) := by
  decide +kernel
example : viaClean blakeT (rawRow (blakeRow 3)) = viaSends (blake2sSends (blakeRow 3)) := by
  decide +kernel

/-- Every interaction of the rows has multiplicity `1`, so Clean's `activeMessages` drops none. -/
example : ∀ i ∈ rowInts xorT (rawRow xorRow) ++ rowInts jumpT (jumpRaw jumpRow3) ++
    rowInts blakeT (rawRow (blakeRow 3)), i.mult = 1 := by
  decide +kernel

/-! ## The theorems on the same rows -/

/-- The `XOR` fill row sends `xorSends xorRow`: its typed row read back is itself. -/
example : SendsOpcode xorT (rawRow xorRow) (xorSends xorRow) := by
  have h := xor_sendsOpcode (t := xorT) rfl (rawRow xorRow)
  rwa [show valueFromOffset XorRow 0 (xorT.environment (rawRow xorRow)) = xorRow from
    rowAt_toElements _ xorRow] at h

/-- The `BLAKE2S` row sends `blake2sSends` of itself. -/
example (j : Fin 8) : SendsOpcode blakeT (rawRow (blakeRow j)) (blake2sSends (blakeRow j)) := by
  have h := blake2s_sendsOpcode (t := blakeT) rfl (rawRow (blakeRow j))
  rwa [show valueFromOffset Blake2sRow 0 (blakeT.environment (rawRow (blakeRow j))) =
    blakeRow j from rowAt_toElements _ (blakeRow j)] at h

/-- The `JUMP` row's indicator is the raw cell after its columns and its inverse witness. -/
example : (Statement.jumpRaw jumpRow3)[size JumpRow + 1]?.getD 0 = 1 := by decide +kernel

/-! ## Concrete readings -/

/-- The `XOR` fill row reads cell `g^5` with counts `1, g, g²` and pushes `g, g², g³`. -/
example : ((xorSends xorRow).mem.map fun m ↦ (toElements m).toArray) =
    [#[gpow 5, 1, 0, 0, 0], #[gpow 5, g, 0, 0, 0], #[gpow 5, g ^ 2, 0, 0, 0]] := by
  decide +kernel
example : ((xorSends xorRow).mem.map fun m ↦ (toElements m.bump).toArray) =
    [#[gpow 5, g, 0, 0, 0], #[gpow 5, g ^ 2, 0, 0, 0], #[gpow 5, g ^ 3, 0, 0, 0]] := by
  decide +kernel

/-- The product row's third read carries the executor's product `x · y` at `g^4`. -/
example : ((mulSends (mulRow g)).mem.map fun m ↦ (toElements m).toArray).getLast? =
    some #[gpow 4, 1, mulXY.limb 0, mulXY.limb 1, mulXY.limb 2] := by
  decide +kernel

/-- The `JUMP` row to the sentinel pushes `(g^31, 1)` with its indicator `1`. -/
example : #[(jumpSends jumpRow3 1).push.pc, (jumpSends jumpRow3 1).push.fp] = #[gpow 31, 1] := by
  decide +kernel

/-- Read without its witness cells, the same row's indicator is `0` and its push is the
fall-through `(g^4, 1)`, not the jump: the indicator is load-bearing. -/
example : (rawRow jumpRow3)[size JumpRow + 1]?.getD 0 = 0 := by decide +kernel
example : #[(jumpSends jumpRow3 0).push.pc, (jumpSends jumpRow3 0).push.fp] = #[gpow 4, 1] := by
  decide +kernel
example : #[(jumpSends jumpRow3 0).push.pc, (jumpSends jumpRow3 0).push.fp] ≠ #[gpow 31, 1] := by
  decide +kernel

/-- Every row of the opcode tables makes at most nine memory reads. -/
example : (xorSends xorRow).mem.length = 3 ∧ (setSends setRow1).mem.length = 1 ∧
    (blake2sSends (blakeRow 0)).mem.length = 9 := ⟨rfl, rfl, rfl⟩

/-! ## The blocks and the verifier -/

/-- Row `4` of the memory block: cell `4`, the product `x · y`, finalized at count `g`. -/
def memRow4 : MemRow K := ⟨gpow 4, g, #v[mulXY.limb 0, mulXY.limb 1, mulXY.limb 2]⟩

/-- It pushes `(g^4, 1, x·y)` and pulls `(g^4, g, x·y)` on the memory channel, by Clean's
evaluation (on the block's component; the row's place in the block plays no part). -/
example : viaClean (memT memCnt) (rawRow memRow4) =
    [[], [], [], [], [#[gpow 4, g, mulXY.limb 0, mulXY.limb 1, mulXY.limb 2]],
      [#[gpow 4, 1, mulXY.limb 0, mulXY.limb 1, mulXY.limb 2]]] := by
  decide +kernel

/-- The same by the closed form, which sends nothing on the state channel. -/
example : rowMessagesOn (memT memCnt) (rawRow memRow4) MemChannel.toRaw .pull =
    [#[gpow 4, g, mulXY.limb 0, mulXY.limb 1, mulXY.limb 2]] := by
  rw [memBlock_rowMessagesOn rfl (rawRow memRow4) (rowAt_toElements _ memRow4)]
  decide +kernel
example : rowMessagesOn (memT memCnt) (rawRow memRow4) StateChannel.toRaw .pull = [] := by
  rw [memBlock_rowMessagesOn rfl (rawRow memRow4) (rowAt_toElements _ memRow4)]
  decide +kernel

/-- The verifier of the fixture's program pulls the sentinel `(g^31, 1)` and pushes `(1, 1)`,
and sends nothing on the memory channel. -/
example : verifierMessagesOn (fillW 1 g memCnt) StateChannel.toRaw .pull = [#[gpow 31, 1]] := by
  rw [verifier_messagesOn]
  decide +kernel
example : verifierMessagesOn (fillW 1 g memCnt) StateChannel.toRaw .push = [#[1, 1]] := by
  rw [verifier_messagesOn]
  decide +kernel
example : verifierMessagesOn (fillW 1 g memCnt) MemChannel.toRaw .pull = [] := by
  rw [verifier_messagesOn]
  decide +kernel

/-- Every row of the fixture's six opcode tables sends some `OpcodeSends` with at most nine
memory reads. -/
example : ∀ t ∈ (fillW 1 g memCnt).tables.take 6, ∀ row,
    ∃ s, SendsOpcode t row s ∧ s.mem.length ≤ 9 :=
  exists_sendsOpcode _

/-- Every interaction of the fixture has multiplicity `1`, by the theorem. -/
example : ∀ i ∈ (fillW 1 g memCnt).interactions, i.mult = 1 := interactions_mult_eq_one _

end LeanerVMTests.Arithmetization.Rows
