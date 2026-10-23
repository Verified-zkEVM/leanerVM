import LeanerVM.Arithmetization.Rows
import LeanerVMTests.Arithmetization.Statement

/-!
# Tests: what a row sends

A classic test for kernel evaluation. The closed forms of `LeanerVM.Arithmetization.Rows` are
evaluated on the rows of the hand-built witness of the constraint-statement tests
(`LeanerVMTests.Arithmetization.Statement`) and compared, channel by channel and in the
kernel, with Clean's own evaluation of each row circuit (`rowMessagesOn_eq`, through
`Component.rowOperations`), which is independent of the theorems; the theorems are then
applied to the same rows. The memory block is tested on a one-row table, never on the
witness's `2^16` rows.

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

/-! ## Raw rows -/

/-- A typed row as the raw row a table holds. -/
def asRow {Row : TypeMap} [ProvableType Row] (r : Row K) : Array K := (toElements r).toArray

/-- A `JUMP` row with its two local witnesses `w = b = 1`, as the fixture's `JUMP` table holds
it. -/
def asJumpRow (r : JumpRow K) : Array K := asRow r ++ #[1, 1]

/-! ## The six channels of a row, by Clean's evaluation -/

/-- A row's messages on the six channels, through Clean's row circuit. -/
def viaClean (t : Air.Flat.Table K) (row : Array K) : List (List (Array K)) :=
  [StatePull.toRaw, StatePush.toRaw, BytecodePull.toRaw, BytecodePush.toRaw, MemPull.toRaw,
    MemPush.toRaw].map fun c ↦
      ((t.component.rowOperations.interactions.map (·.eval (t.environment row))).filter
        (·.channel.name = c.name)).map (·.msg)

/-- The same six lists from an `OpcodeSends`. -/
def viaSends (s : OpcodeSends) : List (List (Array K)) :=
  [[#[s.pull.pc, s.pull.fp]], [#[s.push.pc, s.push.fp]], [(toElements s.bc).toArray],
    [(toElements s.bc.bump).toArray], s.mem.map fun m ↦ (toElements m).toArray,
    s.mem.map fun m ↦ (toElements m.bump).toArray]

/-! ## The closed forms against Clean, on the fixture's rows -/

example : viaClean xorT (asRow xorRow) = viaSends (xorSends xorRow) := by decide +kernel
example : viaClean (mulT g) (asRow (mulRow g)) = viaSends (mulSends (mulRow g)) := by
  decide +kernel
example : viaClean (setT 1) (asRow (setRow0 1)) = viaSends (setSends (setRow0 1)) := by
  decide +kernel
example : viaClean (setT 1) (asRow setRow1) = viaSends (setSends setRow1) := by decide +kernel
example : viaClean derefT (asRow derefRow) = viaSends (derefSends derefRow) := by
  decide +kernel
example : viaClean jumpT (asJumpRow jumpRow3) = viaSends (jumpSends jumpRow3 1) := by
  decide +kernel
example : viaClean jumpT (asJumpRow jumpRow16) = viaSends (jumpSends jumpRow16 1) := by
  decide +kernel
example : viaClean blakeT (asRow (blakeRow 3)) = viaSends (blake2sSends (blakeRow 3)) := by
  decide +kernel

/-! ## The theorems on the same rows -/

/-- The `XOR` fill row sends `xorSends xorRow`: its typed row read back is itself. -/
example : SendsOpcode xorT (asRow xorRow) (xorSends xorRow) := by
  have h := xor_sendsOpcode (t := xorT) rfl (asRow xorRow)
  rwa [show valueFromOffset XorRow 0 (xorT.environment (asRow xorRow)) = xorRow from
    rowAt_toElements fillData xorRow] at h

/-- The `BLAKE2S` row sends `blake2sSends` of itself. -/
example (j : Fin 8) : SendsOpcode blakeT (asRow (blakeRow j)) (blake2sSends (blakeRow j)) := by
  have h := blake2s_sendsOpcode (t := blakeT) rfl (asRow (blakeRow j))
  rwa [show valueFromOffset Blake2sRow 0 (blakeT.environment (asRow (blakeRow j))) =
    blakeRow j from rowAt_toElements fillData (blakeRow j)] at h

/-- The `JUMP` row's indicator is the raw cell after its columns and its inverse witness. -/
example : (asJumpRow jumpRow3)[size JumpRow + 1]?.getD 0 = 1 := by decide +kernel

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
example : (asRow jumpRow3)[size JumpRow + 1]?.getD 0 = 0 := by decide +kernel
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

/-- A one-row memory block over the fixture's data. -/
def memT1 : Air.Flat.Table K :=
  mkT memTable (size MemRow) [asRow memRow4] fun r hr ↦ by
    rw [List.mem_singleton] at hr
    subst hr
    exact Vector.size_toArray _

/-- Its row pushes `(g^4, 1, x·y)` and pulls `(g^4, g, x·y)`, by Clean's evaluation. -/
example : viaClean memT1 (asRow memRow4) =
    [[], [], [], [], [#[gpow 4, g, mulXY.limb 0, mulXY.limb 1, mulXY.limb 2]],
      [#[gpow 4, 1, mulXY.limb 0, mulXY.limb 1, mulXY.limb 2]]] := by
  decide +kernel

/-- The same by the closed form, which sends nothing on the state channels. -/
example : rowMessagesOn memT1 (asRow memRow4) MemPull.toRaw =
    [#[gpow 4, g, mulXY.limb 0, mulXY.limb 1, mulXY.limb 2]] := by
  rw [memBlock_rowMessagesOn rfl (asRow memRow4) (rowAt_toElements fillData memRow4)]
  decide +kernel
example : rowMessagesOn memT1 (asRow memRow4) StatePull.toRaw = [] := by
  rw [memBlock_rowMessagesOn rfl (asRow memRow4) (rowAt_toElements fillData memRow4)]
  decide +kernel

/-- The verifier of the fixture's program pulls the sentinel `(g^31, 1)`, and sends nothing on
the memory channels. -/
example : rowMessagesOn (fillW 1 g memCnt).verifierTable
    (toElements (fillW 1 g memCnt).publicInput).toArray StatePull.toRaw = [#[gpow 31, 1]] := by
  rw [verifier_rowMessagesOn rfl]
  decide +kernel
example : rowMessagesOn (fillW 1 g memCnt).verifierTable
    (toElements (fillW 1 g memCnt).publicInput).toArray MemPull.toRaw = [] := by
  rw [verifier_rowMessagesOn rfl]
  decide +kernel

/-- Every row of the fixture's six opcode tables sends some `OpcodeSends` with at most nine
memory reads. -/
example : ∀ t ∈ (fillW 1 g memCnt).tables.take 6, ∀ row,
    ∃ s, SendsOpcode t row s ∧ s.mem.length ≤ 9 :=
  exists_sendsOpcode _

end LeanerVMTests.Arithmetization.Rows
