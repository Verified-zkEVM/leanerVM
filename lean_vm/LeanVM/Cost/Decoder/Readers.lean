module

public import LeanVM.Cost.Decoder.Log
public import LeanVM.Guest.B1.Sig.Bytes
public import Statement.Theorems
import all LeanVM.Guest.B1.Sig.Interface
import all LeanVM.Guest.B1.Main.Interface

/-!
# The guest decoder's compiled chain: the cell readers, the seed and the statement

`B1.Main`'s readers of `main`'s frame and the memory, compiled bottom-up, each a function of its
own, under the statement's encodings of their values (`Statement/Theorems.lean`):

* the cells' digests and claims: `digestOfCells`, `deferOfCells`, `fixedOfCells`, and a
  signature claim's four cells (`Sig.xmssClaimOf`, `Sig.sphincsClaimOf`; a bit vector of cells
  through `cellVal_eq`, `cellPairVal_eq`: its number, a `BitVec.ofFin`);
* the memory's cells (`cellAt`, `readCells`, `slotCells`), the claims of a table's slots
  (`xmssAt`, `sphincsAt`), a DA digest's slot (`daDigestAt`);
* **the seed** (`decSeed`) and **the statement** (`decStmt`).

The reader `rd` (the memory's index, `Located.readIn`) and `main`'s valuation `σ` are closures:
the decoder's top level supplies them.
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.B1 LeanVM.Guest.B1.Main

@[expose] public section

/-! ## Cells -/

cost_compile digestOfCellsC := Main.digestOfCells
cost_compile deferOfCellsC := deferOfCells
cost_compile fixedOfCellsC := fixedOfCells

/-! ## A signature claim's cells: bit vectors as their numbers -/

theorem kToNat_lane (a : K) : LeanVM.Protocol.Verifier.kToNat a = (K.lane a).toNat := rfl
cost_rewrite kToNat_lane

theorem cellNat_lt (c : E) : Sig.cellNat c < 2 ^ 128 := by
  rw [← Sig.toNat_cellVal]; exact BitVec.isLt _

/-- A cell's `128` bits, as their number (`++` unfolds to `Nat.lor` and shifts). -/
theorem cellVal_eq (c : E) : Sig.cellVal c = BitVec.ofFin ⟨Sig.cellNat c, cellNat_lt c⟩ :=
  BitVec.eq_of_toNat_eq (by rw [Sig.toNat_cellVal]; rfl)
cost_rewrite cellVal_eq

/-- Two cells' `256` bits, as their number. -/
theorem cellPairVal_eq (lo hi : E) : Sig.cellPairVal lo hi =
    BitVec.ofFin ⟨Sig.cellNat lo + 2 ^ 128 * Sig.cellNat hi, by
      have := cellNat_lt lo; have := cellNat_lt hi; omega⟩ := by
  apply BitVec.eq_of_toNat_eq
  rw [Sig.cellPairVal, BitVec.toNat_append, Sig.toNat_cellVal, Sig.toNat_cellVal,
    Nat.shiftLeft_eq, mul_comm, LeanVM.Guest.Value.two_pow_mul_or (cellNat_lt lo)]
  simp only [BitVec.toNat_ofFin]; omega
cost_rewrite cellPairVal_eq

cost_compile xmssClaimOfC := Sig.xmssClaimOf
cost_compile sphincsClaimOfC := Sig.sphincsClaimOf

/-! ## The memory's cells -/

cost_compile cellAtC := cellAt
cost_compile readCellsC := readCells
cost_compile slotCellsC := slotCells
cost_compile xmssAtC := xmssAt
cost_compile sphincsAtC := sphincsAt
cost_compile daDigestAtC := daDigestAt

/-! ## The seed and the statement -/

cost_compile decSeedC := decSeed

set_option maxHeartbeats 4000000 in
cost_compile decStmtC := decStmt

end

end LeanVM.Cost.Decoder
