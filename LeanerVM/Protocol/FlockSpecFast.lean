/-
  LeanerVM.Protocol.FlockSpecFast

  The honest Flock column of the BLAKE2s inhabitant, as compiled code computes it: the circuit
  compiled once, each compression's block traced on its 64-bit words, the cells read off the
  words.
-/

module

public import LeanerVM.Protocol.FlockSpec
public import LeanerVM.Protocol.ToArkLib.Flock.CircuitFast

/-!
# The BLAKE2s Flock column, compiled

`Blake2sFlock.genColumn` traces `blake2sCircuit` on each row's input block as a bitset of
`2 ^ 14` bits, every gate a few operations on numbers of that size, about 0.4 s a compression.
`genColumnFast` compiles the circuit once (`ProductCircuit.compile`), traces each block on its
64-bit words (`Compiled.traceW`) and reads the cells off the words (`cellOfW`); it is
`genColumn` by `ProductCircuit.rep_traceW` and `packCell_of_rep`. Compiled code runs it
through the `@[csimp]` theorems `genColumn_eq_genColumnFast` and, for the inhabitant whose
`gen` field holds it, `blake2sFlockSpec_eq_blake2sFlockSpecFast`. No definition a theorem
states changes.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly ProductCircuit

@[expose] public section

namespace Blake2sFlock

open Blake2sCircuit

/-- Cell `s` of a block given by its words: word `s`. -/
def cellOfW (zw : Array UInt64) (s : Fin 256) : K := BF64.ofBitVec (zw.getD s 0).toBitVec

/-- A cell of a bitset is the word of the words that hold it. -/
theorem packCell_of_rep {zw : Array UInt64} {z : Form m} (h : Rep zw z) (s : Fin 256) :
    packCell z s = cellOfW zw s := by
  rw [packCell, cellOfW]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro c hc
  have hs := s.isLt
  have hj : 64 * s.val + c < 64 * nWords m := by show _ < 64 * 256; omega
  rw [BitVec.getLsbD_extractLsb', decide_eq_true hc, Bool.true_and, ← h.2 _ hj,
    show (64 * s.val + c) / 64 = s.val by omega, show (64 * s.val + c) % 64 = c by omega]

variable {κ : ℕ}

/-- The honest column, as compiled code computes it: the circuit compiled once, each block traced
on its words, the cells read off the words. -/
def genColumnFast (rows : Vector (Fin 18 → K) (2 ^ κ)) : Column (8 + κ) :=
  let pc := compile (blake2sCircuit : ProductCircuit m)
  let blocks : Vector (Array UInt64) (2 ^ κ) := rows.map fun l ↦ pc.traceW (inputForm l)
  ⟨Vector.ofFn fun u ↦ cellOfW blocks[((cubeSplit 8 κ).symm u).2] ((cubeSplit 8 κ).symm u).1⟩

/-- The compiled column is the honest column. -/
@[csimp] theorem genColumn_eq_genColumnFast : @genColumn = @genColumnFast := by
  funext κ rows
  simp only [genColumn, genColumnFast, columnOf]
  congr 2
  funext u
  simp only [Fin.getElem_fin, Vector.getElem_map, honestBlock]
  exact packCell_of_rep (rep_traceW _ _) _

/-- The BLAKE2s inhabitant with the compiled generator. -/
def blake2sFlockSpecFast : FlockSpec where
  r1cs := blake2sCircuit.toBlockR1CS E
  slot := slots
  compress_of_holds := compress_of_holds
  gen := genColumnFast
  holds_gen := fun rows ↦ by
    rw [← genColumn_eq_genColumnFast]
    exact holds_gen rows
  slots_gen := fun rows t h ↦ by
    rw [← genColumn_eq_genColumnFast]
    exact slots_gen rows t h

/-- Compiled code passes the inhabitant with the compiled generator. -/
@[csimp] theorem blake2sFlockSpec_eq_blake2sFlockSpecFast :
    @blake2sFlockSpec = @blake2sFlockSpecFast := by
  unfold blake2sFlockSpec blake2sFlockSpecFast
  congr 1
  exact genColumn_eq_genColumnFast

end Blake2sFlock

end
end LeanerVM.Protocol
