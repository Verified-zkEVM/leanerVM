/-
  Probe for task code-layer1, deliverables B.3, B.5, B.6, B.7 and C.

  Layer 1's definitions evaluated against numbers produced by the pinned leanVM: every
  expected value below is copied from the output of `values.py`, which calls the pinned Python
  verifier's own functions (and, for the bytecode table, a transcription of the Rust encoder).

  Run from the repository root:
    flock .claude/reports/blueprint-review/logs/lean.lock \
      lake env lean .claude/reports/blueprint-review/probes/code-layer1/ValuesProbe.lean
-/
import LeanerVM.Protocol.FixedColumns
import LeanerVM.Protocol.Stack
import LeanerVM.Protocol.Padding
import LeanerVM.Protocol.ClaimWeights
import LeanerVM.Protocol.BlockClaims

open LeanerVM.Protocol LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization
open CompPoly CMlPolynomialEval

namespace Probe

/-- The oracle's answer, as a function `#guard` can evaluate. -/
def answer {n : ℕ} (q : Column n) (z : Vector E n) : E := OracleInterface.answer q z

/-- The point `ζ` of `values.py`. -/
def zeta : Vector E 4 := #v[E.ofLimbs 3 1 0, E.ofLimbs 5 0 7, E.ofLimbs 2 2 2, E.ofLimbs 0 1 0]

/-- The point `α` of `values.py`. -/
def alpha : Vector E 4 := #v[E.ofLimbs 9 0 1, E.ofLimbs 0 4 0, E.ofLimbs 6 6 0, E.ofLimbs 1 2 3]

/-- `α` with its coordinates reversed. -/
def alphaRev : Vector E 4 := #v[E.ofLimbs 1 2 3, E.ofLimbs 6 6 0, E.ofLimbs 0 4 0, E.ofLimbs 9 0 1]

/-! ## B.6 The bytecode column -/

/-- Sixteen instructions: the six opcodes, the three `DEREF` modes, distinct operands, and the
compiler's padding instruction `SET_CONSTANT [g^0] 0` in the last eight cells, the last index
(the halting address) included. Operand `a` of the Rust is the field element `g^a` here. -/
def prog16 : Program where
  logSize := 4
  logSize_le := by decide
  code i := match i.val with
    | 0 => .xor (gpow 1) (gpow 2) (gpow 3)
    | 1 => .mulNative (gpow 4) (gpow 5) (gpow 6)
    | 2 => .setConstant (gpow 7) (E.ofLimbs 11 12 13)
    | 3 => .deref (gpow 8) (gpow 9) (gpow 10) .pc
    | 4 => .deref (gpow 21) (gpow 22) (gpow 23) .fp
    | 5 => .deref (gpow 24) (gpow 25) (gpow 26) .cell
    | 6 => .jump (gpow 27) (gpow 28) (gpow 29)
    | 7 => .blake2s ![gpow 14, gpow 15, gpow 16, gpow 17] (gpow 18) (gpow 19) (gpow 20)
    | _ => .setConstant (gpow 0) 0

/-- The table the transcription of `bytecode_columns` and `stacked_bytecode_table` gives. -/
def pyTable : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 8, 8, 8, 16, 32, 4, 4, 4, 4, 4, 4, 4, 4, 2, 16, 128, 256, 2097152, 16777216, 134217728, 16384, 1, 1, 1, 1, 1, 1, 1, 1, 4, 32, 11, 512, 4194304, 33554432, 268435456, 32768, 0, 0, 0, 0, 0, 0, 0, 0, 8, 64, 12, 1024, 8388608, 67108864, 536870912, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 1, 0, 0, 0, 131072, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 262144, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 524288, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1048576, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

#guard pyTable.length = 256
-- All 256 cells: the encoding, the opcode values, the slot order and the cell order.
#guard (bytecodeColumn prog16).values.toList.map (·.toNat) = pyTable

/-- The oracle's answer at `(ζ, α)`. -/
def bcAnswer : E := answer (bytecodeColumn prog16) (zeta ++ alpha)

-- The evaluation the pinned verifier makes (`verifier.py:566`), and the native evaluator.
#guard bcAnswer = E.ofLimbs 1219889995492 3571792677380 1279835512890
#guard bytecodeColumnEval prog16 zeta alpha = E.ofLimbs 1219889995492 3571792677380 1279835512890
-- Near miss: with `α` reversed the pinned verifier gets another value, and so does the oracle.
#guard answer (bytecodeColumn prog16) (zeta ++ alphaRev) =
  E.ofLimbs 1332010270628 4168742050444 1982034182034
#guard bcAnswer ≠ E.ofLimbs 1332010270628 4168742050444 1982034182034

/-- The opposite layout: slot bits low, instruction bits high. -/
def wrongColumn (prog : Program) : Column (4 + prog.logSize) :=
  ⟨Vector.ofFn fun i ↦
    let p := (cubeSplit 4 prog.logSize).symm i
    (encodeSlots (prog.code p.2))[p.1]⟩

/-- The analogue of `bytecodeColumn_slot` for the opposite layout, by the same proof script:
the *shape* of that theorem holds of either layout. -/
theorem wrongColumn_slot (prog : Program) (i : Fin (2 ^ prog.logSize)) (s : Fin 16) :
    (wrongColumn prog).values[cubeIndex (k := 4) s i] = (encodeSlots (prog.code i))[s] := by
  simp [wrongColumn, ← cubeSplit_apply]

-- The statement of `bytecodeColumn_slot` itself, word for word, is false of the opposite
-- layout: cell `0 + 16 * 3` is instruction 0's opcode there, and slot 0 of instruction 3 here.
#guard (bytecodeColumn prog16).values.toList[48]! = Opcode.xor.code
#guard (wrongColumn prog16).values.toList[48]! = 0
#guard (wrongColumn prog16).values.toList.map (·.toNat) ≠ pyTable

/-- What the bus phase needs and Layer 1 does not state: the program's share of a bytecode
block is one evaluation of the bytecode column, the slots weighted by `eq(w, ·)`. -/
theorem bytecodeColumn_answer_slots (prog : Program) (z : Vector E prog.logSize)
    (w : Vector E 4) :
    eval₂Mle (bytecodeColumn prog).values (algebraMap K E) (z ++ w) =
      ∑ s : Fin 16, (lagrangeBasis w)[s] *
        eval₂Mle (bytecodeSlotColumn prog s).values (algebraMap K E) z := by
  rw [eval₂Mle, evalMle_split]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  congr 1
  rw [eval₂Mle, ← slice_bytecodeColumn]
  congr 1
  apply Vector.ext
  intro i hi
  simp [slice, CMlPolynomialEval.map]

/-! ## B.5 The index column -/

#guard answer (idxColumn 4) zeta = E.ofLimbs 950617 874814 877803
#guard idxColumnEval zeta = E.ofLimbs 950617 874814 877803
#guard idxColumnEval (#v[E.ofLimbs 3 1 0, E.ofLimbs 5 0 7] : Vector E 2) = E.ofLimbs 109 29 108
#guard (idxColumn 4).values.toList.map (·.toNat) = (List.range 16).map (2 ^ ·)

/-! ## B.2, B.3 Selectors and the two paddings -/

/-- Blocks on 2, 1 and 0 variables. -/
def blocks : Blocks where
  n := 3
  size := ![2, 1, 0]
  descending := by
    show ∀ a b : Fin 3, a ≤ b → ![2, 1, 0] b ≤ ![2, 1, 0] a
    decide

theorem blocks_total_le : blocks.total ≤ 2 ^ 3 := by decide

/-- The tables `[1, 2, 3, 4]`, `[5, 6]`, `[7]`. -/
def tables : blocks.Tables K :=
  show (b : Fin 3) → CMlPolynomialEval K (![2, 1, 0] b) from fun b ↦ match b with
    | 0 => (#v[1, 2, 3, 4] : CMlPolynomialEval K 2)
    | 1 => (#v[5, 6] : CMlPolynomialEval K 1)
    | 2 => (#v[7] : CMlPolynomialEval K 0)

/-- The tables over `E`. -/
def tablesE : blocks.Tables E := fun b ↦ CMlPolynomialEval.map (algebraMap K E) (tables b)

/-- The first three coordinates of `ζ`. -/
def z3 : Vector E 3 := #v[E.ofLimbs 3 1 0, E.ofLimbs 5 0 7, E.ofLimbs 2 2 2]

/-- The selector weights, block by block. -/
def weights : List E := (List.finRange 3).map fun b ↦ blocks.selectorWeight blocks_total_le b z3

/-- The blocks at the low coordinates, block by block. -/
def blocksAt : List E := (List.finRange 3).map fun b ↦
  eval₂Mle (tables b) (algebraMap K E) (blocks.lowPoint blocks_total_le b z3)

-- `eq(sel_b, ζ_hi)` as `Placement.eq_above` computes it (`verifier.py:299-302`).
#guard weights = [E.ofLimbs 3 2 2, E.ofLimbs 6 8 8, E.ofLimbs 2 26 30]
#guard blocksAt = [E.ofLimbs 46 11 42, E.ofLimbs 0 3 0, E.ofLimbs 7 0 0]
-- The witness stack (pad 0) and a leaf stack (pad 1) at `ζ`.
#guard eval₂Mle (blocks.stackColumn tables 3).values (algebraMap K E) z3 = E.ofLimbs 38 3 34
#guard evalMle (blocks.stackAt tablesE 3 1) z3 = E.ofLimbs 32 19 54
-- The padding term of equation (2), `1 + Σ_b eq(sel_b, ζ_hi)` (`verifier.py:589`).
#guard 1 + weights.sum = E.ofLimbs 6 16 20
#guard (List.zipWith (· * ·) weights blocksAt).sum + (1 + weights.sum) = E.ofLimbs 32 19 54
-- Near misses: the wrong pad, and the padding term read as the constant 1.
#guard evalMle (blocks.stackAt tablesE 3 0) z3 ≠ E.ofLimbs 32 19 54
#guard (List.zipWith (· * ·) weights blocksAt).sum + 1 ≠ E.ofLimbs 32 19 54

/-! ## B.7 A column claim as a weight -/

/-- The claim's point on block 1, lifted. -/
def lifted : Vector E 3 := blocks.extendPoint blocks_total_le (1 : Fin 3) #v[E.ofLimbs 3 1 0]

/-- A stack no honest prover commits. -/
def arbitrary : Column 3 := ⟨#v[9, 8, 7, 6, 5, 4, 3, 2]⟩

#guard lifted = #v[E.ofLimbs 3 1 0, 0, 1]
#guard (eqWeight lifted).pair arbitrary = E.ofLimbs 6 1 0
#guard (eqWeight lifted).mle #v[E.ofLimbs 1 1 0, E.ofLimbs 0 2 0, E.ofLimbs 7 0 0] =
  E.ofLimbs 9 18 0
-- Near miss: the selector bits reversed, `(1, 0)`, weigh cells 2 and 3.
#guard (eqWeight (#v[E.ofLimbs 3 1 0, 1, 0] : Vector E 3)).pair arbitrary ≠ E.ofLimbs 6 1 0

/-! ## B.4 Back-loaded padding -/

/-- The table `[3, 5]` on one variable. -/
def short : CMlPolynomialEval K 1 := #v[3, 5]

#guard evalMle (padHigh short 2) ((#v[7] : Vector K 1) ++ (#v[11, 13] : Vector K 2)) = 1935
#guard (padHigh short 2).toList = [0, 0, 0, 0, 0, 0, 3, 5]
-- Near miss: padding on the low variables (front-loaded) is another table.
#guard (padHigh short 2).toList ≠ [0, 0, 0, 3, 0, 0, 0, 5]

/-! ## C A layout need not separate its columns -/

/-- Three columns all read off block 0: `Layout.comap` asks nothing of the renaming. -/
def aliased : Layout 3 (Fin 3) (fun _ ↦ 2) :=
  (blocks.layout blocks_total_le).comap (fun _ ↦ (0 : Fin 3)) (fun _ ↦ rfl)

#guard (List.finRange 3).all fun c ↦ (aliased.read arbitrary c).values.toList = [9, 8, 7, 6]

/-! ## Axioms -/

#print axioms Blocks.unstack_eval₂
#print axioms Blocks.unstack_getElem
#print axioms Blocks.readColumn_eval
#print axioms Blocks.layout
#print axioms Layout.comap
#print axioms Blocks.stack_eval_ambient
#print axioms Blocks.stack_eval_ambient_one
#print axioms Blocks.stackColumn_eval_ambient
#print axioms sumCube_padHigh
#print axioms evalMle_padHigh
#print axioms ColumnClaim.holds_iff_weighted
#print axioms eqWeight
#print axioms idxColumn_eval
#print axioms idxColumnEval_eq
#print axioms bytecodeColumn_answer_boolVec
#print axioms bytecodeColumn_eval
#print axioms BlockClaim.isValid_iff_pairing
#print axioms bytecodeColumn_answer_slots

end Probe
