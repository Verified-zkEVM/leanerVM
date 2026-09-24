/-
  LeanerVMTests.Protocol.FixedColumns

  Regression controls for public-column evaluation and coordinate order.
-/

module

public import LeanerVM.Protocol.FixedColumns
meta import LeanerVM.Protocol.FixedColumns
meta import LeanerVM.Protocol.Field
meta import LeanerVM.Parameters.Field
meta import CompPoly.Multilinear.Basic

/-!
# Fixed-column controls

The asymmetric power-table example detects swapping the two Boolean bits. Public bytecode
checks use two distinct instructions and include a spare zero slot and the extension-field
native evaluation. No private witness is needed to construct any of these columns.
-/

namespace LeanerVMTests.Protocol

open LeanerVM.Protocol LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization
open CompPoly CMlPolynomialEval

@[expose] public section

private def fixedColumnAnswer {n : ℕ} (q : Column n) (z : Vector E n) : E :=
  OracleInterface.answer q z

example (a : ℚ) : evalMle (powerColumnValues a 0) #v[] = 1 := by
  rw [evalMle_powerColumnValues]
  simp

example : evalMle (powerColumnValues (2 : ℚ) 2) #v[3, 5] = 64 := by
  simp only [evalMle_powerColumnValues]
  norm_num [Fin.prod_univ_succ]

example : evalMle (powerColumnValues (2 : ℚ) 2) #v[3, 5] ≠
    evalMle (powerColumnValues (2 : ℚ) 2) #v[5, 3] := by
  simp only [evalMle_powerColumnValues]
  norm_num [Fin.prod_univ_succ]

-- The actual index-column oracle uses the same low-bit-first convention.
#guard fixedColumnAnswer (idxColumn 2) #v[0, 1] = ofK (g ^ 2)
#guard fixedColumnAnswer (idxColumn 2) #v[y, y ^ 2] = idxColumnEval #v[y, y ^ 2]

/-- A public fixture with two different opcodes. -/
def fixedColumnProgram : Program where
  logSize := 1
  logSize_le := by decide
  code i := if i.val = 0 then .xor 1 1 1 else .mulNative 1 1 1

example : (bytecodeColumn fixedColumnProgram).values[
      cubeIndex (k := 1) (m := 4) (0 : Fin 2) (3 : Fin 16)] =
    Opcode.xor.code := by
  exact bytecodeColumn_slot fixedColumnProgram 0 3

example : (bytecodeColumn fixedColumnProgram).values[
      cubeIndex (k := 1) (m := 4) (1 : Fin 2) (3 : Fin 16)] =
    Opcode.mulNative.code := by
  exact bytecodeColumn_slot fixedColumnProgram 1 3

example (i : Fin 2) :
    (bytecodeColumn fixedColumnProgram).values[
      cubeIndex (k := 1) (m := 4) i (15 : Fin 16)] = 0 := by
  exact bytecodeColumn_slot fixedColumnProgram i 15

example : OracleInterface.answer (bytecodeColumn fixedColumnProgram)
      (#v[y] ++ #v[0, 1, y, y ^ 2]) =
    bytecodeColumnEval fixedColumnProgram #v[y] #v[0, 1, y, y ^ 2] :=
  bytecodeColumn_eval fixedColumnProgram _ _

-- Instruction bit 1 selects the second instruction; slot 3 has bits (1,1,0,0).
#guard fixedColumnAnswer (bytecodeColumn fixedColumnProgram)
    ((#v[1] : Vector E 1) ++ (#v[1, 1, 0, 0] : Vector E 4)) = ofK Opcode.mulNative.code
-- Reversing the slot bits selects spare slot 12 and must not return the opcode.
#guard fixedColumnAnswer (bytecodeColumn fixedColumnProgram)
    ((#v[1] : Vector E 1) ++ (#v[0, 0, 1, 1] : Vector E 4)) = 0
#guard fixedColumnAnswer (bytecodeColumn fixedColumnProgram)
    ((#v[1] : Vector E 1) ++ (#v[0, 0, 1, 1] : Vector E 4)) ≠ ofK Opcode.mulNative.code

/-- With no instruction bits, the public program contains exactly one instruction. -/
def singletonColumnProgram : Program where
  logSize := 0
  logSize_le := by decide
  code _ := .xor 1 1 1

#guard fixedColumnAnswer (bytecodeColumn singletonColumnProgram)
    ((#v[] : Vector E 0) ++ (#v[1, 1, 0, 0] : Vector E 4)) = ofK Opcode.xor.code
#guard fixedColumnAnswer (bytecodeColumn singletonColumnProgram)
    ((#v[] : Vector E 0) ++ (#v[1, 1, 1, 1] : Vector E 4)) = 0

example (w : Vector E 4) : OracleInterface.answer (bytecodeColumn singletonColumnProgram)
    ((#v[] : Vector E 0) ++ w) = bytecodeColumnEval singletonColumnProgram #v[] w :=
  bytecodeColumn_eval singletonColumnProgram _ _

end
end LeanerVMTests.Protocol
