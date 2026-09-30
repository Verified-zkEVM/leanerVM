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

The index column is evaluated in the specification's form and against the form with the two
coordinates swapped. The bytecode column uses two distinct instructions, a spare zero slot, the
native evaluation at a point outside `K`, and the slot bits reversed as the mutation. No
private witness is needed to construct any of these columns.
-/

namespace LeanerVMTests.Protocol

open LeanerVM.Protocol LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization
open CompPoly CMlPolynomialEval

@[expose] public section

private def fixedColumnAnswer {n : ℕ} (q : Column n) (z : Vector E n) : E :=
  eval₂Mle q.values (algebraMap K E) z

/-! ## The index column -/

-- Cell `i` holds `g ^ i`, and the point `(0, 1)` of the cube is index 2.
#guard (idxColumn 2).values = #v[1, g, g ^ 2, g ^ 3]
#guard fixedColumnAnswer (idxColumn 2) #v[0, 1] = ofK (g ^ 2)
#guard fixedColumnAnswer (idxColumn 2) #v[y, y ^ 2] = idxColumnEval #v[y, y ^ 2]

-- The specification's characteristic-two form (§6.5) at `κ = 2`, written out: coordinate `k`
-- carries `g ^ (2 ^ k)`.
#guard fixedColumnAnswer (idxColumn 2) #v[y, y ^ 2] =
  (1 + y * (1 + ofK g)) * (1 + y ^ 2 * (1 + ofK (g ^ 2)))
-- High bit first evaluates a different column.
#guard fixedColumnAnswer (idxColumn 2) #v[y, y ^ 2] ≠
  (1 + y * (1 + ofK (g ^ 2))) * (1 + y ^ 2 * (1 + ofK g))

example (z : Vector E 2) : eval₂Mle (idxColumn 2).values (algebraMap K E) z =
    ∏ k : Fin 2, (1 + z[k] * (1 + algebraMap K E (g ^ (2 ^ k.val)))) :=
  (idxColumn_eval z).trans (idxColumnEval_eq z)

/-! ## The bytecode column -/

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

example : eval₂Mle (bytecodeColumn fixedColumnProgram).values (algebraMap K E)
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

-- The same cube point written with the index and the slot: instruction 1, slot 3.
#guard fixedColumnAnswer (bytecodeColumn fixedColumnProgram)
    ((boolVec (1 : Fin (2 ^ 1)) : Vector E 1) ++ (boolVec (m := 4) (3 : Fin 16) : Vector E 4)) =
  ofK Opcode.mulNative.code

-- The native evaluator agrees with the oracle at a point outside `K` and off the cube.
#guard fixedColumnAnswer (bytecodeColumn fixedColumnProgram)
    ((#v[y] : Vector E 1) ++ (#v[y + 1, y ^ 2, y, 1] : Vector E 4)) =
  bytecodeColumnEval fixedColumnProgram #v[y] #v[y + 1, y ^ 2, y, 1]
-- Mutation: with the slot coordinates reversed it does not.
#guard fixedColumnAnswer (bytecodeColumn fixedColumnProgram)
    ((#v[y] : Vector E 1) ++ (#v[y + 1, y ^ 2, y, 1] : Vector E 4)) ≠
  bytecodeColumnEval fixedColumnProgram #v[y] #v[1, y, y ^ 2, y + 1]

/-- With no instruction bits, the public program contains exactly one instruction. -/
def singletonColumnProgram : Program where
  logSize := 0
  logSize_le := by decide
  code _ := .xor 1 1 1

#guard fixedColumnAnswer (bytecodeColumn singletonColumnProgram)
    ((#v[] : Vector E 0) ++ (#v[1, 1, 0, 0] : Vector E 4)) = ofK Opcode.xor.code
#guard fixedColumnAnswer (bytecodeColumn singletonColumnProgram)
    ((#v[] : Vector E 0) ++ (#v[1, 1, 1, 1] : Vector E 4)) = 0

example (w : Vector E 4) : eval₂Mle (bytecodeColumn singletonColumnProgram).values
    (algebraMap K E) ((#v[] : Vector E 0) ++ w) = bytecodeColumnEval singletonColumnProgram #v[] w :=
  bytecodeColumn_eval singletonColumnProgram _ _

end
end LeanerVMTests.Protocol
