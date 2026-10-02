/-
  LeanerVM.Protocol.FixedColumns

  Public index and bytecode columns and their native multilinear evaluations.
-/

module

public import LeanerVM.Protocol.Field
public import LeanerVM.Protocol.ToCompPoly.BitProductTable
public import LeanerVM.Arithmetization.Bytecode

/-!
# Fixed public columns

The two columns both parties know, at leanVM revision
`a386121f84292f6fa663aaa3e570c15bc0240ea2`.

* **The index column** holds the address `g ^ i` at cell `i`. It is the geometric table of
  `ToCompPoly/BitProductTable.lean` at the generator, so its extension is a product of one
  factor per coordinate, `∏_k (1 + ζ_k (1 + g^(2^k)))` in characteristic two. Category A:
  specification §6.5 (`doc/leanvm/body/06-bus-interactions.tex:95-100`).
* **The bytecode column** is the program as one table on `logSize + 4` variables: the
  instruction index in the low `logSize` coordinates, the slot in the high four, low bit first.
  Category B: the layout follows specification §8.1
  (`doc/leanvm/body/08-end-to-end-protocol.tex:4-25`) and
  `crates/lean_vm/src/leaf.rs:570-604, 627-637`; the second verifier evaluates the same table at
  `(zeta, alpha)` (`python-verifier/verifier.py:551-566`). The content of a slot is
  `encodeSlots`, the one definition of the encoding, zero slots included.

Every index of the program is encoded, the last one too: the column knows no sentinel. These
are equalities about the columns' extensions; no theorem here proves that the Rust computes
them.

This module names the program, so it imports the bytecode encoding. It belongs with the leanISA
instance and the compiled verifier; no phase of the oracle protocol imports it.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization
open CompPoly CMlPolynomialEval

@[expose] public section

/-! ## The index column -/

/-- The fixed address column with entry `g ^ i` at Boolean index `i`. -/
def idxColumn (κ : ℕ) : Column κ := ⟨powersTable g κ⟩

/-- The native index-column evaluator over the challenge field. -/
def idxColumnEval {κ : ℕ} (z : Vector E κ) : E :=
  ∏ j : Fin κ, ((1 - z[j]) + z[j] * algebraMap K E (g ^ (2 ^ j.val)))

/-- The native evaluator is the column's extension. -/
theorem idxColumn_eval {κ : ℕ} (z : Vector E κ) :
    eval₂Mle (idxColumn κ).values (algebraMap K E) z = idxColumnEval z :=
  eval₂Mle_powersTable (algebraMap K E) g κ z

/-- The evaluator as the specification writes it in characteristic two (§6.5):
`∏_k (1 + ζ_k (1 + g^(2^k)))`. -/
theorem idxColumnEval_eq {κ : ℕ} (z : Vector E κ) :
    idxColumnEval z = ∏ k : Fin κ, (1 + z[k] * (1 + algebraMap K E (g ^ (2 ^ k.val)))) := by
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [CharTwo.sub_eq_add]
  ring

/-! ## The bytecode column -/

/-- The complete sixteen-slot public bytecode column, with instruction bits first. -/
def bytecodeColumn (prog : Program) : Column (prog.logSize + 4) :=
  ⟨Vector.ofFn fun i ↦
    let p := (cubeSplit prog.logSize 4).symm i
    (encodeSlots (prog.code p.1))[p.2]⟩

/-- The cell of instruction `i` and slot `s` holds that slot, spare slots included. -/
private theorem bytecodeColumn_slot (prog : Program) (i : Fin (2 ^ prog.logSize)) (s : Fin 16) :
    (bytecodeColumn prog).values[cubeIndex (m := 4) i s] = (encodeSlots (prog.code i))[s] := by
  simp [bytecodeColumn, ← cubeSplit_apply]

/-- The bit order, stated at the extension: at the cube point whose low coordinates are the
bits of the instruction index and whose high four are the bits of the slot, the column holds
that slot of that instruction (§8.1: the opcode of instruction `z` is `P(z, 1, 1, 0, 0)`). -/
theorem bytecodeColumn_answer_boolVec (prog : Program) (i : Fin (2 ^ prog.logSize))
    (s : Fin 16) :
    eval₂Mle (bytecodeColumn prog).values (algebraMap K E)
        ((boolVec i : Vector E prog.logSize) ++ (boolVec (m := 4) s : Vector E 4)) =
      algebraMap K E ((encodeSlots (prog.code i))[s]) := by
  rw [eval₂Mle, evalMle_append_boolVec, evalMle_boolVec, slice_getElem]
  simpa only [CMlPolynomialEval.map, Fin.getElem_fin, Vector.getElem_map] using
    congrArg (algebraMap K E) (bytecodeColumn_slot prog i s)

/-- Native bytecode evaluation from the public instruction and slot tables. -/
def bytecodeColumnEval (prog : Program) (z : Vector E prog.logSize) (w : Vector E 4) : E :=
  ∑ s : Fin 16, (lagrangeBasis w)[s] *
    ∑ i : Fin (2 ^ prog.logSize),
      algebraMap K E ((encodeSlots (prog.code i))[s]) * (lagrangeBasis z)[i]

/-- The native evaluator is the column's extension, at every point of `E`. -/
theorem bytecodeColumn_eval (prog : Program) (z : Vector E prog.logSize) (w : Vector E 4) :
    eval₂Mle (bytecodeColumn prog).values (algebraMap K E) (z ++ w) =
      bytecodeColumnEval prog z w := by
  rw [eval₂Mle, evalMle_split]
  unfold bytecodeColumnEval
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  rw [evalMle_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simpa only [slice, Vector.getElem_ofFn, CMlPolynomialEval.map, Vector.getElem_map,
    Fin.getElem_fin] using congrArg (algebraMap K E) (bytecodeColumn_slot prog i s)

end
end LeanerVM.Protocol
