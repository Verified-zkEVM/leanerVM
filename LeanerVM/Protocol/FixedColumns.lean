/-
  LeanerVM.Protocol.FixedColumns

  Public index and bytecode columns and their native multilinear evaluations.
-/

module

public import LeanerVM.Protocol.Field
public import LeanerVM.Protocol.Generic.PowerColumn
public import LeanerVM.Arithmetization.Bytecode

/-!
# Fixed public columns

Protocol-blueprint Layer 1 at leanVM revision
`a386121f84292f6fa663aaa3e570c15bc0240ea2`. Category A: the index-column evaluation
follows specification §6.5 (`doc/leanvm/body/06-bus-interactions.tex:95-100`), and
the bytecode evaluation follows multilinear interpolation. Category B: the sixteen-slot
bytecode encoding and bit order follow specification §8.1
(`doc/leanvm/body/08-end-to-end-protocol.tex:4-23`) and
`crates/lean_vm/src/leaf.rs:570-602,627-637`. Instruction coordinates occupy the low
`prog.logSize` bits; the sixteen slot coordinates occupy the high four bits. The public
program is an explicit input. The Python cross-check is
`python-verifier/verifier.py:551-566`, which evaluates the public table at `(zeta, alpha)`.

The bytecode formula uses the already adopted `encodeSlots` definition, including its
zero slots. Consequently the encoding and spare-slot rules have a single source of truth.
These are Lean column-oracle equalities; no theorem here proves Rust execution correspondence.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization
open CompPoly CMlPolynomialEval

@[expose] public section

/-- The fixed address column with entry `g ^ i` at Boolean index `i`. -/
def idxColumn (κ : ℕ) : Column κ := ⟨powerColumnValues g κ⟩

/-- Boolean readout of the public address column. -/
theorem idxColumn_get (κ : ℕ) (i : Fin (2 ^ κ)) :
    (idxColumn κ).values[i] = g ^ i.val := by
  simp [idxColumn, powerColumnValues]

/-- The native index-column evaluator over the challenge field. -/
def idxColumnEval {κ : ℕ} (z : Vector E κ) : E :=
  ∏ j : Fin κ, ((1 - z[j]) + z[j] * algebraMap K E (g ^ (2 ^ j.val)))

/-- Native evaluation agrees with the actual committed-column oracle interface. -/
theorem idxColumn_eval {κ : ℕ} (z : Vector E κ) :
    OracleInterface.answer (idxColumn κ) z = idxColumnEval z := by
  exact eval₂Mle_powerColumnValues (algebraMap K E) g κ z

/-- One public slot as a column indexed by instruction number. -/
def bytecodeSlotColumn (prog : Program) (s : Fin 16) : Column prog.logSize :=
  ⟨Vector.ofFn fun i ↦ (encodeSlots (prog.code i))[s]⟩

/-- The complete sixteen-slot public bytecode column, with instruction bits first. -/
def bytecodeColumn (prog : Program) : Column (prog.logSize + 4) :=
  ⟨Vector.ofFn fun i ↦
    let p := (cubeSplit prog.logSize 4).symm i
    (encodeSlots (prog.code p.1))[p.2]⟩

/-- Slot readout fixes the exact public instruction and includes all spare slots. -/
theorem bytecodeColumn_slot (prog : Program) (i : Fin (2 ^ prog.logSize)) (s : Fin 16) :
    (bytecodeColumn prog).values[cubeIndex (m := 4) i s] = (encodeSlots (prog.code i))[s] := by
  simp [bytecodeColumn, ← cubeSplit_apply]

/-- Taking a Boolean high-coordinate slice selects the corresponding public slot column. -/
theorem slice_bytecodeColumn (prog : Program) (s : Fin 16) :
    slice (bytecodeColumn prog).values s = (bytecodeSlotColumn prog s).values := by
  simp [slice, bytecodeColumn, bytecodeSlotColumn, ← cubeSplit_apply]

/-- Native bytecode evaluation from the public instruction and slot tables. -/
def bytecodeColumnEval (prog : Program) (z : Vector E prog.logSize) (w : Vector E 4) : E :=
  ∑ s : Fin 16, (lagrangeBasis w)[s] *
    ∑ i : Fin (2 ^ prog.logSize),
      algebraMap K E ((encodeSlots (prog.code i))[s]) * (lagrangeBasis z)[i]

/-- The native public-bytecode formula equals the column oracle at every extension-field point. -/
theorem bytecodeColumn_eval (prog : Program) (z : Vector E prog.logSize) (w : Vector E 4) :
    OracleInterface.answer (bytecodeColumn prog) (z ++ w) = bytecodeColumnEval prog z w := by
  change eval₂Mle (bytecodeColumn prog).values (algebraMap K E) (z ++ w) = _
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
