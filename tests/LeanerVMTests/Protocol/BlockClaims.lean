/-
  LeanerVMTests.Protocol.BlockClaims

  Regression controls for arbitrary-column block readout and padding mutations.
-/

module

public import LeanerVM.Protocol.BlockClaims
public import LeanerVMTests.Protocol.Stacking
import Mathlib.Data.ZMod.Defs
meta import LeanerVM.Protocol.BlockClaims
meta import LeanerVMTests.Protocol.Stacking

/-!
# Block reconstruction controls

The pad can change without changing any block read off the stack. Changing an occupied cell
changes the claim on its block. The pairing of a claim's weight with a table that is no honest
stack is evaluated at a point of the larger field and compared with the block's evaluation,
and with another block's as the mutation.
-/

namespace LeanerVMTests.Protocol

open LeanerVM.Parameters LeanerVM.Protocol CompPoly CMlPolynomialEval

@[expose] public section

/-! ## Reading does not see the pad -/

example (b : Fin blocks.n) :
    blocks.unstack blocks_total_le stack0 b =
      blocks.unstack blocks_total_le (blocks.stackAt tables 3 1) b := by
  simp [stack0]

-- The two stacks differ, in the one cell no block covers.
#guard stack0 ≠ blocks.stackAt tables 3 1

-- The first value of block 1 is occupied, so changing it is observable.
#guard (blocks.unstack blocks_total_le
    (#v[1, 2, 3, 4, 0, 6, 7, 0] : CMlPolynomialEval K 3) (1 : Fin 3))[0] ≠
  (tables (1 : Fin 3))[0]

/-! ## Claims -/

-- The claim holds on the honest stack and fails when the occupied cell changes.
#guard (@decide
    (({ block := (1 : Fin 3), point := #v[0], value := 5 } : BlockClaim blocks K).IsValid
      (RingHom.id K) blocks_total_le stack0)
    (by unfold BlockClaim.IsValid; infer_instance))
#guard (@decide
    (¬ ({ block := (1 : Fin 3), point := #v[0], value := 5 } : BlockClaim blocks K).IsValid
      (RingHom.id K) blocks_total_le (#v[1, 2, 3, 4, 0, 6, 7, 0] : CMlPolynomialEval K 3))
    (by unfold BlockClaim.IsValid; infer_instance))

/-! ## The pairing, evaluated -/

/-- A table that is not the stack of the fixture, with a nonzero uncovered cell. -/
def arbitraryTable : CMlPolynomialEval K 3 := #v[9, 8, 7, 6, 5, 4, 3, 2]

/-- A point of `E` outside `K`. -/
def outsideK : E := E.ofLimbs 0 1 0

/-- A claim on block 1 at a point outside `K`; the value plays no part in the pairing. -/
def claimOnBlock1 : BlockClaim blocks E := ⟨(1 : Fin 3), #v[outsideK], 0⟩

-- The weight paired with the table is block 1 of the table, cells 4 and 5, at the point.
#guard sumCube (hadamard (claimOnBlock1.weight blocks_total_le)
    (CMlPolynomialEval.map (algebraMap K E) arbitraryTable)) =
  eval₂Mle (#v[5, 4] : CMlPolynomialEval K 1) (algebraMap K E) #v[outsideK]
-- Mutation: it is not cells 2 and 3, which reversed selector bits would read.
#guard sumCube (hadamard (claimOnBlock1.weight blocks_total_le)
    (CMlPolynomialEval.map (algebraMap K E) arbitraryTable)) ≠
  eval₂Mle (#v[7, 6] : CMlPolynomialEval K 1) (algebraMap K E) #v[outsideK]

example (q : CMlPolynomialEval K 3) (c : BlockClaim blocks E) :
    c.IsValid (algebraMap K E) blocks_total_le q ↔
      sumCube (hadamard (c.weight blocks_total_le)
        (CMlPolynomialEval.map (algebraMap K E) q)) = c.value :=
  c.isValid_iff_pairing (algebraMap K E) blocks_total_le q

/-! ## A map of the entries that is not injective -/

/-- One block on zero variables. -/
def oneCell : Blocks where
  n := 1
  size := fun _ ↦ 0
  descending := fun _ _ _ ↦ Nat.le_refl 0

-- The entries 0 and 5 differ in the window, and are equal modulo five.
example : (#v[0] : CMlPolynomialEval ℤ 0)[0] ≠ (#v[5] : CMlPolynomialEval ℤ 0)[0] :=
  by decide

example :
    ({ block := (0 : Fin 1), point := #v[], value := 0 } :
      BlockClaim oneCell (ZMod 5)).IsValid
        (Int.castRingHom (ZMod 5)) (μ := 0) (by decide) #v[0] ↔
    ({ block := (0 : Fin 1), point := #v[], value := 0 } :
      BlockClaim oneCell (ZMod 5)).IsValid
        (Int.castRingHom (ZMod 5)) (μ := 0) (by decide) #v[5] := by
  apply BlockClaim.isValid_iff_of_map_window_eq
  intro x _
  fin_cases x
  decide

end
end LeanerVMTests.Protocol
