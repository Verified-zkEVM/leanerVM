/-
  LeanerVMTests.Protocol.Claims

  Regression controls for arbitrary-column block readout and padding mutations.
-/

module

public import LeanerVM.Protocol.Generic.Claims
public import LeanerVMTests.Protocol.Stacking
import Mathlib.Data.ZMod.Defs
meta import LeanerVM.Protocol.Generic.Claims
meta import LeanerVMTests.Protocol.Stacking

/-!
# Block reconstruction controls

Padding can change without changing any reconstructed block. Changing an occupied cell
changes the corresponding Boolean-point claim. The mixed-ring pairing theorem is also
checked at arbitrary ambient tables, not just the honest fixture.
-/

namespace LeanerVMTests.Protocol

open LeanerVM.Parameters LeanerVM.Protocol CompPoly CMlPolynomialEval

@[expose] public section

example (b : Fin blocks.n) :
    blocks.unstack blocks_total_le stack0 b =
      blocks.unstack blocks_total_le (blocks.stackAt 3 1) b := by
  simp [stack0]

-- This rejects the false strengthening that all ambient cells are recovered by unstacking.
example : stack0 ≠ blocks.stackAt 3 1 := by
  intro h
  have hx := congrArg (fun v : CMlPolynomialEval K 3 ↦ v[7]) h
  change (blocks.stackAt 3 0)[7] = (blocks.stackAt 3 1)[7] at hx
  rw [blocks.stackAt_getElem_of_total_le 0 (by decide) (by decide),
    blocks.stackAt_getElem_of_total_le 1 (by decide) (by decide)] at hx
  exact zero_ne_one hx

example (q : CMlPolynomialEval K 3) (c : BlockClaim blocks E) :
    c.IsValid (algebraMap K E) blocks_total_le q ↔
      sumCube (hadamard (c.weight blocks_total_le)
        (CMlPolynomialEval.map (algebraMap K E) q)) = c.value :=
  c.isValid_iff_pairing (algebraMap K E) blocks_total_le q

-- The first value of block 1 is occupied, so changing it is observable.
#guard (blocks.unstack blocks_total_le
    (#v[1, 2, 3, 4, 0, 6, 7, 0] : CMlPolynomialEval K 3) (1 : Fin 3))[0] ≠
  (blocks.values (1 : Fin 3))[0]

-- The corresponding claim holds on the honest column and rejects the occupied-cell mutation.
#guard (@decide
    (({ block := (1 : Fin 3), point := #v[0], value := 5 } : BlockClaim blocks K).IsValid
      (RingHom.id K) blocks_total_le stack0)
    (by unfold BlockClaim.IsValid; infer_instance))
#guard (@decide
    (¬ ({ block := (1 : Fin 3), point := #v[0], value := 5 } : BlockClaim blocks K).IsValid
      (RingHom.id K) blocks_total_le (#v[1, 2, 3, 4, 0, 6, 7, 0] : CMlPolynomialEval K 3))
    (by unfold BlockClaim.IsValid; infer_instance))

/-- A single occupied integer cell, used to test a noninjective coefficient map. -/
def mappedWindowBlock : Blocks ℤ where
  n := 1
  size := fun _ ↦ 0
  values := fun _ ↦ #v[0]
  descending := fun _ _ _ ↦ Nat.le_refl 0

-- The source coefficients disagree inside the window, but become equal modulo five.
example : (#v[0] : CMlPolynomialEval ℤ 0)[0] ≠ (#v[5] : CMlPolynomialEval ℤ 0)[0] :=
  by decide

example :
    ({ block := (0 : Fin 1), point := #v[], value := 0 } :
      BlockClaim mappedWindowBlock (ZMod 5)).IsValid
        (Int.castRingHom (ZMod 5)) (μ := 0) (by decide) #v[0] ↔
    ({ block := (0 : Fin 1), point := #v[], value := 0 } :
      BlockClaim mappedWindowBlock (ZMod 5)).IsValid
        (Int.castRingHom (ZMod 5)) (μ := 0) (by decide) #v[5] := by
  apply BlockClaim.isValid_iff_of_map_window_eq
  intro x _
  fin_cases x
  decide

end
end LeanerVMTests.Protocol
