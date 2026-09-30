/-
  Probe for task code-layer1, deliverable C and the findings: the selection identity Layer 1
  does not have. leanVM reads the eighteen BLAKE2S limb columns off `q_flock` by freezing the
  LOW coordinates to a slot's bits (`crates/pcs/src/stack_open.rs:84-97`, `StackClaim::Strided`:
  "Equivalent to a `Point` with `low_point = slot_bits ++ point`"). Layer 1 slices on the high
  index only. This file states and proves the mirrored identity, to show what is missing and
  that it is a generic fact of the same size as `evalMle_append_boolVec`.

  Run from the repository root:
    flock .claude/reports/blueprint-review/logs/lean.lock \
      lake env lean .claude/reports/blueprint-review/probes/code-layer1/StridedProbe.lean
-/
import LeanerVM.Protocol.ToCompPoly.Multilinear
import LeanerVM.Parameters.Field

open LeanerVM.Protocol LeanerVM.Parameters CompPoly CMlPolynomialEval

namespace Probe

variable {R : Type*} [CommRing R]

/-- The strided slice of a table at the low index `i`: the entries whose low `k` bits are `i`. -/
def sliceLow {k m : ℕ} (t : CMlPolynomialEval R (k + m)) (i : Fin (2 ^ k)) :
    CMlPolynomialEval R m :=
  Vector.ofFn fun j ↦ t[cubeIndex i j]

/-- A Boolean low coordinate selects the strided slice at that index. -/
theorem evalMle_boolVec_append {k m : ℕ} (t : CMlPolynomialEval R (k + m)) (i : Fin (2 ^ k))
    (s : Vector R m) :
    evalMle t ((boolVec i : Vector R k) ++ s) = evalMle (sliceLow t i) s := by
  rw [evalMle_eq_sum, sum_cube_split, evalMle_eq_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.sum_eq_single i]
  · rw [lagrangeBasis_cubeIndex, lowVec_append, highVec_append]
    have h := lagrangeBasis_boolVec (R := R) i i
    simp only [if_true] at h
    simp only [Fin.getElem_fin] at h ⊢
    rw [h, one_mul]
    simp [sliceLow]
  · intro i' _ hi
    rw [lagrangeBasis_cubeIndex, lowVec_append, highVec_append]
    have h := lagrangeBasis_boolVec (R := R) i i'
    simp only [if_neg hi] at h
    simp only [Fin.getElem_fin] at h ⊢
    rw [h, zero_mul, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Slot 1 of four (two low bits) of an eight-cell table: cells 1 and 5. -/
def packed : CMlPolynomialEval K 3 := #v[K.ofBits 10, K.ofBits 11, K.ofBits 12, K.ofBits 13,
  K.ofBits 20, K.ofBits 21, K.ofBits 22, K.ofBits 23]

#guard (sliceLow (k := 2) (m := 1) packed (1 : Fin 4)).toList = [K.ofBits 11, K.ofBits 21]
-- The point `(slot bits 1, 0 | z)` reads the strided slice at `z`.
#guard evalMle packed (#v[1, 0, K.ofBits 7] : Vector K 3) =
  evalMle (#v[K.ofBits 11, K.ofBits 21] : CMlPolynomialEval K 1) #v[K.ofBits 7]
-- Near miss: the aligned slice at high index 1 is cells 2 and 3, another column.
#guard (slice (k := 1) (m := 2) packed (1 : Fin 4)).toList = [K.ofBits 12, K.ofBits 13]

#print axioms evalMle_boolVec_append

end Probe
