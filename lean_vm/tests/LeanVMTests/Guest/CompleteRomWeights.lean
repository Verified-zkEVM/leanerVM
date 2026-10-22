import LeanVM.E2E.Batch.Weights

/-!
# Tests: G2's potential (T6-prob, package P5)

* `weightsPot_nil`, `weightsPot_step`, `one_le_weightsPot`, `weightsWith_someH`, the
  certificate's bound and the specification rest on Lean's three standard axioms.
* **The escape bound** is `1/|E| = 2^-192` (`invE_eq`).
* **The hypothesis `cs ≠ []` is needed**: without children both weights are zero whenever the
  chain is answered, so `one_le_weightsPot` would make every answered log bad.
* **The start's witness**: the equality weight of a point with itself is `1` in characteristic
  two (`eqEval_self`), the weight of `A0` at `λ_0,2 = 1` and `z = p_0`.
* **A challenge may break doom**: the affine `x ↦ x` is not identically zero, and `0` kills it,
  so the bound of one bad value per challenge is attained.
-/

namespace LeanVMTests.Guest.CompleteRomWeights

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Node LeanVM.Guest.Batch
open LeanVM.E2E LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open scoped ENNReal

/- The enumeration of `Digest` must never be unfolded by unification. -/
attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest

/-- info: 'LeanVM.E2E.weightsPot_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.E2E.weightsPot_nil

/-- info: 'LeanVM.E2E.weightsPot_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.E2E.weightsPot_step

/--
info: 'LeanVM.E2E.one_le_weightsPot' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanVM.E2E.one_le_weightsPot

/--
info: 'LeanVM.E2E.weightsWith_someH' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanVM.E2E.weightsWith_someH

/--
info: 'LeanVM.Guest.Batch.weightsCert_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanVM.Guest.Batch.weightsCert_bound

/--
info: 'LeanVM.Guest.Batch.weightsRestSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanVM.Guest.Batch.weightsRestSpec

/-- The statements P3b and P6 consume. -/
example {ℓ : Log} {t : Bytes}
    (ht : look ℓ t = none) :
    (∑ u, weightsPot (ℓ ++ [(t, u)])) / Fintype.card Digest ≤
      weightsPot ℓ + ((2 : ℝ≥0∞)⁻¹ ^ 192 +
        failBound batchSeedsAll (ℓ.length + 2)) :=
  weightsPot_step ht

example {ℓ : Log} {cs : List ChildClaims} (h : WeightsVanish ℓ cs)
    (hne : cs ≠ []) (hs : ∀ c ∈ cs, ChildShaped LeanVM.Guest.End.bytecode c)
    (hlen : cs.length ≤ 16) : 1 ≤ weightsPot ℓ :=
  one_le_weightsPot h hne hs hlen

/-- The escape bound per group of challenges is `2^-192`. -/
example : invE = (2 : ℝ≥0∞)⁻¹ ^ 192 := invE_eq

/-- Without children, both weights are zero wherever the chain is answered. -/
example (L : Bytes → Option Digest) (s0 : Digest)
    (rounds : List (E × E)) (w : E × E) (h : weightsWith L s0 [] rounds = some w) :
    w = (0, 0) := by
  simp only [weightsWith, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := h
  simp [matrixWeightA, matrixWeightB, sumE]

/-- A point's equality weight with itself is `1`. -/
example : eqEval [(1 : E), 0, 1] [1, 0, 1] = 1 := eqEval_self _

/-- One bad value is attained: `x ↦ x` is affine and not zero, and `0` kills it. -/
example : ZDoom 1 (fun z ↦ z.getD 0 0) [] ∧ ¬ ZDoom 1 (fun z ↦ z.getD 0 0) [0] := by
  refine ⟨⟨[1], rfl, by simp⟩, ?_⟩
  rintro ⟨w, hw, hne⟩
  obtain rfl : w = [] := List.eq_nil_of_length_eq_zero (by simpa using hw)
  simp at hne

end LeanVMTests.Guest.CompleteRomWeights
