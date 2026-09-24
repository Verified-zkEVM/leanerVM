/-
  LeanerVMTests.Protocol.AmbientStacking

  Regression controls for empty, full, and padded ambient stack evaluation.
-/

module

public import LeanerVM.Protocol.Generic.AmbientStacking
public import LeanerVMTests.Protocol.Stacking
meta import LeanerVM.Protocol.Generic.AmbientStacking
meta import LeanerVMTests.Protocol.Stacking

/-!
# Ambient padding controls

An empty family evaluates to its padding, a full family has no padding weight, and a genuinely
padded family needs that weight even at an extension-field point outside the Boolean cube.
-/

namespace LeanerVMTests.Protocol

open LeanerVM.Parameters LeanerVM.Protocol CompPoly CMlPolynomialEval

@[expose] public section

example (z : Vector K 2) : evalMle (emptyBlocks.stackAt 2 1) z = 1 := by
  have ht : emptyBlocks.stackAt 2 1 = Vector.replicate (2 ^ 2) (1 : K) := by
    apply Vector.ext
    intro i hi
    rw [emptyBlocks.stackAt_getElem_of_total_le 1 hi (by
      have he : emptyBlocks.total = 0 := by decide
      rw [he]
      exact Nat.zero_le i)]
    simp only [Vector.getElem_replicate]
  rw [ht]
  exact evalMle_replicate_one z

/-- Three fully packed blocks of heights two, one, one. -/
def fullBlocks : Blocks K where
  n := 3
  size := ![1, 0, 0]
  values := fun b ↦ match b with
    | 0 => #v[1, 2]
    | 1 => #v[3]
    | 2 => #v[4]
  descending := by
    show ∀ a b : Fin 3, a ≤ b → ![1, 0, 0] b ≤ ![1, 0, 0] a
    decide

example (z : Vector K 2) :
    (∑ b : Fin fullBlocks.n, fullBlocks.selectorWeight (μ := 2) (by decide) b z) = 1 :=
  fullBlocks.sum_selectorWeight_of_total_eq (by decide) z

-- Dropping the padding correction changes the extension at this off-base-field point.
#guard eval₂Mle (blocks.stackAt 3 1) (algebraMap K E)
    #v[E.ofLimbs 0 1 0, E.ofLimbs 0 1 0, E.ofLimbs 0 1 0] ≠
  eval₂Mle (blocks.stackAt 3 0) (algebraMap K E)
    #v[E.ofLimbs 0 1 0, E.ofLimbs 0 1 0, E.ofLimbs 0 1 0]

end
end LeanerVMTests.Protocol
