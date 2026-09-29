/-
  LeanerVM.Protocol.ToVCVio.UniformSample

  Counting bounds on the probability of an event under a uniform sample.
  Candidate for VCVio.
-/

module

public import VCVio.OracleComp.Constructions.SampleableType

/-!
# Counting bounds for uniform samples

VCVio's `probEvent_uniformSample` says that the probability of an event under a uniform sample
of a finite type is the number of its witnesses over the size of the type. The two bounds here
are the forms a soundness argument uses: an event with at most `k` witnesses has probability at
most `k/|α|`, and an event any two of whose witnesses are equal has probability at most
`1/|α|`. The right-hand sides are non-negative reals coerced to extended ones, the type of a
round-by-round error. The second bound takes its hypothesis as a statement about witnesses, so
that no caller has to name the finite set of all elements of the type.
-/

namespace LeanerVM.Protocol

open OracleComp
open scoped NNReal ENNReal

public section

variable {α : Type} [SampleableType α] [Fintype α]

/-- An event with at most `k` witnesses has probability at most `k/|α|` under a uniform
sample. -/
theorem probEvent_uniformSample_le_of_card_le (p : α → Prop) [DecidablePred p] {k : ℕ}
    (h : (Finset.univ.filter p).card ≤ k) :
    Pr[p | $ᵗ α] ≤ ((k / Fintype.card α : ℝ≥0) : ℝ≥0∞) := by
  rw [probEvent_uniformSample, ENNReal.coe_div (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),
    ENNReal.coe_natCast, ENNReal.coe_natCast]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr h) _

/-- An event any two of whose witnesses are equal has probability at most `1/|α|` under a
uniform sample. -/
theorem probEvent_uniformSample_le_of_subsingleton (p : α → Prop)
    (h : ∀ a b, p a → p b → a = b) :
    Pr[p | $ᵗ α] ≤ ((1 / Fintype.card α : ℝ≥0) : ℝ≥0∞) := by
  classical
  have hcard : (Finset.univ.filter p).card ≤ 1 :=
    Finset.card_le_one.mpr fun a ha b hb ↦
      h a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  simpa only [Nat.cast_one] using probEvent_uniformSample_le_of_card_le p hcard

end
end LeanerVM.Protocol
