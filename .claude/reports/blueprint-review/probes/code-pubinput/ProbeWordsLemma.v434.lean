import LeanerVM.Parameters.Field
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.LinearCombination

/-!
# The pinned verifiers' check on the two public words: the algebra of its soundness

The pinned Rust, Python and recursion-guest verifiers read two scalars `c₀, c₁`, check one
equation `c₀ + y·c₁ = interp(w₀, w₁, r)` with `interp(lo, hi, t) = lo + t·(lo + hi)`, and pool
three claims: memory limb 0 at `(r, 0, …, 0)` is `c₀`, limb 1 is `c₁`, limb 2 is `0`.

Here the cells of the three memory limbs at indices 0 and 1 are in `K`, the public words are
in `E` (no hypothesis on their top limb), and the three claims are written through the line
identity `q̃(r, 0, …, 0) = (1 - r)·q(0) + r·q(1)`.

`accepts_two_challenges`: if at two distinct challenges some scalars pass the check with the
three claims true, the cells are the limbs of the public words and the top limbs are zero.
So for a stack whose cells are not the public words there is at most one challenge at which
the pinned verifiers' check can pass with true claims: the error is `1/|E|`.

A plain file. It uses the fields and their limb lemmas only.
-/

open LeanerVM.Parameters

namespace WordsLemma

/-- Two lines through points of `E` that differ agree at one challenge at most. The phase's
private `line_challenge_unique` is this at points of `K`. -/
theorem line_unique {A B C D : E} (hne : ¬ (A = C ∧ B = D)) {r₁ r₂ : E}
    (h₁ : (1 - r₁) * A + r₁ * B = (1 + r₁) * C + r₁ * D)
    (h₂ : (1 - r₂) * A + r₂ * B = (1 + r₂) * C + r₂ * D) : r₁ = r₂ := by
  have e₁ : (A - C) + r₁ * (B - A - C - D) = 0 := by linear_combination h₁
  have e₂ : (A - C) + r₂ * (B - A - C - D) = 0 := by linear_combination h₂
  by_cases hβ : B - A - C - D = 0
  · exfalso
    apply hne
    have hα : A = C := by
      rw [hβ, mul_zero, add_zero, sub_eq_zero] at e₁
      exact e₁
    refine ⟨hα, ?_⟩
    have hb : B = C + C + D := by linear_combination hβ + hα
    rw [hb, CharTwo.add_self_eq_zero, zero_add]
  · have h : (r₁ - r₂) * (B - A - C - D) = 0 := by linear_combination e₁ - e₂
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hβ)

/-- `u + y·v` with `u, v` in `K` is the word with limbs `(u, v, 0)`. -/
theorem two_limbs (u v : K) : ofK u + y * ofK v = E.ofLimbs u v 0 := by
  rw [ofLimbs_eq, show ofK (0 : K) = 0 from map_zero (algebraMap K E)]
  ring

/-- What an accepting run of the pinned verifiers says at the challenge `r`, when the three
pooled claims are true of a stack whose memory limbs have cells `a ℓ` at index 0 and `b ℓ` at
index 1: the scalars are the extensions of limbs 0 and 1, the extension of limb 2 is zero, and
the equation on the words holds. -/
structure Accepts (a b : Fin 3 → K) (w₀ w₁ r c₀ c₁ : E) : Prop where
  /-- The pooled claim on limb 0. -/
  claim₀ : (1 - r) * ofK (a 0) + r * ofK (b 0) = c₀
  /-- The pooled claim on limb 1. -/
  claim₁ : (1 - r) * ofK (a 1) + r * ofK (b 1) = c₁
  /-- The pooled claim on limb 2, at value zero. -/
  claim₂ : (1 - r) * ofK (a 2) + r * ofK (b 2) = 0
  /-- The check: `c₀ + y·c₁ = interp(w₀, w₁, r)`. -/
  words : c₀ + y * c₁ = w₀ + r * (w₀ + w₁)

/-- Accepting at two distinct challenges forces the cells: the public words are the two-limb
words of the cells, and the top cells are zero. -/
theorem accepts_two_challenges {a b : Fin 3 → K} {w₀ w₁ r₁ r₂ c₀ c₁ c₀' c₁' : E}
    (hr : r₁ ≠ r₂) (h₁ : Accepts a b w₀ w₁ r₁ c₀ c₁) (h₂ : Accepts a b w₀ w₁ r₂ c₀' c₁') :
    w₀ = E.ofLimbs (a 0) (a 1) 0 ∧ w₁ = E.ofLimbs (b 0) (b 1) 0 ∧ a 2 = 0 ∧ b 2 = 0 := by
  -- The two low limbs, as one line through the two-limb words of the cells.
  have hw : ofK (a 0) + y * ofK (a 1) = w₀ ∧ ofK (b 0) + y * ofK (b 1) = w₁ := by
    by_contra hne
    refine hr (line_unique hne ?_ ?_)
    · linear_combination h₁.claim₀ + y * h₁.claim₁ + h₁.words
    · linear_combination h₂.claim₀ + y * h₂.claim₁ + h₂.words
  -- The top limb, as a line through zero.
  have ht : ofK (a 2) = 0 ∧ ofK (b 2) = 0 := by
    by_contra hne
    refine hr (line_unique hne ?_ ?_)
    · linear_combination h₁.claim₂
    · linear_combination h₂.claim₂
  have hz : ofK (0 : K) = 0 := map_zero (algebraMap K E)
  refine ⟨?_, ?_, ofK_injective (ht.1.trans hz.symm), ofK_injective (ht.2.trans hz.symm)⟩
  · rw [← hw.1, two_limbs]
  · rw [← hw.2, two_limbs]

/-- For public words with a zero top limb, as leanISA's are by type: the six cells are the four
lanes and two zeros. -/
theorem cells_eq_lanes {a b : Fin 3 → K} {p : Fin 4 → K} {r₁ r₂ c₀ c₁ c₀' c₁' : E}
    (hr : r₁ ≠ r₂)
    (h₁ : Accepts a b (E.ofLimbs (p 0) (p 1) 0) (E.ofLimbs (p 2) (p 3) 0) r₁ c₀ c₁)
    (h₂ : Accepts a b (E.ofLimbs (p 0) (p 1) 0) (E.ofLimbs (p 2) (p 3) 0) r₂ c₀' c₁') :
    (a 0 = p 0 ∧ a 1 = p 1 ∧ a 2 = 0) ∧ (b 0 = p 2 ∧ b 1 = p 3 ∧ b 2 = 0) := by
  obtain ⟨h0, h1, ha, hb⟩ := accepts_two_challenges hr h₁ h₂
  have l0 := congrArg (fun z : E ↦ z.limb 0) h0
  have l1 := congrArg (fun z : E ↦ z.limb 1) h0
  have m0 := congrArg (fun z : E ↦ z.limb 0) h1
  have m1 := congrArg (fun z : E ↦ z.limb 1) h1
  simp only [limb_ofLimbs, Matrix.cons_val_zero, Matrix.cons_val_one] at l0 l1 m0 m1
  exact ⟨⟨l0.symm, l1.symm, ha⟩, ⟨m0.symm, m1.symm, hb⟩⟩

/-- A public word with a nonzero top limb is accepted at one challenge at most, whatever the
stack: the binding itself excludes it, without the separate rejection of `read_public`. -/
theorem top_limb_zero_of_two_challenges {a b : Fin 3 → K} {w₀ w₁ r₁ r₂ c₀ c₁ c₀' c₁' : E}
    (hr : r₁ ≠ r₂) (h₁ : Accepts a b w₀ w₁ r₁ c₀ c₁) (h₂ : Accepts a b w₀ w₁ r₂ c₀' c₁') :
    w₀.limb 2 = 0 ∧ w₁.limb 2 = 0 := by
  obtain ⟨h0, h1, -, -⟩ := accepts_two_challenges hr h₁ h₂
  rw [h0, h1]
  simp

end WordsLemma

#print axioms WordsLemma.accepts_two_challenges
#print axioms WordsLemma.cells_eq_lanes
#print axioms WordsLemma.top_limb_zero_of_two_challenges
