/-
  LeanVM.Cost.Loop

  The reusable reasoning a certifying compiler to the cost machine would emit against: a loop
  run under an invariant indexed by the iteration count. Spike.
-/

module

public import LeanVM.Cost.Lang

namespace LeanVM.Cost

@[expose] public section

/-- **A loop under an invariant.** If, for every `j < n`, the test is nonzero (price `cc`) in every
state of invariant `P j`, and one run of the body takes such a state to one of `P (j + 1)` (price
at most `cb`, at every fuel), and the test is zero (price `cc`) in every state of `P n`, the loop
with more than `n - j` fuel takes a state of `P j` to one of `P n`, at price at most
`(n - j)·(cc + cb + 1) + cc + 1`. -/
theorem loop_exec {c : Expr} {s : Stmt} {P : ℕ → State → Prop} {n cc cb : ℕ}
    (hc : ∀ j < n, ∀ σ, P j σ → ∃ x, x ≠ 0 ∧ c.eval σ = some (x, cc))
    (hc0 : ∀ σ, P n σ → c.eval σ = some (0, cc))
    (hs : ∀ j < n, ∀ σ, P j σ → ∀ F, ∃ σ' d, s.exec F σ = some (σ', d) ∧ d ≤ cb ∧ P (j + 1) σ') :
    ∀ j ≤ n, ∀ σ, P j σ → ∀ fuel, n - j < fuel →
      ∃ σ' d, (Stmt.loop c s).exec fuel σ = some (σ', d) ∧
        d ≤ (n - j) * (cc + cb + 1) + cc + 1 ∧ P n σ' := by
  intro j hj σ hσ fuel hfuel
  induction h : n - j generalizing j σ fuel with
  | zero =>
    have : j = n := by omega
    subst this
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    exact ⟨σ, cc + 1, by simp [Stmt.exec, hc0 σ hσ], by omega, hσ⟩
  | succ k ih =>
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨x, hx, hcx⟩ := hc j (by omega) σ hσ
    obtain ⟨σ₁, d₁, hs1, hd1, hP1⟩ := hs j (by omega) σ hσ (f + 1)
    obtain ⟨σ₂, d₂, hrest, hd2, hP2⟩ := ih (j + 1) (by omega) σ₁ hP1 f (by omega) (by omega)
    refine ⟨σ₂, cc + d₁ + d₂ + 1, ?_, ?_, hP2⟩
    · simp only [Stmt.exec, hcx, Option.bind_eq_bind, Option.bind_some, hx, ite_false, hs1, hrest,
        Option.pure_def]
    · rw [Nat.succ_mul]
      omega

end

end LeanVM.Cost
