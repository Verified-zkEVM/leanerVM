/-
  LeanerVM.Protocol.ToVCVio.MonadRel

  Relations between the computations of two monads that `pure` and `bind` preserve: what a
  program written once over its primitives inherits from a relation between two choices of the
  primitives. Candidate for VCVio.
-/

module

public import Mathlib.Init

/-!
# Relations preserved by `pure` and `bind`

A `MonadRel m₁ m₂` is a relation between the computations of `m₁` and `m₂`, at every type, that
holds of `pure x` and `pure x` and that `bind` preserves: if it holds of `a₁, a₂` and of
`f₁ x, f₂ x` for every `x`, it holds of `a₁ >>= f₁, a₂ >>= f₂`. A program written once over a
record of primitives, in any monad, relates its two runs on two records whose primitives are
pairwise related, by induction on the program: no parametricity theorem is needed, only that the
program is built from the primitives by `pure` and `bind`. Examples: a run that succeeds on one
reader succeeds on another with the same value; one run simulates another on a log.
-/

namespace LeanerVM.Protocol

@[expose] public section

/-- A relation between computations of two monads that `pure` and `bind` preserve. -/
structure MonadRel (m₁ m₂ : Type → Type) [Monad m₁] [Monad m₂] where
  /-- The relation, at every type. -/
  R : {α : Type} → m₁ α → m₂ α → Prop
  /-- It holds of `pure`. -/
  pure : ∀ {α : Type} (x : α), R (Pure.pure x) (Pure.pure x)
  /-- `bind` preserves it. -/
  bind : ∀ {α β : Type} {a₁ : m₁ α} {a₂ : m₂ α} {f₁ : α → m₁ β} {f₂ : α → m₂ β},
    R a₁ a₂ → (∀ x, R (f₁ x) (f₂ x)) → R (a₁ >>= f₁) (a₂ >>= f₂)

namespace MonadRel

variable {m₁ m₂ : Type → Type} [Monad m₁] [Monad m₂] (𝓡 : MonadRel m₁ m₂)

/-- `map` preserves it, in lawful monads. -/
theorem map [LawfulMonad m₁] [LawfulMonad m₂] {α β : Type} {a₁ : m₁ α} {a₂ : m₂ α}
    (h : 𝓡.R a₁ a₂) (f : α → β) : 𝓡.R (f <$> a₁) (f <$> a₂) := by
  rw [← bind_pure_comp, ← bind_pure_comp]
  exact 𝓡.bind h fun x ↦ 𝓡.pure (f x)

end MonadRel

end

end LeanerVM.Protocol
