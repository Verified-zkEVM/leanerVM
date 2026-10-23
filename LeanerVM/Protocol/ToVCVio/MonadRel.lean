/-
  LeanerVM.Protocol.ToVCVio.MonadRel

  Relations between the computations of two monads that `pure` and `bind` preserve, and
  properties of computations graded by a count that adds up along `bind`: what a program written
  once over its primitives inherits from its primitives. Candidate for VCVio.
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

A `MonadGrade m` is a property of computations of `m` graded by a count: it holds of `pure x` at
`0`, and of `a >>= f` at `n + k` when it holds of `a` at `n` and of every `f x` at `k`. The count
cannot depend on the value `x`, so a program's count follows from its primitives' when no count
of the program depends on a value it reads: the queries a run asks, or the input it consumes.
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

/-- A property of computations graded by a count, additive along `bind`: it holds of `pure` at
`0`, and of `a >>= f` at `n + k` when it holds of `a` at `n` and of `f x` at `k` for every `x`. The
count may not depend on the value `x`: a query count, or the input a reader consumes. -/
structure MonadGrade (m : Type → Type) [Monad m] where
  /-- The property, at every type and count. -/
  P : {α : Type} → m α → Nat → Prop
  /-- It holds of `pure` at `0`. -/
  pure : ∀ {α : Type} (x : α), P (Pure.pure x) 0
  /-- `bind` adds the counts. -/
  bind : ∀ {α β : Type} {a : m α} {f : α → m β} {n k : Nat},
    P a n → (∀ x, P (f x) k) → P (a >>= f) (n + k)

namespace MonadGrade

variable {m : Type → Type} [Monad m] (𝓖 : MonadGrade m)

/-- The count, rewritten. -/
theorem of_eq {α : Type} {a : m α} {n k : Nat} (h : 𝓖.P a n) (e : n = k) : 𝓖.P a k := e ▸ h

/-- `map` keeps the count, in a lawful monad. -/
theorem map [LawfulMonad m] {α β : Type} {a : m α} {n : Nat} (h : 𝓖.P a n) (f : α → β) :
    𝓖.P (f <$> a) n := by
  rw [← bind_pure_comp]
  exact 𝓖.of_eq (𝓖.bind h fun x ↦ 𝓖.pure (f x)) (Nat.add_zero n)

/-- A branch on a condition counts its branch. -/
theorem ite {α : Type} (c : Prop) [Decidable c] {a b : m α} {n k : Nat} (ha : 𝓖.P a n)
    (hb : 𝓖.P b k) : 𝓖.P (if c then a else b) (if c then n else k) := by
  split
  · exact ha
  · exact hb

/-- A branch on a condition whose branches have one count has that count. -/
theorem ite_of {α : Type} (c : Prop) [Decidable c] {a b : m α} {n : Nat} (ha : 𝓖.P a n)
    (hb : 𝓖.P b n) : 𝓖.P (if c then a else b) n := by
  split
  · exact ha
  · exact hb

/-- A branch on a condition, each branch then the same continuation, as `do` notation joins
them: the branch's count, then the continuation's. -/
theorem ite_bind {α β : Type} (c : Prop) [Decidable c] {a b : m α} {j : α → m β} {n k l : Nat}
    (ha : 𝓖.P a n) (hb : 𝓖.P b k) (hj : ∀ x, 𝓖.P (j x) l) :
    𝓖.P (if c then a >>= j else b >>= j) ((if c then n else k) + l) := by
  split
  · exact 𝓖.bind ha hj
  · exact 𝓖.bind hb hj

end MonadGrade

end

end LeanerVM.Protocol
