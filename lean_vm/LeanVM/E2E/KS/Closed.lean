/-
  LeanVM.E2E.KS.Closed

  The deployed verifier queries only through its hash: the relational and closed-predicate forms
  for `verifyAggregateWith`, as `Natural.lean` and `Engine.lean` give them for V_I.
-/

module

public import LeanVM.E2E.KS.Game
public import LeanVM.E2E.Rel

/-!
# The deployed verifier queries only through its hash

* `rel_verifyAggregateWith`: a relation between two monads' computations, closed under `pure` and
  `bind` and relating the two hashes' queries, relates the deployed verifier's two runs.
* `closed_verifyAggregateWith`: a predicate closed under `pure` and `bind` and holding of every hash
  query holds of the deployed verifier's run.
-/

namespace LeanVM.E2E.KS

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom
open LeanVM.E2E

@[expose] public section

section Rel
variable {m n : Type → Type} [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
  (R : ∀ {α : Type}, m α → n α → Prop)
  (hpure : ∀ {α : Type} (a : α), R (pure a) (pure a))
  (hbind : ∀ {α β : Type} (x : m α) (y : n α) (f : α → m β) (g : α → n β), R x y →
    (∀ a, R (f a) (g a)) → R (x >>= f) (y >>= g))
  (H : Bytes → m Digest) (H' : Bytes → n Digest) (hH : ∀ x, R (H x) (H' x))
include hpure hbind hH

/-- **The deployed verifier with related hashes is related.** -/
theorem rel_verifyAggregateWith (guest : Program) (s : NodeStatement) (π : Proof) :
    R (verifyAggregateWith H guest s π) (verifyAggregateWith H' guest s π) := by
  have hHD : ∀ x, R (Da.daHash H x) (Da.daHash H' x) := fun x ↦
    rel_map R hpure hbind _ _ _ (hH x)
  unfold verifyAggregateWith
  refine hbind _ _ _ _ (rel_fiatShamirIvWith R hbind H H' hH _) fun _ ↦ ?_
  refine hbind _ _ _ _ (rel_statementDigestWith R hbind H H' hH _ _) fun _ ↦ ?_
  refine hbind _ _ _ _ ?_ fun _ ↦ ?_
  · unfold verifyWith seedWith
    exact hbind _ _ _ _ (hbind _ _ _ _ (hH _) fun _ ↦ hbind _ _ _ _ (hH _) fun _ ↦ hH _)
      fun _ ↦ rel_runProof R hpure hbind H H' hH _ _ _
  refine hbind _ _ _ _ (rel_allM R hpure hbind _ _ (fun c ↦ ?_) _) fun _ ↦ hpure _
  refine hbind _ _ _ _ ?_ fun _ ↦ hpure _
  unfold Da.vectorDigestOfWith Da.membershipVectorWith Da.membershipChallengesWith
  exact hbind _ _ _ _ (rel_map R hpure hbind _ _ _ (hbind _ _ _ _ (hHD _) fun _ ↦
    hbind _ _ _ _ (hHD _) fun _ ↦ hbind _ _ _ _ (hHD _) fun _ ↦
      rel_squeezesWith R hpure hbind _ _ hHD _ _)) fun _ ↦ hHD _

end Rel

section Closed
variable {m : Type → Type} [Monad m] [LawfulMonad m] (G : ∀ {α : Type}, m α → Prop)
  (hpure : ∀ {α : Type} (a : α), G (pure a))
  (hbind : ∀ {α β : Type} (x : m α) (f : α → m β), G x → (∀ a, G (f a)) → G (x >>= f))
  (H : Bytes → m Digest) (hH : ∀ x, G (H x))
include hpure hbind hH

/-- **The deployed verifier queries only through its hash.** -/
theorem closed_verifyAggregateWith (guest : Program) (s : NodeStatement) (π : Proof) :
    G (verifyAggregateWith H guest s π) := by
  have hHD : ∀ x, G (Da.daHash H x) := fun x ↦ closed_map G hpure hbind _ _ (hH x)
  unfold verifyAggregateWith fiatShamirIvWith statementDigestWith signersDigestWith
    daListDigestWith
  refine hbind _ _ (hbind _ _ (hH _) fun _ ↦ hH _) fun _ ↦ ?_
  refine hbind _ _ ?_ fun _ ↦ ?_
  · repeat' first
      | exact hpure _
      | exact hH _
      | (refine hbind _ _ ?_ fun _ ↦ ?_)
  refine hbind _ _ ?_ fun _ ↦ ?_
  · unfold verifyWith seedWith
    exact hbind _ _ (hbind _ _ (hH _) fun _ ↦ hbind _ _ (hH _) fun _ ↦ hH _)
      fun _ ↦ closed_runProof G hpure hbind H hH _ _ _
  refine hbind _ _ (closed_allM G hpure hbind _ (fun c ↦ ?_) _) fun _ ↦ hpure _
  refine hbind _ _ ?_ fun _ ↦ hpure _
  unfold Da.vectorDigestOfWith Da.membershipVectorWith Da.membershipChallengesWith
  exact hbind _ _ (closed_map G hpure hbind _ _ (hbind _ _ (hHD _) fun _ ↦ hbind _ _ (hHD _)
    fun _ ↦ hbind _ _ (hHD _) fun _ ↦ closed_squeezesWith G hpure hbind _ hHD _ _))
    fun _ ↦ hHD _

end Closed

end
end LeanVM.E2E.KS
