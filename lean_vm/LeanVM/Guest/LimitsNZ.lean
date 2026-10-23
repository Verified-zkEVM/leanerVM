/-
  LeanVM.Guest.LimitsNZ

  `NoZeroChallenge` restricts the Spec's deferring verifier: a child's proof the verifier refusing
  a zero challenge accepts, the Spec's accepts.
-/

module

public import LeanVM.Guest.Limits

/-!
# The zero-challenge refusal is a restriction

`Refines P' P`: the program `P'` is `P` with failures inserted, step for step. Running a refining
program is running the program, where it does not fail (`run_refines`, `runProof_refines`). The
deferring program refusing a zero fold, tail or level batching challenge refines the deferring
program (`deferredProgramNZ_refines`), so `NoZeroChallenge` gives every child's acceptance by the
Spec's deferring verifier (`verifyDeferred_of_nz`): it only removes runs, those with a zero
challenge where the guest divides.
-/

namespace LeanVM.Guest.Limits

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-- **`P'` refines `P`**: it is `P` with failures inserted. -/
inductive Refines {α : Type} : Prog α → Prog α → Prop
  | fail (P : Prog α) : Refines .fail P
  | ret (a : α) : Refines (.ret a) (.ret a)
  | read {k k' : E → Prog α} : (∀ x, Refines (k' x) (k x)) → Refines (.read k') (.read k)
  | sample {k k' : E → Prog α} : (∀ x, Refines (k' x) (k x)) → Refines (.sample k') (.sample k)
  | grind {b : ℕ} {k k' : Prog α} : Refines k' k → Refines (.grind b k') (.grind b k)
  | commit {h w : ℕ} {k k' : Prog α} : Refines k' k → Refines (.commit h w k') (.commit h w k)
  | query {i : ℕ} {ps : List ℕ} {k k' : List (List K) → Prog α} :
      (∀ r, Refines (k' r) (k r)) → Refines (.query i ps k') (.query i ps k)

namespace Refines

variable {α β : Type}

theorem refl : ∀ P : Prog α, Refines P P
  | .ret a => .ret a
  | .fail => .fail _
  | .read k => .read fun x ↦ refl (k x)
  | .sample k => .sample fun x ↦ refl (k x)
  | .grind _ k => .grind (refl k)
  | .commit _ _ k => .commit (refl k)
  | .query _ _ k => .query fun r ↦ refl (k r)

theorem bind {P' P : Prog α} (h : Refines P' P) {f' f : α → Prog β}
    (hf : ∀ a, Refines (f' a) (f a)) : Refines (P'.bind f') (P.bind f) := by
  induction h with
  | fail P => exact .fail _
  | ret a => exact hf a
  | read _ ih => exact .read ih
  | sample _ ih => exact .sample ih
  | grind _ ih => exact .grind ih
  | commit _ ih => exact .commit ih
  | query _ ih => exact .query ih

/-- A `require` before a refining program refines the program. -/
theorem require_bind {c : Prop} [Decidable c] {k' k : Prog α} (h : Refines k' k) :
    Refines ((Prog.require c).bind fun _ ↦ k') k := by
  unfold Prog.require
  split
  · exact h
  · exact .fail _

end Refines

section Run

variable {H : Bytes → Id Digest} {F : KState → Id KState}

/-- **Running a refining program is running the program**, where it does not fail. -/
theorem run_refines {α : Type} {P' P : Prog α} (h : Refines P' P) :
    ∀ (s : St) (r : α × St), Id.run (Compile.run H F P' s) = some r →
      Id.run (Compile.run H F P s) = some r := by
  induction h with
  | fail P =>
    intro s r hr
    simp [Compile.run] at hr
  | ret a => intro s r hr; exact hr
  | read _ ih =>
    intro s r hr
    unfold Compile.run at hr ⊢
    cases hs : s.stream with
    | nil => simp [hs] at hr
    | cons x xs =>
      simp only [hs] at hr ⊢
      exact ih _ _ _ hr
  | sample _ ih =>
    intro s r hr
    unfold Compile.run at hr ⊢
    exact ih _ _ _ hr
  | grind _ ih =>
    intro s r hr
    unfold Compile.run at hr ⊢
    cases hs : s.stream with
    | nil => simp [hs] at hr
    | cons x xs =>
      simp only [hs, Id.run_bind] at hr ⊢
      split at hr
      · rename_i hp
        simp only [hp, ↓reduceIte]
        exact ih _ _ hr
      · simp at hr
  | commit _ ih =>
    intro s r hr
    unfold Compile.run at hr ⊢
    rcases hs : s.stream with _ | ⟨x0, _ | ⟨x1, xs⟩⟩
    · simp [hs] at hr
    · simp [hs] at hr
    · simp only [hs, Id.run_bind] at hr ⊢
      cases hd : digestOfScalars (x0, x1) with
      | none => simp [hd] at hr
      | some root =>
        simp only [hd] at hr ⊢
        exact ih _ _ hr
  | @query i ps k k' _ ih =>
    intro s r hr
    unfold Compile.run at hr ⊢
    cases hroot : s.roots[i]? with
    | none => simp [hroot] at hr
    | some t =>
      obtain ⟨root, height, width⟩ := t
      simp only [hroot, Id.run_bind] at hr ⊢
      cases ho : Id.run (openAll H root height width ps s.openings) with
      | none => simp [ho] at hr
      | some q =>
        obtain ⟨rows, rest⟩ := q
        simp only [ho] at hr ⊢
        exact ih _ _ _ hr

/-- **A refining program accepts only what the program accepts.** -/
theorem runProof_refines {P' P : Prog Bool} (h : Refines P' P) (seed : KState) (π : Proof)
    (hacc : Id.run (runProof H F P' seed π) = true) : Id.run (runProof H F P seed π) = true := by
  unfold runProof at hacc ⊢
  simp only [Id.run_bind] at hacc ⊢
  cases hr : Id.run (Compile.run H F P' ⟨⟨seed, []⟩, π.stream, π.openings, []⟩) with
  | none => rw [hr] at hacc; exact absurd hacc (by simp)
  | some r =>
    rw [run_refines (H := H) (F := F) h _ _ hr]
    rw [hr] at hacc
    exact hacc

end Run

/-! ## The deferring program refusing a zero challenge -/

theorem foldRoundsNZ_refines : ∀ (n : ℕ) (s : WhirState) (lf : List E),
    Refines (foldRoundsNZ n s lf) (foldRounds n s lf)
  | 0, s, lf => Refines.refl _
  | n + 1, s, lf => by
    unfold foldRoundsNZ foldRounds
    refine Refines.bind (Refines.refl _) fun c ↦ ?_
    refine Refines.require_bind ?_
    refine Refines.bind (Refines.refl _) fun quad ↦ ?_
    exact foldRoundsNZ_refines n _ _

theorem tailRoundsNZ_refines : ∀ (n : ℕ) (t : E) (quad : List E),
    Refines (tailRoundsNZ n t quad) (tailRounds n t quad)
  | 0, t, quad => Refines.refl _
  | n + 1, t, quad => by
    unfold tailRoundsNZ tailRounds
    refine Refines.bind (Refines.refl _) fun c ↦ ?_
    refine Refines.require_bind ?_
    split
    · exact Refines.refl _
    · refine Refines.bind (Refines.refl _) fun quad ↦ ?_
      exact Refines.bind (tailRoundsNZ_refines n _ _) fun p ↦ Refines.refl _

/-- The first program of a bind: the same, or a refining one. -/
local macro "refines_head" : tactic => `(tactic| first
  | with_reducible exact Refines.refl _
  | exact foldRoundsNZ_refines _ _ _
  | exact tailRoundsNZ_refines _ _ _)

/-- One step of a refinement proof between two programs written alike. -/
local macro "refines_step" : tactic => `(tactic| first
  | with_reducible exact Refines.refl _
  | apply Refines.require_bind
  | (refine Refines.bind ?h fun _ ↦ ?k; case h => refines_head)
  | split
  | dsimp only
  | exact Refines.refl _)

theorem whirLevelsNZ_refines (logN laneFolds : ℕ) (eb : List E → E) (levels : List Whir.Level) :
    ∀ (index : ℕ) (s : WhirState),
      Refines (whirLevelsNZ logN laneFolds eb index levels s)
        (whirLevels logN laneFolds eb index levels s) := by
  induction levels with
  | nil => intro index s; exact Refines.refl _
  | cons level rest ih =>
    intro index s
    unfold whirLevelsNZ whirLevels
    apply Refines.bind (foldRoundsNZ_refines _ _ _)
    intro p
    obtain ⟨s', lf⟩ := p
    dsimp only
    cases rest with
    | nil =>
      dsimp only
      repeat refines_step
    | cons next rest' =>
      dsimp only
      repeat (first | exact ih _ _ | refines_step)

theorem verifyWhirNZ_refines (logN logInvRate : ℕ) (target : E) (eb : List E → E) :
    Refines (verifyWhirNZ logN logInvRate target eb) (verifyWhir logN logInvRate target eb) := by
  unfold verifyWhirNZ verifyWhir
  repeat (first | exact whirLevelsNZ_refines _ _ _ _ _ _ | refines_step)

theorem verifyStackedOpeningNZ_refines (stackLog logInvRate : ℕ) (claims : List StackClaim) :
    Refines (verifyStackedOpeningNZ stackLog logInvRate claims)
      (verifyStackedOpening stackLog logInvRate claims) := by
  unfold verifyStackedOpeningNZ verifyStackedOpening
  repeat (first | exact verifyWhirNZ_refines _ _ _ _ | refines_step)

theorem deferredProgramNZ_refines (c : FixedClaims) (bytecode : List K) (publicInput : Digest) :
    Refines (deferredProgramNZ c bytecode publicInput) (deferredProgram c bytecode publicInput) := by
  unfold deferredProgramNZ deferredProgram
  refine Refines.bind ?_ fun _ ↦ Refines.refl _
  unfold verifyExecutionNZ verifyExecution
  repeat (first | exact verifyStackedOpeningNZ_refines _ _ _ | refines_step)

/-- **`NoZeroChallenge` only restricts**: the deferring verifier refusing a zero challenge
accepts only proofs the Spec's deferring verifier accepts. -/
theorem verifyDeferred_of_nz {bytecode : List K} {iv publicInput : Digest} {c : FixedClaims}
    {π : Proof} (h : verifyDeferredNZ bytecode iv publicInput c π = true) :
    verifyDeferred bytecode iv publicInput c π = true := by
  unfold verifyDeferredNZ at h
  unfold verifyDeferred verifyDeferredWith
  exact runProof_refines (deferredProgramNZ_refines c bytecode publicInput) _ π h

/-- Under `NoZeroChallenge`, every child's proof is accepted by the deferring verifier. -/
theorem children_verify_of_nz {bytecode : List K} {seed : Digest} {w : NodeWitness}
    (h : NoZeroChallenge bytecode seed w) :
    ∀ c ∈ w.children,
      verifyDeferred bytecode seed (statementDigest seed c.statement) c.fresh c.proof = true :=
  fun c hc ↦ verifyDeferred_of_nz (h c hc)

end
end LeanVM.Guest.Limits
