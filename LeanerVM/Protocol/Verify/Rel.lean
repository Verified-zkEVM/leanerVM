/-
  LeanerVM.Protocol.Verify.Rel

  The chain walk of the executable verifier on two records of its primitives, related by a
  relation that `pure` and `bind` preserve: its two runs are related.
-/

module

public import LeanerVM.Protocol.Verify
public import LeanerVM.Protocol.ToVCVio.MonadRel

/-!
# The chain walk along a relation of its primitives

The chain walk (`walkChain`) is written once over four primitives of `ChainOps`: read a scalar,
squeeze a challenge, read a root, check a nonce; it opens no commitment. For a relation
`𝓡 : MonadRel n₁ n₂` and two records whose four chain primitives are pairwise related
(`ChainOps.Related`), the two runs of every walk are related (`walkChain_rel`), by induction on the
walk: every walk is built from the primitives by `pure` and `bind`. The openings are not part of
the relation. `LeanerVM.Protocol.Verify.Hom` is the same argument for a monad morphism.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash LeanIsa

@[expose] public section

namespace Verify

variable {n₁ n₂ : Type → Type} [Monad n₁] [Monad n₂]

/-- Two records of the walk's primitives whose four chain primitives are pairwise related by `𝓡`;
the openings are left out. -/
structure ChainOps.Related (𝓡 : MonadRel n₁ n₂) (ops₁ : ChainOps n₁) (ops₂ : ChainOps n₂) :
    Prop where
  /-- Reading a scalar. -/
  nextScalar : 𝓡.R ops₁.nextScalar ops₂.nextScalar
  /-- Squeezing a challenge. -/
  sample : 𝓡.R ops₁.sample ops₂.sample
  /-- Reading a root. -/
  nextRoot : 𝓡.R ops₁.nextRoot ops₂.nextRoot
  /-- Checking a nonce. -/
  checkPow : ∀ bits, 𝓡.R (ops₁.checkPow bits) (ops₂.checkPow bits)

variable {𝓡 : MonadRel n₁ n₂} {ops₁ : ChainOps n₁} {ops₂ : ChainOps n₂}
  (h : ChainOps.Related 𝓡 ops₁ ops₂)

private theorem rel_ite_bind {α β : Type} (c : Prop) [Decidable c] {a₁ b₁ : n₁ α}
    {a₂ b₂ : n₂ α} {j₁ : α → n₁ β} {j₂ : α → n₂ β} (ha : 𝓡.R a₁ a₂) (hb : 𝓡.R b₁ b₂)
    (hj : ∀ x, 𝓡.R (j₁ x) (j₂ x)) :
    𝓡.R (if c then a₁ >>= j₁ else b₁ >>= j₁) (if c then a₂ >>= j₂ else b₂ >>= j₂) := by
  split
  · exact 𝓡.bind ha hj
  · exact 𝓡.bind hb hj

include h

theorem nextScalars_rel : ∀ k, 𝓡.R (ops₁.nextScalars k) (ops₂.nextScalars k)
  | 0 => 𝓡.pure _
  | k + 1 => 𝓡.bind h.nextScalar fun _ ↦ 𝓡.bind (nextScalars_rel k) fun _ ↦ 𝓡.pure _

theorem samples_rel : ∀ k, 𝓡.R (samples ops₁ k) (samples ops₂ k)
  | 0 => 𝓡.pure _
  | k + 1 => 𝓡.bind h.sample fun _ ↦ 𝓡.bind (samples_rel k) fun _ ↦ 𝓡.pure _

theorem readRound_rel (d : ℕ) : 𝓡.R (readRound ops₁ d) (readRound ops₂ d) :=
  𝓡.bind (nextScalars_rel h d) fun _ ↦ 𝓡.bind h.sample fun _ ↦ 𝓡.pure _

theorem readRounds_rel (d : ℕ) : ∀ k, 𝓡.R (readRounds ops₁ d k) (readRounds ops₂ d k)
  | 0 => 𝓡.pure _
  | k + 1 => 𝓡.bind (readRound_rel h d) fun _ ↦ 𝓡.bind (readRounds_rel d k) fun _ ↦ 𝓡.pure _

theorem walkSetup_rel : 𝓡.R (walkSetup ops₁) (walkSetup ops₂) :=
  𝓡.bind (nextScalars_rel h 8) fun _ ↦ h.nextRoot

theorem walkLayer_rel (ρ j : ℕ) : 𝓡.R (walkLayer ops₁ ρ j) (walkLayer ops₂ ρ j) :=
  𝓡.bind (readRounds_rel h _ _) fun _ ↦ 𝓡.bind (nextScalars_rel h _) fun _ ↦
    𝓡.bind (nextScalars_rel h _) fun _ ↦ 𝓡.bind (nextScalars_rel h _) fun _ ↦
    𝓡.bind (samples_rel h _) fun _ ↦ 𝓡.bind h.sample fun _ ↦ 𝓡.pure _

theorem walkLayers_rel : ∀ (ρs : List ℕ) (j : ℕ), 𝓡.R (walkLayers ops₁ ρs j) (walkLayers ops₂ ρs j)
  | [], _ => 𝓡.pure _
  | ρ :: rest, j => 𝓡.bind (walkLayer_rel h ρ j) fun _ ↦
      𝓡.bind (walkLayers_rel rest (j + ρ)) fun _ ↦ 𝓡.pure _

theorem walkBus_rel (μBus nValues : ℕ) :
    𝓡.R (walkBus ops₁ μBus nValues) (walkBus ops₂ μBus nValues) :=
  𝓡.bind (samples_rel h 4) fun _ ↦ 𝓡.bind h.sample fun _ ↦ 𝓡.bind h.nextScalar fun _ ↦
    𝓡.bind h.nextScalar fun _ ↦ 𝓡.bind h.sample fun _ ↦ 𝓡.bind (walkLayers_rel h _ _) fun _ ↦
    𝓡.bind (nextScalars_rel h _) fun _ ↦ 𝓡.pure _

theorem walkTables_rel (τmax nCols : ℕ) :
    𝓡.R (walkTables ops₁ τmax nCols) (walkTables ops₂ τmax nCols) :=
  𝓡.bind h.sample fun _ ↦ 𝓡.bind (readRounds_rel h _ _) fun _ ↦
    𝓡.bind (nextScalars_rel h _) fun _ ↦ 𝓡.pure _

theorem walkPub_rel (nSent : ℕ) : 𝓡.R (walkPub ops₁ nSent) (walkPub ops₂ nSent) :=
  𝓡.bind h.sample fun _ ↦ 𝓡.bind (nextScalars_rel h _) fun _ ↦ 𝓡.pure _

theorem walkFlock_rel (k : ℕ) : 𝓡.R (walkFlock ops₁ k) (walkFlock ops₂ k) :=
  𝓡.bind (samples_rel h _) fun _ ↦ 𝓡.bind (nextScalars_rel h _) fun _ ↦
    𝓡.bind h.sample fun _ ↦ 𝓡.bind (readRounds_rel h _ _) fun _ ↦
    𝓡.bind (nextScalars_rel h _) fun _ ↦ 𝓡.bind h.sample fun _ ↦
    𝓡.bind (readRounds_rel h _ _) fun _ ↦ 𝓡.bind (nextScalars_rel h _) fun _ ↦
    𝓡.bind (samples_rel h _) fun _ ↦ 𝓡.pure _

theorem walkFolds_rel : ∀ k, 𝓡.R (walkFolds ops₁ k) (walkFolds ops₂ k)
  | 0 => 𝓡.pure _
  | k + 1 => 𝓡.bind h.sample fun _ ↦ 𝓡.bind (nextScalars_rel h 2) fun _ ↦
      𝓡.bind (walkFolds_rel k) fun _ ↦ 𝓡.pure _

theorem walkTail_rel : ∀ k, 𝓡.R (walkTail ops₁ k) (walkTail ops₂ k)
  | 0 => 𝓡.pure _
  | k + 1 => 𝓡.bind h.sample fun _ ↦ rel_ite_bind _ (𝓡.pure _) (nextScalars_rel h 2)
      fun _ ↦ 𝓡.bind (walkTail_rel k) fun _ ↦ 𝓡.pure _

theorem walkPositions_rel (depth : ℕ) :
    ∀ fuel need, 𝓡.R (walkPositions ops₁ depth fuel need) (walkPositions ops₂ depth fuel need)
  | 0, _ => 𝓡.pure _
  | _ + 1, 0 => 𝓡.pure _
  | fuel + 1, _ + 1 => 𝓡.bind h.sample fun _ ↦
      𝓡.bind (walkPositions_rel depth fuel _) fun _ ↦ 𝓡.pure _

theorem walkLevel_rel [LawfulMonad n₁] [LawfulMonad n₂] (sh : LevelShape) :
    𝓡.R (walkLevel ops₁ sh) (walkLevel ops₂ sh) :=
  𝓡.bind (walkFolds_rel h _) fun _ ↦
  rel_ite_bind _ (nextScalars_rel h _) (𝓡.pure _) fun _ ↦
  rel_ite_bind _ (𝓡.pure _) (𝓡.map h.nextRoot _) fun _ ↦
  rel_ite_bind _ (𝓡.pure _) (samples_rel h _) fun _ ↦
  rel_ite_bind _ (𝓡.pure _) h.nextScalar fun _ ↦
  rel_ite_bind _ (𝓡.pure _) (nextScalars_rel h _) fun _ ↦
  𝓡.bind (h.checkPow _) fun _ ↦ 𝓡.bind (walkPositions_rel h _ _ _) fun _ ↦
  𝓡.bind h.sample fun _ ↦ 𝓡.bind (nextScalars_rel h _) fun _ ↦
  rel_ite_bind _ (walkTail_rel h _) (𝓡.pure _) fun _ ↦ 𝓡.pure _

theorem walkLevels_rel [LawfulMonad n₁] [LawfulMonad n₂] :
    ∀ shs, 𝓡.R (walkLevels ops₁ shs) (walkLevels ops₂ shs)
  | [] => 𝓡.pure _
  | sh :: shs => 𝓡.bind (walkLevel_rel h sh) fun _ ↦
      𝓡.bind (walkLevels_rel shs) fun _ ↦ 𝓡.pure _

theorem walkWhir_rel [LawfulMonad n₁] [LawfulMonad n₂] (shs : List LevelShape) :
    𝓡.R (walkWhir ops₁ shs) (walkWhir ops₂ shs) :=
  𝓡.bind (nextScalars_rel h 2) fun _ ↦ 𝓡.bind (walkLevels_rel h shs) fun _ ↦ 𝓡.pure _

/-- **The chain walk along a relation of its primitives**: on two records whose chain primitives
are pairwise related, the two chain walks are related. -/
theorem walkChain_rel [LawfulMonad n₁] [LawfulMonad n₂] (prog : Program) (s : Sizes)
    (input : PublicInput) (shs : List LevelShape) :
    𝓡.R (walkChain ops₁ prog s input shs) (walkChain ops₂ prog s input shs) :=
  𝓡.bind (walkSetup_rel h) fun _ ↦ 𝓡.bind (walkBus_rel h _ _) fun _ ↦
  𝓡.bind (walkTables_rel h _ _) fun _ ↦ 𝓡.bind (walkPub_rel h _) fun _ ↦
  𝓡.bind (walkFlock_rel h _) fun _ ↦ 𝓡.bind h.sample fun _ ↦
  𝓡.bind (walkWhir_rel h shs) fun ⟨_, _⟩ ↦ 𝓡.pure _

end Verify

end

end LeanerVM.Protocol
