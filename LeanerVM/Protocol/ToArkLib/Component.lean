/-
  LeanerVM.Protocol.ToArkLib.Component

  A component of an interactive oracle proof as three pieces of data: its definition, its
  completeness proof, its knowledge-soundness proof; and their sequential composition.
  Candidate for ArkLib.
-/

module

public import ArkLib.OracleReduction.Composition.Sequential.Append.Basic
public import ArkLib.OracleReduction.Composition.Sequential.OracleCompleteness
public import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Guarded

/-!
# Components and their composition

A `Component.Def` packages an ArkLib oracle reduction (an honest prover and a verifier that may
query the input oracles and the prover's messages) together with its message schedule and a
closed-form error, one number per verifier challenge. `Component.Complete` is the proof that
the honest prover convinces the verifier with probability one, plus the two side facts ArkLib's
composition theorem needs: the verifier is a Boolean check followed by a pure verdict, and the
prover's final output makes no oracle query. `Component.Security` adds round-by-round
knowledge soundness in the worst case over transcript prefixes: a knowledge state function and
a round-by-round extractor exist, and each fresh challenge can turn the state from false to
true with probability at most the component's error at that challenge.

Two components in sequence are again a component (`Def.append`): schedules concatenate and
each challenge keeps the error its component assigned it. Completeness composes by a theorem
ArkLib proves. Knowledge soundness composes by a theorem ArkLib states but has not proved at
the pinned revision (its `append_rbrKnowledgeSoundness` is admitted; a proof for a guarded
first verifier exists in ArkLib pull request #615); `KnowledgeAppend` is that statement, taken
as an argument wherever knowledge soundness is composed.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

@[expose] public section

namespace Component

/-- A component: its schedule, its reduction, and its error per challenge. The two instances
say that every prover message can be queried and every challenge can be sampled. -/
structure Def (StmtIn : Type) {ιi : Type} (OStmtIn : ιi → Type) (WitIn : Type)
    (StmtOut : Type) {ιo : Type} (OStmtOut : ιo → Type) (WitOut : Type)
    [∀ i, OracleInterface (OStmtIn i)] [∀ i, OracleInterface (OStmtOut i)] where
  /-- Number of rounds. -/
  n : ℕ
  /-- The message schedule: who speaks in each round, and the type of what is sent. -/
  pSpec : ProtocolSpec n
  /-- Every prover message can be queried. -/
  [msgOracle : ∀ i, OracleInterface (pSpec.Message i)]
  /-- Every challenge can be sampled. -/
  [chalSample : ∀ i, SampleableType (pSpec.Challenge i)]
  /-- The honest prover and the verifier. -/
  red : OracleReduction []ₒ StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec
  /-- The knowledge error charged to each challenge. -/
  err : pSpec.ChallengeIdx → ℝ≥0

attribute [instance] Def.msgOracle Def.chalSample

variable {StmtIn : Type} {ιi : Type} {OStmtIn : ιi → Type} {WitIn : Type}
  {StmtOut : Type} {ιo : Type} {OStmtOut : ιo → Type} {WitOut : Type}
  [∀ i, OracleInterface (OStmtIn i)] [∀ i, OracleInterface (OStmtOut i)]

/-- The completeness half of a component: on every pair of the input relation, the honest run
lands in the output relation with probability one, from any state of the shared oracle. -/
structure Complete (D : Def StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut)) where
  /-- The prover's final output makes no oracle query. -/
  outputPure : D.red.prover.OutputIsPure
  /-- The verifier is a Boolean check followed by a pure verdict. -/
  guarded : D.red.toReduction.verifier.GuardedForm
  /-- Perfect completeness. -/
  complete : ∀ {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)),
    D.red.perfectCompleteness init impl relIn relOut

/-- The security half of a component: completeness, and worst-case round-by-round knowledge
soundness at the component's own error. -/
structure Security (D : Def StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    extends Complete D relIn relOut where
  /-- Round-by-round knowledge soundness at `D.err`. -/
  rbr : ∀ {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)),
    D.red.verifier.toVerifier.rbrKnowledgeSoundnessWorstCase init impl relIn relOut D.err

end Component

/-- Round-by-round knowledge soundness composes across `Verifier.append` when the first
verifier is a check followed by a pure verdict, each challenge keeping its own error. ArkLib
states this and admits it at the pinned revision; every composed knowledge theorem below takes
it as an argument. -/
structure KnowledgeAppend where
  /-- The statement. -/
  append : ∀ {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Stmt₂ Stmt₃ Wit₁ Wit₂ Wit₃ : Type}
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (_guarded : V₁.GuardedForm)
    {ε₁ : pSpec₁.ChallengeIdx → ℝ≥0} {ε₂ : pSpec₂.ChallengeIdx → ℝ≥0},
    V₁.rbrKnowledgeSoundnessWorstCase init impl rel₁ rel₂ ε₁ →
    V₂.rbrKnowledgeSoundnessWorstCase init impl rel₂ rel₃ ε₂ →
    (V₁.append V₂).rbrKnowledgeSoundnessWorstCase init impl rel₁ rel₃
      (Sum.elim ε₁ ε₂ ∘ ChallengeIdx.sumEquiv.symm)

namespace Component

variable {Stmt₁ Stmt₂ Stmt₃ Wit₁ Wit₂ Wit₃ : Type}
  {ι₁ ι₂ ι₃ : Type} {OStmt₁ : ι₁ → Type} {OStmt₂ : ι₂ → Type} {OStmt₃ : ι₃ → Type}
  [∀ i, OracleInterface (OStmt₁ i)] [∀ i, OracleInterface (OStmt₂ i)]
  [∀ i, OracleInterface (OStmt₃ i)]

/-- Two components in sequence: schedules concatenate, each challenge keeps its error. -/
def Def.append (D₁ : Def Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂)
    (D₂ : Def Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃) : Def Stmt₁ OStmt₁ Wit₁ Stmt₃ OStmt₃ Wit₃ where
  n := D₁.n + D₂.n
  pSpec := D₁.pSpec ++ₚ D₂.pSpec
  red := D₁.red.append D₂.red
  err := Sum.elim D₁.err D₂.err ∘ ChallengeIdx.sumEquiv.symm

variable {D₁ : Def Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂}
  {D₂ : Def Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃}
  {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)} {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
  {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}

/-- The guarded form of an appended verifier, from those of its parts. -/
def guardedAppend (G₁ : D₁.red.toReduction.verifier.GuardedForm)
    (G₂ : D₂.red.toReduction.verifier.GuardedForm) :
    (D₁.append D₂).red.toReduction.verifier.GuardedForm :=
  cast (congrArg Verifier.GuardedForm
    (OracleVerifier.append_toVerifier D₁.red.verifier D₂.red.verifier).symm) (G₁.append G₂)

/-- Completeness composes (ArkLib's `append_perfectCompleteness_of_guarded_verifiers`). -/
def Complete.append (C₁ : Complete D₁ rel₁ rel₂) (C₂ : Complete D₂ rel₂ rel₃) :
    Complete (D₁.append D₂) rel₁ rel₃ where
  outputPure := Prover.OutputIsPure.append _ _ C₁.outputPure C₂.outputPure
  guarded := guardedAppend C₁.guarded C₂.guarded
  complete := fun init impl ↦
    OracleReduction.append_perfectCompleteness_of_guarded_verifiers D₁.red D₂.red
      C₁.guarded C₂.guarded (fun _ ↦ Or.inl C₁.outputPure)
      (C₁.complete init impl) (fun s ↦ C₂.complete (pure s) impl)

/-- Security composes, given `KnowledgeAppend`. -/
def Security.append (A : KnowledgeAppend) (S₁ : Security D₁ rel₁ rel₂)
    (S₂ : Security D₂ rel₂ rel₃) : Security (D₁.append D₂) rel₁ rel₃ where
  toComplete := S₁.toComplete.append S₂.toComplete
  rbr := fun init impl ↦ by
    have h := A.append init impl D₁.red.verifier.toVerifier D₂.red.verifier.toVerifier
      S₁.guarded (S₁.rbr init impl) (S₂.rbr init impl)
    change (D₁.red.verifier.append D₂.red.verifier).toVerifier.rbrKnowledgeSoundnessWorstCase
      init impl rel₁ rel₃ _
    rw [OracleVerifier.append_toVerifier]
    exact h

end Component

end
end LeanerVM.Protocol
