/-
  LeanerVM.Protocol.ToArkLib.Component

  A component of an interactive oracle proof as three pieces of data: its definition, its
  completeness proof, its extractor with its knowledge-soundness proof; and their sequential
  composition.
  Candidate for ArkLib.
-/

module

public import ArkLib.OracleReduction.Composition.Sequential.Append.Basic
public import ArkLib.OracleReduction.Composition.Sequential.Append.StateFunction
public import ArkLib.OracleReduction.Composition.Sequential.OracleCompleteness
public import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Guarded
public import LeanerVM.Protocol.ToArkLib.KnowledgeAppend

/-!
# Components and their composition

A `Component.Def` packages an ArkLib oracle reduction (an honest prover and a verifier that may
query the input oracles and the prover's messages) together with its message schedule and a
closed-form error, one number per verifier challenge. `Component.Complete` is the proof that
the honest prover convinces the verifier with probability one, plus the two side facts ArkLib's
composition theorem needs: the verifier is a Boolean check followed by a pure verdict, and the
prover's final output makes no oracle query. `Component.Security` adds round-by-round
knowledge soundness in the worst case over transcript prefixes, for a named extractor: it
carries a round-by-round extractor and its knowledge state function, with the proof that each
fresh challenge can turn the state from false to true with probability at most the component's
error at that challenge.

Two components in sequence are again a component (`Def.append`): schedules concatenate and
each challenge keeps the error its component assigned it. Completeness composes by a theorem
ArkLib proves. Extractors compose by ArkLib's `Extractor.RoundByRound.append`, through the
first verifier's verdict. Their knowledge state functions and the knowledge-soundness bound
compose by the construction and the theorem of `LeanerVM.Protocol.ToArkLib.KnowledgeAppend`,
ported from ArkLib pull request #615 (ArkLib's own `append_rbrKnowledgeSoundness` is admitted
at the pinned revision), so knowledge soundness composes with no assumption.
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

/-- The security half of a component: completeness, a round-by-round extractor with its
knowledge state function, and worst-case round-by-round knowledge soundness for them at the
component's own error. -/
structure Security (D : Def StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    extends Complete D relIn relOut where
  /-- The extractor's intermediate witness type after each round. -/
  witMid : Fin (D.n + 1) → Type
  /-- The round-by-round extractor. The shared oracle is written `OracleSpec.emptySpec.{0, 0}`
  rather than `[]ₒ` to pin a universe `Extractor.RoundByRound` leaves free. -/
  extractor : Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0}) (StmtIn × ∀ i, OStmtIn i)
    WitIn WitOut D.pSpec witMid
  /-- The extractor's knowledge state function, from any state of the shared oracle. -/
  kSF : ∀ {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)),
    D.red.verifier.toVerifier.KnowledgeStateFunction init impl relIn relOut extractor
  /-- Round-by-round knowledge soundness at `D.err`, for this extractor and state function. -/
  rbr : ∀ {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)),
    D.red.verifier.toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut witMid
      extractor (kSF init impl) D.err

/-- A knowledge state function of `V` is one of any verifier equal to `V`, with the same
state. -/
def stateFunctionOfEq {ι : Type} {oSpec : OracleSpec ι} {S T WitIn WitOut : Type} {n : ℕ}
    {pSpec : ProtocolSpec n} {W : Fin (n + 1) → Type}
    {E : Extractor.RoundByRound oSpec S WitIn WitOut pSpec W} {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)} {relIn : Set (S × WitIn)}
    {relOut : Set (T × WitOut)} {V V' : Verifier oSpec S T pSpec} (h : V' = V)
    (K : V.KnowledgeStateFunction init impl relIn relOut E) :
    V'.KnowledgeStateFunction init impl relIn relOut E where
  toFun := K.toFun
  toFun_empty := K.toFun_empty
  toFun_next := K.toFun_next
  toFun_full := by subst h; exact K.toFun_full

/-- Knowledge soundness for a state function carries over to the same state function of an
equal verifier. -/
theorem rbrKnowledgeSoundnessWorstCaseWith_of_eq {ι : Type} {oSpec : OracleSpec ι}
    {S T WitIn WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)] {W : Fin (n + 1) → Type}
    {E : Extractor.RoundByRound oSpec S WitIn WitOut pSpec W} {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)} {relIn : Set (S × WitIn)}
    {relOut : Set (T × WitOut)} {V V' : Verifier oSpec S T pSpec} (h : V' = V)
    {K : V.KnowledgeStateFunction init impl relIn relOut E} {ε : pSpec.ChallengeIdx → ℝ≥0}
    (hK : V.rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut W E K ε) :
    V'.rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut W E (stateFunctionOfEq h K)
      ε := by
  subst h
  exact hK

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
  cast (congrArg _ (OracleVerifier.append_toVerifier _ _).symm) (G₁.append G₂)

/-- Completeness composes (ArkLib's `append_perfectCompleteness_of_guarded_verifiers`). -/
def Complete.append (C₁ : Complete D₁ rel₁ rel₂) (C₂ : Complete D₂ rel₂ rel₃) :
    Complete (D₁.append D₂) rel₁ rel₃ where
  outputPure := Prover.OutputIsPure.append _ _ C₁.outputPure C₂.outputPure
  guarded := guardedAppend C₁.guarded C₂.guarded
  complete := fun init impl ↦
    OracleReduction.append_perfectCompleteness_of_guarded_verifiers D₁.red D₂.red
      C₁.guarded C₂.guarded (fun _ ↦ Or.inl C₁.outputPure)
      (C₁.complete init impl) (fun s ↦ C₂.complete (pure s) impl)

/-- Security composes: the extractors are appended through the first verdict, their state
functions by `Verifier.KnowledgeStateFunction.appendGuarded`, and the bound is
`Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first`. -/
def Security.append (S₁ : Security D₁ rel₁ rel₂) (S₂ : Security D₂ rel₂ rel₃) :
    Security (D₁.append D₂) rel₁ rel₃ where
  toComplete := S₁.toComplete.append S₂.toComplete
  witMid := _
  extractor := S₁.extractor.append S₂.extractor S₁.guarded.out
  kSF := fun init impl ↦ stateFunctionOfEq (OracleVerifier.append_toVerifier _ _)
    (Verifier.KnowledgeStateFunction.appendGuarded S₁.guarded (S₁.kSF init impl)
      (S₂.kSF init impl))
  rbr := fun init impl ↦ rbrKnowledgeSoundnessWorstCaseWith_of_eq _
    (Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first S₁.guarded
      (S₁.kSF init impl) (S₂.kSF init impl) (S₁.rbr init impl) (S₂.rbr init impl))

end Component

end
end LeanerVM.Protocol
