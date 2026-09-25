/-
  LeanerVM.Protocol.Spine.Phase

  The hole interfaces: what a phase or a generic component of the proof system is, as data
  (`Def`), and what its two proofs are (`Complete`, `Security`); their sequential composition;
  and the one ArkLib theorem the composition of knowledge soundness waits on (`KnowledgeAppend`).
-/

module

public import ArkLib.OracleReduction.Composition.Sequential.Append.Basic
public import ArkLib.OracleReduction.Composition.Sequential.OracleCompleteness
public import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Guarded
public import LeanerVM.Protocol.Spine.Seams

/-!
# Holes: `Def`, `Complete`, `Security`, and their composition

Protocol roadmap, section *The spine*, convention *Holes*. Every unit of work of the proof
system is a `Component`: an ArkLib oracle reduction with its message schedule and its closed-form
per-challenge error (`Component.Def`), the proofs that the honest prover convinces the verifier
(`Component.Complete`), and the proof that a convinced verifier means the input relation held
(`Component.Security`). A phase of the leanVM protocol is a component over the one committed
oracle (`Phase.Def`); a generic component (a sumcheck, a grand product, a batching step) is a
`Component.Def` over whatever statements it reduces.

## ArkLib's objects, introduced

* A `ProtocolSpec n` is the schedule of `n` rounds: for each, who speaks (`P_to_V` or `V_to_P`)
  and the type of what is sent. Prover messages are `Message`s, verifier messages `Challenge`s;
  `ChallengeIdx` indexes the latter, and an error bound is a function of it, one number per
  challenge.
* An `OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec` is a prover and
  an oracle verifier. The verifier sees the statement, the challenges, and *oracle access* to the
  oracle statements `OStmtIn` and to the prover's messages; it outputs a statement and exposes
  output oracles chosen among its inputs. `oSpec` is a shared oracle (a random oracle, say); the
  spine uses none (`[]ₒ`).
* `perfectCompleteness init impl relIn relOut`: on every `(statement, witness)` in `relIn`, the
  honest execution ends in `relOut` with probability one. `init` and `impl` implement the shared
  oracle from a state drawn from `init`; with no shared oracle they are inert, and every
  statement here quantifies over them.
* `rbrKnowledgeSoundnessWorstCase init impl relIn relOut err` (round-by-round knowledge
  soundness, worst case over transcript prefixes): there is a *knowledge state function*, a
  predicate on partial transcripts and intermediate witnesses, true at the start exactly when the
  input relation holds, that a prover message cannot make true, that a fresh challenge makes true
  with probability at most `err i`, and that the verifier's acceptance into `relOut` implies at
  the end, together with a round-by-round *extractor* that computes the earlier witness from the
  later one. The interactive knowledge error is the sum of `err` (ArkLib ledger A3 for the
  implication to plain knowledge soundness).
* `Verifier.GuardedForm`: a verifier that is a Boolean check followed by a pure verdict, as
  data. Every leanVM phase verifier is one, and ArkLib's composition theorems ask for it.
* `Prover.OutputIsPure`: the prover's final output makes no oracle query. Trivially true here.
* `OracleReduction.append`: run one reduction, then the next from its output; the schedules
  concatenate (`++ₚ`), the errors are placed side by side
  (`Sum.elim … ∘ ChallengeIdx.sumEquiv.symm`).

## What ArkLib proves and what it owes

Perfect completeness composes: `append_perfectCompleteness_of_guarded_verifiers` is proved at
the pin and is used below. Round-by-round knowledge soundness of an append is admitted at the
pin (`Append/Security.lean`, ledger A2, ArkLib #676) and is proved with a guarded first verifier
in ArkLib #615. `KnowledgeAppend` states exactly that theorem, in #615's shape, so that hole C1
is one term: a local proof under `Protocol/Generic/`, or the pin bump. Every knowledge theorem
of the spine takes a `KnowledgeAppend` as its first argument; none depends on the admitted
theorem (the kernel audit rejects `sorryAx`).

Category A. Target: T4, through `Compose.lean`'s master theorems.

## Wrong readings excluded

* `Complete` is not implied by `Security`, and `Security` extends `Complete`: a `Def` lands
  with its `Complete`; its `Security` may land later, as its own pull request.
* The errors compose by placement, not by addition: `Def.append` keeps one number per challenge.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

@[expose] public section

namespace Component

/-- The definition half of a component: its schedule, its reduction, and its per-challenge
error. The instances on the schedule (an oracle interface on every prover message, a sampler on
every challenge) travel with it. -/
structure Def (StmtIn : Type) {ιi : Type} (OStmtIn : ιi → Type) (WitIn : Type)
    (StmtOut : Type) {ιo : Type} (OStmtOut : ιo → Type) (WitOut : Type)
    [∀ i, OracleInterface (OStmtIn i)] [∀ i, OracleInterface (OStmtOut i)] where
  /-- Number of rounds. -/
  n : ℕ
  /-- The message schedule. -/
  pSpec : ProtocolSpec n
  /-- Every prover message can be queried. -/
  [msgOracle : ∀ i, OracleInterface (pSpec.Message i)]
  /-- Every challenge can be sampled. -/
  [chalSample : ∀ i, SampleableType (pSpec.Challenge i)]
  /-- The reduction: honest prover and verifier. -/
  red : OracleReduction []ₒ StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec
  /-- The closed-form knowledge error charged to each challenge. -/
  err : pSpec.ChallengeIdx → ℝ≥0

attribute [instance] Def.msgOracle Def.chalSample

variable {StmtIn : Type} {ιi : Type} {OStmtIn : ιi → Type} {WitIn : Type}
  {StmtOut : Type} {ιo : Type} {OStmtOut : ιo → Type} {WitOut : Type}
  [∀ i, OracleInterface (OStmtIn i)] [∀ i, OracleInterface (OStmtOut i)]

/-- The completeness half: the verifier is guarded, the prover's output is pure (both are what
ArkLib's composition theorem asks for), and the honest execution lands in the output relation
from any shared-oracle state. -/
structure Complete (D : Def StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut)) where
  /-- The prover's final output makes no oracle query. -/
  outputPure : D.red.prover.OutputIsPure
  /-- The verifier is a check followed by a pure verdict. -/
  guarded : D.red.toReduction.verifier.GuardedForm
  /-- Perfect completeness, from every shared-oracle state. -/
  complete : ∀ {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)),
    D.red.perfectCompleteness init impl relIn relOut

/-- The security half: completeness, and round-by-round knowledge soundness at the
component's own error. -/
structure Security (D : Def StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    extends Complete D relIn relOut where
  /-- Worst-case round-by-round knowledge soundness at `D.err`. -/
  rbr : ∀ {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)),
    D.red.verifier.toVerifier.rbrKnowledgeSoundnessWorstCase init impl relIn relOut D.err

end Component

/-! ## The composition theorem ArkLib owes -/

/-- What ledger A2 owes (ArkLib #676, proved in ArkLib #615 as
`append_rbrKnowledgeSoundnessWorstCase_of_guarded_first`): worst-case round-by-round knowledge
soundness composes across `Verifier.append` when the first verifier is guarded, the errors placed
side by side. Hole C1 is one term of this type; until it exists, every knowledge theorem of the
spine takes one as an argument. -/
structure KnowledgeAppend where
  /-- The theorem. -/
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

/-! ## Sequential composition of components -/

namespace Component

variable {Stmt₁ Stmt₂ Stmt₃ Wit₁ Wit₂ Wit₃ : Type}
  {ι₁ ι₂ ι₃ : Type} {OStmt₁ : ι₁ → Type} {OStmt₂ : ι₂ → Type} {OStmt₃ : ι₃ → Type}
  [∀ i, OracleInterface (OStmt₁ i)] [∀ i, OracleInterface (OStmt₂ i)]
  [∀ i, OracleInterface (OStmt₃ i)]

/-- Run one component, then the next from its output: schedules concatenate, errors sit side by
side. -/
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

/-- The guarded form of an appended verifier, from the guarded forms of its parts. -/
def guardedAppend (G₁ : D₁.red.toReduction.verifier.GuardedForm)
    (G₂ : D₂.red.toReduction.verifier.GuardedForm) :
    (D₁.append D₂).red.toReduction.verifier.GuardedForm :=
  cast (congrArg Verifier.GuardedForm
    (OracleVerifier.append_toVerifier D₁.red.verifier D₂.red.verifier).symm) (G₁.append G₂)

/-- Completeness composes: ArkLib's `append_perfectCompleteness_of_guarded_verifiers`. -/
def Complete.append (C₁ : Complete D₁ rel₁ rel₂) (C₂ : Complete D₂ rel₂ rel₃) :
    Complete (D₁.append D₂) rel₁ rel₃ where
  outputPure := Prover.OutputIsPure.append _ _ C₁.outputPure C₂.outputPure
  guarded := guardedAppend C₁.guarded C₂.guarded
  complete := fun init impl ↦
    OracleReduction.append_perfectCompleteness_of_guarded_verifiers D₁.red D₂.red
      C₁.guarded C₂.guarded (fun _ ↦ Or.inl C₁.outputPure)
      (C₁.complete init impl) (fun s ↦ C₂.complete (pure s) impl)

/-- Security composes, given the theorem ArkLib owes. -/
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

/-! ## Phases: components over the one committed oracle -/

namespace Phase

variable (I : M3Instance)

/-- A phase of the leanVM protocol: a component from a statement to a statement over the one
committed oracle, with the trivial witness (the oracle is the witness). -/
abbrev Def (StmtIn StmtOut : Type) : Type 1 :=
  Component.Def StmtIn (TheOracle I) Unit StmtOut (TheOracle I) Unit

/-- The completeness half of a phase, against its two seams. -/
abbrev Complete {StmtIn StmtOut : Type} (D : Def I StmtIn StmtOut)
    (relIn : Set ((StmtIn × ∀ i, TheOracle I i) × Unit))
    (relOut : Set ((StmtOut × ∀ i, TheOracle I i) × Unit)) : Type :=
  Component.Complete D relIn relOut

/-- The security half of a phase, against its two seams. -/
abbrev Security {StmtIn StmtOut : Type} (D : Def I StmtIn StmtOut)
    (relIn : Set ((StmtIn × ∀ i, TheOracle I i) × Unit))
    (relOut : Set ((StmtOut × ∀ i, TheOracle I i) × Unit)) : Type :=
  Component.Security D relIn relOut

/-! ## Pass-through phases

A phase with no round that maps the statement and leaves the oracle alone. It is the shape of
every bookkeeping step (relabelling claims, dropping a consumed clause), the inhabitant that
shows `Phases` and `Phases.Complete` are not empty, and the two unfolding lemmas below are the
ones every zero-round or pure phase would otherwise prove again. -/

variable {StmtIn StmtOut : Type}

/-- The prover of a pass-through phase: no message, the statement mapped, the oracle kept. -/
def passThroughProver (f : StmtIn → StmtOut) :
    OracleProver []ₒ StmtIn (TheOracle I) Unit StmtOut (TheOracle I) Unit !p[] where
  PrvState := fun _ ↦ (StmtIn × ∀ i, TheOracle I i) × Unit
  input := _root_.id
  sendMessage := fun i ↦ Fin.elim0 i.1
  receiveChallenge := fun i ↦ Fin.elim0 i.1
  output := fun p ↦ pure ((f p.1.1, p.1.2), ())

/-- The verifier of a pass-through phase: maps the statement, exposes the input oracle. -/
def passThroughVerifier (f : StmtIn → StmtOut) :
    OracleVerifier []ₒ StmtIn (TheOracle I) StmtOut (TheOracle I) !p[] where
  verify := fun s _ ↦ pure (f s)
  outputOracle := .inl
    { embed := Function.Embedding.inl
      hEq := fun _ ↦ rfl
      outputInterface_heq := fun _ ↦ HEq.rfl }

/-- A pass-through phase: no round, no error. -/
def passThrough (f : StmtIn → StmtOut) : Def I StmtIn StmtOut where
  n := 0
  pSpec := !p[]
  red := ⟨passThroughProver I f, passThroughVerifier I f⟩
  err := fun i ↦ Fin.elim0 i.1

/-- The pass-through verifier exposes its input oracle unchanged. -/
theorem passThrough_materializeOutput (f : StmtIn → StmtOut) (challenges : (!p[]).Challenges)
    (o : ∀ i, TheOracle I i) (messages : (!p[]).Messages) :
    (passThroughVerifier I f).materializeOutput challenges o messages = o := by
  funext i
  rfl

/-- As an ordinary verifier, the pass-through verifier returns the mapped statement and the
oracle. -/
theorem passThroughVerifier_toVerifier_run (f : StmtIn → StmtOut) (s : StmtIn)
    (o : ∀ i, TheOracle I i) (tr : (!p[]).FullTranscript) :
    (passThroughVerifier I f).toVerifier.run (s, o) tr = pure (f s, o) := by
  simp only [Verifier.run, OracleVerifier.toVerifier]
  rw [passThrough_materializeOutput]
  rfl

/-- The pass-through verifier is pure, as data. -/
def passThroughPure (f : StmtIn → StmtOut) : (passThroughVerifier I f).toVerifier.PureForm where
  verify := fun p _ ↦ (f p.1, p.2)
  verify_eq := fun ⟨s, o⟩ tr ↦ passThroughVerifier_toVerifier_run I f s o tr

/-- The completeness half of a pass-through phase, for any two seams the map carries one into
the other. -/
def passThroughComplete (f : StmtIn → StmtOut)
    {relIn : Set ((StmtIn × ∀ i, TheOracle I i) × Unit)}
    {relOut : Set ((StmtOut × ∀ i, TheOracle I i) × Unit)}
    (h : ∀ s o, ((s, o), ()) ∈ relIn → ((f s, o), ()) ∈ relOut) :
    Complete I (passThrough I f) relIn relOut where
  outputPure := ⟨_, fun _ ↦ rfl⟩
  guarded := (passThroughPure I f).toGuardedForm
  complete := fun init impl ↦ by
    apply Reduction.perfectCompleteness_of_run_support
    intro stmtIn witIn hIn x hx
    obtain ⟨s, o⟩ := stmtIn
    have hrun : ((passThrough I f).red.toReduction.run (s, o) witIn).run =
        pure (some (((show (passThrough I f).pSpec.FullTranscript from fun i ↦ Fin.elim0 i),
          (f s, o), ()), (f s, o))) := rfl
    rw [hrun, support_pure, Set.mem_singleton_iff] at hx
    exact ⟨_, hx, h s o hIn, rfl⟩

end Phase

end
end LeanerVM.Protocol
