/-
  LeanerVM.Protocol.ToArkLib.Component

  A component of an interactive oracle proof as pieces of data: its definition, its guarded
  form, its completeness proof, its extractor with its knowledge-soundness proof at a given
  error; and their sequential composition. Candidate for ArkLib.
-/

module

public import ArkLib.OracleReduction.Composition.Sequential.Append.Basic
public import ArkLib.OracleReduction.Composition.Sequential.Append.StateFunction
public import ArkLib.OracleReduction.Composition.Sequential.OracleCompleteness
public import ArkLib.OracleReduction.Composition.Sequential.NoAmbient
public import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Guarded
public import LeanerVM.Protocol.ToArkLib.KnowledgeAppend

/-!
# Components and their composition

A `Component.Def` is an ArkLib oracle reduction (an honest prover and a verifier that may query
the input oracles and the prover's messages) at a given message schedule: the schedule is a
parameter of the type, so two components can only be composed, and a component can only fill a
slot, when their schedules are the ones written down. A `Def` carries no error.

`Component.Guarded` is the fact ArkLib's composition theorems need of a verifier: it is a
Boolean check followed by a pure verdict. `Component.Complete` extends it with perfect
completeness, the honest prover convincing the verifier with probability one.
`Component.Extraction` extends it with a round-by-round extractor and its knowledge state
function: everything knowledge soundness is stated for, and it computes. `Component.Security`
extends the extraction, independently of completeness, with round-by-round knowledge soundness
in the worst case over transcript prefixes at a given error: the proof that each fresh
challenge can turn the state from false to true with probability at most the error at that
challenge. The error is a parameter, not a field, so that the error a component is proved at
is the one its consumer demands. It is a real number, which compiled code cannot hold, so a
security takes no real number as an argument: it is stated at its exact error, counting bad
challenges with `Nat.card`, and raised with `Security.mono`, which, like `Security.append`, is
inlined before compilation. A security then computes, its extractor included. A new combinator
that takes a security is inlined the same way (`@[macro_inline]`), and a `let` binding a
security inside a definition would bring the errors back into compiled code.

Two components in sequence are again a component (`Def.append`): schedules concatenate, and so
do the errors (`errAppend`). Completeness composes by a theorem ArkLib proves; the prover's
final output makes no oracle query since the shared oracle is empty. Extractors compose by
ArkLib's `Extractor.RoundByRound.append`, through the first verifier's verdict. Their knowledge
state functions and the knowledge-soundness bound compose by the construction and the theorem
of `LeanerVM.Protocol.ToArkLib.KnowledgeAppend`, ported from ArkLib pull request #615 (ArkLib's
own `append_rbrKnowledgeSoundness` is admitted at the pinned revision), so knowledge soundness
composes with no assumption.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

@[expose] public section

/-! ## Errors side by side -/

/-- The errors of two schedules in sequence: each challenge keeps the error its schedule
assigned it. -/
def errAppend {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    (ε₁ : pSpec₁.ChallengeIdx → ℝ≥0) (ε₂ : pSpec₂.ChallengeIdx → ℝ≥0) :
    (pSpec₁ ++ₚ pSpec₂).ChallengeIdx → ℝ≥0 :=
  Sum.elim ε₁ ε₂ ∘ ChallengeIdx.sumEquiv.symm

/-- The sum of the errors of two schedules in sequence is the sum of the sums. -/
theorem sum_errAppend {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    (ε₁ : pSpec₁.ChallengeIdx → ℝ≥0) (ε₂ : pSpec₂.ChallengeIdx → ℝ≥0) :
    ∑ i, errAppend ε₁ ε₂ i = ∑ i, ε₁ i + ∑ i, ε₂ i := by
  rw [← ChallengeIdx.sumEquiv.sum_comp (errAppend ε₁ ε₂)]
  simp only [errAppend, Function.comp_apply, Equiv.symm_apply_apply, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr]

/-- The values satisfying `p`, counted as a subtype, are those of the filtered universe: errors
count bad challenges with `Nat.card`, which needs no `Fintype` instance, and proofs count them
with `Finset`. -/
theorem natCard_subtype_eq_card_filter {α : Type} [Fintype α] (p : α → Prop) [DecidablePred p] :
    Nat.card {a // p a} = (Finset.univ.filter p).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

namespace Component

/-! ## The four pieces -/

/-- A component at a schedule: its reduction. The instances say that every prover message can
be queried and every challenge can be sampled. -/
structure Def (StmtIn : Type) {ιi : Type} (OStmtIn : ιi → Type) (WitIn : Type)
    (StmtOut : Type) {ιo : Type} (OStmtOut : ιo → Type) (WitOut : Type)
    {n : ℕ} (pSpec : ProtocolSpec n)
    [∀ i, OracleInterface (OStmtIn i)] [∀ i, OracleInterface (OStmtOut i)]
    [∀ i, OracleInterface (pSpec.Message i)] [∀ i, SampleableType (pSpec.Challenge i)] where
  /-- The honest prover and the verifier. -/
  red : OracleReduction []ₒ StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec

variable {StmtIn : Type} {ιi : Type} {OStmtIn : ιi → Type} {WitIn : Type}
  {StmtOut : Type} {ιo : Type} {OStmtOut : ιo → Type} {WitOut : Type}
  [∀ i, OracleInterface (OStmtIn i)] [∀ i, OracleInterface (OStmtOut i)]
  {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, OracleInterface (pSpec.Message i)] [∀ i, SampleableType (pSpec.Challenge i)]

/-- The guarded form of a component: its verifier is a Boolean check followed by a pure
verdict. -/
structure Guarded (D : Def StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec) where
  /-- The check and the verdict. -/
  guarded : D.red.toReduction.verifier.GuardedForm

/-- A front component: its verifier is a check and a verdict that read the statement and the
transcript alone and hand the oracles on, so it never reads the oracles. The witness of
oracle-freeness a compiled verifier needs of every component before an opening. -/
structure Front {OStmt : ιi → Type} [∀ i, OracleInterface (OStmt i)]
    (D : Def StmtIn OStmt WitIn StmtOut OStmt WitOut pSpec) where
  /-- The check, on the statement and the transcript. -/
  check : StmtIn → pSpec.FullTranscript → Bool
  /-- The verdict, on the statement and the transcript. -/
  out : StmtIn → pSpec.FullTranscript → StmtOut
  /-- The verifier is guarded with exactly these, the oracles handed on. -/
  verify_eq : D.red.verifier.toVerifier.IsGuardedWith (fun p tr ↦ check p.1 tr)
    (fun p tr ↦ (out p.1 tr, p.2))

/-- A front component is guarded. -/
def Front.toGuarded {OStmt : ιi → Type} [∀ i, OracleInterface (OStmt i)]
    {D : Def StmtIn OStmt WitIn StmtOut OStmt WitOut pSpec} (F : Front D) : Guarded D :=
  ⟨⟨_, _, F.verify_eq⟩⟩

/-- The completeness half of a component: on every pair of the input relation, the honest run
lands in the output relation with probability one, from any state of the shared oracle. -/
structure Complete (D : Def StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut)) extends Guarded D where
  /-- Perfect completeness. -/
  complete : ∀ {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)),
    D.red.perfectCompleteness init impl relIn relOut

/-- The extraction of a component: its guarded form, a round-by-round extractor and its
knowledge state function. It presupposes no completeness, and it computes. -/
structure Extraction (D : Def StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut)) extends Guarded D where
  /-- The extractor's intermediate witness type after each round. -/
  witMid : Fin (n + 1) → Type
  /-- The round-by-round extractor. The shared oracle is written `OracleSpec.emptySpec.{0, 0}`
  rather than `[]ₒ` to pin a universe `Extractor.RoundByRound` leaves free. -/
  extractor : Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0}) (StmtIn × ∀ i, OStmtIn i)
    WitIn WitOut pSpec witMid
  /-- The extractor's knowledge state function, from any state of the shared oracle. -/
  kSF : ∀ {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)),
    D.red.verifier.toVerifier.KnowledgeStateFunction init impl relIn relOut extractor

/-- The security half of a component, at a given error: an extraction, with worst-case
round-by-round knowledge soundness for its extractor and state function at that error. -/
structure Security (D : Def StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (err : pSpec.ChallengeIdx → ℝ≥0) extends Extraction D relIn relOut where
  /-- Round-by-round knowledge soundness at `err`, for this extractor and state function. -/
  rbr : ∀ {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)),
    D.red.verifier.toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut witMid
      extractor (kSF init impl) err

/-- Security at an error is security at any larger error. Inlined before compilation, so the
errors, real numbers, never reach compiled code and a security built with it computes. -/
@[macro_inline]
def Security.mono {D : Def StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn)}
    {relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut)}
    {ε ε' : pSpec.ChallengeIdx → ℝ≥0} (h : ∀ i, ε i ≤ ε' i) (S : Security D relIn relOut ε) :
    Security D relIn relOut ε' where
  toExtraction := S.toExtraction
  rbr := fun init impl s i tr ↦ (S.rbr init impl s i tr).trans (ENNReal.coe_le_coe.mpr (h i))

/-- The extractor that keeps the witness at every round. The shared oracle is written
`OracleSpec.emptySpec.{0, 0}` rather than `[]ₒ` to pin a universe `Extractor.RoundByRound`
leaves free. -/
def keepExtractor (S W : Type) {n : ℕ} (pSpec : ProtocolSpec n) :
    Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0}) S W W pSpec (fun _ ↦ W) where
  eqIn := rfl
  extractMid := fun _ _ _ w ↦ w
  extractOut := fun _ _ w ↦ w

/-! ## Composition -/

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
  {m₁ m₂ : ℕ} {pSpec₁ : ProtocolSpec m₁} {pSpec₂ : ProtocolSpec m₂}
  [∀ i, OracleInterface (pSpec₁.Message i)] [∀ i, SampleableType (pSpec₁.Challenge i)]
  [∀ i, OracleInterface (pSpec₂.Message i)] [∀ i, SampleableType (pSpec₂.Challenge i)]

/-- Two components in sequence: the schedules concatenate. -/
def Def.append (D₁ : Def Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    (D₂ : Def Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂) :
    Def Stmt₁ OStmt₁ Wit₁ Stmt₃ OStmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂) where
  red := D₁.red.append D₂.red

variable {D₁ : Def Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁}
  {D₂ : Def Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂}
  {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)} {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
  {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}

/-- The guarded form of an appended verifier, from those of its parts. -/
def guardedAppend (G₁ : D₁.red.toReduction.verifier.GuardedForm)
    (G₂ : D₂.red.toReduction.verifier.GuardedForm) :
    (D₁.append D₂).red.toReduction.verifier.GuardedForm :=
  cast (congrArg _ (OracleVerifier.append_toVerifier _ _).symm) (G₁.append G₂)

/-- Guarded forms compose. -/
def Guarded.append (G₁ : Guarded D₁) (G₂ : Guarded D₂) : Guarded (D₁.append D₂) where
  guarded := guardedAppend G₁.guarded G₂.guarded

/-- Two front components over the same oracles in sequence are front: the first check, then the
second on the first verdict. -/
def Front.append {OStmt : ι₁ → Type} [∀ i, OracleInterface (OStmt i)]
    {E₁ : Def Stmt₁ OStmt Wit₁ Stmt₂ OStmt Wit₂ pSpec₁}
    {E₂ : Def Stmt₂ OStmt Wit₂ Stmt₃ OStmt Wit₃ pSpec₂} (F₁ : Front E₁) (F₂ : Front E₂) :
    Front (E₁.append E₂) where
  check := fun s tr ↦ F₁.check s tr.fst && F₂.check (F₁.out s tr.fst) tr.snd
  out := fun s tr ↦ F₂.out (F₁.out s tr.fst) tr.snd
  verify_eq := fun p tr ↦ by
    have h := (F₁.toGuarded.guarded.append F₂.toGuarded.guarded).verify_eq p tr
    change (E₁.red.verifier.append E₂.red.verifier).toVerifier.verify p tr = _
    rw [OracleVerifier.append_toVerifier]
    exact h

/-- Completeness composes (ArkLib's `append_perfectCompleteness_of_guarded_verifiers`); the
first prover's output is pure since the shared oracle is empty. -/
def Complete.append (C₁ : Complete D₁ rel₁ rel₂) (C₂ : Complete D₂ rel₂ rel₃) :
    Complete (D₁.append D₂) rel₁ rel₃ where
  toGuarded := C₁.toGuarded.append C₂.toGuarded
  complete := fun init impl ↦
    OracleReduction.append_perfectCompleteness_of_guarded_verifiers D₁.red D₂.red
      C₁.guarded C₂.guarded (fun _ ↦ Or.inl (Prover.instOutputIsPureEmpty _))
      (C₁.complete init impl) (fun s ↦ C₂.complete (pure s) impl)

/-- Extractions compose: the extractors are appended through the first verdict, their state
functions by `Verifier.KnowledgeStateFunction.appendGuarded`. -/
def Extraction.append (X₁ : Extraction D₁ rel₁ rel₂) (X₂ : Extraction D₂ rel₂ rel₃) :
    Extraction (D₁.append D₂) rel₁ rel₃ where
  toGuarded := X₁.toGuarded.append X₂.toGuarded
  witMid := _
  extractor := X₁.extractor.append X₂.extractor X₁.guarded.out
  kSF := fun init impl ↦ stateFunctionOfEq (OracleVerifier.append_toVerifier _ _)
    (Verifier.KnowledgeStateFunction.appendGuarded X₁.guarded (X₁.kSF init impl)
      (X₂.kSF init impl))

/-- Security composes, at the errors side by side: the extractions are appended, and the bound
is `Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first`. Inlined before
compilation, like `Security.mono`, so a composed security computes. -/
@[macro_inline]
def Security.append {ε₁ : pSpec₁.ChallengeIdx → ℝ≥0} {ε₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (S₁ : Security D₁ rel₁ rel₂ ε₁) (S₂ : Security D₂ rel₂ rel₃ ε₂) :
    Security (D₁.append D₂) rel₁ rel₃ (errAppend ε₁ ε₂) where
  toExtraction := S₁.toExtraction.append S₂.toExtraction
  rbr := fun init impl ↦
    rbrKnowledgeSoundnessWorstCaseWith_of_eq (OracleVerifier.append_toVerifier _ _)
      (Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first S₁.guarded
        (S₁.kSF init impl) (S₂.kSF init impl) (S₁.rbr init impl) (S₂.rbr init impl))

end Component

end
end LeanerVM.Protocol
