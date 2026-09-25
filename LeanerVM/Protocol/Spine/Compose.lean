/-
  LeanerVM.Protocol.Spine.Compose

  The commit phase, the bundle of the five other phases, the composed oracle protocol
  `leanVmPiop`, its error, and the two master theorems, conditional on the bundle's proofs and
  (for knowledge) on the theorem ArkLib owes.
-/

module

public import LeanerVM.Protocol.Spine.Phase

/-!
# The oracle protocol and its master theorems

Protocol roadmap, section *The spine*, items 6 and 7 of *What the spine fixes*. The oracle
protocol is

```text
leanVmPiop P = commit ⟫ P.bus ⟫ P.table ⟫ P.pub ⟫ P.flock ⟫ P.opening
```

where `commit` is defined and proved here (the prover sends the stack as the one oracle message
and the verifier passes the statement through: ArkLib's `SendSingleWitness` shape) and the five
others are the fields of a `Phases I`, the holes P1 to P8 of the roadmap. Its relation is `M3Rel I`
on input and `Seam.done I` (nothing) on output.

The two master theorems are proved once, by folding the binary composition of
`LeanerVM.Protocol.Spine.Phase`:

* `piop_perfectCompleteness`: from a `Phases.Complete`, the completeness half of the five
  phases, and the commit phase's proved here (`commitComplete`), by ArkLib's proved composition.
* `piop_rbrKnowledgeSoundness`: from a `Phases.Security` and a `KnowledgeAppend` (hole C1,
  ledger A2), round-by-round knowledge soundness at `piopError P`, the six errors side by side,
  with the commit phase's proved here (`commitSecurity`).

The extractor of the whole protocol starts with the commit phase's (`commitExtractor`): it reads
the stack off the first message, straight-line, and every later phase's extractor is the
identity on the trivial witness. The adaptor of Layer 3 turns that stack into leanISA's
witness (`witnessOf`), and T4 (Layer 13) applies it to the extracted stack.

Category A. Target: T4's ideal-oracle half; Layer 12 compiles it and Layer 13 composes it with
the adaptor and T1.

## Wrong readings excluded

* `Set.univ` as the output relation says the last phase leaves nothing to check; a protocol whose
  opening phase output a nontrivial relation would owe it to WHIR (Layer 11).
* The commit phase has no challenge, so its error is the empty function; `piopError` on the
  composed schedule is defined by the same placement `Def.append` uses.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

@[expose] public section

variable (I : M3Instance)

/-! ## The commit phase -/

/-- The schedule of the commit phase: one prover message, the stack. -/
@[reducible]
def commitSpec : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[Column I.μ]⟩

/-- The honest commit prover: sends the stack and keeps the statement. -/
def commitProver :
    OracleProver []ₒ I.Stmt NoOracle (Column I.μ) I.Stmt (TheOracle I) Unit (commitSpec I) where
  PrvState := fun _ ↦ I.Stmt × Column I.μ
  input := fun p ↦ (p.1.1, p.2)
  sendMessage | ⟨0, _⟩ => fun st ↦ pure (st.2, st)
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun st ↦ pure ((st.1, fun _ ↦ st.2), ())

/-- The one message of the commit phase is the one output oracle. -/
def commitEmbedding : OracleOutputEmbedding NoOracle (commitSpec I).Message (TheOracle I) where
  embed := ⟨fun _ ↦ Sum.inr ⟨0, rfl⟩, fun a b _ ↦ Subsingleton.elim a b⟩
  hEq := fun _ ↦ rfl
  outputInterface_heq := fun _ ↦ HEq.rfl

/-- The commit verifier: passes the statement through and exposes the message as the oracle. -/
def commitVerifier : OracleVerifier []ₒ I.Stmt NoOracle I.Stmt (TheOracle I) (commitSpec I) where
  verify := fun s _ ↦ pure s
  outputOracle := .inl (commitEmbedding I)

/-- The commit phase as a component: no challenge, so no error. -/
def commitDef : Component.Def I.Stmt NoOracle (Column I.μ) I.Stmt (TheOracle I) Unit where
  n := 1
  pSpec := commitSpec I
  red := ⟨commitProver I, commitVerifier I⟩
  err := fun _ ↦ 0

/-! ### Its two proofs

The commit phase is the spine's own obligation: its prover's output is pure, its verifier is
pure (it returns the statement and exposes the message), and its honest run lands in
`Seam.commit`. -/

/-- The commit prover's output makes no oracle query. -/
theorem commitOutputPure : (commitDef I).red.prover.OutputIsPure := ⟨_, fun _ ↦ rfl⟩

/-- The commit verifier exposes its one message as the one output oracle. -/
theorem commit_materializeOutput (challenges : (commitSpec I).Challenges)
    (o : ∀ i, NoOracle i) (messages : (commitSpec I).Messages) :
    (commitVerifier I).materializeOutput challenges o messages = fun _ ↦ messages ⟨0, rfl⟩ := by
  unfold OracleVerifier.materializeOutput commitVerifier
  change OracleVerifier.materializeOutputOracle (Sum.inl (commitEmbedding I)) challenges o
    messages = _
  simp only [OracleVerifier.materializeOutputOracle]
  funext i
  fin_cases i
  rfl

/-- As an ordinary verifier, the commit verifier returns the statement and the message. -/
theorem commitVerifier_toVerifier_run (s : I.Stmt) (o : ∀ i, NoOracle i)
    (tr : (commitSpec I).FullTranscript) :
    (commitVerifier I).toVerifier.run (s, o) tr = pure (s, fun _ ↦ tr 0) := by
  simp only [Verifier.run, OracleVerifier.toVerifier]
  rw [commit_materializeOutput]
  rfl

/-- The commit verifier is pure, as data. -/
def commitVerifierPure : (commitVerifier I).toVerifier.PureForm where
  verify := fun p tr ↦ (p.1, fun _ ↦ tr 0)
  verify_eq := fun ⟨s, o⟩ tr ↦ commitVerifier_toVerifier_run I s o tr

/-- The commit verifier is guarded (with the trivial guard). -/
def commitGuarded : (commitDef I).red.toReduction.verifier.GuardedForm :=
  (commitVerifierPure I).toGuardedForm

/-- **Perfect completeness of the commit phase**: on `M3Holds I input q`, sending `q` lands in
`Seam.commit`, which is `M3Holds` of the message. -/
theorem commitComplete_run {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (commitDef I).red.perfectCompleteness init impl (M3Rel I) (Seam.commit I) := by
  apply Reduction.perfectCompleteness_of_run_support
  intro stmtIn witIn hIn x hx
  obtain ⟨s, o⟩ := stmtIn
  have hrun : ((commitDef I).red.toReduction.run (s, o) witIn).run =
      pure (some (((show (commitDef I).pSpec.FullTranscript from
        ProtocolSpec.Transcript.concat (m := 0) witIn (default : (commitSpec I).Transcript 0)),
        (s, fun _ ↦ witIn), ()), (s, fun _ ↦ witIn))) := rfl
  rw [hrun, support_pure, Set.mem_singleton_iff] at hx
  exact ⟨_, hx, hIn, rfl⟩

/-- The completeness half of the commit phase. -/
def commitComplete : Component.Complete (commitDef I) (M3Rel I) (Seam.commit I) where
  outputPure := commitOutputPure I
  guarded := commitGuarded I
  complete := commitComplete_run I

/-! ### Its knowledge half

The commit phase has no challenge, so its knowledge error is zero and its extractor is the
reading of the stack off the one message: the first instance of the extractor discipline of the
roadmap (acceptance test 24), computable and straight-line. -/

/-- The intermediate witnesses of the commit phase: always a stack. -/
abbrev commitWitMid : Fin 2 → Type := fun _ ↦ Column I.μ

/-- The extractor of the commit phase reads the stack off the one message. The shared oracle is
written `OracleSpec.emptySpec.{0, 0}` rather than `[]ₒ` to pin the universe `Extractor.RoundByRound`
leaves free, so that the definition is not universe polymorphic. -/
def commitExtractor :
    Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0}) (I.Stmt × ∀ i, NoOracle i) (Column I.μ)
      Unit (commitSpec I) (commitWitMid I) where
  eqIn := rfl
  extractMid := fun m _ tr _ ↦ tr ⟨0, Nat.succ_pos m.val⟩
  extractOut := fun _ tr _ ↦ tr 0

/-- The run of the commit verifier, at the transcript type a state function sees. -/
theorem commitVerifier_toVerifier_run' (s : I.Stmt) (o : ∀ i, NoOracle i)
    (tr : (commitSpec I).Transcript (Fin.last 1)) :
    Verifier.run (s, o) tr (commitVerifier I).toVerifier =
      pure (s, fun _ ↦ tr ⟨0, Nat.succ_pos 0⟩) :=
  commitVerifier_toVerifier_run I s o tr

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- The knowledge state function of the commit phase: before the message, `M3Holds` of the
intermediate witness; after it, `M3Holds` of the message. -/
def commitStateFunction :
    (commitVerifier I).toVerifier.KnowledgeStateFunction init impl (M3Rel I) (Seam.commit I)
      (commitExtractor I) where
  toFun := fun m stmt tr w ↦
    if h : m.val = 0 then M3Holds I stmt.1 w
    else M3Holds I stmt.1 (tr ⟨0, Nat.pos_of_ne_zero h⟩)
  toFun_empty := fun _ _ ↦ Iff.rfl
  toFun_next := fun m _ stmt tr msg w h ↦ by
    have hm : m.val = 0 := by omega
    simp only [Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false, dite_false] at h
    simp only [Fin.val_castSucc, hm, dite_true]
    exact h
  toFun_full := fun stmt tr _ h ↦ by
    obtain ⟨s, o⟩ := stmt
    simp only [Fin.val_last, one_ne_zero, dite_false]
    rw [commitVerifier_toVerifier_run'] at h
    change Pr[_ | OptionT.mk (do let st ← init; (simulateQ impl
      (OptionT.run (pure (s, fun _ ↦ tr ⟨0, Nat.succ_pos 0⟩)))).run' st)] > 0 at h
    rw [OptionT.run_pure, simulateQ_pure] at h
    obtain ⟨y, hy, hp⟩ := probEvent_pos_iff.mp h
    simp [OptionT.mem_support_iff] at hy
    obtain ⟨_, rfl⟩ := hy
    exact hp

/-- **Round-by-round knowledge soundness of the commit phase**, at error zero: there is no
challenge, and the extractor reads the stack off the message. -/
theorem commitRbr :
    (commitVerifier I).toVerifier.rbrKnowledgeSoundnessWorstCase init impl (M3Rel I)
      (Seam.commit I) (fun _ ↦ 0) :=
  ⟨commitWitMid I, commitExtractor I, commitStateFunction I init impl,
    fun _ i ↦ (IsEmpty.false i).elim⟩

/-- The security half of the commit phase. -/
def commitSecurity : Component.Security (commitDef I) (M3Rel I) (Seam.commit I) where
  toComplete := commitComplete I
  rbr := fun init impl ↦ commitRbr I init impl

/-! ## The bundle of phases -/

/-- The five phases after the commit, each against the spine's seams: the holes P1 to P8. -/
structure Phases where
  /-- The bus phase (Layer 6): from `M3Holds` on the oracle to the zerocheck claims, the bus
  forms and the boundary claims. -/
  bus : Phase.Def I I.Stmt (I.Stmt × BusOut I)
  /-- The table sumcheck (Layer 7): from linear claims to column claims. -/
  table : Phase.Def I (I.Stmt × BusOut I) (I.Stmt × TableOut I)
  /-- The public-input phase (Layer 8): the public cells become column claims. -/
  pub : Phase.Def I (I.Stmt × TableOut I) (I.Stmt × PubOut I)
  /-- The Flock phase (Layer 9): the auxiliary predicate becomes a weighted claim. -/
  flock : Phase.Def I (I.Stmt × PubOut I) (I.Stmt × FlockOut I)
  /-- The opening phase (Layer 10): the pool is batched and opened against the oracle. -/
  opening : Phase.Def I (I.Stmt × FlockOut I) Unit

variable {I}

/-- The whole protocol as one component. -/
def Phases.toDef (P : Phases I) :
    Component.Def I.Stmt NoOracle (Column I.μ) Unit (TheOracle I) Unit :=
  (((((commitDef I).append P.bus).append P.table).append P.pub).append P.flock).append P.opening

/-- The completeness halves of the five phases, against the seams; the commit phase's is
`commitComplete`. -/
structure Phases.Complete (P : Phases I) where
  /-- P1. -/
  bus : Phase.Complete I P.bus (Seam.commit I) (Seam.bus I)
  /-- P3. -/
  table : Phase.Complete I P.table (Seam.bus I) (Seam.table I)
  /-- P5, the completeness half. -/
  pub : Phase.Complete I P.pub (Seam.table I) (Seam.pub I)
  /-- P6, the completeness half. -/
  flock : Phase.Complete I P.flock (Seam.pub I) (Seam.flock I)
  /-- P7. -/
  opening : Phase.Complete I P.opening (Seam.flock I) (Seam.done I)

/-- The whole protocol's completeness half: the commit phase's, then five binary compositions. -/
def Phases.Complete.toDef {P : Phases I} (C : P.Complete) :
    Component.Complete P.toDef (M3Rel I) (Seam.done I) :=
  (((((commitComplete I).append C.bus).append C.table).append C.pub).append C.flock).append
    C.opening

/-- The security halves of the five phases, against the seams; the commit phase's is
`commitSecurity`. -/
structure Phases.Security (P : Phases I) where
  /-- P1 and P2. -/
  bus : Phase.Security I P.bus (Seam.commit I) (Seam.bus I)
  /-- P3 and P4. -/
  table : Phase.Security I P.table (Seam.bus I) (Seam.table I)
  /-- P5. -/
  pub : Phase.Security I P.pub (Seam.table I) (Seam.pub I)
  /-- P6. -/
  flock : Phase.Security I P.flock (Seam.pub I) (Seam.flock I)
  /-- P7 and P8. -/
  opening : Phase.Security I P.opening (Seam.flock I) (Seam.done I)

/-- The whole protocol's security half: the commit phase's, then five binary compositions, given
the theorem ArkLib owes. -/
def Phases.Security.toDef (A : KnowledgeAppend) {P : Phases I} (S : P.Security) :
    Component.Security P.toDef (M3Rel I) (Seam.done I) :=
  (((((commitSecurity I).append A S.bus).append A S.table).append A S.pub).append A
    S.flock).append A S.opening

/-! ## The oracle protocol -/

/-- The oracle protocol: the commit phase, then the five phases of `P`. -/
def leanVmPiop (P : Phases I) :
    OracleReduction []ₒ I.Stmt NoOracle (Column I.μ) Unit (TheOracle I) Unit P.toDef.pSpec :=
  P.toDef.red

/-- Its verifier. -/
def leanVmVerifier (P : Phases I) :
    OracleVerifier []ₒ I.Stmt NoOracle Unit (TheOracle I) P.toDef.pSpec :=
  P.toDef.red.verifier

/-- Its honest prover. -/
def leanVmProver (P : Phases I) :
    OracleProver []ₒ I.Stmt NoOracle (Column I.μ) Unit (TheOracle I) Unit P.toDef.pSpec :=
  P.toDef.red.prover

/-- Its per-challenge error: the six phases' errors side by side. -/
def piopError (P : Phases I) : P.toDef.pSpec.ChallengeIdx → ℝ≥0 := P.toDef.err

/-! ## The master theorems -/

/-- **Perfect completeness of the oracle protocol.** On every `(input, q)` with
`M3Holds I input q`, the honest prover convinces the verifier with probability one. -/
theorem piop_perfectCompleteness (P : Phases I) (C : P.Complete) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (leanVmPiop P).perfectCompleteness init impl (M3Rel I) (Seam.done I) :=
  C.toDef.complete init impl

/-- **Round-by-round knowledge soundness of the oracle protocol**, at the error `piopError P`,
given the composition theorem ArkLib owes (hole C1). This is the round-by-round statement (a
knowledge state function and a round-by-round extractor exist, the bad transition at each
challenge has probability at most `piopError P` of it); the plain reading, "a straight-line
extractor returns a stack `q` with `M3Holds I input q` except with probability
`Σ piopError P`", is ArkLib's `rbrKnowledgeSoundness_implies_knowledgeSoundness`, admitted at the
pin (ledger A3), which Layer 12 takes as an interface. -/
theorem piop_rbrKnowledgeSoundness (A : KnowledgeAppend) (P : Phases I) (S : P.Security)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (leanVmVerifier P).toVerifier.rbrKnowledgeSoundnessWorstCase init impl (M3Rel I)
      (Seam.done I) (piopError P) :=
  (S.toDef A).rbr init impl

end
end LeanerVM.Protocol
