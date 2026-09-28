/-
  LeanerVM.Protocol.ToArkLib.PassThrough

  The component with no round that maps the statement and leaves the oracles and the witness
  alone, with its completeness and knowledge-soundness proofs. Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.Component

/-!
# The pass-through component

`Component.passThrough OStmt f` sends nothing and outputs `f` of the input statement, the same
oracles and the same witness. It is the shape of every bookkeeping step (relabelling claims,
dropping a clause the previous step consumed), and its two unfolding lemmas are the ones any
zero-round or pure component would otherwise prove again. It is proved in both halves: complete
whenever `f` carries the input relation into the output relation, and knowledge sound at error
zero, with the extractor that keeps the witness, whenever `f` also reflects the output relation
back into the input relation.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec

@[expose] public section

namespace Component

variable {ι : Type} (OStmt : ι → Type) [∀ i, OracleInterface (OStmt i)]
  {StmtIn StmtOut W : Type}

/-- The prover: no message, the statement mapped, oracles and witness kept. -/
def passThroughProver (f : StmtIn → StmtOut) :
    OracleProver []ₒ StmtIn OStmt W StmtOut OStmt W !p[] where
  PrvState := fun _ ↦ (StmtIn × ∀ i, OStmt i) × W
  input := _root_.id
  sendMessage := fun i ↦ Fin.elim0 i.1
  receiveChallenge := fun i ↦ Fin.elim0 i.1
  output := fun p ↦ pure ((f p.1.1, p.1.2), p.2)

/-- The verifier: maps the statement and exposes the input oracles as the output oracles. -/
def passThroughVerifier (f : StmtIn → StmtOut) :
    OracleVerifier []ₒ StmtIn OStmt StmtOut OStmt !p[] where
  verify := fun s _ ↦ pure (f s)
  outputOracle := .inl
    { embed := Function.Embedding.inl
      hEq := fun _ ↦ rfl
      outputInterface_heq := fun _ ↦ HEq.rfl }

/-- The pass-through component: no round, no error. -/
def passThrough (f : StmtIn → StmtOut) : Def StmtIn OStmt W StmtOut OStmt W where
  n := 0
  pSpec := !p[]
  red := ⟨passThroughProver OStmt f, passThroughVerifier OStmt f⟩
  err := fun i ↦ Fin.elim0 i.1

/-- The output oracles are the input oracles. -/
theorem passThrough_materializeOutput (f : StmtIn → StmtOut) (challenges : (!p[]).Challenges)
    (o : ∀ i, OStmt i) (messages : (!p[]).Messages) :
    (passThroughVerifier OStmt f).materializeOutput challenges o messages = o := by
  funext i
  rfl

/-- As an ordinary verifier, the pass-through verifier returns the mapped statement and the
oracles. -/
theorem passThroughVerifier_toVerifier_run (f : StmtIn → StmtOut) (s : StmtIn)
    (o : ∀ i, OStmt i) (tr : (!p[]).FullTranscript) :
    (passThroughVerifier OStmt f).toVerifier.run (s, o) tr = pure (f s, o) := by
  simp only [Verifier.run, OracleVerifier.toVerifier]
  rw [passThrough_materializeOutput]
  rfl

/-- The pass-through verifier is pure, as data. -/
def passThroughPure (f : StmtIn → StmtOut) :
    (passThroughVerifier OStmt f).toVerifier.PureForm where
  verify := fun p _ ↦ (f p.1, p.2)
  verify_eq := fun ⟨s, o⟩ tr ↦ passThroughVerifier_toVerifier_run OStmt f s o tr

/-- Completeness, for any two relations `f` carries one into the other. -/
def passThroughComplete (f : StmtIn → StmtOut)
    {relIn : Set ((StmtIn × ∀ i, OStmt i) × W)} {relOut : Set ((StmtOut × ∀ i, OStmt i) × W)}
    (h : ∀ s o w, ((s, o), w) ∈ relIn → ((f s, o), w) ∈ relOut) :
    Complete (passThrough OStmt f) relIn relOut where
  outputPure := ⟨_, fun _ ↦ rfl⟩
  guarded := (passThroughPure OStmt f).toGuardedForm
  complete := fun init impl ↦ by
    apply Reduction.perfectCompleteness_of_run_support
    intro stmtIn witIn hIn x hx
    obtain ⟨s, o⟩ := stmtIn
    have hrun : ((passThrough OStmt f).red.toReduction.run (s, o) witIn).run =
        pure (some (((show (passThrough OStmt f).pSpec.FullTranscript from
          fun i ↦ Fin.elim0 i), (f s, o), witIn), (f s, o))) := rfl
    rw [hrun, support_pure, Set.mem_singleton_iff] at hx
    exact ⟨_, hx, h s o witIn hIn, rfl⟩

/-! ## Knowledge soundness -/

/-- The extractor keeps the witness. The shared oracle is written `OracleSpec.emptySpec.{0, 0}`
rather than `[]ₒ` to pin a universe `Extractor.RoundByRound` leaves free. -/
def passThroughExtractor : Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0})
    (StmtIn × ∀ i, OStmt i) W W !p[] (fun _ ↦ W) where
  eqIn := rfl
  extractMid := fun i ↦ Fin.elim0 i
  extractOut := fun _ _ w ↦ w

variable (f : StmtIn → StmtOut) {relIn : Set ((StmtIn × ∀ i, OStmt i) × W)}
  {relOut : Set ((StmtOut × ∀ i, OStmt i) × W)}
  (h : ∀ s o w, ((f s, o), w) ∈ relOut → ((s, o), w) ∈ relIn)
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- The knowledge state function: the input relation, at the only round. -/
def passThroughStateFunction :
    (passThroughVerifier OStmt f).toVerifier.KnowledgeStateFunction init impl relIn relOut
      (passThroughExtractor OStmt) where
  toFun := fun _ stmt _ w ↦ (stmt, w) ∈ relIn
  toFun_empty := fun _ _ ↦ Iff.rfl
  toFun_next := fun m ↦ Fin.elim0 m
  toFun_full := fun stmt tr w hpos ↦ by
    obtain ⟨s, o⟩ := stmt
    rw [passThroughVerifier_toVerifier_run OStmt f s o tr] at hpos
    change Pr[_ | OptionT.mk (do let st ← init; (simulateQ impl
      (OptionT.run (pure (f s, o)))).run' st)] > 0 at hpos
    exact h s o w (by simp at hpos; exact hpos.2)

/-- Round-by-round knowledge soundness at error zero: no challenge, the witness is kept. -/
theorem passThrough_rbr :
    (passThroughVerifier OStmt f).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl relIn
      relOut (fun _ ↦ W) (passThroughExtractor OStmt) (passThroughStateFunction OStmt f h init impl)
      (fun i ↦ Fin.elim0 i.1) :=
  fun _ i ↦ Fin.elim0 i.1

/-- The security half, with the extractor that keeps the witness, whenever `f` carries the input
relation into the output relation and back. -/
def passThroughSecurity (hc : ∀ s o w, ((s, o), w) ∈ relIn → ((f s, o), w) ∈ relOut) :
    Security (passThrough OStmt f) relIn relOut where
  toComplete := passThroughComplete OStmt f hc
  witMid := fun _ ↦ W
  extractor := passThroughExtractor OStmt
  kSF := passThroughStateFunction OStmt f h
  rbr := passThrough_rbr OStmt f h

end Component

end
end LeanerVM.Protocol
