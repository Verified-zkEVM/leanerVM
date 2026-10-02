/-
  LeanerVM.Protocol.Spine.Compose

  The commit phase, the bundle of the five other phases at their slots, the composed oracle
  protocol, its extractor and the stack it extracts, and the two master theorems.
-/

module

public import LeanerVM.Protocol.ToArkLib.SendOracle
public import LeanerVM.Protocol.ToArkLib.ExtractIn
public import LeanerVM.Protocol.Spine.Phase
public import LeanerVM.Protocol.Spine.Errors

/-!
# The oracle protocol and its master theorems

The oracle protocol is `commit ⟫ bus ⟫ table ⟫ pub ⟫ flock ⟫ opening`. The commit phase sends
the stack as the one oracle message; it is the send-oracle component of
`LeanerVM.Protocol.ToArkLib.SendOracle` at the stack, both its proofs included. The five other
phases are the fields of a `Phases I`, each at its slot's schedule (`LeanerVM.Protocol.Spine.
Errors`), the four before the opening as front phases that never query the stack; their proofs
are the fields of `Phases.Complete` and `Phases.Security`, the latter at the slots' errors. The
protocol starts from `M3Rel I` and ends with nothing left to check.

`piop_perfectCompleteness`: given every phase's completeness, the honest prover convinces the
verifier with probability one on every stack satisfying `M3Holds`.
`piop_rbrKnowledgeSoundness`: given every phase's security, the verifier is round-by-round
knowledge sound at `piopError I`, the slots' errors side by side, for the extractor
`piopExtractor`: the commit phase's, which reads the stack off the first message, followed by
the phases' own, each appended through the verdict of the verifiers before it. The composition
across phases is proved (`Component.Security.append`). The stack the extractor returns on a
transcript, `piopExtractedStack`, is the committed message, whatever the phases' extractors do
(`piopExtractedStack_eq`).
`piop_rbrKnowledgeSoundness_exists` is the same with the extractor forgotten. Its plain reading,
"a straight-line extractor returns a stack satisfying `M3Holds` except with probability the sum
of `piopError`", is ArkLib's `rbrKnowledgeSoundness_implies_knowledgeSoundness`, admitted at the
pinned revision.

Both theorems are stated in the ideal oracle model, over an abstract instance, and are
conditional only on the phases' proofs; the compiled verifier and the leanISA instance are built
on top of them.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

@[expose] public section

variable (I : M3Instance)

/-! ## The commit phase -/

/-- The commit phase: the prover sends the stack, the verifier keeps the statement and exposes
the message as the oracle. No challenge. -/
abbrev commitDef : Component.Def I.Stmt NoOracle (Column I.μ) I.Stmt (TheOracle I) Unit
    (commitSpec I) :=
  Component.sendOracle I.Stmt (Column I.μ)

/-- Its extractor: read the stack off the message. -/
abbrev commitExtractor := Component.sendExtractor (S := I.Stmt) (M := Column I.μ)

/-- Perfect completeness of the commit phase: on `M3Holds I input q`, sending `q` lands in
`Seam.commit`, which is `M3Holds` of the message. -/
def commitComplete : Component.Complete (commitDef I) (M3Rel I) (Seam.commit I) :=
  Component.sendOracleComplete (M3Rel I)

/-- Knowledge soundness of the commit phase, at error zero. -/
def commitSecurity : Component.Security (commitDef I) (M3Rel I) (Seam.commit I) (commitError I) :=
  Component.sendOracleSecurity (M3Rel I)

/-! ## The bundle of phases -/

/-- The five phases after the commit, each at its slot. -/
structure Phases where
  /-- The bus phase: from `M3Holds` of the oracle to the point, the forms and the boundary
  claims (§5.2 to §5.4). -/
  bus : Phase.FrontDef I I.Stmt (I.Stmt × BusOut I) (busSpec I)
  /-- The table sumcheck: from the forms to column claims (§5.5). -/
  table : Phase.FrontDef I (I.Stmt × BusOut I) (I.Stmt × TableOut I) (tableSpec I)
  /-- The public-input phase: the public lines become column claims (§8.2). -/
  pub : Phase.FrontDef I (I.Stmt × TableOut I) (I.Stmt × PubOut I) pubSpec
  /-- The Flock phase: the Flock predicate becomes a weighted claim (Annex C). -/
  flock : Phase.FrontDef I (I.Stmt × PubOut I) (I.Stmt × FlockOut I) (flockSpec I)
  /-- The opening phase: the pool is batched and opened against the oracle (§8.5). -/
  opening : Phase.Def I (I.Stmt × FlockOut I) Unit openingSpec

variable {I}

/-- The whole protocol as one component. -/
def Phases.toDef (P : Phases I) :
    Component.Def I.Stmt NoOracle (Column I.μ) Unit (TheOracle I) Unit (piopSpec I) :=
  (((((commitDef I).append P.bus.toDef).append P.table.toDef).append P.pub.toDef).append
    P.flock.toDef).append P.opening

/-- The completeness halves of the five phases, against the seams. -/
structure Phases.Complete (P : Phases I) where
  /-- The bus phase's. -/
  bus : Phase.Complete I P.bus.toDef (Seam.commit I) (Seam.bus I)
  /-- The table sumcheck's. -/
  table : Phase.Complete I P.table.toDef (Seam.bus I) (Seam.table I)
  /-- The public-input phase's. -/
  pub : Phase.Complete I P.pub.toDef (Seam.table I) (Seam.pub I)
  /-- The Flock phase's. -/
  flock : Phase.Complete I P.flock.toDef (Seam.pub I) (Seam.flock I)
  /-- The opening phase's. -/
  opening : Phase.Complete I P.opening (Seam.flock I) (Seam.done I)

/-- The whole protocol's completeness: the commit phase's, then five compositions. -/
def Phases.Complete.toDef {P : Phases I} (C : P.Complete) :
    Component.Complete P.toDef (M3Rel I) (Seam.done I) :=
  (((((commitComplete I).append C.bus).append C.table).append C.pub).append C.flock).append
    C.opening

/-- The security halves of the five phases, against the seams, at the slots' errors. -/
structure Phases.Security (P : Phases I) where
  /-- The bus phase's. -/
  bus : Phase.Security I P.bus.toDef (Seam.commit I) (Seam.bus I) (busError I)
  /-- The table sumcheck's. -/
  table : Phase.Security I P.table.toDef (Seam.bus I) (Seam.table I) (tableError I)
  /-- The public-input phase's. -/
  pub : Phase.Security I P.pub.toDef (Seam.table I) (Seam.pub I) pubError
  /-- The Flock phase's. -/
  flock : Phase.Security I P.flock.toDef (Seam.pub I) (Seam.flock I) (flockError I)
  /-- The opening phase's. -/
  opening : Phase.Security I P.opening (Seam.flock I) (Seam.done I) (openingError I)

/-- The whole protocol's security: the commit phase's, then five compositions, at
`piopError I`. `noncomputable` since the slots' errors are real numbers it takes as arguments;
its extractor is written out as `piopExtractor`, which computes. -/
noncomputable def Phases.Security.toDef {P : Phases I} (S : P.Security) :
    Component.Security P.toDef (M3Rel I) (Seam.done I) (piopError I) :=
  (((((commitSecurity I).append S.bus).append S.table).append S.pub).append S.flock).append
    S.opening

/-- The whole protocol's extraction: the commit phase's, then five compositions. It is what
`Phases.Security.toDef` carries, and it computes. -/
def Phases.Security.extraction {P : Phases I} (S : P.Security) :
    Component.Extraction P.toDef (M3Rel I) (Seam.done I) :=
  (((((commitSecurity I).toExtraction.append S.bus.toExtraction).append
    S.table.toExtraction).append S.pub.toExtraction).append S.flock.toExtraction).append
    S.opening.toExtraction

/-! ## The oracle protocol -/

/-- The oracle protocol: the commit phase, then the five phases of `P`. -/
def leanVmPiop (P : Phases I) :
    OracleReduction []ₒ I.Stmt NoOracle (Column I.μ) Unit (TheOracle I) Unit (piopSpec I) :=
  P.toDef.red

/-- Its verifier. -/
def leanVmVerifier (P : Phases I) :
    OracleVerifier []ₒ I.Stmt NoOracle Unit (TheOracle I) (piopSpec I) :=
  P.toDef.red.verifier

/-- Its honest prover. -/
def leanVmProver (P : Phases I) :
    OracleProver []ₒ I.Stmt NoOracle (Column I.μ) Unit (TheOracle I) Unit (piopSpec I) :=
  P.toDef.red.prover

/-- Its extractor: the commit phase's, which reads the stack off the first message, followed by
the five phases', each appended through the verdict of the verifiers before it. -/
def piopExtractor (P : Phases I) (S : P.Security) :
    Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0}) (I.Stmt × ∀ i, NoOracle i)
      (Column I.μ) Unit (piopSpec I) S.extraction.witMid :=
  S.extraction.extractor

/-- The stack the extractor returns on a transcript: the fold of the phases' extractors down to
the commit round. -/
def piopExtractedStack (P : Phases I) (S : P.Security) (s : I.Stmt × ∀ i, NoOracle i)
    (tr : (piopSpec I).FullTranscript) : Column I.μ :=
  Extractor.RoundByRound.extractIn (piopExtractor P S) s tr ()

/-- The first round of the protocol is the commit message. -/
private theorem zero_lt_piopRounds : 0 < piopRounds I := by
  simp only [piopRounds]
  omega

/-- The extractor's first step reads the commit message: the commit phase's step does, and a
composition keeps the first step of its first part. -/
private theorem piopExtractor_readsFirst (P : Phases I) (S : P.Security) :
    Extractor.RoundByRound.ReadsFirst (piopExtractor P S) := by
  unfold piopExtractor Phases.Security.extraction
  simp only [Component.Extraction.append, commitSecurity, Component.sendOracleSecurity]
  exact Extractor.RoundByRound.readsFirst_append _ _ _ (by omega)
    (Extractor.RoundByRound.readsFirst_append _ _ _ (by omega)
      (Extractor.RoundByRound.readsFirst_append _ _ _ (by omega)
        (Extractor.RoundByRound.readsFirst_append _ _ _ (by omega)
          (Extractor.RoundByRound.readsFirst_append _ _ _ (by omega)
            Component.sendExtractor_readsFirst))))

/-- **The extractor reads the stack.** On every transcript the extracted stack is the committed
message, the first entry of the commit phase's part of the transcript, whatever the five
phases' extractors do: the fold of the extractors ends with the first round's step, which is
the commit phase's, and that step reads its message. -/
theorem piopExtractedStack_eq (P : Phases I) (S : P.Security) (s : I.Stmt × ∀ i, NoOracle i)
    (tr : (piopSpec I).FullTranscript) :
    piopExtractedStack P S s tr = tr.fst.fst.fst.fst.fst 0 := by
  apply eq_of_heq
  refine (Extractor.RoundByRound.extractIn_heq_of_readsFirst _ (piopExtractor_readsFirst P S)
    zero_lt_piopRounds s tr ()).trans ?_
  exact ((FullTranscript.fst_heq tr.fst.fst.fst.fst 0).trans
    ((FullTranscript.fst_heq tr.fst.fst.fst _).trans ((FullTranscript.fst_heq tr.fst.fst _).trans
      ((FullTranscript.fst_heq tr.fst _).trans (FullTranscript.fst_heq tr _))))).symm

/-! ## The master theorems -/

/-- **Perfect completeness.** On every `(input, q)` with `M3Holds I input q`, the honest prover
convinces the verifier with probability one. -/
theorem piop_perfectCompleteness (P : Phases I) (C : P.Complete) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (leanVmPiop P).perfectCompleteness init impl (M3Rel I) (Seam.done I) :=
  C.toDef.complete init impl

/-- **Round-by-round knowledge soundness** at `piopError I`, for the extractor
`piopExtractor P S` (the commit phase's, then the phases') and its knowledge state function,
composed from the phases' own by a proved composition: each challenge can turn the state from
false to true with probability at most its slot's error. The extractor's stack is the committed
message (`piopExtractedStack_eq`); see the module docstring for the plain reading and what it
waits on. -/
theorem piop_rbrKnowledgeSoundness (P : Phases I) (S : P.Security) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (leanVmVerifier P).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl (M3Rel I)
      (Seam.done I) S.extraction.witMid (piopExtractor P S) (S.extraction.kSF init impl)
      (piopError I) :=
  S.toDef.rbr init impl

/-- The same with the extractor forgotten: some extractor and knowledge state function exist
(ArkLib's existential form). A soundness statement only. -/
theorem piop_rbrKnowledgeSoundness_exists (P : Phases I) (S : P.Security) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (leanVmVerifier P).toVerifier.rbrKnowledgeSoundnessWorstCase init impl (M3Rel I)
      (Seam.done I) (piopError I) :=
  ⟨_, _, _, piop_rbrKnowledgeSoundness P S init impl⟩

end
end LeanerVM.Protocol
