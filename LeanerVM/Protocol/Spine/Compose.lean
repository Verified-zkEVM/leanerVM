/-
  LeanerVM.Protocol.Spine.Compose

  The commit phase, the bundle of the five other phases, the composed oracle protocol and its two
  master theorems.
-/

module

public import LeanerVM.Protocol.ToArkLib.SendOracle
public import LeanerVM.Protocol.Spine.Phase

/-!
# The oracle protocol and its master theorems

The oracle protocol is `commit ⟫ bus ⟫ table ⟫ pub ⟫ flock ⟫ opening`. The commit phase sends
the stack as the one oracle message; it is the send-oracle component of
`LeanerVM.Protocol.ToArkLib.SendOracle` at the stack, both its proofs included. The five other
phases are the fields of a `Phases I`, to be supplied with their proofs (`Phases.Complete`,
`Phases.Security`). The protocol starts from `M3Rel I` and ends with nothing left to check.

`piop_perfectCompleteness`: given every phase's completeness, the honest prover convinces the
verifier with probability one on every stack satisfying `M3Holds`.
`piop_rbrKnowledgeSoundness`: given every phase's security and the composition theorem ArkLib
admits (`KnowledgeAppend`), the verifier is round-by-round knowledge sound at `piopError P`,
the phases' errors side by side. Its extractor begins with the commit phase's, which reads the
stack off the first message; the later phases' extractors are the identity on the trivial
witness. Its plain reading, "a straight-line extractor returns a stack satisfying `M3Holds`
except with probability the sum of `piopError`", is ArkLib's
`rbrKnowledgeSoundness_implies_knowledgeSoundness`, admitted at the pinned revision.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

@[expose] public section

variable (I : M3Instance)

/-! ## The commit phase -/

/-- The schedule of the commit phase: one prover message, the stack. -/
abbrev commitSpec : ProtocolSpec 1 := Component.sendSpec (Column I.μ)

/-- The commit phase: the prover sends the stack, the verifier keeps the statement and exposes
the message as the oracle. No challenge, error zero. -/
abbrev commitDef : Component.Def I.Stmt NoOracle (Column I.μ) I.Stmt (TheOracle I) Unit :=
  Component.sendOracle I.Stmt (Column I.μ)

/-- Its extractor: read the stack off the message. -/
abbrev commitExtractor := Component.sendExtractor (S := I.Stmt) (M := Column I.μ)

/-- Perfect completeness of the commit phase: on `M3Holds I input q`, sending `q` lands in
`Seam.commit`, which is `M3Holds` of the message. -/
def commitComplete : Component.Complete (commitDef I) (M3Rel I) (Seam.commit I) :=
  Component.sendOracleComplete (M3Rel I)

/-- Completeness and knowledge soundness of the commit phase, at error zero. -/
def commitSecurity : Component.Security (commitDef I) (M3Rel I) (Seam.commit I) :=
  Component.sendOracleSecurity (M3Rel I)

/-! ## The bundle of phases -/

/-- The five phases after the commit. -/
structure Phases where
  /-- The bus phase: from `M3Holds` of the oracle to the zerocheck claims at `ζ`, the bus forms
  and the boundary claims (§5.2 to §5.4). -/
  bus : Phase.Def I I.Stmt (I.Stmt × BusOut I)
  /-- The table sumcheck: from linear claims to column claims (§5.5). -/
  table : Phase.Def I (I.Stmt × BusOut I) (I.Stmt × TableOut I)
  /-- The public-input phase: the public cells become column claims (§8.2). -/
  pub : Phase.Def I (I.Stmt × TableOut I) (I.Stmt × PubOut I)
  /-- The Flock phase: the auxiliary predicate becomes a weighted claim (§7). -/
  flock : Phase.Def I (I.Stmt × PubOut I) (I.Stmt × FlockOut I)
  /-- The opening phase: the pool is batched and opened against the oracle (§4.1). -/
  opening : Phase.Def I (I.Stmt × FlockOut I) Unit

variable {I}

/-- The whole protocol as one component. -/
def Phases.toDef (P : Phases I) :
    Component.Def I.Stmt NoOracle (Column I.μ) Unit (TheOracle I) Unit :=
  (((((commitDef I).append P.bus).append P.table).append P.pub).append P.flock).append P.opening

/-- The completeness halves of the five phases, against the seams. -/
structure Phases.Complete (P : Phases I) where
  /-- The bus phase's. -/
  bus : Phase.Complete I P.bus (Seam.commit I) (Seam.bus I)
  /-- The table sumcheck's. -/
  table : Phase.Complete I P.table (Seam.bus I) (Seam.table I)
  /-- The public-input phase's. -/
  pub : Phase.Complete I P.pub (Seam.table I) (Seam.pub I)
  /-- The Flock phase's. -/
  flock : Phase.Complete I P.flock (Seam.pub I) (Seam.flock I)
  /-- The opening phase's. -/
  opening : Phase.Complete I P.opening (Seam.flock I) (Seam.done I)

/-- The whole protocol's completeness: the commit phase's, then five compositions. -/
def Phases.Complete.toDef {P : Phases I} (C : P.Complete) :
    Component.Complete P.toDef (M3Rel I) (Seam.done I) :=
  (((((commitComplete I).append C.bus).append C.table).append C.pub).append C.flock).append
    C.opening

/-- The security halves of the five phases, against the seams. -/
structure Phases.Security (P : Phases I) where
  /-- The bus phase's. -/
  bus : Phase.Security I P.bus (Seam.commit I) (Seam.bus I)
  /-- The table sumcheck's. -/
  table : Phase.Security I P.table (Seam.bus I) (Seam.table I)
  /-- The public-input phase's. -/
  pub : Phase.Security I P.pub (Seam.table I) (Seam.pub I)
  /-- The Flock phase's. -/
  flock : Phase.Security I P.flock (Seam.pub I) (Seam.flock I)
  /-- The opening phase's. -/
  opening : Phase.Security I P.opening (Seam.flock I) (Seam.done I)

/-- The whole protocol's security: the commit phase's, then five compositions, given
`KnowledgeAppend`. -/
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

/-- Its error per challenge: the phases' errors side by side. -/
def piopError (P : Phases I) : P.toDef.pSpec.ChallengeIdx → ℝ≥0 := P.toDef.err

/-! ## The master theorems -/

/-- **Perfect completeness.** On every `(input, q)` with `M3Holds I input q`, the honest prover
convinces the verifier with probability one. -/
theorem piop_perfectCompleteness (P : Phases I) (C : P.Complete) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (leanVmPiop P).perfectCompleteness init impl (M3Rel I) (Seam.done I) :=
  C.toDef.complete init impl

/-- **Round-by-round knowledge soundness** at `piopError P`, given `KnowledgeAppend`: a
knowledge state function and a round-by-round extractor exist, and each challenge can turn
the state from false to true with probability at most its error. The extractor's stack
satisfies `M3Holds` (see the module docstring for the plain reading and what it waits on). -/
theorem piop_rbrKnowledgeSoundness (A : KnowledgeAppend) (P : Phases I) (S : P.Security)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (leanVmVerifier P).toVerifier.rbrKnowledgeSoundnessWorstCase init impl (M3Rel I)
      (Seam.done I) (piopError P) :=
  (S.toDef A).rbr init impl

end
end LeanerVM.Protocol
