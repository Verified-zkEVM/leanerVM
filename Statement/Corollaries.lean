module

public import Statement.Theorems

/-!
# Corollaries

End statements that follow from `Statement.Theorems`, stated in their composed form: what an
accepted proof of the leanISA guest program establishes (`AggregateSound`), and the guest program's
completeness on the two simplest families of covered nodes (`GuestCompleteRecursion`,
`GuestCompleteLeaf`). `lean_vm` proves `LeanVM.corollaries_of_theorems : Statement.Theorems decode →
Statement.Corollaries decode` from the fields of `Theorems` alone, and `LeanVM.corollaries_hold`.
A reviewer who trusts `Theorems` need not read this file.
-/

@[expose] public section

open scoped ENNReal

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

/-- **The decoding `d` explains the statement `s`**: it is the deployed seed, `s` and a witness
holding `s`; or the decoded seed and statement, with the deployed seed and `s`, give a Keccak-256
collision among the candidates. -/
def Explains (guest : Program) (s : NodeStatement) (d : Decoded) : Prop :=
  (d.seed = deployedSeed guest ∧ d.statement = s ∧
      NodeRel (bytecodeWords guest) (deployedSeed guest) s d.witness) ∨
    HasCollision (collisionCandidates d.seed d.statement (deployedSeed guest) s)

open OracleComp OracleSpec in
/-- **The outer verifier's acceptance, explained.** In the random-permutation experiment of
`LeanVm.lean`, the adversary, querying `π` and `π⁻¹`, outputs a proof. The event: the verifier
accepts it as a proof of `guest` on the digest, under the deployed seed, of a statement `s` whose
deferred claim has the guest program's shape, and yet the execution the knowledge extractor
`extractorRpm` reads off the adversary's transcript and the proof does not explain `s` (`Explains`:
decode to the deployed seed, `s` and a witness holding it, or give a Keccak-256 collision among
`collisionCandidates`). It composes `KnowledgeSoundness`, `GuestKnowledge` and `DigestBinds`;
its probability is at most the bound of `KnowledgeSoundness`,
`(Q + 2^14) · 2^-128 + 5 (Q + 2^14)² · 2^-256`, for at most `Q ≤ 2^128` queries to `π`, `π⁻¹`.
Keccak-256 and Keccak-f[1600] outside the executed program are built from `π`; the statement's
digest and the collisions are of the deployed Keccak-256, which the guest program computes. -/
def AggregateSound (guest : Program) (decode : Decoder) : Prop :=
  ∀ (A : RpmAdversary) (Q : ℕ), Common.IsWeightBound A permQueries Q → Q ≤ 2 ^ 128 →
    Pr{let z ← rpmExperiment A}[∃ s : NodeStatement, z.accepted ∧ z.program = guest ∧
      publicDigest z.input = statementDigest (deployedSeed guest) s ∧
      s.defer.Shaped (bytecodeWords guest) ∧
      ¬ ∃ t, extractorRpm z.program z.input z.transcript z.proof = some t ∧
        Explains guest s (decode t.image)] ≤
      (Q + 2 ^ 14 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 128 +
        5 * (Q + 2 ^ 14 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256

end LeanVM.Node

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node LeanVM.Guest LeanVM.Guest.Hints

/-- **Every recursion node of at most `2048` claims has a valid execution of the leanISA guest
program**: for every seed, statement `s` and witness `w` with `NodeRel`, within the deployed limits
(so at most `16` children), every child one the guest program accepts (`ChildOk`), holding no raw
leanXMSS or leanSPHINCS signature and no blob directly, with at most `2048` declared claims,
coverage slots and children's declared claims, there is a valid execution of the leanISA guest program on the statement's digest of
committed size in `[2^22, 2^28]`. The first family of `Covered`. -/
abbrev GuestCompleteRecursion : Prop :=
  ∀ (seed : Digest) (s : NodeStatement) (w : NodeWitness),
    NodeRel (bytecodeWords guest) seed s w → Limits s w →
    (∀ c ∈ w.children, ChildOk (bytecodeWords guest) seed c) →
    (direct s.claims.xmss w.xmss).length = 0 → (direct s.claims.sphincs w.sphincs).length = 0 →
    (direct s.claims.da w.da).length = 0 →
    s.claims.xmss.length + s.claims.sphincs.length + s.claims.da.length ≤ 2048 →
    coverage s w ≤ 2048 →
    (w.children.map fun c ↦ c.statement.claims.xmss.length + c.statement.claims.sphincs.length +
      c.statement.claims.da.length).sum ≤ 2048 →
    ∃ t : Trace guest,
      ValidExecution guest (PublicInput.ofDigest (statementDigest seed s)) t ∧
      2 ^ 22 ≤ t.committedSize ∧ t.committedSize ≤ 2 ^ 28

/-- **Every leaf of at most `2048` raw signatures has a valid execution of the leanISA guest
program**: for every seed, statement `s` and witness `w` with `NodeRel`, within the deployed limits,
every child one the guest program accepts (vacuous here), with no child and no blob held directly, at most `2048` raw leanXMSS and leanSPHINCS signatures
together and at most `2048` declared claims and coverage slots, there is a valid execution of the
leanISA guest program on the statement's digest of committed size in `[2^22, 2^28]`. The
second family of `Covered`. -/
abbrev GuestCompleteLeaf : Prop :=
  ∀ (seed : Digest) (s : NodeStatement) (w : NodeWitness),
    NodeRel (bytecodeWords guest) seed s w → Limits s w →
    (∀ c ∈ w.children, ChildOk (bytecodeWords guest) seed c) →
    w.children = [] → (direct s.claims.da w.da).length = 0 →
    (direct s.claims.xmss w.xmss).length + (direct s.claims.sphincs w.sphincs).length ≤ 2048 →
    s.claims.xmss.length + s.claims.sphincs.length + s.claims.da.length ≤ 2048 →
    coverage s w ≤ 2048 →
    ∃ t : Trace guest,
      ValidExecution guest (PublicInput.ofDigest (statementDigest seed s)) t ∧
      2 ^ 22 ≤ t.committedSize ∧ t.committedSize ≤ 2 ^ 28

end LeanVM.Guest.Budget

namespace Statement

/-- **The corollaries**, each following from `Theorems`. -/
structure Corollaries (decode : LeanVM.Node.Decoder) : Prop where
  /-- An accepted proof of the leanISA guest program on the digest of `s` under the deployed seed
  is explained by the extracted execution (it decodes to that seed, `s` and a witness holding
  `s`) or by a Keccak-256 collision, except with the bound of `knowledgeSoundness`: from
  `knowledgeSoundness`, `guestKnowledge` and `digestBinds`. -/
  aggregateSound : LeanVM.Node.AggregateSound LeanVM.Guest.guest decode
  /-- The leanISA guest program is complete on every recursion node of at most `2048` claims
  holding no raw signature and no blob itself: from `guestCompleteCovered`. -/
  guestCompleteRecursion : LeanVM.Guest.Budget.GuestCompleteRecursion
  /-- The leanISA guest program is complete on every leaf of at most `2048` raw signatures, holding
  no blob: from `guestCompleteCovered`. -/
  guestCompleteLeaf : LeanVM.Guest.Budget.GuestCompleteLeaf

end Statement

end
