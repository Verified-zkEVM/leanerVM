# Dossier `lib-arklib`: ArkLib's framework for interactive oracle reductions at the pin

Reviewed: ArkLib at the pin `dca90385` (sources read in `.lake/packages/Arklib/`), leanerVM `main`
at `b435631`, ArkLib `origin/main` at `7653a901e` (fetched 2026-09-29, 347 commits after the pin),
ArkLib pull request #615 at its head `ca7a2577`. Every Lean statement below is copied from the
file named with it. Every probe is reproduced in the appendix with its command and its output.

**PRELIMINARY VERSION, being extended section by section. The summary is rewritten last.**

## Results established so far (evidence in the sections and the appendix)

1. leanerVM's master theorems and everything they are built from depend on the three standard
   axioms only (`propext`, `Classical.choice`, `Quot.sound`); no `sorryAx` (probe `AxiomsLeanerVM`).
2. ArkLib at the pin admits the composition of soundness, knowledge soundness and both
   round-by-round notions (`Verifier.append_*`, `Verifier.seqCompose_*`), and the implications
   from round-by-round knowledge soundness to plain knowledge soundness and soundness
   (`#print axioms` shows `sorryAx`; probe `AxiomsArkLibBuilt`; source `Security/Implications.lean`).
   They are still admitted on `origin/main`.
3. The local file `LeanerVM/Protocol/ToArkLib/KnowledgeAppend.lean` is the file of pull request
   #615 at `ca7a2577` up to the header, the module keywords, a namespace, added docstrings, two
   lemmas replaced by references to ArkLib's own, two names qualified, and the omission of the
   four wrapper theorems. Pull request #615 is open, not merged, and in conflict with `main`.
4. The notion is not vacuous: a verifier that accepts everything has no knowledge state
   function (no round), and is not knowledge sound at error 0 (one challenge), whatever the
   extractor; it is knowledge sound at error 1, as every verifier is (probe `NonVacuity`).
5. ArkLib's extractor type accepts an extractor that chooses a witness by classical choice, and
   such an extractor is "knowledge sound at error 0" for every relation whose language the
   verifier decides (probe `Extractors`): the existential form of the notion is soundness, not
   knowledge. The named form is meaningful only if the named extractor is read.
6. The three extractors of leanerVM are compiled definitions and run (probe `Extractors`).
7. `Component.Def` carries the real-valued error, so every phase definition with a challenge is
   `noncomputable`, and neither the verifier nor the extractor can be compiled when reached
   through the phase definition (probe `ExtractorsExpectedFailure`).

## D. Adequacy: what round-by-round knowledge soundness, in ArkLib's worst-case form with a named extractor, guarantees

### D.0 The statement under review

leanerVM's soundness master theorem is an instance of one ArkLib predicate,
`Verifier.rbrKnowledgeSoundnessWorstCaseWith`, applied to the verifier of the composed oracle
protocol after it has been turned into a plain verifier (`toVerifier`, section D.5):

`LeanerVM/Protocol/Spine/Compose.lean:167-177` (leanerVM `b435631`):

```lean
/-- **Round-by-round knowledge soundness** at `piopError P`, for the extractor
`piopExtractor P S` (the commit phase's, then the phases') and its knowledge state function,
composed from the phases' own by a proved composition: each challenge can turn the state from
false to true with probability at most its error. The extractor's stack satisfies `M3Holds` (see
the module docstring for the plain reading and what it waits on). -/
theorem piop_rbrKnowledgeSoundness (P : Phases I) (S : P.Security) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (leanVmVerifier P).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl (M3Rel I)
      (Seam.done I) S.toDef.witMid (piopExtractor P S) (S.toDef.kSF init impl)
      (piopError P) :=
  S.toDef.rbr init impl
```

Its arguments are: the input relation `M3Rel I` (pairs of a public input and a stack `q`), the
output relation `Seam.done I` (everything), the family of intermediate witness types
`S.toDef.witMid`, the extractor `piopExtractor P S`, the knowledge state function
`S.toDef.kSF init impl`, and the error per challenge `piopError P`. The shared oracle is empty
(`[]ₒ`). Everything below is about what this predicate says and what it does not say.

### D.1 The definition, in mathematical language

**Setting.** A protocol has `n` rounds. Each round is either a prover message of a type `M_k`
or a verifier challenge of a finite type `C_k`. A *prefix* `τ ∈ Tr_k` is the list of the first
`k` entries (messages and challenges); `Tr_n` is the set of full transcripts. Statements are
`s ∈ S`, input witnesses `W_in`, output statements `T`, output witnesses `W_out`. The relations
are `R_in ⊆ S × W_in` and `R_out ⊆ T × W_out`. The verifier is a function
`V : S × Tr_n → (computation with failure) T`; *accepting* means returning some `t ∈ T`, and
*rejecting* means failing.

**The extractor** (ArkLib `Extractor.RoundByRound`) is a family of intermediate witness types
`W_0, …, W_n` with `W_0 = W_in`, and functions

* `extractOut : S × Tr_n × W_out → W_n` (from the output witness to the last intermediate witness),
* `extractMid_k : S × Tr_{k+1} × W_{k+1} → W_k` for every round `k < n` (one round backwards).

It has no law of its own. It is given no query log, no access to the shared oracle and no
randomness, and nothing bounds its running time.

`.lake/packages/Arklib/ArkLib/OracleReduction/Security/RoundByRound.lean:77-86` (ArkLib `dca90385`):

```lean
structure RoundByRound
    (oSpec : OracleSpec ι) (StmtIn WitIn WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    (WitMid : Fin (n + 1) → Type) where
  /-- The first intermediate witness type is equal to the input witness type -/
  eqIn : WitMid 0 = WitIn
  /-- Extract intermediate witness for round `m` from intermediate witness for round `m+1`,
    using the transcript up to round `m+1` -/
  extractMid : (m : Fin n) → StmtIn → Transcript m.succ pSpec → WitMid m.succ → WitMid m.castSucc
  /-- Construct the intermediate witness for the final round from the output witness -/
  extractOut : StmtIn → FullTranscript pSpec → WitOut → WitMid (.last n)
```

**The knowledge state function** (ArkLib `Verifier.KnowledgeStateFunction`) is a family of
predicates `K_k ⊆ S × Tr_k × W_k`, `k = 0, …, n`, with three laws:

1. *Start* (`toFun_empty`): for all `s` and `w ∈ W_0`: `(s, w) ∈ R_in ⟺ K_0(s, ∅, w)`.
2. *Prover rounds* (`toFun_next`): for every round `k` that is a prover message, all `s`,
   `τ ∈ Tr_k`, messages `m ∈ M_k` and `w ∈ W_{k+1}`:
   `K_{k+1}(s, τ‖m, w) ⟹ K_k(s, τ, extractMid_k(s, τ‖m, w))`.
   No prover message can make the state true unless the witness extracted one round back was
   already good.
3. *End* (`toFun_full`): for all `s`, full `τ` and `w_out`: if the probability that `V(s, τ)`
   returns some `t` with `(t, w_out) ∈ R_out` is positive, then
   `K_n(s, τ, extractOut(s, τ, w_out))`. The probability is over the initial state of the
   shared oracle (drawn by `init`) and the oracle's answers (`impl`); for a verifier that makes
   no query to a shared oracle it is 0 or 1.

`.lake/packages/Arklib/ArkLib/OracleReduction/Security/RoundByRound.lean:164-189` (ArkLib `dca90385`):

```lean
structure KnowledgeStateFunction
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    {WitMid : Fin (n + 1) → Type}
    (extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    where
  /-- The knowledge state function: takes in round index, input statement, transcript up to that
      round, and intermediate witness of that round, and returns True/False. -/
  toFun : (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → WitMid m → Prop
  /-- The input statement and witness are in the input relation if and only if the state function is
      true for the empty transcript and the input witness -/
  toFun_empty : ∀ stmtIn witMid,
    ⟨stmtIn, cast extractor.eqIn witMid⟩ ∈ relIn ↔ toFun 0 stmtIn default witMid
  /-- If the state function is true for a partial transcript extended with a prover message, then
    the state function is also true for the original partial transcript with the extracted
    intermediate witness -/
  toFun_next : ∀ m, pSpec.dir m = .P_to_V →
    ∀ stmtIn tr msg witMid, toFun m.succ stmtIn (tr.concat msg) witMid →
      toFun m.castSucc stmtIn tr (extractor.extractMid m stmtIn (tr.concat msg) witMid)
  /-- If the verifier can output a statement `stmtOut` that is in the output relation with some
    output witness `witOut`, then the state function is true for the full transcript and the
    extracted last middle witness. -/
  toFun_full : ∀ stmtIn tr witOut,
    Pr[fun stmtOut => (stmtOut, witOut) ∈ relOut
    | OptionT.mk do (simulateQ impl (verifier.run stmtIn tr)).run' (← init)] > 0 →
    toFun (.last n) stmtIn tr (extractor.extractOut stmtIn tr witOut)
```

**The bound** (ArkLib `Verifier.rbrKnowledgeSoundnessWorstCaseWith`). For a statement `s`, a
verifier round `k` and a prefix `τ ∈ Tr_k`, call *bad set* the set of challenges

    Bad_k(s, τ) = { c ∈ C_k : ∃ w ∈ W_{k+1},  K_{k+1}(s, τ‖c, w)  ∧  ¬ K_k(s, τ, extractMid_k(s, τ‖c, w)) }.

The predicate says: for **every** statement `s`, **every** verifier round `k` and **every**
prefix `τ ∈ Tr_k`,

    Pr_{c ← C_k uniform} [ c ∈ Bad_k(s, τ) ]  ≤  ε_k.

`.lake/packages/Arklib/ArkLib/OracleReduction/Security/RoundByRound.lean:551-568` (ArkLib `dca90385`):

```lean
/-- Worst-case-per-prefix RBR knowledge soundness for one exact
intermediate-witness family, extractor, and knowledge-state function. -/
def rbrKnowledgeSoundnessWorstCaseWith
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (WitMid : Fin (n + 1) → Type)
    (extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  ∀ stmtIn : StmtIn,
  ∀ i : pSpec.ChallengeIdx,
  ∀ transcript : Transcript i.1.castSucc pSpec,
    Pr[fun challenge =>
      ∃ witMid,
        ¬ kSF i.1.castSucc stmtIn transcript
          (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
          kSF i.1.succ stmtIn (transcript.concat challenge) witMid
      | $ᵗ (pSpec.Challenge i)] ≤ rbrKnowledgeError i
```

**What is quantified over, and what is not.**

| Object | Quantified how |
| --- | --- |
| Statements `s` | universally, including the statements that have a valid witness |
| Verifier rounds `k` | universally; each has its own error `ε_k` |
| Prefixes `τ` | universally: every list of prover messages and earlier challenges, whether or not any prover could reach it with noticeable probability |
| Intermediate witnesses `w` | existentially inside the event: the worst one counts |
| The challenge `c` | the only random variable: uniform on `C_k` (the `SampleableType` instance; its two laws, full support and equal probabilities, force the uniform distribution on a finite type, `VCVio/OracleComp/Constructions/SampleableType.lean:44-47`) |
| Provers | **not at all**: no prover, no prover state and no input witness appears |
| The shared oracle | only inside law 3 (can the verifier accept). The state function and the extractor cannot depend on the oracle's state or on a query log |
| `WitMid`, the extractor, the state function | named arguments of the predicate ("With"); in `rbrKnowledgeSoundnessWorstCase` they are existentially quantified |

**What "worst case" adds.** ArkLib's older predicate `rbrKnowledgeSoundness` bounds the same
event in a game: a prover is run against the challenger up to round `k`, which produces the
prefix, then the challenge is drawn, and the bound is on the probability over the whole game
(so it is an average over the earlier challenges). It quantifies over provers, and the prefix
is a random variable:

`.lake/packages/Arklib/ArkLib/OracleReduction/Security/RoundByRound.lean:416-437` (ArkLib `dca90385`):

```lean
def rbrKnowledgeSoundness (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  ∃ WitMid : Fin (n + 1) → Type,
  ∃ extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid,
  ∃ kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor,
  ∀ stmtIn : StmtIn,
  ∀ witIn : WitIn,
  ∀ prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec,
  ∀ i : pSpec.ChallengeIdx,
    Pr[fun ⟨transcript, challenge, _proveQueryLog⟩ =>
      ∃ witMid,
        ¬ kSF i.1.castSucc stmtIn transcript
          (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
          kSF i.1.succ stmtIn (transcript.concat challenge) witMid
    | do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (do
          let ⟨⟨transcript, _⟩, proveQueryLog⟩ ← prover.runWithLogToRound i.1.castSucc stmtIn witIn
          let challenge ← liftComp (pSpec.getChallenge i) _
          return (transcript, challenge, proveQueryLog))).run' (← init)] ≤
      rbrKnowledgeError i
```

The worst-case form implies the averaged one with the same errors (proved:
`Verifier.rbrKnowledgeSoundnessWorstCaseWith_implies_rbrKnowledgeSoundnessWith`,
`Security/RoundByRound.lean:625`, three standard axioms, probe `AxiomsArkLibBuilt`). The
converse fails: from the averaged bound at round `k` one gets, for one fixed value of the earlier
challenges, only `ε_k` multiplied by the inverse probability of those challenges. The difference
matters exactly where it should: a Fiat–Shamir (state-restoration) prover chooses among many
prefixes, so it needs the bound at every prefix, which only the worst-case form gives. The
worst-case form is the one of the literature (D.2), and the one leanerVM states.

**The plain reading, proved by probe.** Run the extractor backwards along a full transcript
`τ`: `w_n = extractOut(s, τ, w_out)`, `w_k = extractMid_k(s, τ_{≤k}, w_{k+1})`, and write
`Ext(s, τ, w_out) = w_0 ∈ W_in`. Then, for any verifier, extractor and knowledge state
function, with **no** hypothesis on the errors:

> for all `s`, `τ`, `w_out`: if `V` can accept `(s, τ)` with an output `t` such that
> `(t, w_out) ∈ R_out`, then `(s, Ext(s, τ, w_out)) ∈ R_in`, **or** there is a verifier round
> `k` of `τ` whose challenge `τ_k` lies in `Bad_k(s, τ_{<k})`.

This is `Probe.accept_imp_extract_or_bad` of the probe `PlainReading` (appendix), proved in 40
lines by induction on the round, on the three standard axioms. With the bound of the
predicate, each bad set has probability at most `ε_k`. So the predicate reduces knowledge
soundness to: "no challenge of the accepted transcript fell in the bad set of its prefix".
What remains to get a statement about a prover is a union bound over the verifier rounds
(interactive prover: `Σ_k ε_k`) or over the prover's queries (Fiat–Shamir prover with `Q`
queries: about `Q · max_k ε_k`). That last step is what ArkLib admits (D.3); it is a
statement about ArkLib's execution semantics, not about the protocol.

**Instantiated to leanVM.** `S` is the public input (there is no input oracle), `W_in` is the
stack `q`, the first message is the stack, `W_out` is trivial and `R_out` is everything. The
commit phase's extractor returns the first message whatever intermediate witness it is handed
(`Component.sendExtractor`, `LeanerVM/Protocol/ToArkLib/SendOracle.lean:134-138`), so
`Ext(s, τ, ()) = τ_0`. The master theorem therefore reads: *for every public input and every
transcript, if the verifier accepts then the stack sent as the first message satisfies
`M3Holds`, unless some challenge of the transcript lies in the bad set of its prefix; and every
bad set has probability at most `piopError` of its round.* At the level of the oracle protocol
this is a soundness statement about the committed oracle. The extraction of the stack from a
commitment is not in it: it belongs to the compiled protocol (WHIR, Merkle trees, the random
oracle), which the blueprint places in Layers 11 and 12 behind assumed interfaces.

## Appendix: the probes

Every probe was run from the root of leanerVM (`main` at `b435631`, ArkLib at the pin
`dca90385`) with

    flock .claude/reports/blueprint-review/logs/lean.lock lake env lean .claude/reports/blueprint-review/probes/lib-arklib/<File>.lean

The output is reproduced after each source. Axioms reported as `[propext, Classical.choice,
Quot.sound]` are the three standard axioms of Lean and Mathlib; `sorryAx` marks an admitted proof.

### Probe `AxiomsLeanerVM`

Source (`probes/lib-arklib/AxiomsLeanerVM.lean`):

```lean
import LeanerVM.Protocol.Spine.Compose
import LeanerVM.Protocol.PublicInput

/-! Probe B1: `#print axioms` of leanerVM's master theorems, phases and composition. -/

open LeanerVM.Protocol

#print axioms LeanerVM.Protocol.piop_perfectCompleteness
#print axioms LeanerVM.Protocol.piop_rbrKnowledgeSoundness
#print axioms LeanerVM.Protocol.piop_rbrKnowledgeSoundness_exists
#print axioms LeanerVM.Protocol.commitSecurity
#print axioms LeanerVM.Protocol.commitComplete
#print axioms LeanerVM.Protocol.publicInputSecurity
#print axioms LeanerVM.Protocol.publicInputComplete
#print axioms LeanerVM.Protocol.Component.Security.append
#print axioms LeanerVM.Protocol.Component.Complete.append
#print axioms LeanerVM.Protocol.Verifier.KnowledgeStateFunction.appendGuarded
#print axioms LeanerVM.Protocol.Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first
#print axioms LeanerVM.Protocol.piopExtractor
#print axioms LeanerVM.Protocol.commitExtractor
#print axioms LeanerVM.Protocol.PublicInput.extractor
#print axioms LeanerVM.Protocol.Component.sendExtractor
#print axioms LeanerVM.Protocol.Phases.Security.toDef
#print axioms LeanerVM.Protocol.Phases.Complete.toDef
```

Output:

```text
'LeanerVM.Protocol.piop_perfectCompleteness' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.piop_rbrKnowledgeSoundness' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.piop_rbrKnowledgeSoundness_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.commitSecurity' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.commitComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.publicInputSecurity' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.publicInputComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Component.Security.append' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Component.Complete.append' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Verifier.KnowledgeStateFunction.appendGuarded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'LeanerVM.Protocol.Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'LeanerVM.Protocol.piopExtractor' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.commitExtractor' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.PublicInput.extractor' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Component.sendExtractor' depends on axioms: [propext, Quot.sound]
'LeanerVM.Protocol.Phases.Security.toDef' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Phases.Complete.toDef' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```

### Probe `AxiomsArkLibBuilt`

Source (`probes/lib-arklib/AxiomsArkLibBuilt.lean`):

```lean
import LeanerVM.Protocol.Spine.Compose
import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.OracleReduction.Composition.Sequential.General
import ArkLib.OracleReduction.Composition.Sequential.GuardedNary
import ArkLib.OracleReduction.Composition.Sequential.OracleCompleteness
import ArkLib.OracleReduction.Composition.Sequential.Append.RoundByRound
import ArkLib.Data.MvPolynomial.SchwartzZippelCounting

/-! Probe B2: `#print axioms` of the ArkLib declarations the blueprint cites, for the modules
that leanerVM's build contains (ArkLib at the pin `dca90385`). -/

-- definitions
#print axioms Reduction.completeness
#print axioms Reduction.perfectCompleteness
#print axioms OracleReduction.perfectCompleteness
#print axioms Verifier.soundness
#print axioms Verifier.knowledgeSoundness
#print axioms Extractor.Straightline
#print axioms Verifier.StateFunction
#print axioms Verifier.KnowledgeStateFunction
#print axioms Extractor.RoundByRound
#print axioms Verifier.rbrSoundness
#print axioms Verifier.rbrKnowledgeSoundness
#print axioms Verifier.rbrKnowledgeSoundnessWorstCase
#print axioms Verifier.rbrKnowledgeSoundnessWorstCaseWith
#print axioms Verifier.GuardedForm
#print axioms Prover.OutputIsPure
#print axioms OracleVerifier.toVerifier
#print axioms OracleReduction.append
#print axioms OracleReduction.seqCompose
#print axioms ProtocolSpec.seqCompose
#print axioms Extractor.RoundByRound.append
#print axioms Verifier.StateFunction.append
#print axioms Verifier.GuardedForm.append
-- proved theorems
#print axioms Verifier.rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness
#print axioms Verifier.rbrSoundnessWorstCase_implies_rbrSoundness
#print axioms Verifier.rbrKnowledgeSoundnessWorstCaseWith_implies_rbrKnowledgeSoundnessWith
#print axioms ProtocolSpec.probEvent_simulateQ_addLift_getChallenge_bind_le
#print axioms Reduction.perfectCompleteness_of_run_support
#print axioms OracleReduction.append_perfectCompleteness_of_pure_verifiers
#print axioms OracleReduction.append_perfectCompleteness_of_guarded_verifiers
#print axioms OracleReduction.append_completeness_of_guarded_verifiers
#print axioms OracleReduction.seqCompose_completeness_of_guarded_verifiers
#print axioms OracleReduction.seqCompose_perfectCompleteness_of_guarded_verifiers
#print axioms Reduction.seqCompose_completeness_of_guarded_verifiers
#print axioms Reduction.append_completeness_of_guarded_verifiers
#print axioms Reduction.append_completeness_of_guarded_prover_factorization
#print axioms Verifier.append_rbrSoundnessWorstCase_of_pure_first
#print axioms Prover.OutputIsPure.append
#print axioms OracleVerifier.append_toVerifier
#print axioms MvPolynomial.schwartz_zippel_counting
#print axioms prob_eval_zero_le_div
#print axioms MvPolynomial.prob_eval_zero_le_div
-- admitted at the pin
#print axioms Verifier.append_soundness
#print axioms Verifier.append_knowledgeSoundness
#print axioms Verifier.append_rbrSoundness
#print axioms Verifier.append_rbrKnowledgeSoundness
#print axioms OracleVerifier.append_rbrKnowledgeSoundness
#print axioms Verifier.seqCompose_soundness
#print axioms Verifier.seqCompose_knowledgeSoundness
#print axioms Verifier.seqCompose_rbrSoundness
#print axioms Verifier.seqCompose_rbrKnowledgeSoundness
#print axioms OracleVerifier.seqCompose_rbrKnowledgeSoundness
#print axioms OracleVerifier.numQueries
```

Output:

```text
'Reduction.completeness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Reduction.perfectCompleteness' depends on axioms: [propext, Classical.choice, Quot.sound]
'OracleReduction.perfectCompleteness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Verifier.soundness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Verifier.knowledgeSoundness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Extractor.Straightline' does not depend on any axioms
'Verifier.StateFunction' depends on axioms: [propext, Classical.choice, Quot.sound]
'Verifier.KnowledgeStateFunction' depends on axioms: [propext, Classical.choice, Quot.sound]
'Extractor.RoundByRound' depends on axioms: [propext, Quot.sound]
'Verifier.rbrSoundness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Verifier.rbrKnowledgeSoundness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Verifier.rbrKnowledgeSoundnessWorstCase' depends on axioms: [propext, Classical.choice, Quot.sound]
'Verifier.rbrKnowledgeSoundnessWorstCaseWith' depends on axioms: [propext, Classical.choice, Quot.sound]
'Verifier.GuardedForm' does not depend on any axioms
'Prover.OutputIsPure' depends on axioms: [propext]
'OracleVerifier.toVerifier' does not depend on any axioms
'OracleReduction.append' depends on axioms: [propext, Classical.choice, Quot.sound]
'OracleReduction.seqCompose' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProtocolSpec.seqCompose' depends on axioms: [propext]
'Extractor.RoundByRound.append' depends on axioms: [propext, Classical.choice, Quot.sound]
'Verifier.StateFunction.append' depends on axioms: [propext, Classical.choice, Quot.sound]
'Verifier.GuardedForm.append' depends on axioms: [propext, Classical.choice, Quot.sound]
'Verifier.rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Verifier.rbrSoundnessWorstCase_implies_rbrSoundness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Verifier.rbrKnowledgeSoundnessWorstCaseWith_implies_rbrKnowledgeSoundnessWith' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ProtocolSpec.probEvent_simulateQ_addLift_getChallenge_bind_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Reduction.perfectCompleteness_of_run_support' depends on axioms: [propext, Classical.choice, Quot.sound]
'OracleReduction.append_perfectCompleteness_of_pure_verifiers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'OracleReduction.append_perfectCompleteness_of_guarded_verifiers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'OracleReduction.append_completeness_of_guarded_verifiers' depends on axioms: [propext, Classical.choice, Quot.sound]
'OracleReduction.seqCompose_completeness_of_guarded_verifiers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'OracleReduction.seqCompose_perfectCompleteness_of_guarded_verifiers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Reduction.seqCompose_completeness_of_guarded_verifiers' depends on axioms: [propext, Classical.choice, Quot.sound]
'Reduction.append_completeness_of_guarded_verifiers' depends on axioms: [propext, Classical.choice, Quot.sound]
'Reduction.append_completeness_of_guarded_prover_factorization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Verifier.append_rbrSoundnessWorstCase_of_pure_first' depends on axioms: [propext, Classical.choice, Quot.sound]
'Prover.OutputIsPure.append' depends on axioms: [propext, Classical.choice, Quot.sound]
'OracleVerifier.append_toVerifier' depends on axioms: [propext, Classical.choice, Quot.sound]
.claude/reports/blueprint-review/probes/lib-arklib/AxiomsArkLibBuilt.lean:52:14: error(lean.unknownIdentifier): Unknown constant `MvPolynomial.schwartz_zippel_counting`
'prob_eval_zero_le_div' depends on axioms: [propext, Classical.choice, Quot.sound]
.claude/reports/blueprint-review/probes/lib-arklib/AxiomsArkLibBuilt.lean:54:14: error(lean.unknownIdentifier): Unknown constant `MvPolynomial.prob_eval_zero_le_div`
'Verifier.append_soundness' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Verifier.append_knowledgeSoundness' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Verifier.append_rbrSoundness' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Verifier.append_rbrKnowledgeSoundness' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'OracleVerifier.append_rbrKnowledgeSoundness' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Verifier.seqCompose_soundness' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Verifier.seqCompose_knowledgeSoundness' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Verifier.seqCompose_rbrSoundness' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Verifier.seqCompose_rbrKnowledgeSoundness' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'OracleVerifier.seqCompose_rbrKnowledgeSoundness' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'OracleVerifier.numQueries' depends on axioms: [sorryAx]
exit=1   (the two `Unknown constant` lines are the only errors: the names the blueprint gives do not exist)
```

### Probe `NonVacuity`

Source (`probes/lib-arklib/NonVacuity.lean`):

```lean
import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Guarded
import LeanerVM.Protocol.ToArkLib.GuardedVerdict

/-! Probe D4: non-vacuity of ArkLib's round-by-round knowledge soundness (pin `dca90385`).

Relation: the statement is a bit, and only `true` has a witness. -/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Probe

variable {ι : Type} {oSpec : OracleSpec ι}
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Only the statement `true` has a witness. -/
def relIn : Set (Bool × Unit) := {p | p.1 = true}

/-- The trivial output relation: everything. -/
def relOut : Set (Unit × Unit) := Set.univ

/-! ## (a0) No round: the accept-everything verifier has no knowledge state function at all. -/

/-- The verifier with no round that accepts every statement. -/
def acceptAll0 : Verifier oSpec Bool Unit !p[] where
  verify := fun _ _ => pure ()

theorem acceptAll0_no_stateFunction {W : Fin 1 → Type}
    (E : Extractor.RoundByRound oSpec Bool Unit Unit !p[] W) :
    IsEmpty ((acceptAll0 (oSpec := oSpec)).KnowledgeStateFunction init impl relIn relOut E) := by
  refine ⟨fun K => ?_⟩
  have hacc : Pr[fun t => (t, ()) ∈ relOut | OptionT.mk do
      (simulateQ impl ((acceptAll0 (oSpec := oSpec)).run false default)).run' (← init)] > 0 := by
    have h1 := Verifier.guarded_accepting_of_mem init impl (acceptAll0 (oSpec := oSpec))
      (fun _ _ => true) (fun _ _ => ()) (fun _ _ => by simp [acceptAll0]) false default rfl
      {t | (t, ()) ∈ relOut} (by simp [relOut])
    exact lt_of_lt_of_eq zero_lt_one h1.symm
  have hfull := K.toFun_full false default () hacc
  have hin := (K.toFun_empty false (E.extractOut false default ())).mpr hfull
  simp [relIn] at hin

/-! ## (a1) One challenge: the accept-everything verifier is not knowledge sound at error 0,
whatever the extractor and the state function. -/

/-- One verifier challenge, a bit. -/
@[reducible] def pSpec1 : ProtocolSpec 1 := ⟨!v[.V_to_P], !v[Bool]⟩

instance : ∀ i, SampleableType (pSpec1.Challenge i)
  | ⟨0, _⟩ => (inferInstance : SampleableType Bool)

/-- The verifier with one challenge that accepts every statement. -/
def acceptAll1 : Verifier oSpec Bool Unit pSpec1 where
  verify := fun _ _ => pure ()

theorem acceptAll1_full {W : Fin 2 → Type}
    {E : Extractor.RoundByRound oSpec Bool Unit Unit pSpec1 W}
    (K : (acceptAll1 (oSpec := oSpec)).KnowledgeStateFunction init impl relIn relOut E)
    (s : Bool) (tr : pSpec1.FullTranscript) :
    K (Fin.last 1) s tr (E.extractOut s tr ()) := by
  apply K.toFun_full
  have h1 := Verifier.guarded_accepting_of_mem init impl (acceptAll1 (oSpec := oSpec))
    (fun _ _ => true) (fun _ _ => ()) (fun _ _ => by simp [acceptAll1]) s tr rfl
    {t | (t, ()) ∈ relOut} (by simp [relOut])
  exact lt_of_lt_of_eq zero_lt_one h1.symm

theorem acceptAll1_not_sound_at_zero {W : Fin 2 → Type}
    (E : Extractor.RoundByRound oSpec Bool Unit Unit pSpec1 W)
    (K : (acceptAll1 (oSpec := oSpec)).KnowledgeStateFunction init impl relIn relOut E) :
    ¬ (acceptAll1 (oSpec := oSpec)).rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut
      W E K (fun _ => 0) := by
  intro h
  have h0 := h false ⟨0, rfl⟩ (show Transcript (0 : Fin 2) pSpec1 from default)
  simp only [ENNReal.coe_zero, nonpos_iff_eq_zero] at h0
  rw [probEvent_eq_zero_iff] at h0
  refine h0 true (by rw [support_uniformSample]; trivial) ?_
  refine ⟨E.extractOut false _ (), ?_, acceptAll1_full init impl K false _⟩
  intro hk
  have hin := (K.toFun_empty false _).mpr hk
  simp [relIn] at hin

/-- It is knowledge sound at error 1, as every verifier with a challenge is: the error is what
carries the content. -/
def acceptAll1_extractor : Extractor.RoundByRound oSpec Bool Unit Unit pSpec1 (fun _ => Unit) where
  eqIn := rfl
  extractMid := fun _ _ _ _ => ()
  extractOut := fun _ _ _ => ()

def acceptAll1_stateFunction :
    (acceptAll1 (oSpec := oSpec)).KnowledgeStateFunction init impl relIn relOut
      acceptAll1_extractor where
  toFun := fun m s _ _ => if m.val = 0 then s = true else True
  toFun_empty := fun s w => by simp [relIn]
  toFun_next := fun m hm => by
    have : m = 0 := Subsingleton.elim _ _
    subst this
    exact absurd hm (by decide)
  toFun_full := fun s tr w _ => by simp

theorem acceptAll1_sound_at_one :
    (acceptAll1 (oSpec := oSpec)).rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut
      (fun _ => Unit) acceptAll1_extractor (acceptAll1_stateFunction init impl) (fun _ => 1) := by
  intro s i tr
  simp

/-! ## Positive control: the verifier that checks the bit is knowledge sound at error 0. -/

/-- The verifier with one challenge that accepts `true` only. -/
def checkBit : Verifier oSpec Bool Unit pSpec1 where
  verify := fun s _ => if s then pure () else failure

def checkBit_guarded : (checkBit (oSpec := oSpec)).GuardedForm where
  check := fun s _ => s
  out := fun _ _ => ()
  verify_eq := fun s tr => by simp [checkBit]

def checkBit_stateFunction :
    (checkBit (oSpec := oSpec)).KnowledgeStateFunction init impl relIn relOut
      acceptAll1_extractor where
  toFun := fun _ s _ _ => s = true
  toFun_empty := fun s w => by simp [relIn]
  toFun_next := fun m hm => by
    have : m = 0 := Subsingleton.elim _ _
    subst this
    exact absurd hm (by decide)
  toFun_full := fun s tr w h =>
    (LeanerVM.Protocol.Verifier.GuardedForm.of_probEvent_pos checkBit_guarded init impl s tr _ h).1

theorem checkBit_sound_at_zero :
    (checkBit (oSpec := oSpec)).rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut
      (fun _ => Unit) acceptAll1_extractor (checkBit_stateFunction init impl) (fun _ => 0) := by
  intro s i tr
  simp only [ENNReal.coe_zero, nonpos_iff_eq_zero]
  rw [probEvent_eq_zero_iff]
  rintro c - ⟨w, h1, h2⟩
  exact h1 h2

/-! ## (b) A knowledge state function is neither constantly true nor constantly false, as soon
as the relation has a statement with a witness and one without. -/

theorem stateFunction_false_at {S WI T WO : Type} {n : ℕ} {p : ProtocolSpec n}
    {V : Verifier oSpec S T p} {W : Fin (n + 1) → Type} {R : Set (S × WI)} {R' : Set (T × WO)}
    {E : Extractor.RoundByRound oSpec S WI WO p W}
    (K : V.KnowledgeStateFunction init impl R R' E) (s : S) (hs : ∀ w, (s, w) ∉ R)
    (w : W 0) : ¬ K 0 s default w :=
  fun h => hs _ ((K.toFun_empty s w).mpr h)

theorem stateFunction_true_at {S WI T WO : Type} {n : ℕ} {p : ProtocolSpec n}
    {V : Verifier oSpec S T p} {W : Fin (n + 1) → Type} {R : Set (S × WI)} {R' : Set (T × WO)}
    {E : Extractor.RoundByRound oSpec S WI WO p W}
    (K : V.KnowledgeStateFunction init impl R R' E) (s : S) (w : W 0)
    (h : (s, cast E.eqIn w) ∈ R) : K 0 s default w :=
  (K.toFun_empty s w).mp h

/-! ## (c) With the output relation everything, the last law of a knowledge state function of
a guarded verifier says exactly: if the check passes, the state is true at the extracted
witness. -/

theorem full_iff_of_univ {S WI T WO : Type} {n : ℕ} {p : ProtocolSpec n}
    [∀ i, SampleableType (p.Challenge i)] {V : Verifier oSpec S T p} (G : V.GuardedForm) {W : Fin (n + 1) → Type}
    {E : Extractor.RoundByRound oSpec S WI WO p W}
    (F : S → p.FullTranscript → W (Fin.last n) → Prop) :
    (∀ s tr w, Pr[fun t => (t, w) ∈ (Set.univ : Set (T × WO)) | OptionT.mk do
        (simulateQ impl (V.run s tr)).run' (← init)] > 0 → F s tr (E.extractOut s tr w)) ↔
      ∀ s tr w, G.check s tr = true → F s tr (E.extractOut s tr w) := by
  constructor
  · intro h s tr w hc
    apply h
    have h1 := Verifier.guarded_accepting_of_mem init impl V G.check G.out G.verify_eq s tr hc
      {t | (t, w) ∈ (Set.univ : Set (T × WO))} (by simp)
    exact lt_of_lt_of_eq zero_lt_one h1.symm
  · intro h s tr w hp
    exact h s tr w
      (LeanerVM.Protocol.Verifier.GuardedForm.of_probEvent_pos G init impl s tr _ hp).1

end Probe

#print axioms Probe.acceptAll0_no_stateFunction
#print axioms Probe.acceptAll1_not_sound_at_zero
#print axioms Probe.acceptAll1_sound_at_one
#print axioms Probe.checkBit_sound_at_zero
#print axioms Probe.full_iff_of_univ
```

Output:

```text
'Probe.acceptAll0_no_stateFunction' depends on axioms: [propext, Classical.choice, Quot.sound]
'Probe.acceptAll1_not_sound_at_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Probe.acceptAll1_sound_at_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Probe.checkBit_sound_at_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Probe.full_iff_of_univ' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```

### Probe `PlainReading`

Source (`probes/lib-arklib/PlainReading.lean`):

```lean
import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.Data.MvPolynomial.SchwartzZippelCounting

/-! Probe D3: the transcript-level reading of ArkLib's round-by-round knowledge soundness
(pin `dca90385`), proved here because ArkLib admits `rbrKnowledgeSoundness_implies_knowledgeSoundness`.

For a verifier `V`, an extractor `E` and a knowledge state function `K`:
if `V` can accept a full transcript with an output in the output relation, then either the
witness computed from the transcript by running `E` backwards is in the input relation, or, at
some verifier round of that transcript, the challenge is in the bad set of the prefix before it.
`rbrKnowledgeSoundnessWorstCaseWith` is the statement that every bad set has probability at most
the error of its round. No probability is used in the implication itself. -/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Probe

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ}
  {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
  {V : Verifier oSpec StmtIn StmtOut pSpec} {W : Fin (n + 1) → Type}
  {E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec W}

/-- The straight-line extractor read off a round-by-round extractor: from the intermediate
witness after round `m`, back to an input witness, one round at a time. -/
def toInput (E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec W) (s : StmtIn) :
    (m : Fin (n + 1)) → Transcript m pSpec → W m → WitIn :=
  Fin.induction (fun _ w => cast E.eqIn w)
    (fun m ih tr w => ih (Fin.init tr) (E.extractMid m s tr w))

/-- The bad challenges after a prefix, at the verifier round `j`. -/
def badSet (K : V.KnowledgeStateFunction init impl relIn relOut E) (s : StmtIn)
    (j : pSpec.ChallengeIdx) (pre : Transcript j.1.castSucc pSpec) : Set (pSpec.Challenge j) :=
  {c | ∃ w, ¬ K j.1.castSucc s pre (E.extractMid j.1 s (pre.concat c) w) ∧
    K j.1.succ s (pre.concat c) w}

/-- Worst-case round-by-round knowledge soundness is: every bad set has probability at most the
error of its round. By definition. -/
theorem rbr_iff_badSet (K : V.KnowledgeStateFunction init impl relIn relOut E)
    (ε : pSpec.ChallengeIdx → ℝ≥0) :
    V.rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut W E K ε ↔
      ∀ s j pre, Pr[fun c => c ∈ badSet K s j pre | $ᵗ (pSpec.Challenge j)] ≤ ε j :=
  Iff.rfl

/-- Some verifier round before round `m` of the transcript has its challenge in the bad set of
the prefix before it. -/
def badSomewhere (K : V.KnowledgeStateFunction init impl relIn relOut E) (s : StmtIn) :
    (m : Fin (n + 1)) → Transcript m pSpec → Prop :=
  Fin.induction (fun _ => False)
    (fun m ih tr =>
      (∃ h : pSpec.dir m = .V_to_P,
        (tr (Fin.last m) : pSpec.Challenge ⟨m, h⟩) ∈ badSet K s ⟨m, h⟩ (Fin.init tr)) ∨
      ih (Fin.init tr))

/-- A true state after round `m` yields a valid extracted input witness, unless a challenge
before round `m` was bad. -/
theorem state_imp (K : V.KnowledgeStateFunction init impl relIn relOut E) (s : StmtIn) :
    ∀ (m : Fin (n + 1)) (tr : Transcript m pSpec) (w : W m), K m s tr w →
      (s, toInput E s m tr w) ∈ relIn ∨ badSomewhere K s m tr := by
  intro m
  induction m using Fin.induction with
  | zero =>
    intro tr w h
    left
    have htr : tr = default := Subsingleton.elim _ _
    subst htr
    simpa [toInput] using (K.toFun_empty s w).mpr h
  | succ m ih =>
    intro tr w h
    have htr : Transcript.concat (tr (Fin.last m)) (Fin.init tr) = tr := Fin.snoc_init_self tr
    simp only [toInput, badSomewhere, Fin.induction_succ]
    by_cases hprev : K m.castSucc s (Fin.init tr) (E.extractMid m s tr w)
    · rcases ih _ _ hprev with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (Or.inr h2)
    · refine Or.inr (Or.inl ?_)
      have h' : K m.succ s (Transcript.concat (tr (Fin.last m)) (Fin.init tr)) w :=
        (congrArg (fun t : Transcript m.succ pSpec => K m.succ s t w) htr).mpr h
      have hprev' : ¬ K m.castSucc s (Fin.init tr)
          (E.extractMid m s (Transcript.concat (tr (Fin.last m)) (Fin.init tr)) w) :=
        (congrArg (fun t : Transcript m.succ pSpec =>
          ¬ K m.castSucc s (Fin.init tr) (E.extractMid m s t w)) htr).mpr hprev
      by_cases hdir : pSpec.dir m = .V_to_P
      · exact ⟨hdir, w, hprev', h'⟩
      · exact absurd (K.toFun_next m (Direction.not_P_to_V_eq_V_to_P hdir) s (Fin.init tr)
          (tr (Fin.last m)) w h') hprev'

/-- **The plain reading.** If the verifier can accept the transcript `tr` with an output that the
output relation relates to `wOut`, then the witness extracted from `tr` and `wOut` is in the
input relation, or some challenge of `tr` is in the bad set of the prefix before it. -/
theorem accept_imp_extract_or_bad (K : V.KnowledgeStateFunction init impl relIn relOut E)
    (s : StmtIn) (tr : pSpec.FullTranscript) (wOut : WitOut)
    (hacc : Pr[fun t => (t, wOut) ∈ relOut | OptionT.mk do
      (simulateQ impl (V.run s tr)).run' (← init)] > 0) :
    (s, toInput E s (Fin.last n) tr (E.extractOut s tr wOut)) ∈ relIn ∨
      badSomewhere K s (Fin.last n) tr :=
  state_imp K s (Fin.last n) tr _ (K.toFun_full s tr wOut hacc)

end Probe

#print axioms Probe.accept_imp_extract_or_bad
#print axioms Probe.rbr_iff_badSet
#print axioms schwartz_zippel_counting
#check @schwartz_zippel_counting
#check @prob_eval_zero_le_div
```

Output:

```text
.claude/reports/blueprint-review/probes/lib-arklib/PlainReading.lean:59:0: warning: automatically included section variable(s) unused in theorem `Probe.state_imp`:
  [(i : pSpec.ChallengeIdx) → SampleableType (pSpec.Challenge i)]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [(i : pSpec.ChallengeIdx) → SampleableType (pSpec.Challenge i)] in theorem ...
Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Probe.accept_imp_extract_or_bad' depends on axioms: [propext, Classical.choice, Quot.sound]
'Probe.rbr_iff_badSet' depends on axioms: [propext, Classical.choice, Quot.sound]
'schwartz_zippel_counting' depends on axioms: [propext, Classical.choice, Quot.sound]
@schwartz_zippel_counting : ∀ {F : Type u_1} [inst : Field F] [inst_1 : DecidableEq F] {s : ℕ}
  (f : MvPolynomial (Fin s) F),
  f ≠ 0 →
    ∀ (S : Fin s → Finset F) (d m : ℕ),
      f.totalDegree ≤ d →
        0 < m →
          (∀ (i : Fin s), m ≤ (S i).card) →
            {x ∈ Fintype.piFinset S | (MvPolynomial.eval x) f = 0}.card * m ≤ d * ∏ i, (S i).card
@prob_eval_zero_le_div : ∀ {F : Type} [inst : Field F] {s : ℕ} {S : Fin s → Set F}
  [inst_1 : (i : Fin s) → Fintype ↑(S i)] [inst_2 : ∀ (i : Fin s), Nonempty ↑(S i)] (f : MvPolynomial (Fin s) F),
  f ≠ 0 →
    ∀ (d m : ℕ),
      f.totalDegree ≤ d →
        0 < m →
          (∀ (i : Fin s), m ≤ (S i).toFinset.card) →
            (do
                  let x ← PMF.uniformOfFintype ((i : Fin s) → ↑(S i))
                  pure ((MvPolynomial.eval fun i => ↑(x i)) f = 0))
                True ≤
              ↑d / ↑m
exit=0
```

### Probe `Extractors`

Source (`probes/lib-arklib/Extractors.lean`):

```lean
import LeanerVM.Protocol.Spine.Compose
import LeanerVM.Protocol.PublicInput
import LeanerVM.Protocol.Spine.Toy

/-! Probe D6: what makes an `Extractor.RoundByRound` an algorithm, and the check applied to the
three extractors of leanerVM. ArkLib at the pin `dca90385`, leanerVM at `b435631`. -/

open OracleComp OracleSpec ProtocolSpec LeanerVM.Protocol LeanerVM.Parameters
open scoped NNReal

namespace Probe

/-! ## 1. ArkLib's extractor type accepts a classical choice of witness

A relation `R` on a bit and a natural number, a verifier with no round that accepts the statements
of a decidable language `L`, and the hypothesis that `L` is the language of `R`. The extractor
below *chooses* a witness. It is round-by-round knowledge sound at error zero, for every `R`. -/

variable (R : Set (Bool × ℕ)) (L : Bool → Bool) (hL : ∀ s, L s = true ↔ ∃ w, (s, w) ∈ R)

noncomputable def chooser :
    Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0}) Bool ℕ Unit !p[] (fun _ => ℕ) where
  eqIn := rfl
  extractMid := fun i => i.elim0
  extractOut := fun s _ _ => open Classical in if h : ∃ w, (s, w) ∈ R then h.choose else 0

def decideLanguage : Verifier []ₒ Bool Unit !p[] where
  verify := fun s _ => if L s then pure () else failure

def decideLanguage_guarded : (decideLanguage L).GuardedForm where
  check := fun s _ => L s
  out := fun _ _ => ()
  verify_eq := fun s tr => by simp [decideLanguage]

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

include hL in
theorem chooser_valid (s : Bool) (tr : (!p[]).FullTranscript) (hs : L s = true) :
    (s, (chooser R).extractOut s tr ()) ∈ R := by
  have h : ∃ w, (s, w) ∈ R := (hL s).mp hs
  simp only [chooser, h, dite_true]
  exact h.choose_spec

noncomputable def chooser_stateFunction :
    (decideLanguage L).KnowledgeStateFunction init impl R (Set.univ : Set (Unit × Unit))
      (chooser R) where
  toFun := fun _ s _ w => (s, w) ∈ R
  toFun_empty := fun _ _ => Iff.rfl
  toFun_next := fun i => i.elim0
  toFun_full := fun s tr _ h =>
    chooser_valid R L hL s tr
      (Verifier.GuardedForm.of_probEvent_pos (decideLanguage_guarded L) init impl s tr _ h).1

/-- Knowledge soundness at error zero with an extractor that computes nothing. -/
theorem chooser_sound :
    (decideLanguage L).rbrKnowledgeSoundnessWorstCaseWith init impl R Set.univ (fun _ => ℕ)
      (chooser R) (chooser_stateFunction R L hL init impl) (fun _ => 0) :=
  fun _ i => i.1.elim0

/-! ## 2. The three extractors of leanerVM are compiled definitions

Each `def` below has no `noncomputable`: Lean compiles it, so the extractor it names has code.
(The same line on `chooser` is rejected: see `ExtractorsExpectedFailure.lean`.) -/

def commitExtractorCode (I : M3Instance) := commitExtractor I
def publicInputExtractorCode (I : M3Instance) := PublicInput.extractor I
def piopExtractorCode {I : M3Instance} (P : Phases I) (S : P.Security) := piopExtractor P S
def commitSecurityExtractorCode (I : M3Instance) := (commitSecurity I).extractor
def publicInputSecurityExtractorCode (I : M3Instance) := (publicInputSecurity I).extractor

/-- The composition of two extractors is compiled too. -/
def appendedExtractorCode {I : M3Instance} {D : Phase.Def I I.Stmt (I.Stmt × BusOut I)}
    (S : Phase.Security I D (Seam.commit I) (Seam.bus I)) :=
  ((commitSecurity I).append S).extractor

/-! ## 3. They run: the commit extractor returns the stack that was sent -/

open Toy in
/-- A transcript of the commit phase: the honest stack of the toy instance. -/
def commitTranscript : (commitSpec toy).FullTranscript := fun | ⟨0, _⟩ => honest

open Toy in
#eval ((commitExtractor toy).extractOut ((1 : K), fun i => i.elim0) commitTranscript ()).values.toList
  == honest.values.toList

open Toy in
#eval ((commitSecurity toy).extractor.extractMid (⟨0, Nat.zero_lt_one⟩ : Fin 1)
  ((1 : K), fun i => i.elim0) commitTranscript honest).values.toList == honest.values.toList

open Toy in
#eval (PublicInput.extractor toy).extractOut
  ((((1 : K), (⟨[]⟩ : TableOut toy)), fun _ => honest)) (fun | ⟨0, _⟩ => (0 : E) | ⟨1, _⟩ => ([] : List E)) ()

end Probe

#print axioms Probe.chooser_sound
```

Output:

```text
true
true
PUnit.unit
'Probe.chooser_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```

### Probe `ExtractorsExpectedFailure`

Source (`probes/lib-arklib/ExtractorsExpectedFailure.lean`):

```lean
import LeanerVM.Protocol.Spine.Compose
import LeanerVM.Protocol.PublicInput

/-! Probe D6, expected to fail: without `noncomputable`, Lean refuses the extractor that
chooses a witness, and refuses a definition built on the public-input phase's definition (which
holds a real number). -/

open OracleComp OracleSpec ProtocolSpec LeanerVM.Protocol

namespace Probe

def chooser' (R : Set (Bool × ℕ)) :
    Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0}) Bool ℕ Unit !p[] (fun _ => ℕ) where
  eqIn := rfl
  extractMid := fun i => i.elim0
  extractOut := fun s _ _ => open Classical in if h : ∃ w, (s, w) ∈ R then h.choose else 0

/-- The verifier of the public-input phase, reached through the phase's definition. -/
def publicInputVerifierThroughPhase (I : M3Instance) := (publicInputPhase I).red.verifier

/-- The same verifier, reached directly. -/
def publicInputVerifierDirect (I : M3Instance) := PublicInput.verifier I

/-- The shape of `piopExtractor`: the extractor of a security bundle, with the phase's definition
as an explicit argument. -/
def extractorOf {I : M3Instance} {A B : Type} (D : Phase.Def I A B)
    {relIn : Set ((A × ∀ i, TheOracle I i) × Unit)} {relOut : Set ((B × ∀ i, TheOracle I i) × Unit)}
    (S : Phase.Security I D relIn relOut) := S.extractor

/-- Applied to the public-input phase: rejected, although the extractor itself is compiled. -/
def publicInputExtractorThroughPhase (I : M3Instance) :=
  extractorOf (publicInputPhase I) (publicInputSecurity I)

end Probe
```

Output:

```text
.claude/reports/blueprint-review/probes/lib-arklib/ExtractorsExpectedFailure.lean:12:4: error(lean.dependsOnNoncomputable): failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Classical.propDecidable', which is 'noncomputable'
.claude/reports/blueprint-review/probes/lib-arklib/ExtractorsExpectedFailure.lean:19:4: error(lean.dependsOnNoncomputable): failed to compile definition, consider marking it as 'noncomputable' because it depends on 'publicInputPhase', which is 'noncomputable'
.claude/reports/blueprint-review/probes/lib-arklib/ExtractorsExpectedFailure.lean:31:4: error(lean.dependsOnNoncomputable): failed to compile definition, consider marking it as 'noncomputable' because it depends on 'publicInputPhase', which is 'noncomputable'
exit=1   (expected: the three errors are the result)
```
