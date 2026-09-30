# Dossier `lib-arklib`: ArkLib's framework for interactive oracle reductions at the pin

Task: what ArkLib's oracle-reduction framework defines, proves and admits at the pin, whether
its security notions are an adequate model, and what leanerVM's master theorems mean in
cryptographic terms.

Revisions: leanerVM `main` at `b435631` (the object of the review; the checkout now also holds
`144c5aa`, the Lean 4.34.1 upgrade, section F); ArkLib at the old pin `dca90385` (every
snippet, read in `.lake/packages/Arklib` before the upgrade or with `git show dca90385…:` after
it) and at the new pin `7653a901` (section F; it is the commit this dossier had read as
`origin/main`); pull request #615 at `ca7a2577`; VCVio `f9dc47d9` (old) and `a4232d08` (new).
Every probe (appendix) ran at the old pin; none could be re-run after the upgrade.

## Summary

**What the master theorem means.** `piop_rbrKnowledgeSoundness` says (D.1, with the
transcript-level half proved by probe `PlainReading`): *for every public input and every
transcript, if the verifier accepts then the stack sent as the first message satisfies
`M3Holds`, unless some challenge of the transcript lies in the bad set of its prefix, and every
bad set has probability at most `piopError` of its round.* The probability is over one uniform
challenge at a time, at every prefix (the worst-case form); no prover appears. The step from
this to "an interactive prover convinces the verifier without a good first message with
probability at most `Σ piopError`" is a union bound that ArkLib admits at both pins
(`rbrKnowledgeSoundness_implies_knowledgeSoundness`); the step to Fiat–Shamir security is
stated nowhere in ArkLib. At the oracle-protocol level this is soundness with respect to the
committed oracle; knowledge (extracting the stack from a commitment) belongs to the compiled
protocol, for which ArkLib offers no theorem (`BCSTransform` commented out,
`Commitment.extractability` a placeholder whose body is `False`).

**The definition is adequate with one caveat that matters.** It matches the literature's
round-by-round knowledge soundness (Block et al. 2023, Definition 3.13, quoted in D.2) in its
worst-case-per-prefix form and its per-round errors, with one difference: ArkLib's extractor is
any function, classical choice included. In the existential forms the notion is therefore
soundness only (probe `Extractors`: knowledge soundness at error 0 with an extractor that
computes nothing, for any relation). leanerVM's named form is adequate together with the
reading of the named extractor, which for the spine is "return the first message" and which
compiles (probe `Extractors`). Non-vacuity holds: an accept-everything verifier has no
knowledge state function (no round) and is not knowledge sound at error 0 (one challenge); it is
knowledge sound at error 1, as every verifier is, so the error term is what carries content and
the planned `piopError_le` is the load-bearing companion (probe `NonVacuity`).

**What is proved and admitted.** leanerVM's master theorems, both phases, the composition and
the port depend on the three standard axioms only (probe `AxiomsLeanerVM`). ArkLib admits, at
both pins, the composition of every soundness notion, the round-by-round ⇒ plain implications,
context lifting, Fiat–Shamir completeness (stated, moreover, for a *constant* challenge oracle),
and the sumcheck specification's completeness and knowledge soundness (B.3, F.1). The local
port of #615's guarded-first knowledge append is the pull request's file up to headers, the
module system, docstrings and dropped wrappers (C.1); #615 is open and in conflict; ArkLib now
calls `OracleReduction` legacy and builds a typed framework that has no knowledge notion (F.2).

**Findings** (section G): G.1 *existential round-by-round knowledge soundness has no knowledge
content* (critical as a warning about the definition; leanerVM's named form is safe with the
extractor check); G.2 *the spine's completeness cannot carry an error, and Flock may need one*
(major); G.3 *the blueprint plans on a framework upstream calls legacy and on a pull request
that may not merge* (major); G.4 *no ArkLib statement can serve as the Fiat–Shamir/BCS witness
obligation, and `Verifier.fiatShamir` does not describe the compiled verifier* (major); G.5
*the error bundled in `Component.Def` makes every phase and the composed verifier and extractor
noncomputable* (minor); G.6 *names and line references in the ArkLib table* (minor); G.7, G.8
notes on derivable side conditions and re-implemented components; G.9 negative results.

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

### D.2 Comparison with the standard definitions

**Round-by-round soundness.** Block, Garreta, Katz, Thaler, Tiwari and Zając (*Fiat–Shamir
Security of FRI and Related SNARKs*, ePrint 2023/1071, Definition 3.12, read from the paper's
PDF; it says it follows [CMS19], which follows Canetti et al. 2019) define it with a "doomed
set" `D` of partial and complete transcripts (a state function taking the value *doomed*):

> 1. If x ∉ L then (x, ∅) ∈ D. 2. For any complete transcript τ, if (x, τ) ∈ D then V(x, τ) =
> reject. 3. If (x, τ) is an (i−1)-round partial transcript with (x, τ) ∈ D, then for every
> potential prover next message m, Pr_{c ← C_i}[(x, τ, m, c) ∉ D] ≤ ε(i).

ArkLib's `Verifier.StateFunction` (`Security/RoundByRound.lean:135-152`) is this notion for a
*reduction* (the final condition is "the verifier does not output a statement of the output
language") with two differences of shape. Condition 3 is split into a law for prover messages
(`toFun_next`: a doomed prefix stays doomed after any prover message) and the challenge bound,
which lets ArkLib schedule messages and challenges in any order rather than in alternation;
the two forms are equivalent for alternating protocols (extend the doomed set to a prefix
ending in a prover message by the value at the prefix before it). Condition 1 is an
equivalence, `stmt ∈ langIn ↔ toFun 0 stmt default`; the extra direction is harmless (a state
function may always be defined so) and is what sequential composition uses. Canetti et al.'s
original definition (as I recall it; not re-read for this dossier) is the same three
conditions with a function `State` in place of the set `D`.

**Round-by-round knowledge soundness.** The same paper, Definition 3.13 (verbatim):

> A (public-coin) holographic IOP Π for an indexed relation R has round-by-round knowledge
> with error ε_k if there exists a polynomial-time extractor Ext and for all i there exists a
> (not necessarily efficiently computable) "doomed set" D(i) of partial and complete
> transcripts such that: • (x, ∅) ∈ D(i) for all possible input x, regardless of whether
> x ∈ L or not. • For any possible input x and any complete transcript (x, τ), if (x, τ) ∈ D(i)
> then V(x, τ) = reject. • If i ∈ [μ] and (x, τ) is an (i−1)-round partial transcript such that
> (x, τ) ∈ D(i), then for every potential prover next message m, it holds that, if
> Pr_{c ← C_i}[(x, τ, m, c) ∉ D(i)] > ε_k(i), then Ext(i, x, τ, m) outputs a valid witness for x.

Chiesa and Yogev's book gives (as I recall it) the same notion with a state function: whenever
a prefix is doomed and the next challenge leaves the doomed set with probability above the
error, the extractor, given the prefix up to and including the prover's last message, outputs
a witness. ArkLib's own docstring says that its knowledge state function "deliberately differs
from ABF26 Definition A.5" (Arnon, Boneh, Fenzi, *Open Problems in List Decoding and Correlated
Agreement*, 2026, per ArkLib's bibliography; not read for this dossier), so ArkLib models a
witness-carrying state function of that manuscript, not Definition 3.13 directly.

**Where ArkLib's definition differs, and whether it weakens the guarantee.**

1. *The extractor's resources.* Definition 3.13 asks for a polynomial-time extractor. ArkLib's
   `Extractor.RoundByRound` is any Lean function: classical choice is allowed (D.6, probe
   `Extractors`), and nothing bounds running time. In the existential forms
   (`rbrKnowledgeSoundness`, `rbrKnowledgeSoundnessWorstCase`, and leanerVM's
   `piop_rbrKnowledgeSoundness_exists`) this removes the knowledge content: the probe proves
   "knowledge soundness at error 0" for an arbitrary relation from a verifier that merely
   decides the language, with an extractor that chooses a witness. **This is a real weakening
   of the notion as a definition.** It is repaired only by the named form together with a
   reading of the named extractor (what leanerVM does: `piopExtractor` returns the first
   message). ArkLib's own conversion `Extractor.RoundByRoundOneShot.toRoundByRoundOfRel`
   (`Security/RoundByRound.lean:102-123`) uses `h.choose`, and its docstring says why:
   "`extractMid` is a mathematical function rather than an algorithm with a tracked running
   time".
2. *What the extractor sees and when.* Definition 3.13 extracts from the prefix `(τ, m)` at
   the round where the prover becomes likely to leave the doomed set. ArkLib extracts backwards
   from the full transcript and the output witness. For an IOP whose witness is its first
   oracle message (leanVM), both read that message, and ArkLib's chain is the identity on it.
   For the Fiat–Shamir reading (D.3), ArkLib's form is at least as usable: the extractor is run
   once, on the final accepting transcript; the bound on each prefix's bad set gives the
   union bound over the prover's queries. This is my analysis; ArkLib proves no Fiat–Shamir
   theorem (D.3).
3. *The state is on (transcript, intermediate witness).* Definition 3.13's doomed set is on
   transcripts alone and the empty transcript is always doomed; ArkLib's state at the empty
   transcript is "the witness is valid" and the bad event has an existential over intermediate
   witnesses. When all intermediate witnesses are trivial (every leanVM phase after the commit
   has `witMid := fun _ ↦ Unit`), ArkLib's knowledge state function is a transcript predicate
   and the notion is round-by-round *soundness* of the verifier with respect to the seams,
   which is exactly what a phase over an already committed oracle can offer.
4. *Errors.* ArkLib's error `pSpec.ChallengeIdx → ℝ≥0` may depend on the protocol (in leanVM
   on the instance `I`, which carries the sizes) but not on the statement; Definition 3.13's
   `ε_k(i)` depends on the index. Equivalent for leanVM, whose sizes index the protocol family.
5. *Acceptance.* ArkLib's law 3 triggers on any positive probability of a related output, so
   a doomed state must reject with probability 1, as in Definition 3.13's second item.
6. *No prover appears* in the worst-case form; Definition 3.13 has none either ("for every
   potential prover next message"). The averaged `rbrKnowledgeSoundness` does quantify over
   provers and is the weaker notion (D.1).

**State-restoration knowledge soundness and straight-line extraction.** State-restoration
soundness (Ben-Sasson, Chiesa, Spooner 2016; Chiesa–Yogev) lets the prover rewind the verifier
to any earlier state at most `Q` times; round-by-round soundness implies it with error about
`Q · ε` (Theorem 3.15 of the paper above, quoted in D.3). ArkLib defines the state-restoration
games (`Security/StateRestoration.lean:133-154` at the pin) and states no theorem from
round-by-round to state restoration (the statements are commented out,
`Security/Implications.lean:230-254`); the theorems from state restoration to plain soundness
have `sorry` inside their statements (`:269, :284`). Straight-line extraction in the random
oracle model (the extractor reads the prover's oracle queries and never rewinds) is the shape
of ArkLib's `Extractor.Straightline` (`Security/Basic.lean:248-254`, which takes the prover's
and the verifier's query logs), but no ArkLib theorem produces such an extractor from a
round-by-round one at the pin, and the round-by-round extractor itself receives no query log.

### D.3 Which standard consequences are proved and which are admitted

`#print axioms` of probe `AxiomsArkLibBuilt` for the modules in leanerVM's build; source and
ArkLib's committed axiom baseline (B.3) for the others (`Security/Implications.lean` is not in
leanerVM's build). "main" is `origin/main` at `7653a901e`.

| Implication | Where (pin) | Pin | main |
| --- | --- | --- | --- |
| worst-case rbr knowledge ⇒ averaged rbr knowledge (`rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness`, `…With_implies_…With`) | `Security/RoundByRound.lean:606, 625` | proved | proved |
| worst-case rbr soundness ⇒ averaged rbr soundness | `:589` | proved | proved |
| rbr knowledge ⇒ rbr soundness (`rbrKnowledgeSoundness_implies_rbrSoundness`) | `Security/Implications.lean:87` | proved (not in the baseline; the proof is in the file) | proved |
| one-shot rbr knowledge ⇒ rbr knowledge | `Security/RoundByRound.lean:657` | proved, with a classical-choice extractor | proved |
| rbr knowledge ⇒ plain knowledge soundness (`rbrKnowledgeSoundness_implies_knowledgeSoundness`, error `Σ ε`) | `Security/Implications.lean:223-228` | **admitted** (`by sorry`) | admitted |
| rbr soundness ⇒ soundness (`rbrSoundness_implies_soundness`) | `:79-83` | **admitted** | admitted |
| knowledge soundness ⇒ soundness | `:49-63` | **admitted** | admitted |
| rbr ⇒ state restoration | `:230-254` | commented out | commented out |
| state restoration ⇒ plain | `:259-313` | admitted, `sorry` in the statements | same |
| Fiat–Shamir completeness (`fiatShamir_completeness`) | `FiatShamir/Basic.lean:163-173` | **admitted**, and stated with the challenge oracle fixed to the constant function `default` (finding *Fiat–Shamir completeness is stated for a constant oracle*) | admitted |
| Fiat–Shamir (knowledge) soundness | — | not stated ("TODO", `:175`) | not stated |
| BCS transform | `BCS/Basic.lean` | commented out | commented out |

So a reader of `piop_rbrKnowledgeSoundness` trusts the *definition* (D.1) and, for the plain
reading, the union bound. The transcript-level half of that reading is proved by the probe
`PlainReading` (`accept_imp_extract_or_bad`); the probabilistic half (a union bound over the
rounds of an interactive execution, or over the queries of a Fiat–Shamir prover) is the
admitted `rbrKnowledgeSoundness_implies_knowledgeSoundness` and the absent Fiat–Shamir theorem.
For the expected form of the latter, the paper above states (Theorem 3.15, verbatim): "if
(P, V) is a public-coin IOP for R with … round-by-round knowledge error ε_rbr-k(x) … then
BCS^H(P, V) is a non-interactive random oracle proof system for R with … adaptive knowledge
error ε_fs-k(x, Q, κ) = Q·ε_rbr-k(x) + 3(Q²+1)/2^κ against Q-query adversaries". The blueprint's
`FiatShamirSecurity` interface names this shape ("error Q · max_i ε_i",
`docs/roadmap/protocol-blueprint.md:1224`); nothing in ArkLib at the pin or on `origin/main`
states it.

### D.4 Non-vacuity of the notion, by probe

Probe `NonVacuity` (appendix), on the relation "the statement is a bit and only `true` has a
witness" (`relIn := {p | p.1 = true}`, `relOut := Set.univ`), for any shared oracle, any
`init`, any `impl`:

* **(a0) No round, accept everything.** `acceptAll0` (`verify := fun _ _ => pure ()`) has *no*
  knowledge state function at all, for any extractor: `acceptAll0_no_stateFunction :
  IsEmpty (acceptAll0.KnowledgeStateFunction init impl relIn relOut E)`. Law 3 forces the
  state at `false`, law 1 then puts `false` in the language.
* **(a1) One challenge, accept everything.** `acceptAll1_not_sound_at_zero`: for *every*
  extractor `E` and *every* knowledge state function `K`, `¬ rbrKnowledgeSoundnessWorstCaseWith
  … W E K (fun _ => 0)`. The attempt fails exactly where it should: at the statement `false`,
  the empty prefix and the challenge `true`, the state after the challenge is forced true by
  acceptance and the state before is forced false by the relation, so the bad set is everything
  and its probability is 1, not 0.
* **The error carries the content.** `acceptAll1_sound_at_one`: the same verifier *is*
  knowledge sound at error 1 (state "valid witness" at round 0, `True` afterwards). Every
  verifier with a challenge satisfies the predicate at error 1. Consequently a theorem of the
  form `rbrKnowledgeSoundnessWorstCaseWith … ε` says nothing until `ε` is read; in leanerVM the
  error `piopError P := P.toDef.err` is *data supplied by each phase's definition*
  (`Component.Def.err`), not derived from anything, and a phase may charge 1 to a challenge and
  discharge its `rbr` obligation trivially. The blueprint's planned `piopError_le`
  (`Σ i, piopError s i ≤ 2^40/|E| + flockError`, `docs/roadmap/protocol-blueprint.md:1130`)
  is therefore the load-bearing companion of the master theorem, and it does not exist yet.
* **Positive control.** `checkBit` (`verify := fun s _ => if s then pure () else failure`) is
  knowledge sound at error 0 with the trivial extractor (`checkBit_sound_at_zero`): the
  intended object inhabits the definition.
* **(b) Constant state functions.** `stateFunction_false_at`: for any knowledge state function
  and any statement with no witness, the state at round 0 is false for every witness;
  `stateFunction_true_at`: for a statement with a valid witness it is true. So a knowledge state
  function is never constantly true nor constantly false as soon as the relation has a
  statement with a witness and one without. (The state "valid at round 0, `True` afterwards"
  is allowed, at error 1: see the previous item.)
* **(c) Trivial output relation.** `full_iff_of_univ`: for a guarded verifier (a Boolean check
  followed by a deterministic verdict, D.5 and section A) and `relOut = Set.univ`, the last law
  of a knowledge state function is equivalent to "if the check passes on `(s, tr)` then the
  state at the full transcript holds at the extracted witness". Confirmed: with the spine's
  `Seam.done I` (`fun _ _ ↦ True`, `LeanerVM/Protocol/Spine/Seams.lean:191`) and its output
  statement `Unit`, "accept" means "the verifier returns rather than fails", and law 3 says
  exactly "accepted ⇒ state true". A design consequence: since the final output statement is
  `Unit`, the last phase can only reject by failing; a verifier that returned a Boolean verdict
  would count `false` as an acceptance under `Set.univ`.

### D.5 The oracle verifier is judged through `toVerifier`

An `OracleVerifier` (section A) computes with query access to the input oracles and to the
prover's messages. Every security predicate ArkLib gives it (`OracleVerifier.rbrSoundness`,
`rbrKnowledgeSoundness`, `rbrKnowledgeSoundnessWith`, `Security/RoundByRound.lean:729-758`)
is the predicate of its plain image `toVerifier`, and leanerVM states its master theorem on
`(leanVmVerifier P).toVerifier`:

`.lake/packages/Arklib/ArkLib/OracleReduction/Basic.lean:488-496` (ArkLib `dca90385`):

```lean
/-- An oracle verifier can be seen as a (non-oracle) verifier by providing the oracle interface
  using its knowledge of the oracle statements and the transcript messages in the clear -/
def toVerifier : Verifier oSpec (StmtIn × ∀ i, OStmtIn i) (StmtOut × (∀ i, OStmtOut i)) pSpec where
  verify := fun ⟨stmt, oStmt⟩ transcript => OptionT.mk <|
    Option.map (fun stmtOut =>
      (stmtOut, verifier.materializeOutput
        transcript.challenges oStmt transcript.messages)) <$>
      simulateQ (OracleInterface.simOracle2 oSpec oStmt transcript.messages)
        (verifier.verify stmt transcript.challenges).run
```

`simOracle2` answers each query of the oracle verifier from the actual oracle statements and
the actual messages of the transcript, and the output oracles are materialised. So the plain
verifier's verdict on a transcript is the oracle verifier's verdict when its queries are
answered faithfully; the state function and the extractor are functions of the whole
transcript, including the full contents of every oracle message (the stack `q`, `2^μ` field
elements). This is the standard reading of IOP soundness: the verifier's queries are simulated
from the full messages, and the notions of soundness are stated on full transcripts. Nothing
is lost for soundness at the oracle-protocol level. Three things are outside the statement:

* the verifier's query complexity and locality (an `OracleVerifier` may query every point;
  `OracleVerifier.numQueries` is a `sorry` definition, `Basic.lean:505-507`); they matter for
  the cost of the compiled protocol, not for its soundness;
* the *type* of the oracle message: a prover in the security game can only send an element of
  `Column I.μ` (a table of `2^μ` values in `K`), that is, a genuine multilinear over the base
  field of the announced size. Whether a prover of the compiled protocol can commit to
  something else is the commitment scheme's problem (extractability or list binding of WHIR,
  Layer 11), not this theorem's;
* the composition `OracleVerifier.append` (`Append/Basic.lean:619-629`) routes the second
  verifier's queries through the first's output-oracle simulation; `append_toVerifier`
  (`:658`, proved) says its `toVerifier` is the plain `Verifier.append` of the two `toVerifier`s,
  which is what lets leanerVM compose state functions of plain verifiers.

### D.6 Must an extractor compute? What ArkLib forces, what it allows, how to check

ArkLib forces nothing: `Extractor.RoundByRound` is a structure of Lean functions with no
computability requirement, and ArkLib itself defines a `noncomputable` one with `h.choose`
(`Extractor.RoundByRoundOneShot.toRoundByRoundOfRel`, `Security/RoundByRound.lean:118-123`).
The probe `Extractors` shows the consequence: `chooser R` (extractOut chooses a witness of
`(s, ·) ∈ R` if one exists, classically) is accepted as an extractor and `chooser_sound` proves
`rbrKnowledgeSoundnessWorstCaseWith … (chooser R) … (fun _ => 0)` for the verifier that decides
the language of `R`, for *every* relation `R` with that language. Knowledge has been proved of
nothing.

How to tell a computable extractor:

* `#print axioms` does not tell: `piopExtractor`, `commitExtractor` and `PublicInput.extractor`
  all report `Classical.choice` (probe `AxiomsLeanerVM`), through the proofs and instances
  inside their types, as does nearly every declaration built on Mathlib.
* What tells is the compiler: a `def` without the `noncomputable` keyword is accepted only if
  Lean can generate code for it, and Lean refuses a definition using classical choice in a
  value position ("failed to compile definition, consider marking it as 'noncomputable' because
  it depends on 'Classical.propDecidable'", probe `ExtractorsExpectedFailure`, line 12). The
  refusal is transitive: a compiled definition cannot call a `noncomputable` one.
* `#eval` is the positive test: it runs the code.

Applied to leanerVM (probe `Extractors`): `commitExtractor I`, `PublicInput.extractor I`,
`piopExtractor P S`, `(commitSecurity I).extractor`, `(publicInputSecurity I).extractor` and an
appended extractor are each the body of a compiled `def`; the commit extractor evaluated on the
toy instance returns the honest stack (`true`, twice), and the public-input extractor returns
`()`. The definitions are moreover one line each: "read the message" (`SendOracle.lean:137-138`)
and "return ()" (`PublicInput.lean:320-321`), so their efficiency is read off directly, which
matters because Lean-computable is not polynomial-time: for a finite witness type and a
decidable relation, exhaustive search is a computable extractor for any sound verifier.

Two limits of the check:

1. `piopExtractor P S` is computable *as a function of* the bundle `S : P.Security`, whose
   `extractor` field any future phase fills. The check must be repeated on each phase's
   `Security` value (`publicInputSecurity` passes today). The type does not enforce it.
2. `Component.Def` carries the real-valued error `err : … → ℝ≥0`, so every phase definition
   with a non-zero error is `noncomputable` (`publicInputPhase`,
   `LeanerVM/Protocol/PublicInput.lean:374-381`, "noncomputable because of the error alone").
   Lean then refuses to compile anything that takes the phase's definition as an argument:
   probe `ExtractorsExpectedFailure` shows `(publicInputPhase I).red.verifier` and
   `extractorOf (publicInputPhase I) (publicInputSecurity I)` rejected, although the verifier
   and the extractor are compiled when named directly. `leanVmVerifier P := P.toDef.red.verifier`
   and `piopExtractor P S` take `P` explicitly, so on the real bundle of phases neither will be
   a compiled definition. This does not affect the theorems; it affects the blueprint's
   promises that the extractor and the honest prover "compute" and the planned code-generation
   probes (finding *the error bundled in the definition makes the protocol noncomputable*).

## B. What is proved and what is admitted at the pin

### B.1 The axioms of leanerVM's theorems (probe `AxiomsLeanerVM`)

Every declaration below depends on exactly the three standard axioms `propext`,
`Classical.choice`, `Quot.sound` (`Component.sendExtractor` on `propext` and `Quot.sound` only)
and on no `sorryAx`: `piop_perfectCompleteness`, `piop_rbrKnowledgeSoundness`,
`piop_rbrKnowledgeSoundness_exists`, `commitSecurity`, `commitComplete`, `publicInputSecurity`,
`publicInputComplete`, `Component.Security.append`, `Component.Complete.append`,
`Verifier.KnowledgeStateFunction.appendGuarded` and
`Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first` (the two declarations
of `KnowledgeAppend.lean`), `piopExtractor`, `commitExtractor`, `PublicInput.extractor`,
`Phases.Security.toDef`, `Phases.Complete.toDef`. Note that `Component.Security.append` and
`Component.Complete.append` are definitions (structures bundling data and proofs), not
theorems, as are `commitSecurity`, `publicInputSecurity` and `appendGuarded`.

This does *not* say that the master theorems are unconditional: they take `P : Phases I`,
`C : P.Complete`, `S : P.Security` as arguments, and only the commit and public-input phases
exist. It says that nothing admitted in ArkLib is consumed.

### B.2 The blueprint's ArkLib table, row by row (`docs/roadmap/protocol-blueprint.md:232-251`)

"exists" means the name resolves at the pin at the place given; "proved" means no `sorryAx`
(by probe where the module is in leanerVM's build, marked P; else by ArkLib's axiom baseline,
B.3, marked B, and by reading the proof, marked S).

| Blueprint row | At the pin | Line reference | Proof status |
| --- | --- | --- | --- |
| `ProtocolSpec n`, `Direction`, `MessageIdx`, `ChallengeIdx`, `FullTranscript`, `Transcript` (`ProtocolSpec/Basic.lean`) | exist | `Direction` is in `OracleReduction/Prelude.lean:66-69`, not `ProtocolSpec/Basic.lean` | definitions |
| `OracleInterface` with `Query`, `Response`, `answer` (`OracleInterface.lean:53-73`) | exist; the class (`:54-57`) has fields `Query` and `toOC : OracleContext Query (ReaderM Message)`; `Response` (`:67`) and `answer` (`:75-78`) are derived | `answer` is at `:76`, outside 53-73 | definitions |
| `Prover`, `Verifier`, `OracleVerifier`, `Reduction`, `OracleReduction`, `OracleProof` (`Basic.lean:222-669`) | exist (`:222-229, :247-250, :322-344, :624-628, :632-641, :669-675`) | correct | definitions; `OracleVerifier.numQueries` (`:505-507`) is a `sorry` definition, unused by leanerVM |
| `Reduction.completeness`, `perfectCompleteness`, `OracleReduction.perfectCompleteness` (`Security/Basic.lean:89-103, 460-469`) | exist (`:89, :103, :460, :469`) | correct | definitions (P) |
| `Verifier.knowledgeSoundness`, `Extractor.Straightline` (`Security/Basic.lean:248-359`) | exist (`:248-254, :344-361`) | correct | definitions (P) |
| `Verifier.KnowledgeStateFunction`, `Extractor.RoundByRound`, `rbrKnowledgeSoundness`, `rbrKnowledgeSoundnessWorstCase`, `rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness` (`RoundByRound.lean:77-190, 416, 534, 606`), `…WorstCaseWith` (`:553`) | exist (`:164, :77, :416, :534, :606, :553`) | correct | the implication is proved (P) |
| `Verifier.rbrKnowledgeSoundness_implies_rbrSoundness` (`Implications.lean:85`) | exists (`:87`, docstring at 85) | correct | proved (B, S) |
| `OracleReduction.append`, `OracleReduction.seqCompose`, `ProtocolSpec.seqCompose` (`Append/Basic.lean:709`, `General.lean:255`) | exist (`:709`, `:255`, `ProtocolSpec/SeqCompose.lean:359`) | correct | definitions (P) |
| `Reduction.seqCompose_perfectCompleteness_of_pure`, `OracleReduction.append_perfectCompleteness_of_pure_verifiers`, `seqCompose_completeness_of_guarded_verifiers` | exist (`Completeness.lean:66`, `Append/Completeness.lean:259`, `GuardedNary.lean:45` and `OracleCompleteness.lean:77`) | correct | proved (P for the last two; B for the first, whose module is not in leanerVM's build). The theorem the spine actually uses, `OracleReduction.append_perfectCompleteness_of_guarded_verifiers` (`OracleCompleteness.lean:56`), is not in the table; proved (P) |
| `Verifier.append_rbrSoundnessWorstCase_of_pure_first`, `Verifier.StateFunction.append`, `Extractor.RoundByRound.append` (`Append/RoundByRound.lean:37`, `Append/StateFunction.lean:292, 75`) | exist | correct | proved (P) |
| `Component.ReduceClaim`, `CheckClaim`, `RandomQuery`, `DoNothing` (`ProofSystem/Component/`) "all proved" | the namespaces are `ReduceClaim`, `CheckClaim`, `RandomQuery`, `DoNothing` (no `Component.` prefix) | | no `sorry` in the four files and none of their names in the baseline (B, S). But `CheckClaim`'s oracle verifier is a pass-through that checks nothing at run time (`CheckClaim.lean:19-24`: "the verifier is a pure pass-through … does *not* run any check at runtime; the checked predicate … is instead carried by the output relation"); only the plain-reduction variant `guard`s. Not consumed by leanerVM at `b435631` |
| `Sumcheck.Spec.reduction`, `StatementRound`, `relationRound`, `Sumcheck.Domain` (`Spec/General.lean:171`, `SingleRound.lean:130-144`, `Domain.lean`) | exist (`General.lean:172`; `SingleRound.lean:130-145`); the domain structure is `SumcheckDomain` in the root namespace (`Domain.lean:55`), not `Sumcheck.Domain` | one off / name | definitions. Not consumed by leanerVM at `b435631` |
| `MvPolynomial.MLE`, `eqPolynomial`, `eqTilde`, `eqTilde_append`, `MLE_eq_zero_iff`, `MLEEquivFin` (`Data/MvPolynomial/Multilinear.lean`) | exist (`:151, :88, :95, :116, :252, :421`), namespace `MvPolynomial` | correct | proved (B: none in the baseline; no `sorry` in the file) |
| `MvPolynomial.schwartz_zippel_counting`, `prob_eval_zero_le_div` (`SchwartzZippelCounting.lean`) | the first is `schwartz_zippel_counting` in the **root** namespace (`:30`); `MvPolynomial.schwartz_zippel_counting` is an unknown constant (probe). `prob_eval_zero_le_div` (`:131`) is stated with Mathlib's `PMF.uniformOfFintype`, not with VCVio's `Pr[· | $ᵗ α]` that every ArkLib error bound uses; a bridge is needed (leanerVM's `ToVCVio/UniformSample.lean` supplies one for a subsingleton bad set) | name wrong | proved (P) |
| `Reduction.fiatShamir`, `Verifier.fiatShamir`, `fsChallengeOracle` (`FiatShamir/Basic.lean:114-138`) | `Verifier.fiatShamir` `:130`, `Reduction.fiatShamir` `:140`; `fsChallengeOracle` is an alias in `ProtocolSpec/Basic.lean:854` | partly off | definitions; the one theorem of the file is admitted |
| `Commitment.Scheme`, `binding`, `perfectCorrectness_of_opening_perfectCompleteness` (`Commitments/Functional/Basic.lean`) | exist (`:67, :220, :128`) | correct | proved (B, S). `Commitment.extractability` (`:250-255`) is a placeholder whose body is `False` under its quantifiers: it is never satisfiable (finding *commitment extractability is a placeholder*) |
| `ToyProblem.Codegen` | file exists, no `sorry` | | |
| `SampleableType`, `uniformSample`, `$ᵗ` (VCVio `SampleableType.lean:44`) | exist (`:44-47, :51, :53`) | correct | class laws force uniformity (D.1) |

Line references are those of the pin; the sources are `.lake/packages/Arklib/ArkLib/…`.

### B.3 ArkLib's axiom baseline, and the admitted table

`scripts/axiom_baseline.json` at the pin (dated 2026-09-08, last changed by ArkLib #887) is
the output of ArkLib's `axiomsweep` tool (`scripts/AxiomSweep.lean:8-60`): it walks the
compiled environment of the whole library and records every declaration whose statement or
proof depends on `sorryAx` ("the same information as `#print axioms`, for the whole library at
once"). It is an allow-list: ArkLib's CI runs `lake exe axiomsweep --check`
(`.github/workflows/ci.yml:162-163`), which fails when a tainted declaration is missing from
the file and stays green when a listed one has since been proved. The `build` check run of the
pin commit concluded `success` (`gh api …/commits/dca90385…/check-runs`). Hence: a declaration
absent from the baseline is `sorryAx`-free at the pin; one present may or may not be. The
baseline lists 291 declarations (`"sorry"`) and no non-standard axiom (`"nonstandard": []`).
The entries relevant here (the full list of the non-lattice entries was read):

* `Verifier.append_{soundness,knowledgeSoundness,rbrSoundness,rbrKnowledgeSoundness}`,
  `OracleVerifier.append_*`, `Verifier.seqCompose_*`, `OracleVerifier.seqCompose_*`;
* `Verifier.knowledgeSoundness_implies_soundness`, `rbrSoundness_implies_soundness`,
  `rbrKnowledgeSoundness_implies_knowledgeSoundness`, the four `sr*` theorems;
* `Verifier.liftContext_*`, `OracleVerifier.liftContext_*`, `Reduction.liftContext_*`,
  `OracleReduction.liftContext_*`, `Verifier.StateFunction.liftContext`,
  `Extractor.RoundByRound.liftContext` (definitions);
* `fiatShamir_completeness`; the `DuplexSpongeFS.*`, `FSProverState.*`, `FSVerifierState.*`,
  `HashStateWithInstructions.*`, `OracleSpec.QueryLog.BadEventDS.*` families;
* `Sumcheck.Spec.reduction_perfectCompleteness`, `Sumcheck.Spec.oracleVerifier_rbrKnowledgeSoundness`,
  `Sumcheck.Spec.SingleRound.{reduction_perfectCompleteness, oracleReduction_perfectCompleteness,
  verifier_rbrKnowledgeSoundness, oracleVerifier_rbrKnowledgeSoundness, extractorLens_rbr_knowledge_soundness,
  oCtxLens_complete}`, `…SingleRound.Simple.*_rbrKnowledgeSoundness`, `…SingleRound.Simpler.oracleReduction` (a definition);
* `SendSingleWitness.oracleReduction_completeness`, `NoInteraction.reduction_completeness`;
* `CodingTheory.rs_mcaError_le_in_johnson_range` and the other `CodingTheory.*`, `ProximityGap.*`, `StirIOP.*`, `Fri.*`, `Binius.*`, `RingSwitching.*` entries;
* `OracleVerifier.numQueries`, `MvPolynomial.basis`, `Fin.sumCases`.

Counted `sorry` in code (non-comment lines) of the files involved: `Security/Implications.lean`
9, `Append/Security.lean` 4, `General.lean` 2, `Basic.lean` 1 (the `numQueries` definition),
`FiatShamir/Basic.lean` 1, `LiftContext/Reduction.lean` 10, `Sumcheck/Spec/SingleRound.lean`
13, `Component/SendWitness.lean` 1, `CapacityBounds.lean` 3; 0 in `Security/Basic.lean`,
`RoundByRound.lean`, `RbrGame.lean`, `Execution.lean`, `OracleInterface.lean`,
`ProtocolSpec/*.lean`, `Append/{Basic,StateFunction,RoundByRound,Completeness,Execution}.lean`,
`GuardedCompleteness.lean`, `GuardedNary.lean`, `OracleCompleteness.lean`, `CWSS/Guarded.lean`,
`Commitments/Functional/Basic.lean`, `Component/{ReduceClaim,CheckClaim,RandomQuery,DoNothing}.lean`,
`Sumcheck/Spec/General.lean`, `Domain.lean`, `Multilinear.lean`, `SchwartzZippelCounting.lean`.
Whole library at the pin: 192 code occurrences of `sorry` in 77 files.

**The blueprint's "Admitted at the pin" table (`:257-267`), checked.**

| Row | Checked |
| --- | --- |
| A1 sumcheck: `Sumcheck.Spec.SingleRound.verifier_rbrKnowledgeSoundness` and the lens instances `sorry` | correct (`SingleRound.lean:1091-1094`, `:1010-1080`). Omits that the sumcheck's **perfect completeness** is admitted too: `Sumcheck.Spec.SingleRound.reduction_perfectCompleteness` (`:1085-1088`, `lensComplete := by simp; sorry`, through the admitted `Reduction.liftContext_perfectCompleteness`) and hence `Sumcheck.Spec.reduction_perfectCompleteness` (`General.lean:211`), both in the baseline |
| A2 composition: `Verifier.append_knowledgeSoundness`, `append_rbrKnowledgeSoundness`, `seqCompose_rbrKnowledgeSoundness` admitted (issue #676) | correct (probe: `sorryAx`); also `append_soundness`, `append_rbrSoundness`, `seqCompose_{soundness,knowledgeSoundness,rbrSoundness}` and the `OracleVerifier.*` forms |
| A3 `rbrKnowledgeSoundness_implies_knowledgeSoundness`, `rbrSoundness_implies_soundness` admitted | correct; also `knowledgeSoundness_implies_soundness` |
| A4 every `liftContext_*` security theorem admitted | correct; the definitions `Verifier.StateFunction.liftContext` and `Extractor.RoundByRound.liftContext` are `sorry` too |
| A5 `fiatShamir_completeness` admitted; `BCSTransform` commented out (#627); `DuplexSponge` security admitted | correct; and no Fiat–Shamir *soundness* statement exists (D.3) |
| A8 `rs_mcaError_le_in_johnson_range` external admit | correct (`CapacityBounds.lean:203`, in the baseline) |
| A9 ring switching packing leaves `sorry` | correct (`RingSwitching.*` in the baseline) |

## C. The ported composition theorem (`LeanerVM/Protocol/ToArkLib/KnowledgeAppend.lean`)

### C.1 Provenance, verified

`git show ca7a2577:ArkLib/OracleReduction/Composition/Sequential/Append/Knowledge.lean` in the
sibling ArkLib checkout (after `git fetch origin`; the commit is
"style(ring-switching): align names and streamline documentation", 2026-09-09, head of pull
request #615, `feat(ring-switching): add reusable packing proofs and protocol integrations`,
author alexanderlhicks) gives a 632-line file, saved as
`probes/lib-arklib/Knowledge_pr615_ca7a2577.lean.txt`. `diff` against the local 587-line file
shows exactly these differences (the whole `diff` output was read):

1. Header: the local file adds its own title lines and keeps the ArkLib copyright, license
   and "Authors: ArkLib Contributors" lines.
2. The pull request's file is a classic Lean file (`import …`); the local one is a `module`
   with `public import` of the same two modules and an `@[expose] public section`. (The pull
   request predates ArkLib's move to the module system, which is the pin's own commit,
   `dca90385 feat(module-system): migrate to modules (#897)`; this is one reason the pull
   request is in conflict with `main`.)
3. The module docstring is rewritten (the pull request's says the same things: guarded first
   verifier, exact-object worst-case theorem, import it explicitly to avoid a cycle).
4. Everything is wrapped in `namespace LeanerVM.Protocol` (so the declarations are
   `LeanerVM.Protocol.Verifier.KnowledgeAppend.*`,
   `LeanerVM.Protocol.Verifier.KnowledgeStateFunction.appendGuarded`,
   `LeanerVM.Protocol.Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first`).
5. The two lemmas `witness_left` and `witness_right` (six and nine lines of proof in the pull
   request) are replaced by references to ArkLib's own `Extractor.wit_mid_append_left` and
   `wit_mid_append_right` (`Append/StateFunction.lean:51-71` at the pin), which are the same
   statements.
6. Docstrings are added to fourteen declarations that had none.
7. Two names are qualified (`Verifier.guarded_accepting_of_mem`,
   `Verifier.append_run_guardedLeft`), as the namespace requires.
8. The four wrappers of the pull request are omitted: the averaged exact-object form
   (`append_rbrKnowledgeSoundnessWith_of_worstCase_of_guarded_first`), the existential
   worst-case form (`append_rbrKnowledgeSoundnessWorstCase_of_guarded_first`), the existential
   averaged form (`append_rbrKnowledgeSoundness_of_worstCase_of_guarded_first`) and the
   `OracleVerifier` form.

No proof step of the two main declarations differs. The blueprint's description ("verbatim
port … except that its two lemmas on the witness type reuse the pinned ArkLib's proofs; the
wrappers into the existential and averaged forms are left out", file docstring `:31-37`) is
accurate. Both declarations depend on the three standard axioms (probe `AxiomsLeanerVM`).

### C.2 What the two declarations say

`Verifier.KnowledgeStateFunction.appendGuarded G K₁ K₂` (`KnowledgeAppend.lean:474-488`)
builds, from a guarded form `G` of the first verifier and knowledge state functions `K₁`
(for `V₁`, relations `R₁ → R₂`) and `K₂` (for `V₂`, `R₂ → R₃`), a knowledge state function of
`V₁.append V₂` for `R₁ → R₃` and for ArkLib's appended extractor `E₁.append E₂ G.out`. Its
state (`state`, `:182-196`) is: up to and including the seam, `K₁` on the prefix; after the
seam, "the first check passes on the first half **and** `K₂` on the second half, at the
statement the first verifier outputs (`G.out s tr₁`)".

`Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first` (`:510-518`):

`LeanerVM/Protocol/ToArkLib/KnowledgeAppend.lean:508-518` (leanerVM `b435631`):

```lean
extractors and knowledge states. The first round of the right component is included. -/
theorem append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first (G : V₁.GuardedForm)
    (K₁ : V₁.KnowledgeStateFunction init impl R₁ R₂ E₁)
    (K₂ : V₂.KnowledgeStateFunction init impl R₂ R₃ E₂)
    {ε₁ : pSpec₁.ChallengeIdx → ℝ≥0} {ε₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrKnowledgeSoundnessWorstCaseWith init impl R₁ R₂ W₁ E₁ K₁ ε₁)
    (h₂ : V₂.rbrKnowledgeSoundnessWorstCaseWith init impl R₂ R₃ W₂ E₂ K₂ ε₂) :
    (V₁.append V₂).rbrKnowledgeSoundnessWorstCaseWith init impl R₁ R₃
      (Witness W₁ W₂) (E₁.append E₂ G.out) (KnowledgeStateFunction.appendGuarded G K₁ K₂)
      (Sum.elim ε₁ ε₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  classical
```

In words: if `V₁` is worst-case round-by-round knowledge sound for `(E₁, K₁)` at errors `ε₁`
and `V₂` for `(E₂, K₂)` at errors `ε₂`, then `V₁.append V₂` is, for the appended extractor and
state function, at the error that assigns to each challenge **the error of the component it
belongs to** (`Sum.elim ε₁ ε₂ ∘ ChallengeIdx.sumEquiv.symm`). No additive term appears: a bad
transition of the composite at a challenge of the first component is a bad transition of
`K₁` at the same prefix (`state_left`, `extractMid_left`); at a challenge of the second
component, including its first round where the seam extraction happens (`backward_right`,
`extractMid_seam`, `left_related`), it is a bad transition of `K₂` at the prefix's second half
and the statement `G.out s tr₁`. Since `h₂` is quantified over all statements, it applies to
that statement whatever `tr₁` is. This is the right error for round-by-round notions (each
challenge keeps its own bound); the sum `Σ ε` only appears when passing to plain knowledge
soundness (D.3).

**Hypotheses.** `G : V₁.GuardedForm` (the first verifier is a Boolean check followed by a
deterministic verdict, `CWSS/Guarded.lean:112-118`, section A) is the only hypothesis beyond
the two components' soundness; the second verifier is arbitrary; either component may have
no round; the shared oracle is arbitrary but the state functions and errors are for the same
`init`, `impl`. The guarded form is *data*: the composed extractor and state use `G.out`, the
first verifier's verdict function, to compute the statement handed to the second component.
On a rejected first half `G.out` is whatever the form says (ArkLib's `ofEmpty` uses a fallback);
it is used only under `G.check = true` in the proofs, so this is harmless.

**Is it a real restriction for leanVM's phases?** No. Over the empty shared oracle every
verifier is guarded: ArkLib proves `Verifier.GuardedForm.ofEmpty`
(`Composition/Sequential/NoAmbient.lean:46-55` at the pin: `check := (V.verify stmt tr).run.runEmpty.isSome`,
`out := ….getD (fallback stmt)`), together with `Prover.instOutputIsPureEmpty` (`:39-43`).
leanerVM's phases live over `[]ₒ` (`Component.Def.red : OracleReduction []ₒ …`), and
leanerVM supplies the guarded forms by hand (`PublicInput.guarded`,
`sendVerifierPure.toGuardedForm`), which is more readable but not necessary. It would be a
restriction for a verifier that queries a shared oracle (a random oracle): such a verifier is
not guarded, and the compiled protocol's verifier (Merkle paths hashed through the oracle) is
of that kind; the blueprint composes only at the oracle-protocol level, where none is.

### C.3 State of the upstream today (2026-09-29, read-only `gh`)

* Pull request #615: **open**, not a draft, `mergeable: CONFLICTING`, created 2026-07-07,
  last updated 2026-09-08, head `ca7a2577`. Its `Knowledge.lean` is not on `origin/main`
  (`Composition/Sequential/Append/` on `origin/main` has the same eleven files as the pin,
  no `Knowledge.lean`); `Append/Security.lean` on `origin/main` still admits
  `append_soundness`, `append_knowledgeSoundness`, `append_rbrSoundness`,
  `append_rbrKnowledgeSoundness` (four `sorry`).
* Issue #676 ("Sequential-composition and context-lifting layer is stubbed, making composed
  security theorems vacuous"): **open**, body refreshed 2026-09-26. Its current scope says
  (verbatim): "This remains an open **legacy `OracleReduction`** issue. … Generic legacy append
  soundness, knowledge soundness, and round-by-round security still contain admissions in
  `Composition/Sequential/Append/Security.lean`; derived wrappers inherit them. …
  `Security/Implications.lean` still have proof gaps. … Native Sumcheck (#1214), shared
  strategy execution (#1216), and native composition (#1218) are separate proved results. They
  do not repair the axiom dependencies of legacy protocol clients. Use #1 for the current
  interaction framework and #1222–#1229 for the next composition work. Keep this issue open
  until its remaining legacy claims are proved with correct assumptions or its consumers
  migrate with verified correspondence. Do not assume an unrestricted stateful composition
  statement is provable merely because its components are secure from the same fresh
  initialization." The last sentence is a warning that the admitted `append_rbrKnowledgeSoundness`
  (stateful shared oracle, second component proved from a fresh `init`) may be unprovable as
  stated; leanerVM's port avoids the problem by requiring both components at the same `init`
  and `impl` and, for completeness, the second from every deterministic state.

Consequence for the blueprint's plan "the port is deleted, and its two names in
`Component.lean` replaced by ArkLib's, when the pin moves past #615" (`:260`, `:1143-1144`,
`:1429`): there is no evidence that #615 will merge in its current form (conflicting, pre-module,
on a framework ArkLib now calls legacy, section F). The condition should be stated as "when a
revision of ArkLib contains a proved guarded-first append for
`rbrKnowledgeSoundnessWorstCaseWith`", whichever pull request brings it, and the plan should
allow that this never happens on the legacy framework (finding *the deletion condition of the
port names a pull request that may not merge*).

## E. Perfect completeness

### E.1 ArkLib's definition

`ArkLib/OracleReduction/Security/Basic.lean:89-105` (ArkLib `dca90385`, read with `git show`):

```lean
def completeness (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (completenessError : ℝ≥0) : Prop :=
  ∀ stmtIn : StmtIn,
  ∀ witIn : WitIn,
  (stmtIn, witIn) ∈ relIn →
    let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
      QueryImpl.addLift impl challengeQueryImpl
    Pr[fun ⟨⟨_, (prvStmtOut, witOut)⟩, stmtOut⟩ =>
        ((stmtOut, witOut) ∈ relOut ∧ prvStmtOut = stmtOut) | OptionT.mk do
          (simulateQ pImpl (reduction.run stmtIn witIn).run).run' (← init)] ≥ 1 - completenessError

/-- A reduction satisfies **perfect completeness** if it satisfies completeness with error `0`. -/
def perfectCompleteness (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) : Prop :=
  completeness init impl relIn relOut reduction 0
```

In words: for every `(stmtIn, witIn)` in the input relation, run the honest prover and the
verifier (`Reduction.run`, `Execution.lean:209-216`: the prover runs, then the verifier on the
transcript; challenges answered uniformly by `challengeQueryImpl`, shared oracle by `impl` from
a state drawn by `init`); the probability that the run does not fail, the verifier's output
statement with the prover's output witness is in the output relation, **and** the prover's
output statement equals the verifier's, is at least `1 − ε`. Perfect completeness is `ε = 0`,
so probability 1 (`perfectCompleteness_eq_prob_one`, `:165`). Failure (the verifier rejecting)
counts against completeness. `OracleReduction.perfectCompleteness` (`:469`) is the same for
`toReduction`.

### E.2 What the composition theorem needs

leanerVM's `Component.Complete.append` (`Component.lean:162-169`) applies
`OracleReduction.append_perfectCompleteness_of_guarded_verifiers`
(`Composition/Sequential/OracleCompleteness.lean:56-67`, proved, probe `AxiomsArkLibBuilt`):

`.lake/packages/Arklib/ArkLib/OracleReduction/Composition/Sequential/OracleCompleteness.lean:54-67` (ArkLib `dca90385`):

```lean
/-- Oracle reductions with guarded ordinary verifiers compose perfectly when prover execution
factors at the seam and the suffix is perfectly complete from every shared state. -/
theorem append_perfectCompleteness_of_guarded_verifiers
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    (V₁ : R₁.toReduction.verifier.GuardedForm) (V₂ : R₂.toReduction.verifier.GuardedForm)
    (hSeam : ∀ hn : 0 < n,
      R₁.prover.OutputIsPure ∨ pSpec₂.dir ⟨0, hn⟩ = .P_to_V)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : ∀ s : σ, R₂.perfectCompleteness (pure s) impl rel₂ rel₃) :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  change (R₁.append R₂).completeness init impl rel₁ rel₃ 0
  simpa only [add_zero] using
    append_completeness_of_guarded_verifiers R₁ R₂ V₁ V₂ hSeam h₁ h₂
```

Its hypotheses: guarded forms of both plain verifiers (so that a run is "the prover's run,
then a deterministic check and verdict", `GuardedCompleteness.lean:44-48`); the seam condition
`hSeam` (if the second protocol has a round: the first prover's output is a pure function of
its state, `Prover.OutputIsPure`, *or* the second protocol starts with a prover message), which
is what makes the appended prover's execution factor into the two provers' executions
(`Prover.SimulatedAppendFactorization`, `Append/Simulation.lean:131-153`); completeness of the
first component from `init`; and completeness of the second **from every deterministic state
`pure s`** of the shared oracle, because the second component starts in whatever state the
first left. leanerVM asks every component for completeness from every `init` (`Complete.complete`,
`Component.lean:84-85`), which gives both. Over the empty shared oracle the guarded forms and
the pure outputs are automatic (C.2).

### E.3 Completeness with an error

ArkLib at the pin composes completeness **with errors**, and the errors add:
`Reduction.append_completeness_of_guarded_verifiers` (`GuardedCompleteness.lean:161-173`,
error `ε₁ + ε₂`), `OracleReduction.append_completeness_of_guarded_verifiers`
(`OracleCompleteness.lean:39-52`), and the `n`-ary `seqCompose_completeness_of_guarded_verifiers`
(`GuardedNary.lean:45-59`, `OracleCompleteness.lean:77-99`, error `Σ i, ε i`); all proved
(probe `AxiomsArkLibBuilt`). The perfect versions are their `ε = 0` corollaries. So a phase
complete only up to an error can be composed in ArkLib today.

leanerVM's spine cannot take one: `Component.Complete.complete` is `perfectCompleteness`
(`Component.lean:84-85`), `Complete.append` uses the perfect theorem, and the blueprint's
`FlockInterface` (`docs/roadmap/protocol-blueprint.md:1083`) demands
`perfectCompleteness : reduction.perfectCompleteness …`. The blueprint's list of wrong
readings, item 20 (`:1323-1325`), says: "Perfect completeness needs no exceptional-challenge
clause in Layers 4–8 and 10: no inverse of a challenge is taken. Flock's `(1 + r_eq)⁻¹` at
`r_eq = 1` is #3's, inside `flockError`. Witness: `piop_perfectCompleteness` has no side
condition on challenges." The pinned Rust Flock prover does take that inverse
(`crates/flock/src/zerocheck.rs:117`, `let g0 = (claim + r_eq * g1) * (F192::ONE + r_eq).inv();`),
which is undefined at `r_eq = 1` in characteristic 2 (the Rust `inv` returns 0 there,
`crates/primitives/src/field/gf2_64x3.rs:144-153`, so the honest prover sends a wrong `g0`).
Whether the honest Flock prover then fails is for the Flock reviewer; if it does, the Flock
phase has completeness error `1/|E|` per such challenge, not 0, and a completeness failure
cannot be charged to `flockError`, which is a soundness error. Then `FlockInterface`'s
`perfectCompleteness` field is unsatisfiable, `Phases.Complete` cannot be built for the real
protocol, and `piop_perfectCompleteness` is vacuous for it. The fix is available at the pin:
give `Component.Complete` an error field and use the additive theorems (finding *the spine's
completeness cannot carry an error*).

## F. What the new pin `7653a901` changes for the blueprint

The review's object is `main` at `b435631`, pinned to ArkLib `dca90385`. On 2026-09-29 the
owner merged `144c5aa` ("chore(deps): upgrade to Lean 4.34.1"), which moves the pins to ArkLib
`7653a901` (347 commits later; the revision this dossier had read as `origin/main`), VCVio
`a4232d08`, CompPoly `572f9973`, Lean `v4.34.1`. What follows was read in
`.lake/packages/Arklib` at `7653a901` and `.lake/packages/VCVio` at `a4232d08`; the probes'
outputs are about the old pin and were not re-run (the checkout cannot run Lean until rebuilt).

### F.1 The admitted theorems of the old pin are still admitted

ArkLib's axiom baseline shrinks from 291 to 286 entries between the pins, but among the
declarations of the composition layer, the implications, the lifting, Fiat–Shamir and the
sumcheck specification **none was removed and none added** (the two baselines were compared by
name over the prefixes `Verifier.`, `OracleVerifier.`, `Reduction.`, `OracleReduction.`,
`Sumcheck.`, `fiatShamir`, `SendSingleWitness`, `NoInteraction`, `Extractor.`,
`CodingTheory.rs_mca`). Code-line `sorry` counts at the new pin: `Security/Implications.lean`
9 (unchanged), `Append/Security.lean` 4 (unchanged: `append_soundness`, `append_knowledgeSoundness`,
`append_rbrSoundness`, `append_rbrKnowledgeSoundness`), `General.lean` 2, `FiatShamir/Basic.lean` 1,
`LiftContext/Reduction.lean` 10, `Sumcheck/Spec/SingleRound.lean` 13 (one fewer than the old
pin; the leaves `verifier_rbrKnowledgeSoundness` and the lens instances remain). So, for the
blueprint's ledger: the knowledge-soundness composition (A2), the round-by-round ⇒ plain
implications (A3), context lifting (A4), Fiat–Shamir completeness (A5) and the sumcheck
round-by-round knowledge soundness and completeness (A1) are exactly as admitted at the new
pin as at the old. `OracleVerifier.numQueries` is still `sorry` (`Basic.lean:505-507`),
`Commitment.extractability` still has `False` for its body (`Commitments/Functional/Basic.lean:249-254`),
`fiatShamir_completeness` is still stated for the constant challenge oracle
(`FiatShamir/Basic.lean:163-173`).

### F.2 `OracleReduction` is now the "legacy" framework; the typed framework has no knowledge notion

ArkLib's guide already called `ArkLib/OracleReduction/` "legacy IOR abstractions and security
theory" and `ArkLib/Interaction/` "typed interactions and dependent reduction foundations" at
the old pin (`AGENTS.md`, unchanged at `7653a901`). Between the pins `ArkLib/Interaction/`
grew from 7 to 28 files (+7280 lines) and `ArkLib/ProofSystem/Sumcheck/Interaction/` was
created (22 files, +3963 lines): the design documents (`docs/design/05-roadmap.md`, dated
2026-09-26) say the composition milestones "C1–C8 are merged" and "the immediate goal is to
complete native Sumcheck: computable messages and honest execution, round-by-round security,
and precisely stated extraction guarantees". At `7653a901`:

* the typed framework proves *plain* soundness and completeness of composed interactions and
  of native sumcheck (`Interaction/CompositionSoundness.lean`: `run_appendFlat_soundness*`;
  `Sumcheck/Interaction/ProtocolSoundness.lean:201 execute_soundness`,
  `ProtocolCompleteness.lean:110 execute_perfectCompleteness`), with no `sorry` under
  `ArkLib/Interaction/` or `Sumcheck/Interaction/` per its status page;
* it defines **no** knowledge soundness, no round-by-round notion and no extractor: a search
  for `knowledgeSound`, `rbrKnowledge`, `RoundByRound` and `extractor` in those two trees finds
  nothing;
* issue #676 (refreshed 2026-09-26, C.3) directs composition work to the typed framework
  ("Use #1 for the current interaction framework and #1222–#1229 for the next composition
  work") and keeps the legacy admissions open "until its remaining legacy claims are proved
  with correct assumptions or its consumers migrate with verified correspondence".

Consequences. (1) The spine's vocabulary (`OracleReduction`, `OracleVerifier.toVerifier`,
`KnowledgeStateFunction`, `rbrKnowledgeSoundnessWorstCaseWith`, `GuardedForm`,
`OracleReduction.append`, the guarded completeness theorems, `Verifier.GuardedForm.ofEmpty`)
exists at the new pin with the same shapes (checked by name); leanerVM's port compiled
against it with proof-only edits (F.3). (2) Nothing in the typed framework can replace the
master theorems today: it has no notion of knowledge soundness. (3) The blueprint's
expectation that upstream will prove the legacy admissions (its ledger's "Action" column,
`docs/roadmap/protocol-blueprint.md:257-267`; "the port is deleted … when the pin moves past
#615") runs against upstream's stated direction, which is migration rather than repair
(finding *the blueprint plans on a framework upstream calls legacy*). The status file's line
"the spine stays on `OracleReduction`, whose security definitions the new executor does not
yet carry" (`protocol-status.md:201`) is the accurate description and should become the
blueprint's.

### F.3 The probability API

VCVio at `a4232d08` introduces the notation `Pr{let x ← mx}[p x]` (`prEvent`,
`VCVio/EvalDist/ProbabilityNotation.lean:27`) and keeps `probEvent` with the lemma
`Pr{let x ← mx}[p x] = Pr[ p | mx]` (`VCVio/EvalDist/Defs/Basic.lean:1102`), so the two
spellings denote the same number. ArkLib at `7653a901` restates every security definition in
the new notation (the `diff` of `Security/RoundByRound.lean` between the pins is the notation
and the lemma names `probEvent_*` → `prEvent_*`, `OptionT.prEvent_mk_*`; the mathematical
content of `KnowledgeStateFunction`, `rbrKnowledgeSoundnessWorstCase(With)` and the two
implications is unchanged). leanerVM `144c5aa` follows: `git diff b435631 144c5aa --
LeanerVM/Protocol` is 77 lines in, 76 out, confined to proofs and notation
(`GuardedVerdict.lean`, `UniformSample.lean`, `KnowledgeAppend.lean`: `Pr[P | c]` →
`Pr{let x ← c}[P x]`, `if_pos`/`dif_pos` → `ite_eq_left`/`dite_eq_left`, `probEvent_mono` →
`prEvent_mono`; `PublicInput.lean` 10 lines, `Field.lean` 15 lines for CompPoly's new `K`).
`docs/dependencies.md` at `144c5aa` says the bridges' "relations, extraction conditions, and
error bounds are retained" and asks to "review these statement changes alongside the kernel
audit, rather than relying on successful elaboration alone". The statements of the two
theorems of `KnowledgeAppend.lean` differ from `b435631` only in the spelling of the three
probabilities they mention (`state_full`'s hypothesis and the two `calc` blocks); I read the
diff and confirm no other change to a statement. The probes of this dossier are written in
the old notation; at the new pin they would need the same mechanical rewriting before they run
(unverified: no Lean run is possible in the checkout).

### F.4 The local port is still needed

`Composition/Sequential/Append/` at `7653a901` has the same eleven files as at `dca90385` and
no `Knowledge.lean`; pull request #615 is open and conflicting (C.3). The local
`KnowledgeAppend.lean` remains the only proved guarded-first knowledge append, and
`Component.Security.append` depends on it at both revisions.

### F.5 The other named pull requests and issues (state on 2026-09-29, `gh api`, read-only)

| Number | Kind | Title | State | Created / updated |
| --- | --- | --- | --- | --- |
| #615 | PR | feat(ring-switching): add reusable packing proofs and protocol integrations | open, conflicting | 2026-07-07 / 2026-09-08 |
| #676 | issue | Sequential-composition and context-lifting layer is stubbed, making composed security theorems vacuous | open | 2026-08-02 / 2026-09-26 |
| #627 | issue | Design: the BCS transform as a change of oracle implementation (QueryImpl), with a staged opening plan | open | 2026-07-10 / 2026-07-11 |
| #818 | PR | feat(gkr): formalize the GKR protocol with perfect completeness | open | 2026-08-31 / 2026-09-04 |
| #848 | PR | feat(dsfs): prove Theorems 6.1 and 6.2 | open | 2026-09-03 / 2026-09-17 |
| #469 | PR | feat(dsfs): statements of Section 5 | open | 2026-04-19 / 2026-09-17 |
| #383 | PR | feat: completeness and rbrKnowledgeSoundness of FRI-Binius protocols | open | 2026-03-03 / 2026-09-26 |
| #992 | PR | feat(fri): prove end-to-end soundness of the computable IOP | open | 2026-09-22 / 2026-09-22 |
| #1128 | PR | feat(sumcheck): expose honest round polynomial identities | open | 2026-09-24 / 2026-09-24 |
| #1129 | PR | test(sumcheck): cover collision, degree and challenge-order controls | open | 2026-09-24 / 2026-09-24 |
| #900 | issue | feat(data): formalize extension-ring block readout | open | 2026-09-18 / 2026-09-24 |
| #901 | issue | feat(data): formalize multiset product injectivity and collision bounds | open | 2026-09-18 / 2026-09-24 |
| #926 | PR (draft) | feat(lift-context): close the structural obligations in LiftContext/Reduction.lean | open | 2026-09-21 / 2026-09-21 |

None is merged. The status file's dates ("open since 2026-09-08" for #615, "since 2026-09-04"
for #818) are last-update dates, not opening dates (minor).

## G. Findings

Severities as the brief defines them. "Blueprint" is `docs/roadmap/protocol-blueprint.md` at
`144c5aa` (its ArkLib text is unchanged from `b435631` except the pins table).

### G.1 The existential form of round-by-round knowledge soundness has no knowledge content (critical, as a warning; not a defect of a leanerVM theorem)

*Evidence.* `Extractor.RoundByRound` (`Security/RoundByRound.lean:77-86` at `dca90385`) is
a structure of unconstrained functions; probe `Extractors` builds `chooser R`, which selects a
witness by `Classical.choice`, and proves `chooser_sound :
rbrKnowledgeSoundnessWorstCaseWith … (chooser R) … (fun _ => 0)` for the verifier that decides
the language of any relation `R`. ArkLib's own `toRoundByRoundOfRel` (`:118-123`) does the
same. *Classification:* a deviation forced by an upstream library; ArkLib has no notion of
running time. *Consequence for leanerVM:* `piop_rbrKnowledgeSoundness_exists` and any theorem
stated with `rbrKnowledgeSoundness`/`rbrKnowledgeSoundnessWorstCase` (the blueprint's Layer
9 `FlockInterface.rbrKnowledgeSoundness : … rbrKnowledgeSoundnessWorstCase …`, `:1084`, and its
Layer 10 sketch `:1127-1129`) are soundness statements, not knowledge statements. The named
form the spine uses is adequate only together with a reading of the extractor. *Proposed
change.* In the blueprint's row for `rbrKnowledgeSoundness` (`:239`) and in the wrong-readings
item 24 (`:1333`), add: "ArkLib's extractor type accepts a classical choice (ArkLib's
`toRoundByRoundOfRel` is one); a theorem in the existential forms `rbrKnowledgeSoundness` or
`rbrKnowledgeSoundnessWorstCase` therefore proves soundness only. Every interface and theorem
of this roadmap is stated in the `With` form with a compiled extractor, and the compiled
status is checked by a `def` without `noncomputable` at each phase's `Security`." Change
`FlockInterface.rbrKnowledgeSoundness` (`:1084`) to the `With` form with named extractor and
state function.

### G.2 The spine's completeness cannot carry an error, and Flock may need one (major)

*Evidence.* `Component.Complete.complete` is `perfectCompleteness`
(`LeanerVM/Protocol/ToArkLib/Component.lean:84-85`); the blueprint's `FlockInterface` demands
`perfectCompleteness` (`:1083`) and item 20 of the wrong readings (`:1323-1325`) charges the
Flock inverse's failure at `r_eq = 1` to `flockError`, a soundness error. The pinned Rust
prover takes the inverse (`crates/flock/src/zerocheck.rs:117`), which is 0 at `r_eq = 1`
(`crates/primitives/src/field/gf2_64x3.rs:144-153`). ArkLib at both pins composes
completeness with additive errors (`Reduction.append_completeness_of_guarded_verifiers`
`GuardedCompleteness.lean:161-173`, the oracle and `n`-ary forms, section E.3), proved.
*Classification:* an error of the blueprint (if the honest Flock prover fails at `r_eq = 1`,
which the Flock reviewer must confirm; otherwise a note). *Proposed change.* Add a field
`err : ℝ≥0` to `Component.Complete` (or to `Component.Def`) with
`complete : ∀ init impl, D.red.completeness init impl relIn relOut err`, compose by
`OracleReduction.append_completeness_of_guarded_verifiers` (`err₁ + err₂`), state
`piop_completeness` with the sum and `piop_perfectCompleteness` as its corollary when every
phase's error is 0; give `FlockInterface` a completeness error; rewrite item 20 as "no phase
of Layers 4–8 and 10 takes an inverse of a challenge; the Flock phase's completeness error is
its own field and is summed".

### G.3 The blueprint plans on a framework ArkLib calls legacy, and on a pull request that may not merge (major)

*Evidence.* Section F.2 and C.3: `AGENTS.md` at both pins, issue #676's refreshed scope,
`docs/design/05-roadmap.md` at `7653a901`; #615 open and conflicting; no relevant admission
lifted between the pins. The blueprint's ledger says of A2 "the port is deleted … when the
pin moves past #615" (`:260`, `:1143`, `:1429`) and of A3 "the plain corollary is stated once
the implication lands upstream" (`:261`). *Classification:* an error of the blueprint's plan.
*Proposed change.* Replace the A2 action by "kept until ArkLib, on whatever framework, proves
a guarded-first append for the worst-case named form; if the legacy framework is not
repaired, the port stays as a `ToArkLib` candidate"; replace A3's action by "the plain
corollary is stated from the transcript-level reading (this dossier's `PlainReading` probe
proves it in 40 lines) and a union bound proved locally, since upstream has no plan to prove
`rbrKnowledgeSoundness_implies_knowledgeSoundness`"; add to the ledger a row "typed
Interaction framework: no knowledge soundness at `7653a901`; migration of the spine is not
possible until it has one".

### G.4 Fiat–Shamir and BCS: ArkLib has no statement to serve as the witness obligation (major)

*Evidence.* Blueprint A5 (`:263`): "Named interfaces `FiatShamirSecurity` and `BcsSecurity`
with the upstream theorem as witness obligation". At both pins: `fiatShamir_completeness`
(`FiatShamir/Basic.lean:163-173`) is admitted **and** initialises the challenge oracle to the
constant function `fun ⟨i, _⟩ => default`, so it is not a random-oracle statement and is false
in general for a protocol with a non-zero completeness error whose honest prover fails at the
default challenge (my inference, not machine-checked); Fiat–Shamir soundness is a `TODO`
(`:175`); the round-by-round ⇒ state-restoration statements are commented out
(`Implications.lean:230-254`); `BCSTransform` is commented out (`BCS/Basic.lean`);
`Commitment.extractability` is `False` under quantifiers (`Commitments/Functional/Basic.lean:250-255`).
Also, `Verifier.fiatShamir` (`FiatShamir/Basic.lean:130-136`) applies to a plain `Verifier`
whose messages are whole; on `toVerifier` of the IOPP it would hash entire oracle messages, so
the blueprint's `verify_iff_compiled` sketch, "`Verifier.fiatShamir (leanVmIopp …).verifier`
accepts … under the BLAKE2s challenge oracle" (`:1218-1221`), names an ArkLib definition that
does not describe leanVM's compiled verifier (Merkle roots in the transcript, openings in the
proof). *Classification:* an error of the blueprint. *Proposed change.* State in A5 that no
ArkLib theorem, at either pin, states Fiat–Shamir or BCS knowledge soundness, that
`fiatShamir_completeness` as stated is not the random-oracle model, and that `FiatShamirSecurity`
and `BcsSecurity` are assumed interfaces whose witness obligation is the literature (the
paper quoted in D.3, Theorem 3.15) until ArkLib states them; drop `Verifier.fiatShamir` from
`verify_iff_compiled` or apply it to a verifier of the compiled (Merkle-root) protocol.

### G.5 The error bundled in `Component.Def` makes every phase and the composed protocol noncomputable (minor, auditability)

*Evidence.* `publicInputPhase` is `noncomputable` "because of the error alone"
(`PublicInput.lean:374-381`); probe `ExtractorsExpectedFailure` shows that the verifier and
the extractor reached through the phase's definition are rejected by the compiler.
`leanVmVerifier P := P.toDef.red.verifier` and `piopExtractor P S` take the bundle `P` as an
argument, so on the real protocol neither is compiled; the blueprint promises "the honest
prover is computable" (`:1145`) and "the extractor computes" (`:1333`) and plans
code-generation probes. *Proposed change.* Move `err` out of `Component.Def` into the
`Security` structure (it is a property of the soundness proof, not of the reduction), or
keep the reduction in a separate computable structure that `Def` extends; then `leanVmPiop`,
`leanVmVerifier` and `piopExtractor` compile.

### G.6 Line references and names in the blueprint's ArkLib table (minor)

`MvPolynomial.schwartz_zippel_counting` does not exist (`schwartz_zippel_counting`, root
namespace); `prob_eval_zero_le_div` is a `PMF` statement, not a VCVio one; `Sumcheck.Domain`
is `SumcheckDomain`; `Direction` is in `Prelude.lean`; `fsChallengeOracle` is in
`ProtocolSpec/Basic.lean:854`; `OracleInterface`'s `answer` is at `:76`; the theorem the spine
uses for completeness, `OracleReduction.append_perfectCompleteness_of_guarded_verifiers`, is
not in the table; `CheckClaim`'s oracle variant checks nothing at run time; the sumcheck
specification's perfect completeness is admitted too (A1). Section B.2 has the corrected
entries.

### G.7 `Component.Complete`'s two side conditions are derivable (note)

Over `[]ₒ`, `Verifier.GuardedForm.ofEmpty` and `Prover.instOutputIsPureEmpty`
(`Composition/Sequential/NoAmbient.lean:39-55`, both pins) give `guarded` and `outputPure` for
every component; leanerVM proves them by hand (`PublicInput.guarded`, `sendVerifierPure`).
Keeping the hand-written guarded forms is defensible (the check is readable), but the fields
could be defaults, shrinking what a phase author must supply.

### G.8 Locally re-implemented objects that ArkLib has (note)

`Component.passThrough` (`ToArkLib/PassThrough.lean`) is ArkLib's `ReduceClaim.oracleReduction`
with identity oracle map (`ReduceClaim.lean:282-323`, proved completeness and existential
round-by-round knowledge soundness `:441`); `Component.sendOracle` (`ToArkLib/SendOracle.lean`)
is `SendSingleWitness.oracleReduction` (`SendWitness.lean:395-443`, whose completeness is
admitted at both pins and whose knowledge soundness is only in the coordinate-wise
special-soundness form). The local versions are justified by the `With` form with a guarded
form as data; the docstring of `SendOracle.lean:6` says so for `SendSingleWitness`, the one of
`PassThrough.lean` does not name `ReduceClaim`. `ToVCVio/UniformSample.lean`'s bound for a
subsingleton bad set has no ArkLib counterpart in VCVio's vocabulary (ArkLib's
`prob_eval_zero_le_div` is on `PMF`).

### G.9 Negative results

* The definitions `KnowledgeStateFunction`, `rbrKnowledgeSoundnessWorstCaseWith`,
  `perfectCompleteness`, `GuardedForm`, `OutputIsPure` were read in full at `dca90385`; no
  way was found to satisfy `rbrKnowledgeSoundnessWorstCaseWith` at error 0 for a verifier that
  accepts a false statement, other than through the extractor (G.1) or through an empty
  output-witness type (which makes the output relation empty and is visible in the statement).
* The port `KnowledgeAppend.lean` was diffed line by line against #615's file: only the
  differences listed in C.1.
* The composed error is per challenge with no additive term, and the seam round is handled
  (`backward_right`, `extractMid_seam`); read in full, no gap found.
* Every `#print axioms` run reports the three standard axioms only for leanerVM's declarations.

## A. The objects, from scratch (ArkLib at `dca90385`; snippets read with `git show` at that commit)

Read in dependency order. A `Type` is a set of values; `Fin n` is `{0, …, n−1}`; a `structure`
is a record; a `class` is a record found automatically by type; `Prop` is a proposition;
`OracleComp spec α` (VCVio) is a computation that may ask questions to the oracles named by
`spec` and returns an `α`; `ProbComp` is `OracleComp` over one uniform-sampling oracle;
`OptionT m α` adds a failure outcome to `m α`; `Pr[p | c]` is the probability that the
outcome of `c` satisfies `p` (failure is not an outcome; VCVio at `f9dc47d9`); `StateT σ m`
threads a state of type `σ`.

**`Direction`** — who speaks in a round.

`ArkLib/OracleReduction/Prelude.lean:66-69` (ArkLib `dca90385`):

```lean
inductive Direction where
  | P_to_V  -- Message
  | V_to_P -- Challenge
deriving DecidableEq, Inhabited, Repr
```

**`ProtocolSpec n`** — the schedule of an `n`-round protocol: who speaks and the type of what is sent.

`ArkLib/OracleReduction/ProtocolSpec/Basic.lean:30-36` (ArkLib `dca90385`):

```lean
@[ext]
structure ProtocolSpec (n : ℕ) where
  /-- The direction of each message in the protocol. -/
  dir : Fin n → Direction
  /-- The type of each message in the protocol. -/
  «Type» : Fin n → Type
deriving Inhabited
```

**Message and challenge indices, messages, challenges** — the rounds of each direction, as subsets of `Fin n`, and their types.

`ArkLib/OracleReduction/ProtocolSpec/Basic.lean:50-58` (ArkLib `dca90385`):

```lean
/-- Subtype of `Fin n` for the indices corresponding to messages in a protocol specification -/
@[reducible, simp]
def MessageIdx (pSpec : ProtocolSpec n) :=
  {i : Fin n // pSpec.dir i = Direction.P_to_V}

/-- Subtype of `Fin n` for the indices corresponding to challenges in a protocol specification -/
@[reducible, simp]
def ChallengeIdx (pSpec : ProtocolSpec n) :=
  {i : Fin n // pSpec.dir i = Direction.V_to_P}
```


`ArkLib/OracleReduction/ProtocolSpec/Basic.lean:68-77` (ArkLib `dca90385`):

```lean
@[reducible, inline, specialize, simp]
def Message (pSpec : ProtocolSpec n) (i : MessageIdx pSpec) := pSpec.«Type» i.val

/-- Unbundled version of `Message`, which supplies the proof separately from the index. -/
@[reducible, inline, specialize, simp]
def Message' (pSpec : ProtocolSpec n) (i : Fin n) (_ : pSpec.dir i = .P_to_V) := pSpec.«Type» i

/-- The type of the `i`-th challenge in a protocol specification -/
@[reducible, inline, specialize, simp]
def Challenge (pSpec : ProtocolSpec n) (i : ChallengeIdx pSpec) := pSpec.«Type» i.val
```

**`FullTranscript`, `Transcript k`** — the list of all `n` entries, and its prefix of length `k` (the full transcript is `Transcript (Fin.last n)` definitionally).

`ArkLib/OracleReduction/ProtocolSpec/Basic.lean:104-105` (ArkLib `dca90385`):

```lean
@[reducible, inline, specialize]
def FullTranscript (pSpec : ProtocolSpec n) := (i : Fin n) → pSpec.«Type» i
```


`ArkLib/OracleReduction/ProtocolSpec/Basic.lean:261-263` (ArkLib `dca90385`):

```lean
@[reducible, inline, specialize]
def Transcript (k : Fin (n + 1)) (pSpec : ProtocolSpec n) : Type :=
  (pSpec⟦:k.val⟧).FullTranscript
```

**Concatenation of schedules** — `pSpec₁ ++ₚ pSpec₂` runs the first then the second; `seqCompose` iterates it over a family.

`ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:38-43` (ArkLib `dca90385`):

```lean
/-- Appending two `ProtocolSpec`s -/
abbrev append (pSpec : ProtocolSpec m) (pSpec' : ProtocolSpec n) : ProtocolSpec (m + n) :=
  ⟨Fin.vappend pSpec.dir pSpec'.dir, Fin.vappend pSpec.Type pSpec'.Type⟩

@[inherit_doc]
infixl : 65 " ++ₚ " => ProtocolSpec.append
```


`ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:358-362` (ArkLib `dca90385`):

```lean
@[inline]
def seqCompose {m : ℕ} {n : Fin m → ℕ} (pSpec : ∀ i, ProtocolSpec (n i)) :
    ProtocolSpec (Fin.vsum n) where
  dir := Fin.vflatten (fun i => (pSpec i).dir)
  «Type» := Fin.vflatten (fun i => (pSpec i).Type)
```

**`OracleInterface M`** — how a value of type `M` is queried: a query type and an answer, given as an oracle context over `ReaderM M` (the value is read, the answer computed). `Response q` and `answer m q` are derived. leanerVM's instance for a column has queries in `E^n` and answers the multilinear extension (`LeanerVM/Protocol/Field.lean:96-105` at `b435631`).

`ArkLib/OracleReduction/OracleInterface.lean:54-57` (ArkLib `dca90385`):

```lean
@[ext]
class OracleInterface (Message : Type u) where
  Query : Type v
  toOC : OracleContext Query (ReaderM Message)
```


`ArkLib/OracleReduction/OracleInterface.lean:67-78` (ArkLib `dca90385`):

```lean
def Response {Message : Type*} [O : OracleInterface Message]
    (q : O.Query) : Type _ :=
  O.toOC.spec q

def spec {Message : Type*} [O : OracleInterface Message] :
    OracleSpec O.Query :=
  O.toOC.spec

@[implicit_reducible]
def answer {Message : Type*} [O : OracleInterface Message]
    (m : Message) (q : O.Query) : O.Response q :=
  (O.toOC.impl q).run m
```

**`Prover`** — the honest prover as a state machine: a state type per round, `input` from statement and witness, `sendMessage`/`receiveChallenge` per round (computations over the shared oracle `oSpec`), `output` the final statement and witness. Provers of the soundness games are the same structure (with any `WitIn`, `WitOut`).

`ArkLib/OracleReduction/Basic.lean:132-134` (ArkLib `dca90385`):

```lean
@[ext]
structure ProverState (n : ℕ) where
  PrvState : Fin (n + 1) → Type
```


`ArkLib/OracleReduction/Basic.lean:154-162` (ArkLib `dca90385`):

```lean
@[ext]
structure ProverRound {ι : Type} (oSpec : OracleSpec ι) {n : ℕ} (pSpec : ProtocolSpec n)
    extends ProverState n where
  /-- Send a message and update the prover's state -/
  sendMessage (i : MessageIdx pSpec) :
    PrvState i.1.castSucc → OracleComp oSpec (pSpec.Message i × PrvState i.1.succ)
  /-- Receive a challenge and update the prover's state -/
  receiveChallenge (i : ChallengeIdx pSpec) :
    PrvState i.1.castSucc → OracleComp oSpec (pSpec.Challenge i → PrvState i.1.succ)
```


`ArkLib/OracleReduction/Basic.lean:222-229` (ArkLib `dca90385`):

```lean
@[ext]
structure Prover {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut : Type)
    {n : ℕ} (pSpec : ProtocolSpec n) extends
      ProverState n,
      ProverInput StmtIn WitIn (PrvState 0),
      ProverRound oSpec pSpec,
      ProverOutput oSpec (StmtOut × WitOut) (PrvState (Fin.last n))
```

**`Verifier`** — a function of the statement and the full transcript, returning the output statement or failing (rejecting).

`ArkLib/OracleReduction/Basic.lean:247-250` (ArkLib `dca90385`):

```lean
@[ext]
structure Verifier {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn StmtOut : Type) {n : ℕ} (pSpec : ProtocolSpec n) where
  verify : StmtIn → FullTranscript pSpec → OptionT (OracleComp oSpec) StmtOut
```

**`OracleProver`** — a prover whose input statement also carries the contents of the input oracles and whose output carries the output oracles.

`ArkLib/OracleReduction/Basic.lean:255-260` (ArkLib `dca90385`):

```lean
@[reducible, inline]
def OracleProver {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) (WitIn : Type)
    (StmtOut : Type) {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type) (WitOut : Type)
    {n : ℕ} (pSpec : ProtocolSpec n) :=
  Prover oSpec (StmtIn × (∀ i, OStmtIn i)) WitIn (StmtOut × (∀ i, OStmtOut i)) WitOut pSpec
```

**`OracleVerifier`** — `verify` sees the statement and the challenges and may *query* the input oracles and the prover's messages (it never sees a message whole); `outputOracle` says which oracles it hands on: either an embedding naming, for each output oracle, an input oracle or a message it *is* (`OracleOutputEmbedding`), or a simulation computing a virtual output oracle query by query (`OracleOutputSimulation`).

`ArkLib/OracleReduction/Basic.lean:322-344` (ArkLib `dca90385`):

```lean
@[ext]
structure OracleVerifier {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    (StmtOut : Type) {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type)
    {n : ℕ} (pSpec : ProtocolSpec n)
    [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
    where

  /-- The core verification logic. Takes the input statement `stmtIn` and all verifier challenges
  `challenges` (which are determined outside this function, typically by sampling for
  public-coin protocols). Returns the output statement `StmtOut` within an `OracleComp` that has
  access to external oracles `oSpec`, input statement oracles `OStmtIn`, and prover message
  oracles `pSpec.Message`. -/
  verify : StmtIn → pSpec.Challenges →
    OptionT (OracleComp (oSpec + ([OStmtIn]ₒ + [pSpec.Message]ₒ))) StmtOut

  /-- The output family has exactly one semantic representation: either the
  legacy embedded-source form or a virtual query implementation. -/
  outputOracle :
    OracleOutputEmbedding OStmtIn pSpec.Message OStmtOut ⊕
      OracleOutputSimulation oSpec OStmtIn OStmtOut pSpec
```


`ArkLib/OracleReduction/Basic.lean:295-307` (ArkLib `dca90385`):

```lean
structure OracleOutputEmbedding {ιₛᵢ ιₛₒ : Type}
    (OStmtIn : ιₛᵢ → Type) {ιₘ : Type} (Message : ιₘ → Type)
    (OStmtOut : ιₛₒ → Type)
    [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
    [Oₘ : ∀ i, OracleInterface (Message i)]
    [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)] where
  embed : ιₛₒ ↪ ιₛᵢ ⊕ ιₘ
  hEq : ∀ i, OStmtOut i = match embed i with
    | Sum.inl j => OStmtIn j
    | Sum.inr j => Message j
  outputInterface_heq : ∀ i, match embed i with
    | Sum.inl j => HEq (Oₛₒ i) (Oₛᵢ j)
    | Sum.inr j => HEq (Oₛₒ i) (Oₘ j)
```

**`toVerifier`** — the plain verifier of an oracle verifier: answers its queries from the actual oracle contents and messages of the transcript, and materialises the output oracles (D.5).

`ArkLib/OracleReduction/Basic.lean:490-496` (ArkLib `dca90385`):

```lean
def toVerifier : Verifier oSpec (StmtIn × ∀ i, OStmtIn i) (StmtOut × (∀ i, OStmtOut i)) pSpec where
  verify := fun ⟨stmt, oStmt⟩ transcript => OptionT.mk <|
    Option.map (fun stmtOut =>
      (stmtOut, verifier.materializeOutput
        transcript.challenges oStmt transcript.messages)) <$>
      simulateQ (OracleInterface.simOracle2 oSpec oStmt transcript.messages)
        (verifier.verify stmt transcript.challenges).run
```

**`Reduction`, `OracleReduction`, `OracleProof`** — a prover and a verifier; an oracle prover and an oracle verifier; an oracle reduction whose output is a Boolean with no output oracle and no output witness.

`ArkLib/OracleReduction/Basic.lean:624-628` (ArkLib `dca90385`):

```lean
@[ext]
structure Reduction {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n) where
  prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec
  verifier : Verifier oSpec StmtIn StmtOut pSpec
```


`ArkLib/OracleReduction/Basic.lean:632-641` (ArkLib `dca90385`):

```lean
@[ext]
structure OracleReduction {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) (WitIn : Type)
    (StmtOut : Type) {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type) (WitOut : Type)
    {n : ℕ} (pSpec : ProtocolSpec n)
    [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)] [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
    where
  prover : OracleProver oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec
  verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec
```


`ArkLib/OracleReduction/Basic.lean:669-675` (ArkLib `dca90385`):

```lean
@[reducible] def OracleProof {ι : Type} (oSpec : OracleSpec ι)
    (Statement : Type) {ιₛᵢ : Type} (OStatement : ιₛᵢ → Type) (Witness : Type)
    {n : ℕ} (pSpec : ProtocolSpec n)
    [Oₛᵢ : ∀ i, OracleInterface (OStatement i)]
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)] :=
  @OracleReduction ι oSpec Statement ιₛᵢ OStatement Witness Bool Empty
    (fun _ : Empty => Unit) Unit n pSpec Oₛᵢ Oₘ (fun i => nomatch i)
```

**A run** (`Execution.lean`) — `Prover.runToRound` folds the rounds: at a challenge round the challenge is obtained by a query to the challenge oracle `[pSpec.Challenge]ₒ` (one oracle per challenge round, trivial query) and handed to `receiveChallenge`; at a message round `sendMessage` runs. `Reduction.run` runs the prover, then the verifier on the transcript; the verifier's failure makes the run fail.

`ArkLib/OracleReduction/Execution.lean:96-110` (ArkLib `dca90385`):

```lean
def processRound (j : Fin n)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (currentResult : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript j.castSucc × prover.PrvState j.castSucc)) :
      OracleComp (oSpec + [pSpec.Challenge]ₒ)
        (pSpec.Transcript j.succ × prover.PrvState j.succ) := do
  let ⟨transcript, state⟩ ← currentResult
  match hDir : pSpec.dir j with
  | .V_to_P => do
    let challenge ← pSpec.getChallenge ⟨j, hDir⟩
    letI newState := (← prover.receiveChallenge ⟨j, hDir⟩ state) challenge
    return ⟨transcript.concat challenge, newState⟩
  | .P_to_V => do
    let ⟨msg, newState⟩ ← prover.sendMessage ⟨j, hDir⟩ state
    return ⟨transcript.concat msg, newState⟩
```


`ArkLib/OracleReduction/Execution.lean:209-216` (ArkLib `dca90385`):

```lean
def Reduction.run (stmt : StmtIn) (wit : WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
        ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut) := do
  -- `ctxOut` contains both the output statement and witness after running the prover
  let proverResult ← reduction.prover.run stmt wit
  let stmtOut ← liftM (reduction.verifier.run stmt proverResult.1).run
  return ⟨proverResult, ← stmtOut.getM⟩
```

In the security definitions the challenge oracle is implemented by uniform sampling (`challengeQueryImpl`) and the shared oracle `oSpec` by `impl : QueryImpl oSpec (StateT σ ProbComp)` from an initial state drawn by `init : ProbComp σ`; leanerVM's shared oracle is empty (`[]ₒ`), so `init` and `impl` are inert and the master theorems quantify over them.

`ArkLib/OracleReduction/ProtocolSpec/Basic.lean:732-734` (ArkLib `dca90385`):

```lean
def challengeQueryImpl {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)] :
    QueryImpl ([pSpec.Challenge]ₒ'challengeOracleInterface) ProbComp :=
  fun q => $ᵗ (pSpec.Challenge q.1)
```

**Completeness** — section E.1. **Soundness** — for every prover and statement outside the input language, the run ends in the output language with probability at most the error; failure counts for the verifier.

`ArkLib/OracleReduction/Security/Basic.lean:272-283` (ArkLib `dca90385`):

```lean
def soundness (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (soundnessError : ℝ≥0) : Prop :=
  ∀ WitIn WitOut : Type,
  ∀ witIn : WitIn,
  ∀ prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec,
  ∀ stmtIn ∉ langIn,
    let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
      impl.addLift challengeQueryImpl
    letI reduction := Reduction.mk prover verifier
    Pr[fun ⟨_, stmtOut⟩ => stmtOut ∈ langOut | OptionT.mk do
      (simulateQ pImpl (reduction.run stmtIn witIn).run).run' (← init)] ≤ soundnessError
```

**`Extractor.Straightline`, `knowledgeSoundness`** — a straight-line extractor gets the statement, the output witness, the transcript and both query logs and returns an input witness (or fails); knowledge soundness bounds the probability that the run's output is in the output relation while the extracted input witness is not in the input relation (an extractor that fails counts against it, `:329-342`).

`ArkLib/OracleReduction/Security/Basic.lean:248-254` (ArkLib `dca90385`):

```lean
def Straightline :=
  StmtIn → -- input statement
  WitOut → -- output witness
  FullTranscript pSpec → -- reduction transcript
  QueryLog oSpec → -- prover's query log
  QueryLog oSpec → -- verifier's query log
  OptionT (OracleComp oSpec) WitIn -- input witness
```


`ArkLib/OracleReduction/Security/Basic.lean:344-361` (ArkLib `dca90385`):

```lean
def knowledgeSoundness (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) (knowledgeError : ℝ≥0) : Prop :=
  ∃ extractor : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec,
  ∀ stmtIn : StmtIn,
  ∀ witIn : WitIn,
  ∀ prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec,
    let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
      impl.addLift challengeQueryImpl
    let exec := do
      let ⟨⟨⟨transcript, ⟨_, witOut⟩⟩, stmtOut⟩, proveQueryLog, verifyQueryLog⟩
        ← (Reduction.mk prover verifier).runWithLog stmtIn witIn
      let extractedWitIn? ←
        liftM (extractor stmtIn witOut transcript proveQueryLog.fst verifyQueryLog).run
      return (stmtIn, extractedWitIn?, stmtOut, witOut)
    Pr[fun ⟨stmtIn, extractedWitIn?, stmtOut, witOut⟩ =>
        (∀ extractedWitIn ∈ extractedWitIn?, (stmtIn, extractedWitIn) ∉ relIn) ∧
          (stmtOut, witOut) ∈ relOut
      | OptionT.mk do (simulateQ pImpl exec.run).run' (← init)] ≤ knowledgeError
```

**`Verifier.StateFunction`, `rbrSoundness`** — the round-by-round soundness of D.2; `rbrSoundnessWorstCase` (`Security/RoundByRound.lean:517-527`) is its per-prefix form.

`ArkLib/OracleReduction/Security/RoundByRound.lean:135-152` (ArkLib `dca90385`):

```lean
structure StateFunction
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    where
  toFun : (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → Prop
  /-- For all input statement not in the language, the state function is false for that statement
    and the empty transcript -/
  toFun_empty : ∀ stmt, stmt ∈ langIn ↔ toFun 0 stmt default
  /-- If the state function is false for a partial transcript, and the next message is from the
    prover to the verifier, then the state function is also false for the new partial transcript
    regardless of the message -/
  toFun_next : ∀ m, pSpec.dir m = .P_to_V →
    ∀ stmt tr, ¬ toFun m.castSucc stmt tr →
    ∀ msg, ¬ toFun m.succ stmt (tr.concat msg)
  /-- If the state function is false for a full transcript, the verifier will not output a statement
    in the output language -/
  toFun_full : ∀ stmt tr, ¬ toFun (.last n) stmt tr →
    Pr[(· ∈ langOut) | OptionT.mk do (simulateQ impl (verifier.run stmt tr)).run' (← init)] = 0
```


`ArkLib/OracleReduction/Security/RoundByRound.lean:347-365` (ArkLib `dca90385`):

```lean
def rbrSoundness (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  ∃ stateFunction : verifier.StateFunction init impl langIn langOut,
  ∀ stmtIn ∉ langIn,
  ∀ WitIn WitOut : Type,
  ∀ witIn : WitIn,
  ∀ prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec,
  ∀ i : pSpec.ChallengeIdx,
    Pr[fun ⟨transcript, challenge⟩ =>
      ¬ stateFunction i.1.castSucc stmtIn transcript ∧
        stateFunction i.1.succ stmtIn (transcript.concat challenge)
    | do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (do
          let ⟨transcript, _⟩ ← prover.runToRound i.1.castSucc stmtIn witIn
          let challenge ← liftComp (pSpec.getChallenge i) _
          return (transcript, challenge))).run' (← init)] ≤
      rbrSoundnessError i
```

**`KnowledgeStateFunction`, `Extractor.RoundByRound`, `rbrKnowledgeSoundness`, `rbrKnowledgeSoundnessWorstCase`, `rbrKnowledgeSoundnessWorstCaseWith`** — section D.1. The existential worst-case form:

`ArkLib/OracleReduction/Security/RoundByRound.lean:534-549` (ArkLib `dca90385`):

```lean
def rbrKnowledgeSoundnessWorstCase (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  ∃ WitMid : Fin (n + 1) → Type,
  ∃ extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid,
  ∃ kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor,
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

**`Verifier.GuardedForm`, `Prover.OutputIsPure`** — a verifier equal to "if `check` then `pure (out …)` else fail", with `check` and `out` as data; a prover whose `output` is a pure function of its final state.

`ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Guarded.lean:86-89` (ArkLib `dca90385`):

```lean
def IsGuardedWith (V : Verifier oSpec StmtIn StmtOut pSpec)
    (check : StmtIn → FullTranscript pSpec → Bool)
    (out : StmtIn → FullTranscript pSpec → StmtOut) : Prop :=
  ∀ stmt tr, V.verify stmt tr = if check stmt tr then pure (out stmt tr) else failure
```


`ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Guarded.lean:112-118` (ArkLib `dca90385`):

```lean
structure GuardedForm (V : Verifier oSpec StmtIn StmtOut pSpec) where
  /-- The runtime guard. -/
  check : StmtIn → FullTranscript pSpec → Bool
  /-- The verdict where the guard passes. -/
  out : StmtIn → FullTranscript pSpec → StmtOut
  /-- The verifier is guarded with exactly these. -/
  verify_eq : V.IsGuardedWith check out
```


`ArkLib/OracleReduction/Basic.lean:989-992` (ArkLib `dca90385`):

```lean
/-- The prover's output is a deterministic function of its final private state, with no
oracle queries. This condition does not constrain the message-sending steps. -/
class Prover.OutputIsPure (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) where
    output_is_pure : ∃ output : _ → _, ∀ st, P.output st = pure (output st)
```

**`append` of provers, verifiers and reductions** — `Prover.append` (`Append/Basic.lean:58-148`) runs the first prover, feeds its output to the second prover's `input` at the seam; `Verifier.append` runs the first verifier on the first half of the transcript and the second on the second half at the first's output; `OracleVerifier.append` (`:619-629`) routes the second verifier's queries through the first's output-oracle simulation; `OracleReduction.append` pairs them; `seqCompose` (`General.lean:255-268`) iterates.

`ArkLib/OracleReduction/Composition/Sequential/Append/Basic.lean:236-247` (ArkLib `dca90385`):

```lean
def Verifier.append (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂) :
      Verifier oSpec Stmt₁ Stmt₃ (pSpec₁ ++ₚ pSpec₂) where
  verify := fun stmt transcript => do
    return ← V₂.verify (← V₁.verify stmt transcript.fst) transcript.snd

/-- Compose the component provers and verifiers of two reductions. -/
def Reduction.append (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂) :
      Reduction oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂) where
  prover := Prover.append R₁.prover R₂.prover
  verifier := Verifier.append R₁.verifier R₂.verifier
```


`ArkLib/OracleReduction/Composition/Sequential/Append/Basic.lean:709-713` (ArkLib `dca90385`):

```lean
def OracleReduction.append (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂) :
      OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₃ OStmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂) where
  prover := Prover.append R₁.prover R₂.prover
  verifier := OracleVerifier.append R₁.verifier R₂.verifier
```

**`Extractor.RoundByRound.append`, `Verifier.StateFunction.append`** — the appended extractor runs the second extractor on the second half at the statement `verify s tr₁` that a *given* verdict function assigns, then the first on the first half; at the seam it hands the second extractor's round-0 witness to the first's `extractOut` (`Append/StateFunction.lean:75-139`). The appended (language) state function is disjunctive past the seam (`:292`, docstring `:17-19`). The knowledge version is leanerVM's port (section C).

`ArkLib/OracleReduction/Composition/Sequential/Append/StateFunction.lean:73-81` (ArkLib `dca90385`):

```lean
/-- Compose round-by-round extractors using a deterministic intermediate-statement function.
The composed witness family retains the first extractor's final witness at the boundary. -/
def RoundByRound.append
    {WitMid₁ : Fin (m + 1) → Type} {WitMid₂ : Fin (n + 1) → Type}
    (E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁)
    (E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂) :
      Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₃ (pSpec₁ ++ₚ pSpec₂)
        (Fin.append (m := m + 1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega)) where
```

**Completeness composition** — section E.2 and E.3 (`append_perfectCompleteness_of_guarded_verifiers`, `append_completeness_of_guarded_verifiers`, `seqCompose_*`), all proved at both pins.

**`Reduction.fiatShamir`, `Verifier.fiatShamir`, the challenge oracle** — the "slow" Fiat–Shamir: the challenge of round `i` is the answer of an oracle whose query is the statement together with all messages before round `i` (`challengeOracleInterfaceSR`); the transformed verifier receives all messages in one round, derives the challenges by querying that oracle and runs the original verifier.

`ArkLib/OracleReduction/ProtocolSpec/Basic.lean:829-834` (ArkLib `dca90385`):

```lean
@[reducible, inline, specialize]
def challengeOracleInterfaceSR (StmtIn : Type) (pSpec : ProtocolSpec n) :
    ∀ i, OracleInterface (pSpec.Challenge i) := fun i =>
  { Query := StmtIn × pSpec.MessagesUpTo i.1.castSucc
    toOC.spec := fun _ => pSpec.Challenge i
    toOC.impl := fun _ => read }
```


`ArkLib/OracleReduction/FiatShamir/Basic.lean:129-144` (ArkLib `dca90385`):

```lean
/-- The (slow) Fiat-Shamir transformation for the verifier. -/
def Verifier.fiatShamir (V : Verifier oSpec StmtIn StmtOut pSpec) :
    NonInteractiveVerifier (∀ i, pSpec.Message i) (oSpec + fsChallengeOracle StmtIn pSpec)
      StmtIn StmtOut where
  verify := fun stmtIn proof => do
    let messages : pSpec.Messages := proof 0
    let transcript ← (messages.deriveTranscriptFS (oSpec := oSpec) stmtIn)
    Option.getM (← (V.verify stmtIn transcript).run)

/-- The Fiat-Shamir transformation for an (interactive) reduction, which consists of applying the
  Fiat-Shamir transformation to both the prover and the verifier. -/
def Reduction.fiatShamir (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    NonInteractiveReduction (∀ i, pSpec.Message i) (oSpec + fsChallengeOracle StmtIn pSpec)
      StmtIn WitIn StmtOut WitOut where
  prover := R.prover.fiatShamir
  verifier := R.verifier.fiatShamir
```

**`Commitment.Scheme`, `binding`, `extractability`** — keys, `commit : ComKey → Data → OracleComp (Commitment × Decommitment)`, and an opening *proof* for the statement "commitment, query, response" with witness "data, decommitment". `binding` bounds any adversary's probability of opening one commitment to two different responses at the same query; `extractability` is a placeholder (its body is `False`).

`ArkLib/Commitments/Functional/Basic.lean:51-70` (ArkLib `dca90385`):

```lean
/-- Key generation for a commitment scheme, producing a committer key and a verifier key. -/
structure KeyGen where
  keygen : OracleComp oSpec (ComKey × VerifKey)

/-- The commitment algorithm, parameterized by the committer key and the data to commit. -/
structure Commit where
  commit : ComKey → Data → OracleComp oSpec (Commitment × Decommitment)

variable [O : OracleInterface Data] {n : ℕ} (pSpec : ProtocolSpec n)

/-- The opening protocol used to prove a claimed oracle response for committed data. -/
structure Opening where
  opening : (ComKey × VerifKey) →
    Proof oSpec (Commitment × (q : O.Query) × O.Response q) (Data × Decommitment) pSpec

/-- A commitment scheme with key generation, commitment, and opening algorithms. -/
structure Scheme extends
    KeyGen oSpec ComKey VerifKey,
    Commit oSpec Data Commitment Decommitment ComKey,
    Opening oSpec Data Commitment Decommitment ComKey VerifKey pSpec
```


`ArkLib/Commitments/Functional/Basic.lean:220-223` (ArkLib `dca90385`):

```lean
def binding (bindingError : ℝ≥0) : Prop :=
  ∀ AuxState : Type,
  ∀ adversary : BindingAdversary oSpec Data Commitment AuxState pSpec ComKey,
    bindingExperiment init impl scheme AuxState adversary ≤ bindingError
```

**Generic components** — `DoNothing` (identity reduction, `ProofSystem/Component/DoNothing.lean:33-66`), `ReduceClaim` (zero rounds, maps the statement and the witness, `ReduceClaim.lean:50-66`; oracle version `:282-323`), `CheckClaim` (zero rounds; the plain verifier `guard`s a decidable predicate, `CheckClaim.lean:72-73`; the oracle verifier is a pass-through, `:228-231`), `RandomQuery` (one challenge, a query; the verifier outputs the query and both oracles; the output relation says the two oracles agree there, `RandomQuery.lean:45-57, :94-111`), `SendSingleWitness` (one prover message, the witness, which becomes an oracle, `SendWitness.lean:316-343`; completeness admitted, `:440-443`).

`ArkLib/ProofSystem/Component/ReduceClaim.lean:61-66` (ArkLib `dca90385`):

```lean
/-- The verifier for the `ReduceClaim` reduction. -/
def verifier : Verifier oSpec StmtIn StmtOut !p[] where
  verify := fun stmt _ => pure (mapStmt stmt)

/-- The reduction for the `ReduceClaim` reduction. -/
def reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut !p[] where
```


`ArkLib/ProofSystem/Component/CheckClaim.lean:71-73` (ArkLib `dca90385`):

```lean
@[inline, specialize]
def verifier : Verifier oSpec Statement Statement !p[] where
  verify := fun stmt _ => do guard (pred stmt); return stmt
```


`ArkLib/ProofSystem/Component/RandomQuery.lean:44-57` (ArkLib `dca90385`):

```lean
@[reducible, simp]
def relIn : Set ((StmtIn × ∀ i, OStmtIn OStatement i) × WitIn) :=
  { ⟨⟨(), oracles⟩, ()⟩ | oracles 0 = oracles 1 }

/--
The output relation states that if the verifier's single query was `q`, then
`a` and `b` agree on that `q`, i.e. `answer a q = answer b q`.
-/
@[reducible, simp]
def relOut : Set ((StmtOut OStatement × ∀ i, OStmtOut OStatement i) × WitOut) :=
  { ⟨⟨q, oStmt⟩, ()⟩ | answer (oStmt 0) q = answer (oStmt 1) q }

@[reducible]
def pSpec : ProtocolSpec 1 := ⟨!v[.V_to_P], !v[Query OStatement]⟩
```

**Sumcheck specification** — a round's statement is the running target and the challenges so far; the oracle statement is a multivariate polynomial of individual degree `≤ deg` in `n` variables; the round relation says the sum of the polynomial over the remaining cube (`D^(n−i)`) at the challenges equals the target; a round is "prover sends a univariate of degree `≤ deg`, verifier sends a field element"; the whole protocol is the `seqCompose` of `n` rounds. Both the completeness and the round-by-round knowledge soundness of the specification are admitted at both pins (B.3). `SumcheckDomain` (`Domain.lean:55-59`) generalises the evaluation domain to a per-coordinate family.

`ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:130-145` (ArkLib `dca90385`):

```lean
structure StatementRound (i : Fin (n + 1)) where
  -- The target value for sum-check
  target : R
  -- The challenges sent from the verifier to the prover from previous rounds
  challenges : Fin i → R

abbrev OutputStatement := StatementRound R _ (.last n)

/-- Oracle statement for sum-check, which is a multivariate polynomial over `n` variables of
  individual degree at most `deg`, equipped with the poly evaluation oracle interface. -/
@[reducible]
def OracleStatement : Unit → Type := fun _ => R⦃≤ deg⦄[X Fin n]

/-- The sum-check relation for the `i`-th round, for `i ≤ n` -/
def relationRound (i : Fin (n + 1)) :
    Set (((StatementRound R n i) × (∀ i, OracleStatement R n deg i)) × Unit) :=
```


`ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:149-154` (ArkLib `dca90385`):

```lean
namespace SingleRound

/-- The protocol specification for a single round of sum-check.
Has the form `⟨!v[.P_to_V, .V_to_P], !v[R⦃≤ deg⦄[X], R]⟩` -/
@[reducible]
def pSpec : ProtocolSpec 2 :=
```


`ArkLib/ProofSystem/Sumcheck/Spec/General.lean:129-133` (ArkLib `dca90385`):

```lean
def pSpec : ProtocolSpec (Fin.vsum (fun _ : Fin n => 2)) :=
  ProtocolSpec.seqCompose (fun _ => SingleRound.pSpec R deg)
  -- n * 2
  -- fun i => if i % 2 = 0 then (.P_to_V, R⦃≤ d⦄[X]) else (.V_to_P, R)

```


`ArkLib/ProofSystem/Sumcheck/Spec/General.lean:209-228` (ArkLib `dca90385`):

```lean

/-- Perfect completeness for the (full) sum-check protocol -/
theorem reduction_perfectCompleteness :
    (reduction R deg D n oSpec).perfectCompleteness init impl
      (relationRound R n deg D 0) (relationRound R n deg D (.last n)) :=
  Reduction.seqCompose_perfectCompleteness_of_guarded_verifiers
    (fun i => StatementRound R n i × ∀ j, OracleStatement R n deg j)
    (fun _ => Unit) init impl (relationRound R n deg D)
    (SingleRound.reduction R n deg D oSpec)
    (fun _ => inferInstance) (SingleRound.verifierGuardedForm R n deg D oSpec)
    (fun i s => SingleRound.reduction_perfectCompleteness (init := pure s) i)

/-- Round-by-round knowledge soundness with error `deg / |R|` per challenge for the (full)
  sum-check protocol -/
theorem oracleVerifier_rbrKnowledgeSoundness [Fintype R] :
    (oracleVerifier R deg D n oSpec).rbrKnowledgeSoundness init impl
      (relationRound R n deg D 0) (relationRound R n deg D (.last n))
      (fun _ => (deg : ℝ≥0) / (Fintype.card R)) :=
  OracleVerifier.seqCompose_rbrKnowledgeSoundness
    (rel := relationRound R n deg D)
```


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
