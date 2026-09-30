# Dossier `code-pubinput`: the public-input phase as built

Reviewed: leanerVM `main` at `b435631` (the checkout sits on the branch
`docs/protocol-blueprint-review`; since the merge `8d3ea7d` of 2026-09-30 its tracked files are
those of `main` at `144c5aa`, see C.9; every Lean citation below is at `b435631`). Ground truth: leanVM
at the pin `a386121f84292f6fa663aaa3e570c15bc0240ea2` (confirmed by `git rev-parse HEAD` in
`/home/scaraven/Documents/leanEthereum/leanVM`). Libraries at the pins of `b435631`: ArkLib `dca90385`
(confirmed by `git rev-parse HEAD` in `.lake/packages/Arklib` on 2026-09-29, before the
packages moved), VCVio `f9dc47d9`, CompPoly `3468b38c`.

## 0. Summary

**What was examined.** `LeanerVM/Protocol/PublicInput.lean` (400 lines) and the three generic
modules it uses, the spine files it is stated over, its tests, the blueprint's convention row
"Public input", Layer 8, Layer 3's paragraph on the lines and acceptance test 10, the status'
decisions 13 and 15 and its finding on the pinned verifiers' check, the earlier review, and
the pinned specification, Rust, Python and recursion guest. Nine Lean probes were compiled
against the pinned libraries before the environment was lost (C.9); two more are written and
not run; two are argued on paper. Every probe is a copy of the phase's module with one change.

**Conclusions.**

1. **The check on the prover's message is not load-bearing for any theorem of the phase**
   (G.1). The verifier pools the values it computes from the statement (`pooled`), not the
   values it received, so a verifier that reads the message and ignores it is perfectly
   complete and round-by-round knowledge sound against the same seams, same extractor, same
   error `1/|E|`; only the last round of the state function changes. Proved in general: for
   **every** message function and **every** Boolean check the message passes, the phase has a
   `Phase.Security` (`securityG`, no `sorryAx`), with instances "no check, no message", "no
   check, forty-two zeros", "the check with the cells swapped and a prover to match". The
   requirement that a missing or weakened check leave knowledge soundness unprovable is not met
   for this check and cannot be met by any theorem about the phase as designed: the unchecked
   verifier is sound. The earlier review's "each of five wrong verifiers breaks a stated
   theorem" was true of the build it read and is false of the code merged (its own compression
   removed the dependence); the status repeats it.
2. **What the theorems do catch**, each refuted in Lean on a concrete instance with no
   extractor, no state function and no error below one able to repair it: a verifier that pools
   the prover's values without checking them (mutation 2); one that checks the first value only
   and pools the prover's values (3b); one that does not pool the claim of a line whose value is
   not sent (5). A wrong check is caught by completeness only against a fixed honest prover
   (7a, written, not run); an extra check is caught regardless (8, written, not run); a wrong
   point breaks both (6, on paper). Pooling the values sent, as the specification literally says
   and as all three deployed verifiers do, makes the check load-bearing for both theorems.
3. **The theorems are about a verifier none of the three executable verifiers runs** (G.2):
   they check one equation on the two words and pool the scalars sent; the Lean checks per
   limb and pools computed values. The blueprint assigns the deployed check's soundness to
   Layer 12, which can neither state it (its refinement theorem cannot be an "iff" against a
   Rust-faithful `verify`) nor detect the difference (its fixture is an honest proof). The owed
   object is a second `Phase.Def` with its own `Phase.Security`, in Layer 8; its key lemma is
   proved here (`accepts_two_challenges`: the words' equation with true claims at two distinct
   challenges forces the cells and zero top limbs), error `1/|E|`. Recommendation: build the
   deployed phase, let the master theorems and Layer 12 consume it, keep the specification's
   as the reference, and report the specification/implementation disagreement to leanVM.
4. **The top limb** (G.3): the phase pools the third claim only because the instance lists a
   third line, and every theorem of the phase and of the spine holds for an instance that lists
   two; what a missing third line breaks is the adaptor's `satisfiedBy_witnessOf` (not built),
   at `SatisfiedBy.word0_eq`, whose right-hand side has a zero top limb by the type of
   `PublicInput`; behind it `constraintSoundness` and T4. Acceptance test 10's witness exists
   in the tests and rejects what it says, on the pool rather than on the theorem.
5. `PublicLine.sent` is the right primitive and is pinned by prose only (G.4); the message type
   is wider than the transcript (G.5); status text is stale (G.6).

**Findings by severity.** Major: G.1 (the check is not load-bearing; design error introduced by
an audit-surface compression), G.2 (the deployed verifier is unproved and its debt misassigned;
specification and implementations disagree). Minor: G.3 (top-limb audit trail), G.4 (`sent`
pinned by prose), G.6 (stale status). Note: G.5.

**What could not be done.** After the merge of Lean 4.34.1 into the checkout (C.9), no Lean
could run: mutation 6, the deployed phase's full `Phase.Security` (4b), the two-line-instance
display for D.1, and `#print axioms` on the original file are unverified; probes 7a and 8 are
written and unrun. The recorded outputs of the nine probes that ran are unaffected.

---

## C. Mutation probes

### C.0 Method

**How a probe is built.** The phase's module has private imports and private lemmas
(`lineClaim_holds_iff`, `line_challenge_unique`, `pooled_mem_pub`, `bad_challenge_unique`,
`simulateQ_queryValues`, `prover_run_support`), which a plain file cannot reach. So each probe is
a **copy of the whole module, kept a `module` file**, under the namespace
`LeanerVM.Protocol.Probe<k>`, with one mutation applied by exact string replacement, and with
new declarations appended after the copied text. The script is
`probes/code-pubinput/tools/mutate.py`; the replacements of mutation `k` are
`probes/code-pubinput/tools/m<k>.py`; the shared text (the two refutation lemmas, the pool that
reads the message) is `probes/code-pubinput/tools/lib.py`. The probe does not import the
original `LeanerVM.Protocol.PublicInput`.

**The baseline.** `Probe0Baseline.lean` is the module with only the namespace changed (the
`diff` against the source is the two namespace lines). It compiles:

```text
$ flock .claude/reports/blueprint-review/logs/lean.lock lake env lean \
    -D autoImplicit=false -D relaxedAutoImplicit=false \
    .claude/reports/blueprint-review/probes/code-pubinput/Probe0Baseline.lean
'LeanerVM.Protocol.Probe0.publicInputSecurity' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Probe0.publicInputComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```

Every probe below was run with the same command on its own file, from the repository root,
under the shared lock.

**What "caught" means.** For each mutation three things are reported.

- *Unchanged proofs*: the verifier is changed, the verdict lemma `verifier_verify` is restated
  for the verifier as changed (it describes what the verifier does), and `complete`,
  `stateFunction`, `rbr` are left as they are, except where a one-line adaptation is forced by
  the restated verdict. The first declaration that stops compiling is reported with the
  compiler's message.
- *Repair*: whether another state function (or another honest prover) proves the theorem for the
  mutated verifier at the same error. If it does, the mutation **is not caught**: a developer
  who makes the mutation can still produce `Phase.Security`, and with it the master theorems.
- *Refutation*: where no repair exists, a Lean theorem that the mutated verifier has **no**
  round-by-round knowledge soundness at any error below one (whatever the extractor, the
  intermediate witness types and the state function), or is not perfectly complete. Then the
  mutation **is caught**.

**The objects, for a reader who does not know ArkLib** (pin `dca90385`).

- A *verifier* (`Verifier`) maps a statement and a full transcript to an optional output
  statement. An *oracle verifier* (`OracleVerifier`) does the same but reads the prover's
  messages and the input oracles through queries; `toVerifier` turns it into a verifier by
  answering the queries.
- *Perfect completeness* of a reduction (a prover and a verifier) against an input relation and
  an output relation (`Reduction.perfectCompleteness`,
  `ArkLib/OracleReduction/Security/Basic.lean`): on every input in the input relation, with
  probability one the verifier accepts, its output is in the output relation with the prover's
  output witness, **and the prover's output statement equals the verifier's**
  (`perfectCompleteness_eq_prob_one`, `:164-175`).
- A *round-by-round extractor* (`Extractor.RoundByRound`,
  `ArkLib/OracleReduction/Security/RoundByRound.lean:80-91`) maps witnesses backwards, round by
  round, from the output witness to the input witness. Here all witnesses are `Unit`, since the
  stack is the oracle.
- A *knowledge state function* (`Verifier.KnowledgeStateFunction`, same file `:164-186`) is a
  predicate on (round, statement, partial transcript, intermediate witness) with three laws:
  at round 0 it is the input relation (`toFun_empty`); across a **prover** message, if it holds
  after the message it held before (`toFun_next`); if the verifier can output a statement in
  the output relation, it holds of the full transcript (`toFun_full`).
- *Round-by-round knowledge soundness for a given extractor and state function*
  (`Verifier.rbrKnowledgeSoundnessWorstCaseWith`, same file `:553-568`): for every statement,
  every challenge round and every transcript prefix, the probability over the fresh challenge
  that the state goes from false to true is at most the error of that challenge. The
  existential form `rbrKnowledgeSoundnessWorstCase` (`:537-551`) says that some witness types,
  some extractor and some state function exist.

```lean
-- ArkLib dca90385, ArkLib/OracleReduction/Security/RoundByRound.lean:553-568
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

**The verifier under test**, as it stands (`LeanerVM/Protocol/PublicInput.lean:126-137` and
`:229-234`):

```lean
/-- What the verifier pools: the claims it received, then one claim per public line. -/
def pooled (s : I.Stmt × TableOut I) (r : E) : I.Stmt × PubOut I :=
  (s.1, ⟨s.2.columns ++ (I.publicLines s.1).map (lineClaim I r)⟩)

/-- The values the verifier expects in the prover's message: the values at the challenge of the
lines whose value is sent, in order. -/
def expectedValues (input : I.Stmt) (r : E) : List E :=
  ((I.publicLines input).filter (·.sent)).map (lineValue I r)

/-- The verifier's check: the prover's message is the expected values. -/
def check (s : I.Stmt × TableOut I) (r : E) (cs : List E) : Bool :=
  decide (cs = expectedValues I s.1 r)
```

```lean
def verifier : OracleVerifier []ₒ (I.Stmt × TableOut I) (TheOracle I)
    (I.Stmt × PubOut I) (TheOracle I) pSpec where
  verify := fun s chals ↦ do
    let cs ← liftM queryValues
    if check I s (chals ⟨0, rfl⟩) cs then pure (pooled I s (chals ⟨0, rfl⟩)) else failure
  outputOracle := .inl (keepOracles (TheOracle I) pSpec)
```

The observation everything below follows from: **`pooled` does not take `cs`**. The message
enters the verifier in `check` and nowhere else, and the proof of `rbr`
(`PublicInput.lean:350-366`) never mentions `check`.

### C.1 The two refutation lemmas (shared by the probes)

They are stated for the phase's schedule `pSpec` (a challenge in `E`, then a message `List E`)
and proved in each probe that uses them; source in `tools/lib.py`, first developed in the plain
file `ScratchRefute.lean` against the real `LeanerVM.Protocol.PublicInput` (exit 0).

```lean
/-- The transcript `(r, cs)`, built as a knowledge state function reads it. -/
def tr2 (r : E) (cs : List E) : pSpec.FullTranscript :=
  Transcript.concat (m := (1 : Fin 2)) cs
    (Transcript.concat (m := (0 : Fin 2)) r (default : Transcript 0 pSpec))

/-- A guarded verifier on the schedule `pSpec` that, on one statement outside the input
relation, has for every challenge a message it accepts into the output relation is not
round-by-round knowledge sound at an error below one: whatever the extractor and the state
function. -/
theorem not_rbr {StmtIn StmtOut : Type} {relIn : Set (StmtIn × Unit)}
    {relOut : Set (StmtOut × Unit)}
    (V : Verifier []ₒ StmtIn StmtOut pSpec) (G : V.GuardedForm)
    (impl : QueryImpl []ₒ (StateT Unit ProbComp))
    (stmt : StmtIn) (hin : (stmt, ()) ∉ relIn) (msg : E → List E)
    (hacc : ∀ r, G.check stmt (tr2 r (msg r)) = true ∧
      (G.out stmt (tr2 r (msg r)), ()) ∈ relOut)
    (ε : pSpec.ChallengeIdx → ℝ≥0) (hε : ε ⟨0, rfl⟩ < 1) :
    ¬ V.rbrKnowledgeSoundnessWorstCase (pure ()) impl relIn relOut ε := by
  rintro ⟨WitMid, ext, kSF, h⟩
  have hbound := h stmt ⟨0, rfl⟩ (default : Transcript 0 pSpec)
  -- Every challenge is a bad challenge.
  have hall : ∀ r : E, ∃ witMid,
      ¬ kSF (Fin.castSucc 0) stmt (default : Transcript 0 pSpec)
          (ext.extractMid 0 stmt
            (Transcript.concat (m := (0 : Fin 2)) r
              (default : Transcript 0 pSpec)) witMid) ∧
        kSF (Fin.succ 0) stmt (Transcript.concat (m := (0 : Fin 2)) r
          (default : Transcript 0 pSpec)) witMid := by
    intro r
    obtain ⟨hc, hout⟩ := hacc r
    have hpos : Pr[fun stmtOut => (stmtOut, ()) ∈ relOut
        | OptionT.mk do
            (simulateQ impl (V.run stmt (tr2 r (msg r)))).run'
              (← (pure () : ProbComp Unit))] > 0 := by
      have hv : V.run stmt (tr2 r (msg r)) = pure (G.out stmt (tr2 r (msg r))) := by
        have := G.verify_eq stmt (tr2 r (msg r))
        rw [if_pos hc] at this
        exact this
      rw [hv]
      change Pr[_ | OptionT.mk (do let st ← (pure () : ProbComp Unit); (simulateQ impl
        (OptionT.run (pure (G.out stmt (tr2 r (msg r))) :
          OptionT (OracleComp []ₒ) StmtOut))).run' st)] > 0
      rw [OptionT.run_pure, simulateQ_pure]
      rw [gt_iff_lt, probEvent_pos_iff]
      refine ⟨G.out stmt (tr2 r (msg r)), ?_, hout⟩
      simp
    have hfull := kSF.toFun_full stmt (tr2 r (msg r)) () hpos
    have hnext := kSF.toFun_next 1 rfl stmt
      (Transcript.concat (m := (0 : Fin 2)) r (default : Transcript 0 pSpec))
      (msg r) _ hfull
    refine ⟨_, ?_, hnext⟩
    intro h0
    exact hin ((kSF.toFun_empty stmt _).mpr h0)
  -- So the bad event has probability one.
  have hone : Pr[fun challenge : E => ∃ witMid,
      ¬ kSF (Fin.castSucc 0) stmt (default : Transcript 0 pSpec)
          (ext.extractMid 0 stmt
            (Transcript.concat (m := (0 : Fin 2)) challenge
              (default : Transcript 0 pSpec)) witMid) ∧
        kSF (Fin.succ 0) stmt (Transcript.concat (m := (0 : Fin 2)) challenge
          (default : Transcript 0 pSpec)) witMid | $ᵗ E] = 1 := by
    rw [probEvent_eq_one_iff]
    exact ⟨by simp, fun r _ ↦ hall r⟩
  have hle : (1 : ℝ≥0∞) ≤ ((ε ⟨0, rfl⟩ : ℝ≥0) : ℝ≥0∞) := hone ▸ hbound
  exact absurd (ENNReal.coe_lt_one_iff.mpr hε) (not_lt.mpr hle)

/-- A reduction none of whose outcomes, on one input in the input relation, satisfies the
completeness event is not perfectly complete. -/
theorem not_perfectCompleteness {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)]
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) (hin : (stmtIn, witIn) ∈ relIn)
    (h : ∀ x ∈ support (reduction.run stmtIn witIn).run, ∀ result, x = some result →
      ¬ ((result.2, result.1.2.2) ∈ relOut ∧ result.1.2.1 = result.2)) :
    ¬ reduction.perfectCompleteness init impl relIn relOut := by
  intro hc
  rw [Reduction.perfectCompleteness_eq_prob_one] at hc
  have h1 := hc stmtIn witIn hin
  dsimp only at h1
  have hpos := lt_of_lt_of_eq (zero_lt_one' ℝ≥0∞) h1.symm
  obtain ⟨x, hx, hev⟩ := probEvent_pos_iff.mp hpos
  rw [OptionT.mem_support_iff, OptionT.run_mk, mem_support_bind_iff] at hx
  obtain ⟨s, _, hx⟩ := hx
  exact h (some x) (support_simulateQ_run'_subset _ _ s hx) x rfl hev
```

The first lemma is refutation in the strong sense: it denies ArkLib's **existential**
`rbrKnowledgeSoundnessWorstCase`, so no choice of extractor, witness types or state function
helps, and it holds for every error below one, not only `1/|E|`. It is stated for one choice of
the shared-oracle initial state (`pure ()`) and implementation; the phase's `Phase.Security`
owes its bound for every choice, so one choice refutes it.

### C.2 Results so far

| # | Mutation | `complete` | `stateFunction`/`rbr` unchanged | Knowledge sound by another state function? | Verdict |
| --- | --- | --- | --- | --- | --- |
| 1 | no check; lines' values pooled | compiles | `stateFunction.toFun_full` fails | **yes, same error** (`rbr'`, `publicInputSecurity'`) | **not caught** |
| 2 | no check; prover's values pooled | compiles | `toFun_full` fails | no: refuted (`not_knowledgeSound`, toy) | caught by knowledge soundness |
| 3a | first value checked; lines' values pooled | compiles | `toFun_full` fails | **yes, same error** (`rbr'`) | **not caught** |
| 3b | first value checked; prover's values pooled | compiles | `toFun_full` fails | no: refuted (two lines sent) | caught by knowledge soundness |
| 4a | the pinned verifiers' equation; lines' values pooled | compiles | `toFun_full` fails | **yes, same error** (`rbr'`) | **not caught** |
| 4b | the pinned verifiers' equation; prover's values pooled (the deployed verifier) | by C.5 and C.6's arguments | | sound at `1/|E|` by a new argument; key lemma proved (C.13) | a sound verifier, not a mutation to catch |
| 5 | lines not sent are not pooled | compiles | `toFun_full` fails | no: refuted (a line not sent) | caught by knowledge soundness |
| any | any message, any check the message passes; lines' values pooled | proved (`completeG`) | | **yes, same error** (`rbrG`, `securityG`) | **not caught**, in general |
| 6 | claims pooled at a wrong point (paper, C.12) | fails at `lineClaim_holds_iff` | fails | no: both refuted on a height-4 instance | caught by completeness (unverified) |
| 7a | wrong check, honest prover unchanged (written, not run, C.10) | fails at `decide_eq_true hmsg` | compiles | (completeness refuted) | caught by completeness against a fixed prover (unverified) |
| 7b | wrong check, prover adapted, lines' values pooled (run, C.4 `swappedCheck`) | proved | | **yes, same error** | **not caught** |
| 8 | extra check (written, not run, C.11) | fails | compiles | (completeness refuted, for every prover) | caught by completeness (unverified) |

In every probe the unchanged `stateFunction` fails with the same message, at its field
`toFun_full`, because its last round names the original `check` and the original `pooled`:

```text
error: Type mismatch
  Verifier.GuardedForm.of_probEvent_pos (guarded I) init impl stmt tr (fun stmtOut => (stmtOut, x✝) ∈ Seam.pub I) h
has type
  (guarded I).check stmt tr = true ∧ ((guarded I).out stmt tr, x✝) ∈ Seam.pub I
but is expected to have type
  if h0 : ↑(Fin.last 2) = 0 then (stmt, ()) ∈ Seam.table I
  else
    if h1 : ↑(Fin.last 2) = 1 then ((pooled I stmt.1 (tr ⟨0, ⋯⟩), stmt.2), ()) ∈ Seam.pub I
    else check I stmt.1 (tr ⟨0, ⋯⟩) (tr ⟨1, ⋯⟩) = true ∧ ((pooled I stmt.1 (tr ⟨0, ⋯⟩), stmt.2), ()) ∈ Seam.pub I
```

That failure alone says little: the state function is part of the proof, not of the statement
(`Phase.Security` carries it as a field, `kSF`), so whoever changes the verifier changes it too.
The decisive columns are the last two.

(Details of each probe: sections C.3 to C.13.)

### C.3 Mutation 1: the check removed, the lines' values pooled. NOT CAUGHT

File `probes/code-pubinput/Probe1NoCheck.lean` (replacements in `tools/m1.py`).

The mutation (the verifier reads the message and ignores it), with the verdict lemma and the
guarded form restated for it:

```lean
  verify := fun s chals ↦ do
    let _cs ← liftM queryValues
    pure (pooled I s (chals ⟨0, rfl⟩))
```

```lean
theorem verifier_verify (s : I.Stmt × TableOut I) (o : ∀ i, TheOracle I i)
    (tr : pSpec.FullTranscript) :
    (verifier I).toVerifier.verify (s, o) tr = pure (pooled I s (tr 0), o) := by
  -- the original proof, ending `rw [simulateQ_optionT_bind_run, simulateQ_queryValues, pure_bind]; rfl`
def guarded : (verifier I).toVerifier.GuardedForm where
  check := fun _ _ ↦ true
  out := fun p tr ↦ (pooled I p.1 (tr 0), p.2)
  verify_eq := fun ⟨s, o⟩ tr ↦ (verifier_verify I s o tr).trans (if_pos rfl).symm
```

`complete` compiles with one line adapted (`have hc : (guarded I).check (s, o) pr.1 = true := rfl`).
The unchanged `stateFunction` fails at `toFun_full` (message in C.2; line 341 of the probe).

The repair, appended to the probe, is the state function with the check dropped from its last
round; `rbr'` has the original proof of `rbr`, word for word:

```lean
def stateFunction' :
    (verifier I).toVerifier.KnowledgeStateFunction init impl (Seam.table I) (Seam.pub I)
      (extractor I) where
  toFun := fun m stmt tr _ ↦
    if h0 : m.val = 0 then ((stmt, ()) ∈ Seam.table I)
    else ((pooled I stmt.1 (tr ⟨0, by omega⟩), stmt.2), ()) ∈ Seam.pub I
  toFun_empty := fun _ _ ↦ Iff.rfl
  toFun_next := fun m hm stmt tr msg w h ↦ by
    have hm1 : m = 1 := by
      fin_cases m
      · exact absurd hm (by decide)
      · rfl
    subst hm1
    exact h
  toFun_full := fun stmt tr _ h ↦
    (Verifier.GuardedForm.of_probEvent_pos (guarded I) init impl stmt tr _ h).2

theorem rbr' :
    (verifier I).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl (Seam.table I)
      (Seam.pub I) (fun _ ↦ Unit) (extractor I) (stateFunction' I init impl)
      (fun _ ↦ error) := by
  -- the original proof of `rbr`

def publicInputSecurity' (I : M3Instance) :
    Phase.Security I (publicInputPhase I) (Seam.table I) (Seam.pub I) where
  toComplete := publicInputComplete I
  witMid := fun _ ↦ Unit
  extractor := PublicInput.extractor I
  kSF := PublicInput.stateFunction' I
  rbr := PublicInput.rbr' I
```

Output (exit 1 because of the one expected error):

```text
Probe1NoCheck.lean:341:4: error: Type mismatch   [the message of C.2]
'LeanerVM.Protocol.Probe1.PublicInput.verifier_verify' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Probe1.publicInputComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Probe1.publicInputSecurity' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Probe1.publicInputSecurity'' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Reading.** `publicInputSecurity'` is a complete `Phase.Security` of the verifier that checks
nothing, against the spine's two seams, at the error `1/|E|`, on the kernel's three axioms. It
fills the field `pub` of `Phases.Security`, so `piop_rbrKnowledgeSoundness` holds of a protocol
whose public-input verifier accepts every message. This is not a defect of the theorem: the
mutated verifier **is** knowledge sound. The prover's message in this phase is a function of
public data; a verifier that recomputes it has no need to read it.

### C.4 The general form: any message, any check the message passes. NOT CAUGHT

File `probes/code-pubinput/ProbeAnyCheck.lean` (`tools/anycheck.py`): the module unchanged, and
appended to it a phase with two parameters, the prover's message `msg` and the verifier's check
`chk`.

```lean
variable (I : M3Instance)
  (msg : I.Stmt → E → List E)
  (chk : (I.Stmt × TableOut I) → E → List E → Bool)

/-- The prover sends `msg`. -/
def proverG : OracleProver []ₒ (I.Stmt × TableOut I) (TheOracle I) Unit
    (I.Stmt × PubOut I) (TheOracle I) Unit pSpec where
  PrvState
    | ⟨0, _⟩ => ((I.Stmt × TableOut I) × ∀ i, TheOracle I i) × Unit
    | _ => E × (((I.Stmt × TableOut I) × ∀ i, TheOracle I i) × Unit)
  input := _root_.id
  receiveChallenge
    | ⟨0, _⟩ => fun st ↦ pure fun r ↦ (r, st)
    | ⟨1, h⟩ => nomatch h
  sendMessage
    | ⟨0, h⟩ => nomatch h
    | ⟨1, _⟩ => fun st ↦ pure (msg st.2.1.1.1 st.1, st)
  output := fun st ↦ pure ((pooled I st.2.1.1 st.1, st.2.1.2), ())

/-- The verifier checks `chk` and pools the lines' values. -/
def verifierG : OracleVerifier []ₒ (I.Stmt × TableOut I) (TheOracle I)
    (I.Stmt × PubOut I) (TheOracle I) pSpec where
  verify := fun s chals ↦ do
    let cs ← liftM queryValues
    if chk s (chals ⟨0, rfl⟩) cs then pure (pooled I s (chals ⟨0, rfl⟩)) else failure
  outputOracle := .inl (keepOracles (TheOracle I) pSpec)
```

```lean
/-- Perfect completeness, whatever the message and the check, as long as the one passes the
other. -/
theorem completeG (hchk : ∀ s r, chk s r (msg s.1 r) = true) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (OracleReduction.mk (proverG I msg) (verifierG I chk)).perfectCompleteness init impl
      (Seam.table I) (Seam.pub I)

/-- Round-by-round knowledge soundness at `1/|E|`, whatever the check: no hypothesis on
`chk`. -/
theorem rbrG :
    (verifierG I chk).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl (Seam.table I)
      (Seam.pub I) (fun _ ↦ Unit) (extractor I) (stateFunctionG I chk init impl)
      (fun _ ↦ error)

/-- Both halves, for every message and every check the message passes. -/
def securityG (I : M3Instance) (msg : I.Stmt → E → List E)
    (chk : (I.Stmt × TableOut I) → E → List E → Bool)
    (hchk : ∀ s r, chk s r (msg s.1 r) = true) :
    Phase.Security I (phaseG I msg chk) (Seam.table I) (Seam.pub I)

/-- No check at all, and a prover that sends nothing. -/
def noCheckNoMessage (I : M3Instance) := securityG I (fun _ _ ↦ []) (fun _ _ _ ↦ true)
  fun _ _ ↦ rfl

/-- No check at all, and a prover that sends forty-two zeros. -/
def noCheckJunk (I : M3Instance) :=
  securityG I (fun _ _ ↦ List.replicate 42 0) (fun _ _ _ ↦ true) fun _ _ ↦ rfl

/-- The values of the lines with their cells swapped. -/
def swappedValues (I : M3Instance) (input : I.Stmt) (r : E) : List E :=
  ((I.publicLines input).filter (·.sent)).map fun l ↦ (1 + r) * ofK l.cell1 + r * ofK l.cell0

/-- A wrong check, the cells swapped, with a prover that sends what the wrong check expects. -/
def swappedCheck (I : M3Instance) :=
  securityG I (swappedValues I) (fun s r cs ↦ decide (cs = swappedValues I s.1 r))
    fun _ _ ↦ decide_eq_true rfl

/-- The specification's phase is the instance with the expected values and their check. -/
def specification (I : M3Instance) :=
  securityG I (PublicInput.expectedValues I) (PublicInput.check I) fun _ _ ↦ decide_eq_true rfl
```

(The proofs are the module's own with `check` replaced by `chk` and `expectedValues` by `msg`;
full text in the probe file.) Output, exit 0:

```text
'LeanerVM.Protocol.ProbeAny.securityG' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.ProbeAny.noCheckNoMessage' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.ProbeAny.noCheckJunk' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.ProbeAny.swappedCheck' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.ProbeAny.specification' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Reading.** The two theorems of the phase constrain the *pool* (which claims, at which point,
with which value) and nothing else. They do not constrain the prover's message (its length, its
content), nor the check on it. The phase as merged is the instance `specification` of a family
every member of which has the same theorems. In particular:

- mutation 1 (no check), mutation 3 in the form "first value only" and mutation 4 in the form
  "the pinned verifiers' equation" are members (each also run on its own, C.5);
- mutation 7 (a wrong check) is a member **when the honest prover is changed with it**
  (`swappedCheck`). Completeness is a statement about the pair (prover, verifier), and nothing
  fixes the honest prover's message but the verifier's check. So a wrong check on this message
  is caught by completeness only if the prover is held fixed (C.10).

### C.5 Mutations 3a and 4a: a weaker check, the lines' values pooled. NOT CAUGHT

Files `Probe3a.lean`, `Probe4a.lean` (`tools/m3a.py`, `tools/m4a.py`, shared `tools/weak.py`).
The verifier's check is replaced by `checkWeak`; `check` stays defined, since the unchanged
state function names it.

```lean
/-- The weakened check: the first value only. -/                       -- mutation 3a
def checkWeak (s : I.Stmt × TableOut I) (r : E) (cs : List E) : Bool :=
  decide (cs.head? = (expectedValues I s.1 r).head?)
```

```lean
/-- The pinned verifiers' check: with two lines whose value is sent, one equation on the two
values, `c₀ + y·c₁ = e₀ + y·e₁`; with any other number, the check per value. -/   -- mutation 4a
def checkWeak (s : I.Stmt × TableOut I) (r : E) (cs : List E) : Bool :=
  match (I.publicLines s.1).filter (·.sent), cs with
  | [l₀, l₁], [c₀, c₁] => decide (c₀ + y * c₁ = lineValue I r l₀ + y * lineValue I r l₁)
  | ls, cs => decide (cs = ls.map (lineValue I r))
```

In both, `complete` compiles after the honest message is shown to pass the weak check (one line
in 3a, a case split in 4a), the unchanged `stateFunction` fails at `toFun_full` (line 354, line
365), and the state function with `checkWeak` in its last round gives `rbr'` by the original
proof. Output of both (exit 1, the one expected error each):

```text
Probe3a.lean:354:4: error: Type mismatch   [the message of C.2]
'LeanerVM.Protocol.Probe3a.PublicInput.verifier_verify' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Probe3a.PublicInput.complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Probe3a.PublicInput.stateFunction' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Probe3a.PublicInput.rbr' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Probe3a.PublicInput.rbr'' depends on axioms: [propext, Classical.choice, Quot.sound]

Probe4a.lean:365:4: error: Type mismatch   [the message of C.2]
'LeanerVM.Protocol.Probe4a.PublicInput.verifier_verify' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Probe4a.PublicInput.complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Probe4a.PublicInput.stateFunction' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Probe4a.PublicInput.rbr' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Probe4a.PublicInput.rbr'' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### C.6 Mutation 2: no check, the prover's values pooled. CAUGHT by knowledge soundness

File `Probe2TrustProver.lean` (`tools/m2.py`). This is the verifier that trusts the prover. The
pool that reads the message (shared by probes 2, 3b and 4b, in `tools/lib.py`):

```lean
/-- The claims on the lines, a line whose value is sent taking the next value of the message
(zero when the message is too short), the others the value the verifier computes. -/
def claimsFrom (r : E) : List (PublicLine I.toShape) → List E → List (ColumnClaim I)
  | [], _ => []
  | l :: ls, cs =>
    if l.sent then ⟨l.col, linePoint l.pos r, cs.headD 0⟩ :: claimsFrom r ls cs.tail
    else lineClaim I r l :: claimsFrom r ls cs

/-- The pool, with the values the prover sent. -/
def pooledFrom (s : I.Stmt × TableOut I) (r : E) (cs : List E) : I.Stmt × PubOut I :=
  (s.1, ⟨s.2.columns ++ claimsFrom I r (I.publicLines s.1) cs⟩)

/-- On the expected values, the claims are the lines' claims. -/
theorem claimsFrom_expected (r : E) (ls : List (PublicLine I.toShape)) :
    claimsFrom I r ls ((ls.filter (·.sent)).map (lineValue I r)) = ls.map (lineClaim I r)

/-- On the expected values, the pool is the pool of the lines' values. -/
theorem pooledFrom_expected (s : I.Stmt × TableOut I) (r : E) :
    pooledFrom I s r (expectedValues I s.1 r) = pooled I s r
```

The mutation:

```lean
  verify := fun s chals ↦ do
    let cs ← liftM queryValues
    pure (pooledFrom I s (chals ⟨0, rfl⟩) cs)
```

`complete` compiles (the honest message makes the two pools equal, by `pooledFrom_expected`).
The unchanged `stateFunction` fails at `toFun_full` (line 376). No repair exists: appended to
the probe, on the toy instance, with the stack `badLine` whose column 2 is `[1, 1]` where the
statement `1` says `(1, 0)`:

```lean
abbrev badLine : Column 3 := ⟨#v[1, 1, 1, 1, 1, 1, 0, 0]⟩

abbrev badStmt : (K × TableOut toy) × (∀ i, TheOracle toy i) := (((1 : K), ⟨[]⟩), fun _ ↦ badLine)

/-- The wrong stack is outside the table seam. -/
theorem badStmt_not_mem : (badStmt, ()) ∉ Seam.table toy := by
  rintro ⟨-, hl, -⟩
  have h := (hl _ (List.mem_singleton_self _)).2
  exact one_ne_zero h

/-- What a truthful prover sends: the extension of its column 2 at `(r)`. -/
def trueValue (r : E) : E :=
  CMlPolynomialEval.eval₂Mle (toy.column badLine ⟨0, 2⟩).values (algebraMap K E)
    (linePoint (n := 1) (by decide) r)

/-- The mutated verifier accepts it at every challenge, with a pool that holds of the wrong
stack. -/
theorem accepts (r : E) :
    (guarded toy).check badStmt (tr2 r [trueValue r]) = true ∧
      ((guarded toy).out badStmt (tr2 r [trueValue r]), ()) ∈ Seam.pub toy := by
  refine ⟨rfl, ?_, trivial⟩
  intro c hc
  change c ∈ [(⟨⟨0, 2⟩, linePoint (n := 1) (by decide) r, trueValue r⟩ : ColumnClaim toy)] at hc
  rw [List.mem_singleton] at hc
  subst hc
  rfl

/-- No extractor, no state function and no error below one make the mutated verifier
round-by-round knowledge sound against the two seams. -/
theorem not_knowledgeSound (ε : pSpec.ChallengeIdx → ℝ≥0) (hε : ε ⟨0, rfl⟩ < 1) :
    ¬ (verifier toy).toVerifier.rbrKnowledgeSoundnessWorstCase (pure ()) noOracle
      (Seam.table toy) (Seam.pub toy) ε :=
  not_rbr _ (guarded toy) noOracle badStmt badStmt_not_mem (fun r ↦ [trueValue r]) accepts ε hε
```

Output (exit 1, the one expected error):

```text
Probe2TrustProver.lean:376:4: error: Type mismatch   [the message of C.2]
'LeanerVM.Protocol.Probe2.PublicInput.verifier_verify' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Probe2.PublicInput.complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Probe2.PublicInput.stateFunction' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Probe2.PublicInput.rbr' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Probe2.PublicInput.not_knowledgeSound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Reading.** With the prover's values pooled, the check is what ties the pool to the statement,
and its removal is caught: there is no `Phase.Security`. This is the design of the three pinned
verifiers and of the build the earlier review read.

### C.7 Mutation 3b: first value checked, the prover's values pooled. CAUGHT by knowledge soundness

File `Probe3b.lean` (`tools/m3b.py`). Verifier: `if checkWeak … then pure (pooledFrom …) else
failure`, with `checkWeak` of mutation 3a. `complete` compiles; unchanged `stateFunction` fails
at `toFun_full` (line 390). Refuted on an instance with two lines whose value is sent, by a
prover that sends the right first value and the true extension of its wrong second column:

```lean
abbrev twoSent : M3Instance :=
  { toy with publicLines := fun v ↦
      [⟨⟨0, 0⟩, v, 1, true, by decide⟩, ⟨⟨0, 1⟩, 1, 1, true, by decide⟩] }

/-- Column 0 is `[1, 1]`, as the statement `1` says; column 1 is `[1, 0]`, not `[1, 1]`. -/
abbrev badSecond : Column 3 := ⟨#v[1, 1, 1, 0, 1, 0, 0, 0]⟩

def cheat (r : E) : List E := [(1 + r) * ofK 1 + r * ofK 1, trueValue 1 r]

theorem accepts (r : E) :
    (guarded twoSent).check badStmt (tr2 r (cheat r)) = true ∧
      ((guarded twoSent).out badStmt (tr2 r (cheat r)), ()) ∈ Seam.pub twoSent

theorem not_knowledgeSound (ε : pSpec.ChallengeIdx → ℝ≥0) (hε : ε ⟨0, rfl⟩ < 1) :
    ¬ (verifier twoSent).toVerifier.rbrKnowledgeSoundnessWorstCase (pure ()) noOracle
      (Seam.table twoSent) (Seam.pub twoSent) ε
```

```text
Probe3b.lean:390:4: error: Type mismatch   [the message of C.2]
'LeanerVM.Protocol.Probe3b.PublicInput.complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Probe3b.PublicInput.not_knowledgeSound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### C.8 Mutation 5: the claim of a line whose value is not sent is not pooled. CAUGHT by knowledge soundness

File `Probe5.lean` (`tools/m5.py`). The pool keeps only the lines whose value is sent (for
leanISA: the claim on `mem_2` is dropped); prover and verifier output the same pool; the check
is the original.

```lean
/-- The mutated pool: the claims received, then one claim per line whose value is sent. -/
def pooledSent (s : I.Stmt × TableOut I) (r : E) : I.Stmt × PubOut I :=
  (s.1, ⟨s.2.columns ++ ((I.publicLines s.1).filter (·.sent)).map (lineClaim I r)⟩)
```

`complete` compiles (a sub-list of true claims). Unchanged `stateFunction` fails at
`toFun_full` (line 359). Refuted on the toy with its one line not sent: the honest empty
message passes the check, the pool is empty, and the wrong stack is accepted at every
challenge.

```lean
abbrev noneSent : M3Instance :=
  { toy with publicLines := fun v ↦ [⟨⟨0, 2⟩, v, 0, false, by decide⟩] }

theorem accepts (r : E) :
    (guarded noneSent).check badStmt (tr2 r []) = true ∧
      ((guarded noneSent).out badStmt (tr2 r []), ()) ∈ Seam.pub noneSent

theorem not_knowledgeSound (ε : pSpec.ChallengeIdx → ℝ≥0) (hε : ε ⟨0, rfl⟩ < 1) :
    ¬ (verifier noneSent).toVerifier.rbrKnowledgeSoundnessWorstCase (pure ()) noOracle
      (Seam.table noneSent) (Seam.pub noneSent) ε
```

```text
Probe5.lean:359:4: error: Type mismatch   [the message of C.2]
'LeanerVM.Protocol.Probe5.PublicInput.complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Probe5.PublicInput.not_knowledgeSound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Reading.** Given an instance that lists the line, dropping its claim is caught. Whether the
instance lists it is another matter (section D).

### C.9 The probe environment was lost at 09:18 on 2026-09-30 (read this before trusting "not run")

Between the pause and the restart the review branch received the merge `8d3ea7d` of `main`
with `144c5aa chore(deps): upgrade to Lean 4.34.1 (#61)`, which changes `lean-toolchain`
(`v4.33.1` to `v4.34.1`) and `lake-manifest.json` (ArkLib `dca90385` to `7653a901`, VCVio
`f9dc47d9` to `a4232d08`, CompPoly `3468b38c` to `572f9973`, Clean `93c9d1ef` to `42fe4b26`,
Mathlib `0df444a3` to `d13f23b7`, PolyFun `c0c92369` to `41d3b21d` at a new URL). The first
`lake env lean` after that (mine, probe 7a) made Lake re-resolve the manifest: it checked every
package out at its new revision and **deleted and re-cloned PolyFun**, whose oleans at the old
revision are gone (`find / -name PolyFun.olean` finds nothing). The LeanerVM oleans under
`.lake/build` were built by 4.33.1 and are refused by 4.34.1 ("incompatible header"); run with
the 4.33.1 binary and a hand-made `LEAN_PATH` over the surviving package builds, they fail on
`unknown module prefix 'PolyFun'`. So from that moment **no probe can be compiled against the
pins without a rebuild**, which the rules forbid. The coordinator's restart message said
"nothing else changed"; the merge contradicts it, and it invalidated `lake env` as the way to
run probes for every agent (the brief's section 8, added afterwards, records the change and
asks for no Lean run). I edited no tracked file; the change to `.lake/packages` is Lake's
own reaction to the merged manifest. (The library sources under `.lake/packages/` are now at
the new revisions too: every library citation in this dossier was read before 09:18, or is
read with `git show <pin>:<path>` inside the package's repository.)

Probes 1, 2, 3a, 3b, 4a, 5, `ProbeAnyCheck`, `ProbeWordsLemma` and `ScratchRefute` ran before
the change, and their outputs above are as printed. Probes 7a and 8 are written (files
`Probe7a.lean`, `Probe8.lean`, replacements `tools/m7a.py`, `tools/m8.py`) and **not run**; probe
6 and the deployed-verifier phase (4b) are argued on paper below and not written. Each is
marked. Where a conclusion below rests on an unrun probe, the conclusion is stated as what the
probe is written to show, with the reason it should compile, and is flagged **unverified**.

### C.10 Mutation 7: a wrong check (the cells swapped). Caught by completeness ONLY IF the honest prover is held fixed

*With the prover changed with the check*: the probe `ProbeAnyCheck` (C.4, run) proves
`swappedCheck I : Phase.Security I (phaseG I (swappedValues I) (fun s r cs ↦ decide (cs = swappedValues I s.1 r))) (Seam.table I) (Seam.pub I)`.
Both halves hold. **Not caught.**

*With the honest prover unchanged* (file `Probe7a.lean`, **not run**): the verifier checks
`checkWrong`, the prover sends `expectedValues`, the lines' values are pooled.

```lean
/-- The values of the lines with their cells swapped: `(1 + r)·cell1 + r·cell0`. -/
def swappedValues (input : I.Stmt) (r : E) : List E :=
  ((I.publicLines input).filter (·.sent)).map fun l ↦ (1 + r) * ofK l.cell1 + r * ofK l.cell0

/-- The wrong check: the message is the swapped values. -/
def checkWrong (s : I.Stmt × TableOut I) (r : E) (cs : List E) : Bool :=
  decide (cs = swappedValues I s.1 r)
```

Expected: `complete` fails at `have hc : (guarded I).check (s, o) pr.1 = true := decide_eq_true hmsg`
(`hmsg : pr.1 1 = expectedValues I s.1 (pr.1 0)`, but the check asks for `swappedValues`); `rbr`
compiles (it never reads the check). The refutation written in the probe, on the toy at the
statement `1` with the honest stack (`honest`, column 2 `= [1, 0]`): the honest message is
`[(1 + r)·1 + r·0]`, the swapped value is `[(1 + r)·0 + r·1]`, and `1 + r = r` gives `1 = 0`; so
the check rejects at every challenge, every outcome of the run is `none`, and
`not_perfectCompleteness` (C.1, proved) concludes:

```lean
theorem honest_rejected (r : E) : checkWrong toy honestStmt.1 r (expectedValues toy 1 r) = false := by
  apply decide_eq_false
  intro h
  change [(1 + r) * ofK 1 + r * ofK 0] = [(1 + r) * ofK 0 + r * ofK 1] at h
  have h1 : ofK (1 : K) = 1 := map_one (algebraMap K E)
  have h0 : ofK (0 : K) = 0 := map_zero (algebraMap K E)
  rw [h0, h1, List.cons.injEq] at h
  have : (1 : E) = 0 := by linear_combination h.1
  exact one_ne_zero this

/-- Not perfectly complete, for every initial state and implementation of the shared oracle. -/
theorem not_complete {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    ¬ (OracleReduction.mk (prover toy) (verifier toy)).perfectCompleteness init impl
      (Seam.table toy) (Seam.pub toy) := by
  refine not_perfectCompleteness init impl _ honestStmt () honestStmt_mem ?_
  intro x hx result hres
  obtain ⟨pr, hpr, rfl⟩ := Reduction.mem_support_run_of_guarded _ (guarded toy) honestStmt () hx
  obtain ⟨hmsg, -⟩ := prover_run_support toy honestStmt.1 honestStmt.2 pr hpr
  have hc : (guarded toy).check honestStmt pr.1 = false := by
    show checkWrong toy honestStmt.1 (pr.1 0) (pr.1 1) = false
    rw [hmsg]
    exact honest_rejected (pr.1 0)
  rw [hc] at hres
  exact absurd hres (by simp)
```

**Reading.** "A wrong check makes completeness unprovable" holds against a fixed honest prover.
Nothing in the phase, the spine or the blueprint fixes the honest prover's message except the
verifier's own check; the blueprint's acceptance tests contain no transcript-level fixture for
this phase (the dumped-proof fixture is Layer 12's). So a wrong check together with a matching
prover passes both theorems; only a differential test against the Rust prover's transcript
(Layer 12's fixture) would reject it.

*With the prover's values pooled* (the deployed design, not probed): a wrong check is caught
whatever the prover, since the check is then what makes the pooled claims true of an honest
stack: with the honest prover the check rejects; with the prover adapted to the wrong check the
pooled claims carry the swapped values and are false of the honest stack (whenever
`cell0 ≠ cell1`), so completeness fails either way.

### C.11 Mutation 8: an extra check leanVM does not make. Caught by completeness

File `Probe8.lean` (**not run**). The verifier requires, on top of the check, that the message's
first value be nonzero:

```lean
/-- The check with an extra condition: the first value of the message is nonzero. -/
def checkExtra (s : I.Stmt × TableOut I) (r : E) (cs : List E) : Bool :=
  check I s r cs && decide (cs.headD 0 ≠ 0)
```

Expected: `complete` fails at the same line as in 7a (the honest message passes `check` but
`decide_eq_true hmsg` does not prove `checkExtra`); `rbr` compiles. The refutation written in
the probe: the toy at the statement `0`, whose line has cells `(0, 0)`, with the honest stack
`honest0 := ⟨#v[1, 1, 1, 1, 0, 0, 0, 0]⟩`; the line's value is `(1 + r)·0 + r·0 = 0` at every
challenge, so the extra condition fails on the honest message, and (since `check` pins the
message to that value) on every message: no prover passes, honest or adapted. So this mutation
is caught **regardless of the prover**, unlike mutation 7.

```lean
theorem honest_rejected (r : E) :
    checkExtra toy honestStmt.1 r (expectedValues toy 0 r) = false := by
  unfold checkExtra
  rw [Bool.and_eq_false_iff]
  right
  apply decide_eq_false
  intro h
  apply h
  change (1 + r) * ofK 0 + r * ofK 0 = 0
  have h0 : ofK (0 : K) = 0 := map_zero (algebraMap K E)
  rw [h0, mul_zero, mul_zero, add_zero]
```

### C.12 Mutation 6: the claims pooled at a wrong point. Caught by completeness (and by knowledge soundness)

Argued on paper; not written. Change `lineClaim` to pool at `(r, 1, 0, …, 0)` (or any point
other than `(r, 0, …, 0)`), keeping `lineValue`.

*Where the proofs stop.* `lineClaim_holds_iff` (`PublicInput.lean:141-148`) rewrites with
`eval₂Mle_linePoint l.pos`, whose left side is the extension **at `linePoint`**; with another
point the rewrite finds no instance and the lemma is unprovable (its statement is false: the
extension at `(r, 1, 0, …)` is the line through cells 2 and 3, by the selection identity
`evalMle_append_boolVec` at index 1, `ToCompPoly/Multilinear.lean:342-348`). Everything
downstream fails: `pooled_mem_pub` and so `complete`; `bad_challenge_unique` and so `rbr`.

*Completeness is refuted*, on an instance with a column of height 4 (log-height 2, so that a
second coordinate exists; the toy's columns have height 2, on which every point `(r)` is the
line point, so the toy cannot witness this mutation): one line with cells `(0, 0)`, the honest
stack `[0, 0, 1, 1]`. It is in the table seam. The pooled claim has value `lineValue = 0` and the
extension at `(r, 1)` is `(1 - r)·1 + r·1 = 1 ≠ 0` at every challenge; so the verifier's output
is outside `Seam.pub` on every outcome and `not_perfectCompleteness` applies. *Knowledge
soundness is refuted too*: the stack `[1, 1, 0, 0]` violates the line and its claims at `(r, 1)`
hold with value `0` at every challenge (`not_rbr`). Both refutations need the evaluation of a
concrete two-variable table at `(r, 1)` with `r` symbolic, which the toy's `read_eval`
(`Spine/Toy.lean:52-57`) shows `simp` can do on tables of this size. **Unverified** in Lean.

### C.13 Mutation 4b: the deployed verifier (the words' equation, the prover's values pooled). Sound at `1/|E|`, by a different argument

The deployed verifier is the mutation "4a plus 2": the check `checkWeak` of C.5 (mutation 4a)
and the pool `pooledFrom` of C.6. Its completeness holds by the argument of C.6 (the honest
message makes `pooledFrom` equal to `pooled`, and it passes the words' equation, as 4a's
`complete` shows). Its knowledge soundness at `1/|E|` is not a corollary of the phase's: the
bad event is now "some message passes the words' equation and makes all pooled claims true of a
stack outside the table seam", and the message is free. The key lemma is proved (probe
`ProbeWordsLemma.lean`, a plain file, **run before the environment change**, exit 0):

```lean
/-- What an accepting run of the pinned verifiers says at the challenge `r`, when the three
pooled claims are true of a stack whose memory limbs have cells `a ℓ` at index 0 and `b ℓ` at
index 1: the scalars are the extensions of limbs 0 and 1, the extension of limb 2 is zero, and
the equation on the words holds. -/
structure Accepts (a b : Fin 3 → K) (w₀ w₁ r c₀ c₁ : E) : Prop where
  claim₀ : (1 - r) * ofK (a 0) + r * ofK (b 0) = c₀
  claim₁ : (1 - r) * ofK (a 1) + r * ofK (b 1) = c₁
  claim₂ : (1 - r) * ofK (a 2) + r * ofK (b 2) = 0
  words : c₀ + y * c₁ = w₀ + r * (w₀ + w₁)

/-- Accepting at two distinct challenges forces the cells: the public words are the two-limb
words of the cells, and the top cells are zero. -/
theorem accepts_two_challenges {a b : Fin 3 → K} {w₀ w₁ r₁ r₂ c₀ c₁ c₀' c₁' : E}
    (hr : r₁ ≠ r₂) (h₁ : Accepts a b w₀ w₁ r₁ c₀ c₁) (h₂ : Accepts a b w₀ w₁ r₂ c₀' c₁') :
    w₀ = E.ofLimbs (a 0) (a 1) 0 ∧ w₁ = E.ofLimbs (b 0) (b 1) 0 ∧ a 2 = 0 ∧ b 2 = 0

/-- For public words with a zero top limb, as leanISA's are by type: the six cells are the four
lanes and two zeros. -/
theorem cells_eq_lanes {a b : Fin 3 → K} {p : Fin 4 → K} {r₁ r₂ c₀ c₁ c₀' c₁' : E}
    (hr : r₁ ≠ r₂)
    (h₁ : Accepts a b (E.ofLimbs (p 0) (p 1) 0) (E.ofLimbs (p 2) (p 3) 0) r₁ c₀ c₁)
    (h₂ : Accepts a b (E.ofLimbs (p 0) (p 1) 0) (E.ofLimbs (p 2) (p 3) 0) r₂ c₀' c₁') :
    (a 0 = p 0 ∧ a 1 = p 1 ∧ a 2 = 0) ∧ (b 0 = p 2 ∧ b 1 = p 3 ∧ b 2 = 0)

/-- A public word with a nonzero top limb is accepted at one challenge at most, whatever the
stack: the binding itself excludes it, without the separate rejection of `read_public`. -/
theorem top_limb_zero_of_two_challenges {a b : Fin 3 → K} {w₀ w₁ r₁ r₂ c₀ c₁ c₀' c₁' : E}
    (hr : r₁ ≠ r₂) (h₁ : Accepts a b w₀ w₁ r₁ c₀ c₁) (h₂ : Accepts a b w₀ w₁ r₂ c₀' c₁') :
    w₀.limb 2 = 0 ∧ w₁.limb 2 = 0
```

```text
'WordsLemma.accepts_two_challenges' depends on axioms: [propext, Classical.choice, Quot.sound]
'WordsLemma.cells_eq_lanes' depends on axioms: [propext, Classical.choice, Quot.sound]
'WordsLemma.top_limb_zero_of_two_challenges' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The proof is eleven lines: substituting the claims into the words' equation gives
`(1 - r)·A + r·B = (1 + r)·w₀ + r·w₁` with `A = a₀ + y·a₁`, `B = b₀ + y·b₁` in `E`; two roots
force `A = w₀`, `B = w₁` (the phase's own degree-one argument, `line_unique`, over `E` instead of
`K`); `A = ofLimbs a₀ a₁ 0` by `ofLimbs_eq`; the third claim is a line through zero. No
independence of `1, y` over `K` is used until the limbs are read off (`cells_eq_lanes`).

*The phase, if built.* Over an abstract instance the words' equation needs a shape: it combines
the sent values with the powers `1, y, y², …`, and beyond three sent lines those are dependent
over `K`, so the argument fails. The check of C.5 (mutation 4a) handles this by falling back to
the per-value check when the number of sent lines is not two; on that verifier, with
`pooledFrom`, the knowledge state function is

- round 1: `∃ cs, checkWeak s r cs = true ∧ ((pooledFrom s r cs, o), ()) ∈ Seam.pub I`,
- round 2: the same for the message sent,

and the bad-challenge uniqueness splits into: two sent lines `l₀, l₁` (then the pooled claims
force `cs` to be the true extensions, and `accepts_two_challenges` with the third claim replaced
by the unsent lines' claims), or not (then `cs = expectedValues`, `pooledFrom = pooled`, and the
existing `bad_challenge_unique`). The `List` plumbing (that `claimsFrom` holding of the stack
forces `cs` to be the true extensions of the sent lines and the unsent lines' claims) is an
induction on the lines. Estimated at 120 lines; **not written**, since the environment was lost.
Error: `1/|E|` on the one challenge, as for the specification's verifier.

---

## D. The top limb, along the chain

The user's example: "If the verifier does not check, through some reduction or claim, that the
top lane of both public inputs is 0 (the column `mem_2` at cells 0 and 1), will the
knowledge-soundness and completeness theorems catch this?"

### D.1 In the phase and the spine: no

**The third claim exists because the instance lists a third line.** The phase pools one claim
per element of `I.publicLines s.1` (`pooled`, C.0); `publicLines : Stmt → List (PublicLine toShape)`
is a field of `M3Instance` (`Spine/Instance.lean:141-142` at `b435631`):

```lean
  /-- The columns whose first two cells the statement fixes. -/
  publicLines : Stmt → List (PublicLine toShape)
```

and the relation's clause is over the same list (`Spine/Instance.lean:207-211`):

```lean
/-- Cells 0 and 1 of every column the statement fixes hold their values (§8.2). -/
def PublicLinesHold (input : I.Stmt) (q : Column I.μ) : Prop :=
  ∀ l ∈ I.publicLines input,
    (I.column q l.col).values.get ⟨0, Nat.two_pow_pos _⟩ = l.cell0 ∧
      (I.column q l.col).values.get ⟨1, Nat.one_lt_two_pow l.pos.ne'⟩ = l.cell1
```

Every theorem of the phase and of the spine is stated for an arbitrary `I : M3Instance`:
`publicInputSecurity : (I : M3Instance) → Phase.Security I (publicInputPhase I) (Seam.table I) (Seam.pub I)`
(`PublicInput.lean:391-397`), `piop_perfectCompleteness (P : Phases I) (C : P.Complete) …`,
`piop_rbrKnowledgeSoundness (P : Phases I) (S : P.Security) …` (`Spine/Compose.lean:162-177`).
An instance whose `publicLines` lists `mem_0` and `mem_1` only is an `M3Instance` like any
other; on it `M3Holds` says nothing of `mem_2`, the phase pools two claims, and every theorem
instantiates by `publicInputSecurity I'`, `piop_rbrKnowledgeSoundness P S`. No probe is needed
to see this (the quantification is in the types quoted); the probe that was planned (an instance
`twoLines` with `example := publicInputSecurity twoLines` and a `#guard` that a stack with a
nonzero `mem_2` cell 0 satisfies `M3Holds twoLines`) was not run (C.9) and would only have
displayed it. Mutation 5 (C.8) is the same fact from the other side: given a listed line,
dropping its claim is caught; whether it is listed is not the phase's business.

**So the oracle protocol's theorems do not catch a missing third line.** What does is the
adaptor, not built (blueprint Layer 3, `protocol-blueprint.md:813-816` at `b435631`):

```lean
def witnessOf (prog) (s) (q : Column (leanIsaInstance prog s).μ) :
    EnsembleWitness (leanIsaEnsemble prog)                            -- total and computable
theorem satisfiedBy_witnessOf (hs : s.Admissible prog)                 -- the caps: a hypothesis
    (h : M3Holds (leanIsaInstance prog s) input q) : SatisfiedBy prog input (witnessOf prog s q)
```

and behind it leanISA's `constraintSoundness` (leanISA blueprint `:1163-1164`, not built),
`SatisfiedBy → ∃ t, AssignmentRepresents w t ∧ ValidExecution prog input t`, and T4's
`baseVerifier_extractsExecution` (`protocol-blueprint.md:1247-1248`). The links, read in the
Lean sources at `b435631`:

1. *The type of the public words.* `PublicInput` is four lanes of `K`, and its words are built
   with a zero top limb (`LeanerVM/Semantics/Memory.lean:100-110`):

   ```lean
   /-- The 256-bit public input as four `K` lanes (specification §2). -/
   structure PublicInput where
     /-- `input₀, …, input₃`. -/
     lanes : Fin 4 → K
     deriving DecidableEq

   /-- The first memory word, `input₀ + input₁·y`. -/
   def PublicInput.word0 (p : PublicInput) : E := E.ofLimbs (p.lanes 0) (p.lanes 1) 0

   /-- The second memory word, `input₂ + input₃·y`. -/
   def PublicInput.word1 (p : PublicInput) : E := E.ofLimbs (p.lanes 2) (p.lanes 3) 0
   ```

   with `E.ofLimbs c0 c1 c2 = c0 + c1·y + c2·y²` (`Parameters/Field.lean:92`, `:145-146`). **A
   public word with a nonzero top limb is not representable** as a statement. This matches the
   Rust, whose `read_public` rejects it before the protocol starts (`cpu/mod.rs:139-143`:
   "The transcript binds a public input as two 128-bit halves, so a third limb would be dropped
   and two statements would share a transcript. `if public_input.iter().any(|half| half.c2 != 0)
   { return Err(CpuError::PublicInput); }`"), and the Python, whose `Digest.halves` builds
   `E(w0, w1), E(w2, w3)` with no third limb (`verifier.py:216-219`).

2. *What `SatisfiedBy` says of cells 0 and 1.* Two conjuncts, on the image the prover data names
   (`LeanerVM/Arithmetization/Statement.lean:337-340`):

   ```lean
     /-- The first word of the image is `input₀ + input₁·y` (§8.2). -/
     word0_eq : (imageOf w.data).2.read (gpow 0) = some input.word0
     /-- The second word of the image is `input₂ + input₃·y` (§8.2). -/
     word1_eq : (imageOf w.data).2.read (gpow 1) = some input.word1
   ```

   The image is `MemImage κ = Fin (2 ^ κ) → E` (`Memory.lean:77`): the word at index 0 is one
   element of `E`, **three limbs**, and it must equal `input.word0`, whose limb 2 is `0`. The
   memory block's rows are tied to that image limb by limb by `SeedRowsAreTheImage`
   (`Statement.lean:279-283`: the row of index `i` is `(idx i, cntFin i, [limb 0, limb 1, limb 2])`
   of `(imageOf w.data).2 i`). So `SatisfiedBy` requires, of the committed columns `MEM_LO,
   MEM_HI, MEM_TOP` at row 0, the values `(input₀, input₁, 0)`, and at row 1 `(input₂, input₃, 0)`.
   **The link holds**: the top cells are required to be zero, as three-limb values.

3. *What `satisfiedBy_witnessOf` must derive it from.* `witnessOf` "rebuilds … the image from the
   memory columns" (`protocol-blueprint.md:863-864`), so `(imageOf (witnessOf q).data).2 0` is
   the word `ofLimbs (mem_0[0]) (mem_1[0]) (mem_2[0])` read off `q`. `word0_eq` then needs
   `mem_0[0] = input₀`, `mem_1[0] = input₁` **and `mem_2[0] = 0`**. `M3Holds (leanIsaInstance prog s) input q`
   supplies exactly `PublicLinesHold`, i.e. the cells of the listed lines. With three lines the
   three equalities are there. With two lines the third is not, and `satisfiedBy_witnessOf` is
   **false**: the stack that is honest except for `mem_2[0] = 1` satisfies `M3Holds` of the
   two-line instance (nothing else reads that cell as a constraint; the bus carries it
   consistently from the seed row through every read to the finalize row), and its witness has
   `(imageOf …).2.read (gpow 0) = some (ofLimbs input₀ input₁ 1) ≠ some input.word0`
   (`limb_ofLimbs`, `Field.lean:120`). A `witnessOf` that zeroed the top limb itself would
   break `mem_balanced` or `SeedRowsAreTheImage` on any stack where a table reads cell 0, so no
   definition of `witnessOf` rescues the theorem for all stacks.

4. *What the semantics says.* `ValidExecution prog input t` (`Semantics/Execution.lean:110-113`)
   contains `HasPublicBoundary`: `t.image.read (gpow 0) = some input.word0`, the same three-limb
   equality on the trace's image; `constraintSoundness` transports `word0_eq` to it through
   `AssignmentRepresents.image_eq` (`Statement.lean:360`). So a stack with `mem_2[0] = 1`
   accepted by a two-line protocol would be extracted to a witness with no valid execution on
   `input` (a program that reads cell 0 and branches on its top limb has an accepting stack and
   no valid execution on any `PublicInput`), and `baseVerifier_extractsExecution` would be false.

**Anchor.** If the third line were dropped from `leanIsaInstance`, the theorem left without a
proof is `satisfiedBy_witnessOf` (its conjunct `word0_eq`; and `word1_eq` for cell 1), and
through it T4's `baseVerifier_extractsExecution`. Nothing in `LeanerVM/Protocol/` would change:
the phase, the spine and both master theorems would still hold, on the two-line instance,
verbatim. The check on the top limb is therefore **not** a verifier check that the
proof-system theorems can catch; it is a fact about which lines the leanISA instance lists,
caught one layer down, at the wall between the proof system and the arithmetization, by a
theorem that is not yet built. This is the right place for it (the instance is where leanISA
enters), and it means the audit of "does the verifier check the top limb" is an audit of
`leanIsaInstance.publicLines` against `SatisfiedBy.word0_eq`, i.e. of a definition, plus the
existence of `satisfiedBy_witnessOf`.

### D.2 In the tests: acceptance test 10's witness exists today

Acceptance test 10 (`protocol-blueprint.md:1293-1295` at `b435631`): "The claim
`mem_2(r_m, 0…) = 0` is pooled although no scalar is sent for it; omitting it lets a
non-canonical public word pass the line. Witness: the Layer 8 mutation with a nonzero `mem_2` at
cell 0 and the third claim dropped." The test file at `b435631`
(`tests/LeanerVMTests/Protocol/PublicInput.lean:151-180`) has the literal three-line
configuration (the earlier review's item "exercised nowhere" was met):

```lean
/-- Three lines shaped like the memory limbs: two with their value sent, and a third with cells
`(0, 0)` and no value sent. -/
abbrev threeLimbs : M3Instance :=
  { toy with publicLines := fun v ↦
      [⟨⟨0, 0⟩, v, 1, true, by decide⟩, ⟨⟨0, 1⟩, 1, 1, true, by decide⟩,
        ⟨⟨0, 2⟩, 0, 0, false, by decide⟩] }
…
/-- The top column's cell 0 changed to `1`. -/
def badTopLimb : Column 3 := ⟨#v[1, 1, 1, 1, 1, 0, 0, 0]⟩
…
-- The wrong top cell passes the check, which sees the two sent values only, and fails the third
-- claim; the pool without the third claim accepts the stack.
#guard check threeLimbs stmtLimbs y (trueValues threeLimbs badTopLimb 1 y)
#guard ¬ ∀ c ∈ (pooled threeLimbs stmtLimbs y).2.columns, c.Holds badTopLimb
#guard ∀ c ∈ ((pooled threeLimbs stmtLimbs y).2.columns.take 2), c.Holds badTopLimb
```

It rejects what the acceptance test says: the check accepts the stack with the wrong top cell
(no scalar sees it), the third claim fails of it, and the pool without the third claim (the
"mutation with the third claim dropped", written as `.take 2`) accepts it. Two limits:

- it is a `#guard` on the *pool*, not on the theorems: it shows the third claim is what rejects
  the stack, not that a phase without it has no `Phase.Security` (that is the refutation of
  C.8, on `noneSent`);
- it is on a toy-shaped instance built in the test, not on `leanIsaInstance` (not built). The
  acceptance test's real content, that leanISA's instance lists `mem_2` with cells `(0, 0)`, is
  checkable only when Layer 3 lands; the blueprint's prose says it (`:834-836`).

### D.3 In the deployed verifiers: the top limb rides no scalar and is pooled at `0`

Rust prover (`cpu/mod.rs:606-616`): "The top limb of both public words is zero, so its
evaluation is zero at every `r_pi` and rides no scalar"; `pi_limbs = [interp_k(…c0…), interp_k(…c1…), F192::ZERO]`,
only `pi_limbs[..2]` are added to the stream. Rust verifier (`cpu/mod.rs:745-756`): two scalars
read into `pi_limbs[..2]`, `pi_limbs[2]` stays `F192::ZERO`, the combined check, then
`finish_claims`, whose `bind_pi_claim` (`:674-682`) pools `[MEM_LO, MEM_HI, MEM_TOP]` at
`(r, 0, …)` with the three `pi_limbs`. Python (`verifier.py:1398-1402`):
`public_limbs = (*transcript.next_scalars(2), ZERO)`, the combined check
`poly_eval(public_limbs, Y) == multilinear_eval(public_input.halves(), [public_challenge])`,
then three claims on `MEMORY_0, MEMORY_1, MEMORY_2`. Recursion guest
(`crates/rec_aggregation/guests/aggregate.py:1680-1689`): `assert mem == mem_lo + mem_hi * Y_TOWER`
and three pool entries, the third `0`. The statement itself cannot have a nonzero top limb
(`read_public`, D.1 item 1; the Python's `Digest` is 256 bits, `verifier.py:204-219`). The
Lean phase pools the third claim at `lineValue r l₂ = (1 + r)·0 + r·0 = 0` (test `limbValues`),
the same claim.

So the deployed verifiers do check the top limb, through the third pooled claim; the
specification says so too (`08-end-to-end-protocol.tex:83-84`: "pools them, with $0$ for the
top limb, as claims on $\mem_0,\mem_1,\mem_2$"). The Lean matches. What no document says in
one place is that the check lives in the instance's list of lines and is enforced by the
adaptor's theorem, not by the phase's; D.1 is that sentence.

---

## B. Faithfulness: the Lean verifier against the specification, the Rust, the Python and the recursion guest

All leanVM citations at the pin `a386121f`; Lean at `b435631`.

| Item | Specification (`08-end-to-end-protocol.tex`) | Rust (`crates/lean_vm/src/cpu/mod.rs`) | Python (`python-verifier/verifier.py`) | Recursion guest (`crates/rec_aggregation/guests/aggregate.py`) | Lean (`LeanerVM/Protocol/PublicInput.lean`) | Match |
| --- | --- | --- | --- | --- | --- | --- |
| challenge | `r_m ∈ E`, sampled by the verifier (`:29`; `:83` "Sends $r_m\in\E$") | `let r_pi = vs.sample();` (`:745`) | `public_challenge = transcript.sample()` (`:1398`) | `fs, rm = squeeze(fs)` (`:1680`) | `pSpec := ⟨!v[.V_to_P, .P_to_V], !v[E, List E]⟩` (`:99`): round 0 a challenge in `E` | yes |
| prover's message | `c_0, c_1` (`:29`, `:84`) | two scalars, `pi_limbs[..2]` (`:747-749`) | `transcript.next_scalars(2)` (`:1399`) | `mem_lo`, `mem_hi` (`:1682-1683`) | one message, a `List E`; its length is fixed by the check to the number of lines with `sent` (`:132-137`); two for leanISA's lines | yes at leanISA's instance; the type is wider (note in G) |
| the honest values | "claiming `c_ℓ = mem̃_ℓ(r_m, 0, …, 0)`" (`:29`) | computed from the public words: `interp_k(F64(l.pi[0].c0), F64(l.pi[1].c0), r_pi)`, limb 1 likewise (`:611-613`) | (no prover) | (no prover) | `expectedValues I st.2.1.1.1 st.1` (`:219`): the lines' values, a function of the statement and the challenge | yes (B.2) |
| the check | per limb: `c_ℓ = (1 + r_m)·mem[g⁰]_ℓ + r_m·mem[g¹]_ℓ` for `ℓ ∈ {0, 1}` (`:30-31`) | one equation on the words: `pi_limbs[0] + F192::Y * pi_limbs[1] != want` with `want = interp(l.pi[0], l.pi[1], r_pi)`, `interp(lo, hi, t) = lo + t·(lo + hi)` (`:752-755`; `primitives/src/multilinear.rs:39-42`) | `poly_eval(public_limbs, Y) == multilinear_eval(public_input.halves(), [public_challenge])` (`:1400`) | `assert mem == mem_lo + mem_hi * Y_TOWER` with `mem = pi_0 + rm * (pi_0 + pi_1)` (`:1681-1684`) | per limb: `decide (cs = expectedValues I s.1 r)` (`:136-137`), i.e. `c_ℓ = (1 + r)·cell0 + r·cell1` for each sent line | **specification yes; the three implementations no** (B.1) |
| pooled claims | three, on `mem_0, mem_1, mem_2` at `(r_m, 0, …, 0)`, "with 0 for the top limb" (`:84`) | three, `[MEM_LO, MEM_HI, MEM_TOP]` at `point[0] = r`, values `pi_limbs` (`bind_pi_claim`, `:674-682`) | three, `(MEMORY_0, MEMORY_1, MEMORY_2)` at `public_point`, values `public_limbs` (`:1401-1402`) | three pool entries, the third `0` (`:1685-1690`) | one per line of `I.publicLines`, at `linePoint l.pos r`, value `lineValue I r l` (`:123-128`); three for leanISA, the third `(1 + r)·0 + r·0 = 0` | yes in number, point and honest value; **the pooled value's provenance differs** (B.1) |
| order in the pool | (not stated for this step; §8.5 Opening gives the ring-switched claim first) | bus claims, table claims, then the three (`finish_claims`, `:656-667`), in the order `MEM_LO, MEM_HI, MEM_TOP` (`:680`) | `claims.extend(… zip((MEMORY_0, MEMORY_1, MEMORY_2), public_limbs))` after bus and table claims (`:1391`, `:1402`) | appended after the table claims (`:1685-1690`) | `s.2.columns ++ (I.publicLines s.1).map (lineClaim I r)` (`:128`): the claims received, then the lines in the instance's order | yes, given leanISA lists `mem_0, mem_1, mem_2` in this order (blueprint `:834-836`, not built) |
| rejection | "rejecting otherwise" (`:29-31` "checks"; `:101` accepts if "the public-input line" passed) | `return Err(CpuError::PublicInput)` (`:754`) | `require(…, "public input check failed")` (`:1400`) | `assert` (`:1684`) | `failure` (`:233`) | yes |
| error | `1/|E|` "a limb disagreeing with the public words survives with probability at most `1/|E|`" (`:32-33`) | (no analysis) | (none) | (none) | `error := 1 / Fintype.card E` (`:111`), charged to the one challenge | yes |

### B.1 Which verifier do the theorems describe

The specification's, and only it. The three deployed verifiers (the Rust, the Python and the
recursion guest all run the combined equation; `verify-gt-table-pub.md` section 7 established
the same and it is confirmed above first hand) accept every transcript the Lean verifier
accepts, and strictly more: the test at `b435631` (`tests/…/PublicInput.lean:184-210`) pins one
transcript accepted by the words' equation and rejected per limb (`rStar`, `atStar`,
`wordsEquation`). The blueprint (`:1053-1062`) says this and assigns the deployed check's
knowledge soundness to Layer 12: "their knowledge soundness at `1/|E|` is a lemma of its own,
and Layer 12 owes it."

**Is Layer 12 the right place, and is "a lemma" the right shape? No, on both counts.**

- Layer 12's theorem is `verify_iff_compiled` (`:1218-1221`): the executable `verify` accepts
  exactly when the Fiat–Shamir compilation of the oracle verifier accepts. The oracle verifier
  is the composition of the phases, so its public-input step is *this* verifier. If `verify` is
  written from the Rust (combined check, values sent pooled), the "iff" is false on the
  transcripts above. If `verify` is written per limb, `verify_iff_compiled` can hold, but then
  `verify` is not the deployed verifier, the differential fixture (an honest Rust proof, which
  passes both checks) cannot tell, and the deployed verifier's soundness is proved nowhere. In
  neither case is anything "owed by Layer 12" discharged by a lemma inside it.
- The object that is owed is a `Phase.Security` of a different `Phase.Def`: the deployed
  verifier reads the same transcript but computes a different verdict and a different pool.
  Knowledge soundness is a property of the whole reduction against the seams; it is a
  phase-level object, and the place for it is Layer 8. Its statement, precisely:

  ```lean
  -- the deployed verifier: the words' equation, the values sent pooled
  def deployedVerifier (I) : OracleVerifier []ₒ (I.Stmt × TableOut I) (TheOracle I) (I.Stmt × PubOut I) (TheOracle I) pSpec
      -- verify := do let cs ← queryValues; if checkWords I s r cs then pure (pooledFrom I s r cs) else failure
  noncomputable def deployedPhase (I) : Phase.Def I (I.Stmt × TableOut I) (I.Stmt × PubOut I)   -- n = 2, err = 1/|E|
  def deployedSecurity (I) : Phase.Security I (deployedPhase I) (Seam.table I) (Seam.pub I)
  ```

  with `checkWords` as in C.5 (the words' equation when exactly two lines are sent, the
  per-value check otherwise, so that the verifier is total over instances and is the Rust's on
  leanISA's) and `pooledFrom` as in C.6. Its completeness is the argument of C.6 and C.5; its
  knowledge soundness at `1/|E|` rests on the algebraic lemma proved in C.13
  (`accepts_two_challenges`) plus list plumbing.

**The alternatives.**

- (i) *Model the deployed check in the phase and prove it.* Feasible and cheap: the key lemma is
  proved (eleven lines), the phase's other proofs carry over, the estimated total is about 120
  lines. Its error is the same `1/|E|`, by the same degree-one argument in `E` instead of `K`.
  It makes the check load-bearing again (C.6: without the check, no `Phase.Security`), and it
  makes `verify_iff_compiled` provable for a `verify` written from the Rust.
- (ii) *Keep the specification's check and report upstream.* The specification and the three
  implementations disagree; the per-limb check is strictly stronger and costs one more field
  equation; the two are equally sound (the lemma) but not equally strict. This is a leanVM
  finding in its own right (an ambiguity of the specification rather than a bug: nothing is
  unsound), to be reported whichever way leanerVM goes. But keeping only the specification's
  verifier leaves the deployed one unproved and the refinement theorem unstateable.
- (iii) *Both.* Two `Phase.Def`s over the same schedule, both with `Phase.Security`, and a
  lemma that the specification's verifier's acceptance implies the deployed one's (the two
  equations per limb imply the equation on the words; on the values sent, so trivial). The
  master theorems are instantiated with the deployed phase; the specification's stays as the
  documented reference of §8.2.

**Recommendation: (iii), with the deployed phase as the one the master theorems and Layer 12
consume, and the divergence reported to leanVM as an ambiguity of §8.2.** Reason: the report's
object is deployment on L1; the theorem that matters is about the verifier that runs; the
specification's verifier is one lemma away and documents intent. If only one is kept, keep the
deployed one.

### B.2 The honest prover's values

The Lean prover sends `expectedValues I input r` (`:219`), the lines' values `(1 + r)·cell0 + r·cell1`
computed from the statement. The Rust prover does the same: `interp_k(F64(l.pi[0].c0), F64(l.pi[1].c0), r_pi)`
with `interp_k(lo, hi, t) = lo + t·(lo + hi)` (`cpu/mod.rs:611-613`; `multilinear.rs:46-48`),
where `l.pi` is the public input the layout was built from (`layout.rs:83`, `:471` `pi = [exec.mem[0], exec.mem[1]]`).
Neither evaluates the committed column. **They agree.** The blueprint says so (`:1039-1041`).

Does it matter? Not for the theorems: on the accepting path the value is the same as the
column's extension (on an honest stack; the phase's docstring `:40-41`). It matters for what
the message *is*: a function of public data on both sides, hence redundant for the verifier,
hence (C.4) checkable by any check or by none without loss of soundness in the oracle model.
The one place it is not redundant is the Fiat–Shamir transcript, where it is absorbed
(`ps.add_scalar`, `:616-618`) and so binds later challenges, though to a value the verifier
could derive. The test file's adversary model, "a prover that sends its true evaluation"
(`trueValues`, `:45-47`), is the right one for the deployed design (values sent pooled) and is
what the refutations of C.6 and C.7 use.

---

## E. The flag `PublicLine.sent`

At `b435631`, `Spine/Instance.lean:100-114`:

```lean
/-- A column whose first two cells the public statement fixes (§8.2: the two public words are
the first two memory cells). -/
structure PublicLine (S : Shape) where
  /-- The column. -/
  col : S.ColumnId
  /-- The value cell 0 must hold. -/
  cell0 : K
  /-- The value cell 1 must hold. -/
  cell1 : K
  /-- Whether the proof carries the value claimed for this column on the line through its two
  cells (§8.2: it does for the two low limbs of the memory, and not for the top limb, whose
  value is known to be zero). It fixes the transcript, not the relation. -/
  sent : Bool
  /-- The column has a cell 1. -/
  pos : 0 < S.τ col.1
```

**What the theorems say of it.** Nothing: `M3Holds` reads `col, cell0, cell1, pos` only
(`PublicLinesHold`, D.1), and `publicInputSecurity I` holds for every `I`, so for every
assignment of `sent`. Probe C.8 shows the other direction of the same fact: an instance with
`sent = false` on its only line is served, and a verifier that drops unsent claims is refuted
on it. So `sent` is bound by no theorem; what pins leanISA's choice `(true, true, false)` is
(a) the blueprint's prose (`:834-836`, `:1037-1039`) and the status' decision 15, (b) the
definition `leanIsaInstance.publicLines` when Layer 3 lands, and (c) Layer 12's differential
fixture, the only thing that would reject a transcript with three or one scalars. Until (b)
and (c) exist, the pin is prose.

**Does it enlarge what an auditor must trust?** By one Boolean per line, whose only effect in
the phase as built is on the *transcript's format* (which values are sent and checked): the pool
does not depend on it beyond which claims carry a sent value, and with `pooled` reading the
statement, not even that. In the deployed design (values sent pooled) `sent` decides which
pooled values are prover-chosen, so it enters the soundness argument (the unsent lines' claims
are at verifier-computed values, and their falsity is a bad challenge on its own). Either way
the auditor's obligation is the same: "leanISA's instance sends exactly the two low limbs", a
transcript fact checked against the Rust (`:616-618`, `:747-749`).

**Does the specification need the notion?** Not as a notion: §8.2 is written for leanISA's
three limbs and says "the prover sends `c_0, c_1`" and "with 0 for the top limb". A phase over
an abstract instance must say which lines have a scalar; `sent : Bool` is the least it can say.

**Simpler designs considered.**

- *Every line's value sent, the third line modelled "as in the specification".* The
  specification's third claim has a constant value and no scalar; sending a scalar for it makes
  the transcript one scalar longer than leanVM's, so this is not the specification's protocol.
  Rejected.
- *A separate list of constant claims* (`publicLines` for the lines with a scalar, and a list
  "columns whose line is zero" for the rest). Same information, two fields instead of a flag;
  it hard-codes the constant `0`, which is leanISA's accident (cells `(0, 0)`), not a rule of the
  protocol. The flag is simpler and more general. Rejected.
- *Provenance in the claim's type* (a `ColumnClaim` that records whether its value came from
  the prover). This is the deployed design's need, and it is met more simply by pooling the
  values sent (`pooledFrom`) while the claim type stays as it is.
- *Deriving `sent` from the cells* (send a scalar unless the line's value is identically zero).
  A coincidence of leanISA's data, not a rule; would silently change the transcript for another
  instance. Rejected.

Verdict: the flag is the right primitive. Its cost is not the flag but the absence of anything
that pins it (finding in G).

---

## F. Statement checks

Each declaration read at `b435631` against what it should say. The library objects were
introduced in C.0.

- `verifier_verify` (`:253-256`): as an ordinary verifier, on the transcript `tr`, the verdict
  is `pure (pooled I s (tr 0), o)` if `check I s (tr 0) (tr 1)` and `failure` otherwise. Reads
  the challenge at index 0 and the message at index 1 of the transcript, keeps the oracle `o`.
  Correct, and it is what the two proofs start from through `guarded` (`:273-276`).
- `complete` (`:300-302`): `perfectCompleteness init impl (Seam.table I) (Seam.pub I)` for
  every initial state and implementation of the (empty) shared oracle. Direction right (input
  seam to output seam), no hypothesis beyond the seam, probability one (`perfectCompleteness`
  is completeness with error `0`, ArkLib `Security/Basic.lean:103-105`).
- `rbr` (`:350-353`): `rbrKnowledgeSoundnessWorstCaseWith init impl (Seam.table I) (Seam.pub I) (fun _ ↦ Unit) (extractor I) (stateFunction I init impl) (fun _ ↦ error)`.
  The error function assigns `error` to every challenge index; there is one (index 0, `pSpec.dir 0 = .V_to_P`),
  so `1/|E|` is charged to `r` and nothing to the message round (a message round has no error
  in this definition). Right challenge.
- *Tightness.* The bound is attained: on the toy at statement `1` with `badLine` (column 2 =
  `[1, 1]`, outside the table seam), the pooled claim holds at `r = 0` and fails at the sampled
  `y` (`tests/…/PublicInput.lean:116-118`: `#guard ∀ c ∈ (pooled toy stmt1 0).2.columns, c.Holds badLine`
  and `#guard ¬ ∀ c ∈ (pooled toy stmt1 y).2.columns, c.Holds badLine`). With at most one bad
  challenge (`bad_challenge_unique`) and one exhibited, the bad event has probability exactly
  `1/|E|` for that stack: the error cannot be lowered. A wrong statement gives the bad challenge
  `r = 1` (`:120-123`).
- `stateFunction` (`:327-346`): round 0 the table seam; round 1 the public seam of the pool at
  the challenge; round 2 that and the check. `toFun_empty` is `Iff.rfl` (round 0 is the input
  relation by definition), `toFun_next` drops the check, `toFun_full` is the guarded verdict
  lemma. The invariant after the challenge does not mention the message, which is why any
  message can be accepted (C.3).
- `extractor` (`:317-321`): `extractMid`, `extractOut` return `()`. The witness types are `Unit`
  at every round: the stack is the oracle, and the extraction of the stack is the commit
  phase's (`Spine/Compose.lean:58-59`). Correct for this phase; the composition
  (`piopExtractor`) is what carries knowledge.
- `publicInputPhase` (`:376-381`): `n := 2`, `pSpec`, the reduction, `err := fun _ ↦ error`.
  `noncomputable` for the real number only. `publicInputComplete` (`:384-388`),
  `publicInputSecurity` (`:391-397`): the two bundles the spine consumes; both quantify over
  `init impl` inside (the fields `complete`, `kSF`, `rbr` of `Component.Complete`/`Security`).
- `#print axioms`: not run on the originals after 09:18 (C.9). Run on the verbatim copy
  `Probe0Baseline.lean` (its `diff` against the source is the two namespace lines):
  `publicInputSecurity` and `publicInputComplete` depend on `[propext, Classical.choice, Quot.sound]`,
  no `sorryAx`: no admitted ArkLib theorem is in the closure. The earlier review reported the
  same for the reviewed names.
- *`pooled` takes the lines' values, not the values sent.* In the oracle verifier the pool is
  computed only on the accepting path, where `cs = expectedValues`, so the two agree there
  (`pooledFrom_expected`, C.6, proved). Off that path the verifier rejects and pools nothing.
  For a future executable verifier that reads `pooled` and `check`, they agree as long as it
  runs *this* check. They differ exactly on the transcripts of B.1 (the words' equation passes,
  the per-limb check fails): a `verify` written from the Rust pools the values sent there and
  accepts, this verifier rejects. So there is a path on which they differ, and it is the set of
  transcripts on which the two verifiers disagree.

---

## A. Catalogue

`LeanerVM/Protocol/PublicInput.lean` at `b435631`, 400 lines, a `module`; `namespace
LeanerVM.Protocol`, `@[expose] public section`, inner `namespace PublicInput`. Classes:
**load-bearing** (in the statement of a top-level result, or read by later work),
**interface** (what other layers name), **helper** (proof support). The future executable
verifier (Layer 12) reads, per the blueprint (`:1049-1051`), `pSpec`, `check`, `pooled`, and
through them `expectedValues`, `lineValue`, `linePoint`: marked "L12".

| Line | Declaration (copied) | Meaning | Depends on | Class |
| --- | --- | --- | --- | --- |
| 65 | `def linePoint {n : ℕ} (hn : 0 < n) (r : E) : Vector E n := Vector.cast (by omega : 1 + (n - 1) = n) (#v[r] ++ Vector.replicate (n - 1) (0 : E))` | the point `(r, 0, …, 0)` | `E` | load-bearing, L12 |
| 71 | `theorem eval₂Mle_linePoint {n : ℕ} (hn : 0 < n) (q : CMlPolynomialEval K n) (r : E) : CMlPolynomialEval.eval₂Mle q (algebraMap K E) (linePoint hn r) = (1 - r) * ofK (q.get ⟨0, Nat.two_pow_pos n⟩) + r * ofK (q.get ⟨1, Nat.one_lt_two_pow hn.ne'⟩)` | the extension at that point is the line through cells 0 and 1: the bit order is proved (coordinate 0 = low bit) | CompPoly `eval₂Mle`, Layer 1's `evalMle_append_boolVec`, `boolVec_zero` | load-bearing (gives `linePoint` its meaning) |
| 99 | `def pSpec : ProtocolSpec 2 := ⟨!v[.V_to_P, .P_to_V], !v[E, List E]⟩` | the schedule: a challenge in `E`, then a message `List E` | ArkLib `ProtocolSpec` | interface, L12 |
| 101, 105 | `instance : ∀ i, OracleInterface (pSpec.Message i)`, `instance : ∀ i, SampleableType (pSpec.Challenge i)` | the message is read whole; the challenge is uniform in `E` (`Protocol/Field.lean`) | ArkLib, VCVio | interface |
| 111 | `noncomputable def error : ℝ≥0 := 1 / Fintype.card E` | the knowledge error | `Fintype E` | load-bearing |
| 119 | `def lineValue (r : E) (l : PublicLine I.toShape) : E := (1 + r) * ofK l.cell0 + r * ofK l.cell1` | the line through the statement's two cells at `r` | `PublicLine` | load-bearing, L12 |
| 123 | `def lineClaim (r : E) (l : PublicLine I.toShape) : ColumnClaim I := ⟨l.col, linePoint l.pos r, lineValue I r l⟩` | the claim "column `l.col` at `(r, 0, …)` equals the line's value" | `ColumnClaim` | load-bearing |
| 127 | `def pooled (s : I.Stmt × TableOut I) (r : E) : I.Stmt × PubOut I := (s.1, ⟨s.2.columns ++ (I.publicLines s.1).map (lineClaim I r)⟩)` | the verifier's output: the claims received, then one per line | `TableOut`, `PubOut` | load-bearing, L12 |
| 132 | `def expectedValues (input : I.Stmt) (r : E) : List E := ((I.publicLines input).filter (·.sent)).map (lineValue I r)` | the honest message | `PublicLine.sent` | load-bearing, L12 |
| 136 | `def check (s : I.Stmt × TableOut I) (r : E) (cs : List E) : Bool := decide (cs = expectedValues I s.1 r)` | the check: the message is the expected values | — | **interface only**: no theorem of the phase depends on it (C.4), L12 |
| 141 (private) | `lineClaim_holds_iff` | a line's claim holds iff the stack's line at `r` is the statement's | `eval₂Mle_linePoint` | helper |
| 152 (private) | `line_challenge_unique` | two lines through cells in `K` that differ agree at one `r` at most | `ofK_injective`, char 2 | helper (the whole of the soundness argument) |
| 174 (private) | `pooled_mem_pub` | from the table seam, the pool is in the public seam at every `r` | the two above | helper (completeness) |
| 186 (private) | `bad_challenge_unique` | outside the table seam, at most one `r` puts the pool in the public seam | the three above | helper (soundness) |
| 208 | `def prover : OracleProver []ₒ (I.Stmt × TableOut I) (TheOracle I) Unit (I.Stmt × PubOut I) (TheOracle I) Unit pSpec` | the honest prover: receives `r`, sends `expectedValues`, outputs `pooled` | ArkLib `OracleProver` | load-bearing |
| 223 | `def queryValues : OracleComp [pSpec.Message]ₒ (List E)` | the verifier's read of the message | ArkLib oracle query | helper |
| 229 | `def verifier : OracleVerifier []ₒ (I.Stmt × TableOut I) (TheOracle I) (I.Stmt × PubOut I) (TheOracle I) pSpec` | reads the message, checks, pools or rejects; keeps the stack as the oracle | `check`, `pooled`, `keepOracles` | load-bearing |
| 239 (private) | `simulateQ_queryValues` | reading the message returns the transcript's entry | VCVio `simulateQ` | helper |
| 253 | `theorem verifier_verify … : (verifier I).toVerifier.verify (s, o) tr = if check I s (tr 0) (tr 1) then pure (pooled I s (tr 0), o) else failure` | the verdict, as an ordinary verifier | `materializeOutput_of_keepOracles`, `simulateQ_optionT_bind_run` (VCVio) | load-bearing (both proofs start here) |
| 273 | `def guarded : (verifier I).toVerifier.GuardedForm` | the verifier as check + verdict data | `verifier_verify` | load-bearing (ArkLib's composition needs it) |
| 282 (private) | `prover_run_support` | every prover run sends `expectedValues` and outputs `pooled` | ArkLib `processRound` lemmas | helper |
| 300 | `theorem complete … : (OracleReduction.mk (prover I) (verifier I)).perfectCompleteness init impl (Seam.table I) (Seam.pub I)` | perfect completeness | `mem_support_run_of_guarded`, `pooled_mem_pub` | load-bearing |
| 317 | `def extractor : Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0}) ((I.Stmt × TableOut I) × ∀ i, TheOracle I i) Unit Unit pSpec (fun _ ↦ Unit)` | the trivial extractor | ArkLib | load-bearing |
| 327 | `def stateFunction : (verifier I).toVerifier.KnowledgeStateFunction init impl (Seam.table I) (Seam.pub I) (extractor I)` | the three-round invariant | `of_probEvent_pos` | load-bearing |
| 350 | `theorem rbr : (verifier I).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl (Seam.table I) (Seam.pub I) (fun _ ↦ Unit) (extractor I) (stateFunction I init impl) (fun _ ↦ error)` | round-by-round knowledge soundness at `1/|E|` | `probEvent_uniformSample_le_of_subsingleton`, `bad_challenge_unique` | load-bearing |
| 376 | `noncomputable def publicInputPhase : Phase.Def I (I.Stmt × TableOut I) (I.Stmt × PubOut I)` | the phase | all above | interface |
| 384 | `def publicInputComplete : Phase.Complete I (publicInputPhase I) (Seam.table I) (Seam.pub I)` | the completeness bundle | `guarded`, `complete` | interface |
| 391 | `def publicInputSecurity : Phase.Security I (publicInputPhase I) (Seam.table I) (Seam.pub I)` | the security bundle | `extractor`, `stateFunction`, `rbr` | interface |

The three generic modules (all at `b435631`; the brief's section 8 says the first and third
were restated at `144c5aa` on VCVio's new probability notation):

| File:line | Declaration | Meaning | Class |
| --- | --- | --- | --- |
| `ToArkLib/GuardedVerdict.lean:40` | `theorem Verifier.GuardedForm.of_probEvent_pos {V : Verifier oSpec StmtIn StmtOut pSpec} (G : V.GuardedForm) … (h : Pr[P \| OptionT.mk do (simulateQ impl (V.run stmt tr)).run' (← init)] > 0) : G.check stmt tr = true ∧ P (G.out stmt tr)` | if a guarded verifier can output a statement with property `P`, its check passes and its verdict has `P`: the last obligation of a knowledge state function | load-bearing (used by three components) |
| `ToArkLib/GuardedVerdict.lean:73` | `theorem Reduction.mem_support_run_of_guarded (reduction : Reduction …) (G : reduction.verifier.GuardedForm) (stmt) (wit) {y} (hy : y ∈ support (reduction.run stmt wit).run) : ∃ pr ∈ support (reduction.prover.run stmt wit), y = if G.check stmt pr.1 then some (pr, G.out stmt pr.1) else none` | every outcome of a run is a prover run plus the verdict or a rejection: completeness reduces to the prover's runs | load-bearing |
| `ToArkLib/KeepOracles.lean:34` | `def keepOracles : OracleOutputEmbedding OStmt pSpec.Message OStmt` | "the output oracles are the input oracles" | interface |
| `ToArkLib/KeepOracles.lean:42` | `theorem OracleVerifier.materializeOutput_of_keepOracles … (h : V.outputOracle = .inl (keepOracles OStmt pSpec)) … : V.materializeOutput challenges o messages = o` | such a verifier outputs the oracles it was given | helper |
| `ToVCVio/UniformSample.lean:35` | `theorem probEvent_uniformSample_le_of_card_le (p : α → Prop) [DecidablePred p] {k : ℕ} (h : (Finset.univ.filter p).card ≤ k) : Pr[p \| $ᵗ α] ≤ ((k / Fintype.card α : ℝ≥0) : ℝ≥0∞)` | an event with at most `k` witnesses has probability at most `k/\|α\|` under a uniform sample | helper |
| `ToVCVio/UniformSample.lean:44` | `theorem probEvent_uniformSample_le_of_subsingleton (p : α → Prop) (h : ∀ a b, p a → p b → a = b) : Pr[p \| $ᵗ α] ≤ ((1 / Fintype.card α : ℝ≥0) : ℝ≥0∞)` | an event any two of whose witnesses are equal has probability at most `1/\|α\|` | load-bearing (the bound of `rbr`) |

The two `ToVCVio` bounds and the two `ToArkLib` verdict lemmas are generic in the sense the
repository asks of `To*` folders (any oracle spec, any schedule, any finite type); checked by
reading their variable blocks (`GuardedVerdict.lean:35-36`, `UniformSample.lean:31`).

---

## G. Findings

Names in words; the earlier documents' codes in parentheses only where they locate a passage.

### G.1 The check on the public-input message is not load-bearing for any theorem of the phase (major)

*Evidence.* C.3 (the verifier with no check has `Phase.Security` at the same error, no
`sorryAx`), C.4 (for every message function and every check the message passes, `securityG`;
instances with no check, with forty-two zeros, with the swapped check and a matching prover),
C.5 (the first-value check; the words' equation). Root cause: `pooled` (`PublicInput.lean:127-128`)
reads the statement, not the message; the message enters `check` and nowhere else; the proof
of `rbr` (`:350-366`) never mentions `check`. The build the earlier review read pooled the
values sent, and its item "H1: one output, `pooled`" (`docs/reviews/public-input-phase.md:552-573`)
removed the dependence, so the same review's table "each of five wrong verifiers breaks a
stated theorem" (`:104-114`, rows (i) and (v)) stopped being true of the code as merged; the
status repeats the claim (`protocol-status.md:440`).

*Consequence for the requirement.* "A verifier that omits a check leanVM makes, or makes a
weaker one, must have no proof of knowledge soundness" fails for this check, and no theorem
about this phase as designed can restore it: the verifier without the check is knowledge sound.
"A verifier that makes a wrong check must have no proof of completeness" holds only against a
fixed honest prover (C.10); with the prover adapted to the wrong check both theorems hold.

*Classification.* An error of the design (the blueprint's Layer 8 text describes a phase whose
check ties the pool to the statement; the code's does not), introduced by an audit-surface
compression.

*Proposed change.* Pool the values sent: replace `pooled` by `pooledFrom` (C.6, the definition
is in `tools/lib.py`, with `pooledFrom_expected` proved), in `verifier`, `prover.output`,
`guarded.out` and the state function's rounds 1 and 2 (round 1 becomes
`∃ cs, check s r cs ∧ pooledFrom s r cs ∈ Seam.pub`; with the per-limb check `cs` is forced to
`expectedValues`, so `bad_challenge_unique` is unchanged). Then the check is load-bearing: its
removal is refuted (C.6), its weakening is refuted (C.7), and a wrong check breaks
completeness for every prover (C.10, last paragraph). Blueprint `:1035-1037`, as it stands:
"For a line whose value was sent the value pooled is the value sent, since the check has just
passed; for the others it is the value the verifier computes." As proposed: "For a line whose
value was sent the value pooled is the value sent, as §8.2 and the pinned verifiers pool it;
for the others it is the value the verifier computes. The check is what makes the pooled
claims the statement's: without it the prover's values are pooled unchecked and the phase has
no knowledge-soundness proof (test); a verifier that pools the values it computes would be
knowledge sound with no check at all, which is why the pool must read the message." Status
`:440`: strike "each of five wrong verifiers breaks a stated theorem" or requalify it as a
property of the build reviewed, not of the code merged. Tests: add, next to `threeLimbs`, the
refutations of C.6 and C.7 as theorems (they are twenty lines each with the two lemmas of C.1,
which belong in `ToArkLib/`).

### G.2 The theorems are about a verifier none of the three executable verifiers runs, and the debt is assigned to a layer that cannot pay it (major)

*Evidence.* B.1: the specification checks per limb (`08-end-to-end-protocol.tex:30-31`); the
Rust (`cpu/mod.rs:752-755`), the Python (`verifier.py:1400`) and the recursion guest
(`aggregate.py:1681-1684`) check `c₀ + y·c₁ = w₀ + r·(w₀ + w₁)` and pool the scalars sent; the
Lean is the specification's. The blueprint assigns the deployed check's soundness to Layer 12
(`:1053-1062`), whose theorem `verify_iff_compiled` (`:1218-1221`) cannot hold with a `verify`
written from the Rust, and cannot detect the difference with a `verify` written per limb (the
fixture is an honest proof). The status finding (F18) records the divergence correctly and
draws the same wrong assignment (`:330`).

*Classification.* A disagreement between the specification and its three implementations
(a leanVM finding: an ambiguity of §8.2, not an unsoundness: the lemma of C.13 proves the
implementations' check sound at `1/|E|`); the blueprint follows the specification, as a
deliberate deviation from the deployed verifier, and owes the deployed verifier's theorem in
the wrong place and in the wrong shape.

*Proposed change.* Layer 8 builds the deployed phase as well (B.1: `deployedVerifier`,
`deployedPhase`, `deployedSecurity`, with `checkWords` of C.5 and `pooledFrom` of C.6; key
lemma `accepts_two_challenges` proved in `ProbeWordsLemma.lean`), and the master theorems and
Layer 12 consume it; the specification's phase stays with a one-line lemma that its acceptance
implies the deployed one's. Blueprint `:1061-1062`, as it stands: "So the pinned verifiers
accept transcripts this verifier rejects, their knowledge soundness at `1/|E|` is a lemma of
its own, and Layer 12 owes it." As proposed: "So the pinned verifiers accept transcripts this
verifier rejects. Their verifier is a second `Phase.Def` on the same schedule
(`deployedPhase`: the equation on the two words, the values sent pooled), with its own
`Phase.Security` at `1/|E|` (the two low limbs as one line through `E`, `accepts_two_challenges`);
`Phases` and Layer 12 take the deployed phase, and the specification's is kept as the
reference of §8.2 with the lemma that its acceptance implies the deployed one's." Report to
leanVM: §8.2 states two equations, the three implementations check one; both sound; choose.

### G.3 The top limb is checked by the instance's third line and enforced by the adaptor's theorem, which is not built; the acceptance test names the wrong witness (minor)

*Evidence.* D.1: every theorem of the phase and the spine is stated over an arbitrary
`M3Instance`, so an instance with two lines has them all; `SatisfiedBy.word0_eq`
(`Statement.lean:338`) with `PublicInput.word0 = E.ofLimbs input₀ input₁ 0` (`Memory.lean:107`)
requires the top cell to be zero, and `satisfiedBy_witnessOf` (blueprint `:815-816`) is what
would be false without the third line; `constraintSoundness` and `baseVerifier_extractsExecution`
follow. D.2: acceptance test 10's witness exists (`tests/…/PublicInput.lean:151-180`) but shows
the pool, not the theorem, and on a toy-shaped instance.

*Classification.* Not a divergence; an incomplete audit trail in the blueprint.

*Proposed change.* Acceptance test 10 (`:1293-1295`), as it stands: "omitting it lets a
non-canonical public word pass the line. Witness: the Layer 8 mutation with a nonzero `mem_2`
at cell 0 and the third claim dropped." As proposed: "omitting it lets a non-canonical public
word pass the line. The phase and the spine cannot notice: an instance listing two lines has
every one of their theorems. What fails is the adaptor's `satisfiedBy_witnessOf`, at
`SatisfiedBy.word0_eq`, whose right-hand side `input.word0` has a zero top limb by type
(`Memory.lean:107`). Witnesses: the Layer 8 test `threeLimbs` (the third claim rejects the
stack `badTopLimb`; without it the stack passes), and, when Layer 3 lands, a `#guard` that
`(leanIsaInstance prog s).publicLines input` lists `mem_2` with cells `(0, 0)` and `sent = false`."

### G.4 `PublicLine.sent` is pinned by prose only (minor)

*Evidence.* E: the theorems hold for every assignment; leanISA's `(true, true, false)` is in
the blueprint's prose (`:834-836`, `:1037-1039`) and decision 15, with no definition (Layer 3)
and no transcript fixture (Layer 12) yet. *Classification.* Avoidable audit surface until
Layer 3 and 12 land. *Proposed change.* In the convention row "Public input" (`:335`) add: "The
choice is pinned by two tests: Layer 3's `#guard` on `leanIsaInstance.publicLines`, and Layer
12's differential fixture, which reads exactly two scalars (`cpu/mod.rs:747-749`)."

### G.5 The message type is wider than the transcript (note)

The message is a `List E` whose length only the check fixes (`:96-99`, `:136-137`); the
pinned transcript carries exactly two scalars. Layer 12 must serialize the sent values with no
length prefix, which the type does not say (the earlier review's item A4, kept). With the
deployed phase (G.2) the check on the length is the words' equation's pattern match, which
must also reject a wrong length (C.5's `checkWeak` does, through its second branch).

### G.6 Status text stale (minor, known)

`protocol-status.md` at `b435631` still calls the phase "draft #60" (`:5-6`, `:101`, `:119`,
`:146`), merged as `b435631`; and `:440` as in G.1. The brief's section 8 says the status did
not change at `144c5aa`.

### Negative results

- The schedule, the challenge, the number of scalars, the point `(r, 0, …, 0)`, the honest
  values, the three claims and their order, the rejection, and the error agree between the
  specification, the three implementations and the Lean (table in B); checked line by line as
  cited there.
- The bit order of `linePoint` is proved, not assumed (`eval₂Mle_linePoint`), and separated
  from the other order by the test on a two-variable table (`tests/…:60-66`).
- `1 + r` versus `1 - r`: joined by `CharTwo.sub_eq_add` (`:182`), correct in characteristic
  two.
- The error is charged to the right challenge and is tight (F).
- No admitted ArkLib theorem in the closure of the two bundles (F, on the verbatim copy).
- The knowledge state function's three rounds are the right ones and none is trivial (F; the
  bad event is inhabited, C.3's `rbr'` shows the same bound for the unchecked verifier).
- `sent` is no part of the relation (E; `M3Holds` does not read it).
