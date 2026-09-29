# Dossier `code-pubinput`: the public-input phase as built

Reviewed: leanerVM `main` at `b435631` (the checkout sits on the branch
`docs/protocol-blueprint-review`, whose tracked files are those of `main`). Ground truth: leanVM
at the pin `a386121f84292f6fa663aaa3e570c15bc0240ea2` (confirmed by `git rev-parse HEAD` in
`/home/scaraven/Documents/leanEthereum/leanVM`). Libraries at the pins: ArkLib `dca90385`
(confirmed by `git rev-parse HEAD` in `.lake/packages/Arklib`), VCVio `f9dc47d9`, CompPoly
`3468b38c`.

STATUS OF THIS FILE: written in stages. Sections marked "(pending)" are not yet written.

## 0. Summary

**What was examined.** `LeanerVM/Protocol/PublicInput.lean` (400 lines), the three generic
modules it uses, the spine files it is stated over, its tests, the blueprint's Layer 8 and
acceptance test 10, the status' decisions 13 and 15, the earlier review, and the pinned
specification, Rust and Python. Eleven Lean probes were compiled against the pinned libraries
(section C); each is a copy of the phase's module with one change, compiled as a `module` file
under a new namespace.

**Conclusions.**

1. **The check on the prover's message is not load-bearing for any theorem of the phase.** The
   verifier pools the values it computes from the statement (`pooled`), not the values it
   received. So a verifier that reads the message and ignores it is perfectly complete and
   round-by-round knowledge sound against the same two seams, with the same extractor and the
   same error `1/|E|`; only the last round of the state function changes. Proved in Lean, in
   general form: for **every** message function and **every** Boolean check that the message
   passes, the phase has a `Phase.Security` (probe `ProbeAnyCheck`, theorem `securityG`, no
   `sorryAx`). Instances proved: no check and no message; no check and a message of forty-two
   zeros; the check with the two cells swapped together with a prover that sends the swapped
   values. The requirement "a verifier that omits or weakens a check has no proof of knowledge
   soundness; a verifier with a wrong check has no proof of completeness" is therefore **not
   met for the check on `c_0, c_1`**, and cannot be met by any theorem about this phase as it is
   designed: the omission is sound.
2. **The earlier review's claim that "each of five wrong verifiers breaks a stated theorem" is
   false of the code as merged.** It was true of the build reviewed, which pooled the values
   sent; the review's own compression "one output, `pooled`" (its item H1) removed the
   dependence, and the status still repeats the claim.
3. **What the theorems do catch** (each refuted in Lean on a concrete instance, with no
   extractor, no state function and no error below one able to repair it): a verifier that
   pools the prover's values without checking them; one that checks only the first value and
   pools the prover's values; one that does not pool the claim of a line whose value is not
   sent (the top limb). (Wrong point, wrong check with the honest prover unchanged, extra check:
   see section C, pending.)
4. **The top limb** is caught by the phase only because the instance lists a third line. The
   phase and the spine hold for every instance, so an instance with two lines has every theorem
   of the spine and of the phase. What catches a missing third line is the adaptor's theorem
   `satisfiedBy_witnessOf`, which is not built (section D).
5. **The theorems are about a verifier that is not deployed.** The three pinned verifiers (Rust,
   Python, recursion guest) check one combined equation and pool the scalars sent. (Section B.)

**Findings by severity** (section G, pending): to be completed.

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
| 4b | the pinned verifiers' equation; prover's values pooled (the deployed verifier) | (pending) | | | |
| 5 | lines not sent are not pooled | compiles | `toFun_full` fails | no: refuted (a line not sent) | caught by knowledge soundness |
| any | any message, any check the message passes; lines' values pooled | proved (`completeG`) | | **yes, same error** (`rbrG`, `securityG`) | **not caught**, in general |
| 6, 7, 8 | (pending) | | | | |

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

(Details of each probe: sections C.3 onwards, being written.)

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
  is caught by completeness only if the prover is held fixed (C.9, pending).

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
