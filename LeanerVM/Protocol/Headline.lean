/-
  LeanerVM.Protocol.Headline

  leanVM's deployed prover and verifier against leanISA: an accepted proof, except with small
  probability, yields through the straight-line extractor a valid execution of the program on the
  public input, in the random-oracle model with no hypothesis and at BLAKE2s under one named
  hypothesis on the adversary's run; and every proof the deployed prover returns from a valid
  execution that fits the caps is accepted.
-/

module

public import LeanerVM.Protocol.Core
public import LeanerVM.Protocol.LeanIsa.Sound
public import LeanerVM.Protocol.LeanIsa.Complete
public import LeanerVM.Arithmetization.Soundness
public import LeanerVM.Arithmetization.WitnessGen
public import LeanerVM.Arithmetization.HypothesisChecks
public import LeanerVM.Protocol.Compile.Agree
public import LeanerVM.Protocol.AdaptiveGame
public import LeanerVM.Semantics.FillBlocks
public import LeanerVM.Protocol.LeanIsa.ExecutionStack
public import LeanerVM.Protocol.HonestGame

/-!
# The headline theorems

An adversary is a cheating prover: a computation with no coins whose only access to BLAKE2s-256 is
the hash oracle. An adaptive adversary (`AdaptiveAdversary`) outputs a program, a public input and
a proof; the game (`adaptiveGame`) runs it with its queries logged, then leanVM's verifier on the
statement and proof it output, with the verifier's queries logged. An adversary for a fixed
statement (`Adversary`) outputs a proof alone, for a program `prog` and a public input `input`
fixed before it runs (`loggedGame`); it is the adaptive adversary that outputs them with its proof
(`adaptiveGame_const`). The extractor is straight-line and computable: `extract` reads the
announced sizes off the proof and the committed stack off the adversary's queries, `witnessOf`
reads leanISA's witness off the stack, and `extractExecution` reads an execution off the witness
at a program whose sentinel slot is not a `JUMP`, nothing at another.

## Soundness: an execution is extracted

Each theorem bounds the probability that the verifier accepts the statement and proof while the
trace `extractExecution` reads off the adversary's queries is no `ValidExecution` of the program on
the public input. The program's sentinel slot must not be a `JUMP` (`SentinelSafe`, a field of
`WellFormedBytecode`): for an adaptive adversary it is part of the event, or, in the `_wellFormed`
forms, a hypothesis that every program the adversary outputs is `WellFormedBytecode`; at a fixed
statement it is a hypothesis on the program.

* In the random-oracle model, for an adversary of at most `Q` queries, with probability at most
  `(Q + 13700)/2^128 + hashTerm 13700 Q`: `baseVerifier_extractsExecution_rom_adaptive`,
  `baseVerifier_extractsExecution_rom_adaptive_wellFormed`, for an adversary with coins
  `baseVerifier_extractsExecution_rom_adaptive_coins`, and at a fixed statement
  `baseVerifier_extractsExecution_rom`.
* At BLAKE2s-256, for the deployed `verify`, with probability at most `δ` under the named
  hypothesis `BlakeMisbehavesAdaptive A δ` (or `BlakeMisbehaves prog input A δ`):
  `baseVerifier_extractsExecution_adaptive`, `baseVerifier_extractsExecution_adaptive_wellFormed`,
  `baseVerifier_extractsExecution`; for an adversary with coins, a distribution over coin-free
  ones, with `δ` the probability over the coins that the hash misbehaves:
  `baseVerifier_extractsExecution_adaptive_coins`, `baseVerifier_extractsExecution_coins`.

The condition is needed by constraint soundness: some program with a sentinel `JUMP` has a witness
of the constraint statement and no execution on any memory (the test
`exists_satisfiedBy_without_execution`), and `verify` accepts every proof `prove` returns for it.

## Completeness: from an execution

The prover from an execution is one computable term, `proveExecution fuel prog input t ρ`: the
witness generator `witnessGen`, then the deployed `prove` on its witness.
`proveExecution_complete`: for `WellFormedBytecode` and a valid execution `t` that fits the caps
(`Trace.Fits`), `witnessGen` returns a witness `w` of the constraint statement representing the
padded trace `padTrace t (fillStarts prog)`, a valid execution with the same steps
(`Trace.PaddedFrom`); at every fuel and rate `verify` accepts every proof `proveExecution`
returns, and `proveExecution` returns a proof unless the stack does not fit (`StackFits`), the
rate is not valid, or a grind finds no nonce among its `fuel` candidates at a chain state the
prover's run reaches (`ProveReaches`: the state after the announcement and some first rounds of
the run, so every round boundary, a superset of the states the grinds start at).
`proveChecked` runs the decided checks of the hypotheses of the random-oracle form first and
`proveExecution` only when they pass: every proof it returns is accepted, with no hypothesis
(`verify_proveChecked`), and under those hypotheses it is `proveExecution` (`proveChecked_eq`).

**The stack of an execution** (`LeanerVM.Protocol.LeanIsa.ExecutionStack`). `StackFits prog t`
says that leanVM's stack at the sizes of the generated witness has at most `2^maxMu` cells. It
fails from `t.κ ≥ 25` on (`not_stackFits_of_le`), holds for short runs (`StackFits.of_short`),
implies `Trace.Fits` (`StackFits.fits`) and at most `2^25` steps (`StackFits.steps_le`), and is
decided on a valid execution by `stackFitsB`.

## Completeness in the random-oracle model

`proveExecution_rom_complete`: for `WellFormedBytecode`, a valid execution `t` whose stack fits
(`StackFits`), and a valid rate, the honest run from the execution (`honestExecutionGame`: the
witness generator, the deployed prover with every hash a query to one lazy random oracle, then the
verifier on its proof at the same oracle) is rejected with probability at most
`(N + 1) (1 - 2^-17)^min(fuel, 2^64) + N^2 / 2^256`, `N = 264246250 + 6 · fuel`; at most
`2^-154` at the default fuel `2^24` (`proveExecution_rom_complete_default`). It is proved from the
constraint form `honestGame_rom_rejects_le` (`LeanerVM.Protocol.HonestGame`): for a witness of
the constraint statement whose sizes keep the stack within `2^maxMu`, at a valid rate, the
deployed prover and then the verifier on its proof, both asking one lazy random oracle
(`honestGame`), reject with the same probability.

## The lemmas they are proved from

* The constraint forms: the same bounds for the witness `witnessOf` reads off the extracted stack
  failing leanISA's constraint statement `SatisfiedBy`, with no bytecode hypothesis:
  `baseVerifier_extractsWitness_rom_adaptive`, `baseVerifier_extractsWitness_adaptive`,
  `baseVerifier_extractsWitness_adaptive_coins`, `baseVerifier_extractsWitness_rom`,
  `baseVerifier_extractsWitness`, `baseVerifier_extractsWitness_coins`. leanISA's trace extraction
  (`leanIsaTraceExtraction`) turns each into its execution form.
* `prove_complete`: for a witness of the constraint statement, `verify` accepts every proof the
  deployed prover `prove` returns; `prove_eq_none`: when it returns none; `prove_ne_none`: when it
  returns a proof.
* `misbehaves_rom_adaptive`: with the hash a uniformly random function and an adaptive adversary of
  at most `Q` queries, the hash misbehaves on its run with probability at most
  `niError εquery 13700 Q`: a collision or a hit on the whole joint log, the proof's roots those at
  the statement it chose, or a flip on any statement's chain
  (`HashMisbehavesFrom [] (rootsOf prog input) leanVmReader.Flip`). No digest is in play at the
  start: the statement's seed is three queries of the hash, which the verifier asks
  (`FsState.seedWith`), and leanVM's reader reads the statement a chain starts from off the log
  (`leanVmReader`, `stmtOf`). So the bound counts the verifier's seed hashes,
  `13700 = 3 + 13697` queries. The event the theorems use, its flips restricted to groups of the
  chosen statement's chain that the verifier itself asked (`leanVmReader.VerifierFlipFor`), is
  smaller, so the bound holds for it. `misbehaves_rom_adaptive_coins`: the bound for an adaptive
  adversary with coins, a distribution over coin-free ones;
  `baseVerifier_extractsWitness_rom_adaptive_coins` and
  `baseVerifier_extractsExecution_rom_adaptive_coins`: the witness and execution forms for it.
* `BlakeMisbehavesAdaptive A δ`: with BLAKE2s answering, the adversary's run shows a collision or a
  hit on the whole joint log, or a flip on the chain of the statement it chose, on a group of
  Fiat–Shamir queries the verifier itself asked, with probability at most `δ`;
  `BlakeMisbehaves prog input A δ` is it at a fixed statement
  (`blakeMisbehavesAdaptive_const`). `blakeMisbehavesAdaptive_of_comparison`,
  `blakeMisbehaves_of_comparison`: if misbehaving is at most `δ` likelier under BLAKE2s than under
  a random function (`Blake2sActsAsRandomOracle`), the hypothesis holds at the random-oracle bound
  plus `δ`.

**The proofs.** A run under BLAKE2s, or under the lazy random oracle, is a possible run of the game
whose joint log is consistent (`mem_support_runBlake2s_adaptive`, `mem_support_runRandom_adaptive`);
under BLAKE2s its verdict is `verify`'s (`verifyWith_simulateQ`). A possible run of the adaptive
game is one of the game at the statement the prover chose (`mem_support_loggedGame_of_adaptive`).
On such a run, an accepted proof whose extraction fails puts the run inside `HashMisbehavesFrom`,
its flip on the chain of the statement on a group the verifier asked (`Core.core_of_mem_support`),
and `satisfiedBy_witnessOf` turns the extracted stack's `M3Holds` into `SatisfiedBy` at the
admissible sizes `extract` returns; `TraceExtraction.valid` (leanISA's constraint soundness)
turns that into a valid execution. The random-oracle bound is `misbehaves_rom_of` on the adaptive
game in two runs (`adaptiveGame_eq_twoRunGame`), for flips on every statement's chain, which
include those the verifier asked for on the chosen one (`SlotReader.flip_of_verifierFlipFor`).
Completeness from an execution is the generator's correctness (`witnessGen_correct`) followed by
`prove_complete`, `prove_eq_none` and `prove_ne_none`.

**What they do not say.** An adversary with no coins has one run under BLAKE2s, so
`BlakeMisbehavesAdaptive` at `δ < 1` says that this run does not misbehave; an adversary with coins
gets the bound with `δ` the probability over its coins. The hypothesis is about one adversary and is
false for some: the replayer of a stored accepted proof fails it at every `δ < 1`, and so does an
adversary that hashes in its own code. No theorem shows it met by an adversary whose proof is
accepted. The flip clause counts a bad challenge only on a group the verifier itself asked: a chain
of the statement that the adversary explored and abandoned, a bad challenge on it, does not fail the
hypothesis, since the verifier never walks it, and `core` finds its flip on the verifier's own walk.
The broader event, a flip on any chain of the statement (`leanVmReader.FlipFor`), contains it
(`SlotReader.flipFor_of_verifierFlipFor`); the random-oracle bounds hold for both. Completeness says
that every proof `proveExecution` returns is accepted, and when it returns one, not that it does: at
BLAKE2s nothing bounds how often a grind on the run runs out of fuel (the random-oracle bound above
is about a random function), and `Trace.Fits` does not keep the stack within `2^maxMu`: from
`t.κ ≥ 25` on it never fits (`not_stackFits_of_le`), and on a valid execution whose stack does
not fit `proveExecution` returns none at every fuel and rate
(`proveExecution_eq_none_of_not_stackFits`). The generated witness represents the padded trace,
not the given one: the proof is of the same steps over a memory with the fill frames above the
image. -/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization Blake2sHash LeanIsa
open OracleComp OracleSpec Verify ProofRoots LeanVmReader
open Air.Flat (EnsembleWitness)
open LeanerVM.Parameters.Whir (queryGrindingBits)
open scoped NNReal ENNReal

@[expose] public section

/-! ## The hypotheses -/

/-- **BLAKE2s misbehaves on this adaptive adversary's run with probability at most `δ`.** Run the
adversary `A` with BLAKE2s-256 answering its hash queries, then leanVM's verifier on the program,
the public input and the proof `A` output; the joint log of the two runs' queries shows one of:
- a *collision*: two different inputs with one digest (collision resistance);
- a *hit*: a query answered, at its input's first occurrence, by a digest already in play: a
  32-byte half of an earlier 64-byte input (the state or block of a chain step, a child of a Merkle
  node, the seed of a chain's first state), the program hash an earlier seed preimage carries, or
  a digest a chain absorbed as two scalars (a Merkle root); for the verifier's queries, also a
  Merkle root the proof carries (unpredictability: no digest is known before it is computed);
- a *flip*: a Fiat–Shamir challenge, read off a chain of the log by leanVM's reader from a first
  state at which the log holds the three hashes of the seed of the statement `A` output, as a
  challenge of the deployed compiled protocol at that statement, that lies in the bad set of the
  transcript before it: the challenges that turn the protocol's state function from false to
  true, which have density at most `2^-128`, the query positions counted with their grinding
  (correlation intractability of the chain against a sparse relation); on a group of queries the
  verifier itself asked, its nonce step or its first squeeze one of the verifier's queries. Chains
  of the log from the seeds of other statements are not read, nor a chain of this statement that
  the verifier never walked.

The protocol, its bad sets and the reader are those of leanVM, fixed inside this definition. With
no coins the run is one value, and the probability is `0` or `1`. -/
def BlakeMisbehavesAdaptive (A : AdaptiveAdversary) (δ : ℝ≥0∞) : Prop :=
  Pr{let g ← runBlake2s (adaptiveGame verifyWith A)}[
    HashMisbehavesFrom [] (rootsOf g.prog g.input) (leanVmReader.VerifierFlipFor (g.prog, g.input))
      g.toRun] ≤ δ

/-- **BLAKE2s misbehaves on this adversary's run with probability at most `δ`**, for the program
`prog` and the public input `input` fixed before the adversary runs: `BlakeMisbehavesAdaptive` at
the adversary that outputs them with its proof (`blakeMisbehavesAdaptive_const`), its flips those
on the chain of `(prog, input)` on groups the verifier asked. -/
def BlakeMisbehaves (prog : Program) (input : PublicInput) (A : Adversary) (δ : ℝ≥0∞) : Prop :=
  Pr{let g ← runBlake2s (loggedGame verifyWith prog input A)}[
    HashMisbehavesFrom [] (rootsOf prog input) (leanVmReader.VerifierFlipFor (prog, input)) g] ≤ δ

/-- **BLAKE2s acts as a random oracle** for the computation `G` and the event `bad`, up to `δ`:
`bad` is at most `δ` likelier with BLAKE2s-256 answering every query than with a uniformly random
function answering (the lazy random oracle). -/
def Blake2sActsAsRandomOracle {α : Type} (G : OracleComp hashSpec α) (bad : α → Prop)
    (δ : ℝ≥0∞) : Prop :=
  Pr{let x ← runBlake2s G}[bad x] ≤ Pr{let z ← runRandom G}[bad z.1] + δ

/-! ## A fixed statement -/

/-- At a fixed statement, an event of the adaptive game's runs under BLAKE2s is the event of the
game's runs at that statement. -/
private theorem prEvent_runBlake2s_const (prog : Program) (input : PublicInput) (A : Adversary)
    (p : AdaptiveRun → Prop) :
    Pr{let g ← runBlake2s (adaptiveGame verifyWith ((fun proof ↦ (prog, input, proof)) <$> A))}[
      p g] = Pr{let g ← runBlake2s (loggedGame verifyWith prog input A)}[p ⟨g, prog, input⟩] := by
  rw [adaptiveGame_const, runBlake2s, simulateQ_map, prEvent_map]
  rfl

/-- At a fixed statement, an event of the adaptive game's runs under the lazy random oracle is the
event of the game's runs at that statement. -/
private theorem prEvent_runRandom_const (prog : Program) (input : PublicInput) (A : Adversary)
    (p : AdaptiveRun × hashSpec.QueryCache → Prop) :
    Pr{let z ← runRandom (adaptiveGame verifyWith ((fun proof ↦ (prog, input, proof)) <$> A))}[
      p z] = Pr{let z ← runRandom (loggedGame verifyWith prog input A)}[
        p (⟨z.1, prog, input⟩, z.2)] := by
  rw [adaptiveGame_const, runRandom_map, prEvent_map]
  rfl

/-- **At a fixed statement the adaptive hypothesis is the selective one.** -/
theorem blakeMisbehavesAdaptive_const (prog : Program) (input : PublicInput) (A : Adversary)
    (δ : ℝ≥0∞) :
    BlakeMisbehavesAdaptive ((fun proof ↦ (prog, input, proof)) <$> A) δ ↔
      BlakeMisbehaves prog input A δ := by
  unfold BlakeMisbehavesAdaptive BlakeMisbehaves
  rw [prEvent_runBlake2s_const]

/-! ## The extraction -/

/-- **The extracted execution**: the stack `extract` reads off the log, the witness `witnessOf`
reads off the stack, and the trace a trace extraction `X` reads off the witness. Computable: a
definition the compiler runs, whose last step at `leanIsaTraceExtraction` is leanISA's computable
`traceOf`, a walk of the witness's states. -/
def extractTrace {prog : Program} (X : TraceExtraction prog) (input : PublicInput)
    (proof : Proof PrunedMerklePaths) (log : hashSpec.QueryLog) : Option (Trace prog) :=
  (extract Blake2sFlock.blake2sFlockSpec prog input proof log).bind fun e ↦
    X.traceOf input _ (witnessOf Blake2sFlock.blake2sFlockSpec prog e.1 e.2)

/-- **The extracted execution of a chosen program**: `extractTrace` at leanISA's trace
extraction when the program's sentinel slot is not a `JUMP`, nothing otherwise. Computable. -/
def extractExecution (prog : Program) (input : PublicInput) (proof : Proof PrunedMerklePaths)
    (log : hashSpec.QueryLog) : Option (Trace prog) :=
  if hsafe : SentinelSafe prog then extractTrace (leanIsaTraceExtraction hsafe) input proof log
  else none

/-- The sizes `extract` returns are admissible. -/
private theorem admissible_of_extract {F : FlockSpec} {prog : Program} {input : PublicInput}
    {proof : Proof PrunedMerklePaths} {log : hashSpec.QueryLog} {s : Sizes}
    {q : Column (leanIsaμ prog s)} (h : extract F prog input proof log = some ⟨s, q⟩) :
    s.Admissible prog := by
  unfold extract at h
  split at h
  · cases h
  · split_ifs at h with hs
    split at h
    · cases h
    · obtain ⟨_, -, ⟨⟩⟩ := Option.map_eq_some_iff.mp h
      exact hs.1

/-- At a program whose sentinel slot is not a `JUMP`, no valid extracted execution means no
satisfying extracted witness. -/
private theorem noWitness {prog : Program} {input : PublicInput} {proof : Proof PrunedMerklePaths}
    {log : hashSpec.QueryLog} (hsafe : SentinelSafe prog)
    (h : ¬ ∃ t, extractExecution prog input proof log = some t ∧ ValidExecution prog input t) :
    ¬ ∃ e, extract Blake2sFlock.blake2sFlockSpec prog input proof log = some e ∧
      SatisfiedBy prog input (witnessOf Blake2sFlock.blake2sFlockSpec prog e.1 e.2) := by
  rintro ⟨e, he, hsat⟩
  obtain ⟨t, ht, -, hvalid⟩ := (leanIsaTraceExtraction hsafe).valid _ _ _ hsat
  refine h ⟨t, ?_, hvalid⟩
  simp only [extractExecution, hsafe, ↓reduceDIte, extractTrace, he, Option.bind_some]
  exact ht

/-- On a possible run with a consistent joint log whose verdict accepts, no satisfying witness
through the adaptor means the hash misbehaves, a flip being one the verifier asked for on the
statement's chain. -/
private theorem misbehaves_of_escape {prog : Program} {input : PublicInput} {A : Adversary}
    {g : Run} (hg : g ∈ support (loggedGame verifyWith prog input A) ∧ QueryLog.Consistent g.log)
    (hok : g.ok = true)
    (hX : ¬ ∃ e, extract Blake2sFlock.blake2sFlockSpec prog input g.proof g.logA = some e ∧
      SatisfiedBy prog input (witnessOf Blake2sFlock.blake2sFlockSpec prog e.1 e.2)) :
    HashMisbehavesFrom [] (rootsOf prog input) (leanVmReader.VerifierFlipFor (prog, input)) g :=
  Core.core_of_mem_support hg.1 hg.2 hok fun ⟨s, q, he, hm⟩ ↦
    hX ⟨⟨s, q⟩, he, satisfiedBy_witnessOf _ prog s q (admissible_of_extract he) hm⟩

/-- On a possible run of the adaptive game with a consistent joint log whose verdict accepts, no
satisfying witness at the chosen statement means the hash misbehaves, a flip being one the
verifier asked for on that statement's chain. -/
private theorem misbehaves_of_escape_run {A : AdaptiveAdversary} {g : AdaptiveRun}
    (hg : g ∈ support (adaptiveGame verifyWith A)) (hc : QueryLog.Consistent g.log)
    (hok : g.ok = true)
    (hX : ¬ ∃ e, extract Blake2sFlock.blake2sFlockSpec g.prog g.input g.proof g.logA = some e ∧
      SatisfiedBy g.prog g.input (witnessOf Blake2sFlock.blake2sFlockSpec g.prog e.1 e.2)) :
    HashMisbehavesFrom [] (rootsOf g.prog g.input) (leanVmReader.VerifierFlipFor (g.prog, g.input))
      g.toRun :=
  misbehaves_of_escape ⟨mem_support_loggedGame_of_adaptive hg, hc⟩ hok hX

/-! ## Knowledge soundness in the random-oracle model -/

/-- **The random-oracle bound for an adversary that chooses the statement.** With the hash a
uniformly random function and an adaptive adversary `A` of at most `Q` queries, the hash
misbehaves on its run with probability at most `niError εquery 13700 Q`: a collision or a hit on
the joint log, the proof's roots those at the statement `A` chose, or a flip read by leanVM's
reader on the chain of any statement. No digest is in play at the start: every statement's seed
is three queries of the hash, which the verifier asks, and its `13700` queries count them. -/
theorem misbehaves_rom_adaptive {A : AdaptiveAdversary} {Q : ℕ} (hQ : IsTotalQueryBound A Q) :
    Pr{let z ← runRandom (adaptiveGame verifyWith A)}[
      HashMisbehavesFrom [] (rootsOf z.1.prog z.1.input) leanVmReader.Flip z.1.toRun] ≤
      niError εquery 13700 Q := by
  -- elaborated before it meets the goal, so that the event is not unfolded to match it
  have h := misbehaves_rom_of leanVmReader (seedRoots := []) (Nat.zero_le _)
    leanVmReader_startsSafe leanVmReader_density (·.2.2) A hQ
    (fun b ↦ verifyWith hashQuery b.1 b.2.1 b.2.2)
    (fun b ↦ verifierQueries_bound_closed b.1 b.2.1 b.2.2) (fun b ↦ rootsOf b.1 b.2.1)
    fun b ↦ length_rootsOf_le b.1 b.2.1
  rw [adaptiveGame_eq_twoRunGame, runRandom_map, prEvent_map]
  exact h

/-- **The random-oracle bound for an adversary with coins that chooses the statement**: a
distribution `coins` over adaptive adversaries each making at most `Q` queries is a mixture of
coin-free ones, each meeting the bound. -/
theorem misbehaves_rom_adaptive_coins {coins : ProbComp AdaptiveAdversary} {Q : ℕ}
    (hQ : ∀ A ∈ support coins, IsTotalQueryBound A Q) :
    Pr{let A ← coins; let z ← runRandom (adaptiveGame verifyWith A)}[
      HashMisbehavesFrom [] (rootsOf z.1.prog z.1.input) leanVmReader.Flip z.1.toRun] ≤
      niError εquery 13700 Q := by
  rw [← bind_assoc]
  exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun A hA ↦ misbehaves_rom_adaptive (hQ A hA)

/-- The random-oracle error at `13700` verifier queries in closed form. -/
private theorem niError_closed (Q : ℕ) :
    (niError εquery 13700 Q : ℝ≥0∞) ≤ ((Q + 13700 : ℕ) / 2 ^ 128 + hashTerm 13700 Q : ℝ≥0) :=
  ENNReal.coe_le_coe.mpr ((niError_le 13700 Q).trans (le_of_eq (by norm_num)))

/-- **Adaptive knowledge soundness in the random-oracle model, the constraint form**, from which
`baseVerifier_extractsExecution_rom_adaptive` is proved. With the hash a uniformly random
function and an adaptive adversary `A` of at most `Q` queries, the game's verifier accepts the
statement and proof `A` outputs while the witness read off the stack the extractor reads off `A`'s
queries does not satisfy leanISA's constraint statement at that statement with probability at most
`(Q + 13700)/2^128` (the challenges) plus `hashTerm 13700 Q` (collisions and hits). -/
theorem baseVerifier_extractsWitness_rom_adaptive {A : AdaptiveAdversary} {Q : ℕ}
    (hQ : IsTotalQueryBound A Q) :
    Pr{let z ← runRandom (adaptiveGame verifyWith A)}[z.1.ok = true ∧ ¬ ∃ e,
      extract Blake2sFlock.blake2sFlockSpec z.1.prog z.1.input z.1.proof z.1.logA = some e ∧
        SatisfiedBy z.1.prog z.1.input (witnessOf Blake2sFlock.blake2sFlockSpec z.1.prog e.1 e.2)] ≤
      ((Q + 13700 : ℕ) / 2 ^ 128 + hashTerm 13700 Q : ℝ≥0) :=
  (prEvent_mono_of_support _ _ _ fun _ hz h ↦
    (misbehaves_of_escape_run (mem_support_runRandom_adaptive hz).1
      (mem_support_runRandom_adaptive hz).2 h.1 h.2).mono
      fun _ ↦ leanVmReader.flip_of_verifierFlipFor).trans
    ((misbehaves_rom_adaptive hQ).trans (niError_closed Q))

/-- **Adaptive knowledge soundness in the random-oracle model for an adversary with coins**, a
distribution `coins` over adaptive adversaries each making at most `Q` queries: the bound of
`baseVerifier_extractsWitness_rom_adaptive`, each coin-free adversary meeting it. -/
theorem baseVerifier_extractsWitness_rom_adaptive_coins {coins : ProbComp AdaptiveAdversary}
    {Q : ℕ} (hQ : ∀ A ∈ support coins, IsTotalQueryBound A Q) :
    Pr{let A ← coins; let z ← runRandom (adaptiveGame verifyWith A)}[z.1.ok = true ∧ ¬ ∃ e,
      extract Blake2sFlock.blake2sFlockSpec z.1.prog z.1.input z.1.proof z.1.logA = some e ∧
        SatisfiedBy z.1.prog z.1.input (witnessOf Blake2sFlock.blake2sFlockSpec z.1.prog e.1 e.2)] ≤
      ((Q + 13700 : ℕ) / 2 ^ 128 + hashTerm 13700 Q : ℝ≥0) := by
  rw [← bind_assoc]
  exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun A hA ↦
    baseVerifier_extractsWitness_rom_adaptive (hQ A hA)

/-- **The headline in the random-oracle model: adaptive knowledge soundness for an execution.** With
the hash a uniformly random function and an adaptive adversary `A` of at most `Q` queries, the
game's verifier accepts the statement and proof `A` outputs, the chosen program's sentinel slot is
not a `JUMP`, and the trace extracted from `A`'s queries is no valid execution of that program on
that input, with probability at most `(Q + 13700)/2^128 + hashTerm 13700 Q`. -/
theorem baseVerifier_extractsExecution_rom_adaptive {A : AdaptiveAdversary} {Q : ℕ}
    (hQ : IsTotalQueryBound A Q) :
    Pr{let z ← runRandom (adaptiveGame verifyWith A)}[z.1.ok = true ∧ SentinelSafe z.1.prog ∧
      ¬ ∃ t, extractExecution z.1.prog z.1.input z.1.proof z.1.logA = some t ∧
        ValidExecution z.1.prog z.1.input t] ≤
      ((Q + 13700 : ℕ) / 2 ^ 128 + hashTerm 13700 Q : ℝ≥0) :=
  (prEvent_mono_of_support _ _ _ fun _ _ h ↦ ⟨h.1, noWitness h.2.1 h.2.2⟩).trans
    (baseVerifier_extractsWitness_rom_adaptive hQ)

/-- **Adaptive knowledge soundness in the random-oracle model for well-formed programs**: the
execution form for an adversary whose programs, on its runs under the lazy random oracle, are all
`WellFormedBytecode`. The proof uses only `WellFormedBytecode.sentinelSafe`; the fill blocks are
unused here. -/
theorem baseVerifier_extractsExecution_rom_adaptive_wellFormed {A : AdaptiveAdversary} {Q : ℕ}
    (hQ : IsTotalQueryBound A Q)
    (hwf : ∀ z ∈ support (runRandom (adaptiveGame verifyWith A)), WellFormedBytecode z.1.prog) :
    Pr{let z ← runRandom (adaptiveGame verifyWith A)}[z.1.ok = true ∧ ¬ ∃ t,
      extractExecution z.1.prog z.1.input z.1.proof z.1.logA = some t ∧
        ValidExecution z.1.prog z.1.input t] ≤
      ((Q + 13700 : ℕ) / 2 ^ 128 + hashTerm 13700 Q : ℝ≥0) :=
  (prEvent_mono_of_support _ _ _ fun z hz h ↦
    ⟨h.1, (hwf z hz).sentinelSafe, h.2⟩).trans (baseVerifier_extractsExecution_rom_adaptive hQ)

/-- **Adaptive knowledge soundness in the random-oracle model for an execution, for an adversary
with coins**, a distribution `coins` over adaptive adversaries each making at most `Q` queries:
the bound of `baseVerifier_extractsExecution_rom_adaptive`, each coin-free adversary meeting it. -/
theorem baseVerifier_extractsExecution_rom_adaptive_coins {coins : ProbComp AdaptiveAdversary}
    {Q : ℕ} (hQ : ∀ A ∈ support coins, IsTotalQueryBound A Q) :
    Pr{let A ← coins; let z ← runRandom (adaptiveGame verifyWith A)}[z.1.ok = true ∧
      SentinelSafe z.1.prog ∧ ¬ ∃ t,
        extractExecution z.1.prog z.1.input z.1.proof z.1.logA = some t ∧
          ValidExecution z.1.prog z.1.input t] ≤
      ((Q + 13700 : ℕ) / 2 ^ 128 + hashTerm 13700 Q : ℝ≥0) := by
  rw [← bind_assoc]
  exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun A hA ↦
    baseVerifier_extractsExecution_rom_adaptive (hQ A hA)

/-- **The hypothesis from the comparison form.** If misbehaving on the run of an adaptive adversary
of at most `Q` queries, its flips those the verifier asked for on the chain of the statement it
chose, is at most `δ` likelier with BLAKE2s-256 answering than with a uniformly random function,
BLAKE2s misbehaves on it with probability at most the random-oracle bound
`(Q + 13700)/2^128 + hashTerm 13700 Q` plus `δ`. -/
theorem blakeMisbehavesAdaptive_of_comparison {A : AdaptiveAdversary} {Q : ℕ} {δ : ℝ≥0∞}
    (hQ : IsTotalQueryBound A Q)
    (h : Blake2sActsAsRandomOracle (adaptiveGame verifyWith A)
      (fun g ↦ HashMisbehavesFrom [] (rootsOf g.prog g.input)
        (leanVmReader.VerifierFlipFor (g.prog, g.input)) g.toRun) δ) :
    BlakeMisbehavesAdaptive A (((Q + 13700 : ℕ) / 2 ^ 128 + hashTerm 13700 Q : ℝ≥0) + δ) := by
  have hR : Pr{let z ← runRandom (adaptiveGame verifyWith A)}[
      HashMisbehavesFrom [] (rootsOf z.1.prog z.1.input)
        (leanVmReader.VerifierFlipFor (z.1.prog, z.1.input)) z.1.toRun] ≤
      ((Q + 13700 : ℕ) / 2 ^ 128 + hashTerm 13700 Q : ℝ≥0) :=
    (prEvent_mono_of_support _ _ _ fun _ _ h ↦
      h.mono fun _ ↦ leanVmReader.flip_of_verifierFlipFor).trans
      ((misbehaves_rom_adaptive hQ).trans (niError_closed Q))
  exact h.trans (add_le_add_left hR δ)

/-! ## Knowledge soundness of the deployed verifier -/

/-- On a run of the adaptive game under BLAKE2s whose proof `verify` accepts, no satisfying
witness through the adaptor means the hash misbehaves, a flip being one the verifier asked for on
the chosen statement's chain. -/
private theorem misbehaves_of_escape_adaptive {A : AdaptiveAdversary} {g : AdaptiveRun}
    (hg : g ∈ support (runBlake2s (adaptiveGame verifyWith A)))
    (hok : verify g.prog g.input g.proof = true)
    (hX : ¬ ∃ e, extract Blake2sFlock.blake2sFlockSpec g.prog g.input g.proof g.logA = some e ∧
      SatisfiedBy g.prog g.input (witnessOf Blake2sFlock.blake2sFlockSpec g.prog e.1 e.2)) :
    HashMisbehavesFrom [] (rootsOf g.prog g.input) (leanVmReader.VerifierFlipFor (g.prog, g.input))
      g.toRun :=
  have ⟨hg', hc, hok'⟩ := mem_support_runBlake2s_adaptive hg
  misbehaves_of_escape ⟨hg', hc⟩ (hok'.trans hok) hX

/-- **Adaptive knowledge soundness of the deployed verifier, the constraint form**, from which
`baseVerifier_extractsExecution_adaptive` is proved. With BLAKE2s-256 answering the hash, `verify`
accepts the statement and proof the adversary outputs while the witness read off the stack the
extractor reads off its queries does not satisfy leanISA's constraint statement at that statement
with probability at most `δ`, if BLAKE2s misbehaves on its run with probability at most `δ`. -/
theorem baseVerifier_extractsWitness_adaptive {A : AdaptiveAdversary} {δ : ℝ≥0∞}
    (hB : BlakeMisbehavesAdaptive A δ) :
    Pr{let g ← runBlake2s (adaptiveGame verifyWith A)}[
      verify g.prog g.input g.proof = true ∧ ¬ ∃ e,
        extract Blake2sFlock.blake2sFlockSpec g.prog g.input g.proof g.logA = some e ∧
          SatisfiedBy g.prog g.input (witnessOf Blake2sFlock.blake2sFlockSpec g.prog e.1 e.2)] ≤
      δ :=
  (prEvent_mono_of_support _ _ _ fun _ hg h ↦
    misbehaves_of_escape_adaptive hg h.1 h.2).trans hB

/-- **Adaptive knowledge soundness for an adversary with coins, the constraint form**, a
distribution `coins` over coin-free adaptive adversaries: the bound of
`baseVerifier_extractsWitness_adaptive`, with `δ` the probability over the coins that BLAKE2s
misbehaves on the drawn adversary's run. -/
theorem baseVerifier_extractsWitness_adaptive_coins {coins : ProbComp AdaptiveAdversary}
    {δ : ℝ≥0∞}
    (hB : Pr{let A ← coins; let g ← runBlake2s (adaptiveGame verifyWith A)}[
      HashMisbehavesFrom [] (rootsOf g.prog g.input)
        (leanVmReader.VerifierFlipFor (g.prog, g.input)) g.toRun] ≤ δ) :
    Pr{let A ← coins; let g ← runBlake2s (adaptiveGame verifyWith A)}[
      verify g.prog g.input g.proof = true ∧ ¬ ∃ e,
        extract Blake2sFlock.blake2sFlockSpec g.prog g.input g.proof g.logA = some e ∧
          SatisfiedBy g.prog g.input (witnessOf Blake2sFlock.blake2sFlockSpec g.prog e.1 e.2)] ≤
      δ := by
  let : MeasurableSpace AdaptiveAdversary := ⊤
  rw [← bind_assoc, prEvent_bind_eq_lintegral_of_discrete] at hB ⊢
  exact (MeasureTheory.lintegral_mono fun _ ↦ baseVerifier_extractsWitness_adaptive le_rfl).trans hB

/-- **The headline: adaptive knowledge soundness of the deployed verifier, for an execution.** With
BLAKE2s-256 answering the hash, `verify` accepts the statement and proof the adversary outputs, the
chosen program's sentinel slot is not a `JUMP`, and the trace extracted from the adversary's queries
is no valid execution of that program on that input, with probability at most `δ`, if BLAKE2s
misbehaves on its run with probability at most `δ`. -/
theorem baseVerifier_extractsExecution_adaptive {A : AdaptiveAdversary} {δ : ℝ≥0∞}
    (hB : BlakeMisbehavesAdaptive A δ) :
    Pr{let g ← runBlake2s (adaptiveGame verifyWith A)}[
      verify g.prog g.input g.proof = true ∧ SentinelSafe g.prog ∧ ¬ ∃ t,
        extractExecution g.prog g.input g.proof g.logA = some t ∧
          ValidExecution g.prog g.input t] ≤ δ :=
  (prEvent_mono_of_support _ _ _ fun _ _ h ↦ ⟨h.1, noWitness h.2.1 h.2.2⟩).trans
    (baseVerifier_extractsWitness_adaptive hB)

/-- **Adaptive knowledge soundness for well-formed programs**: the execution form for an adversary
whose programs, on its runs under BLAKE2s, are all `WellFormedBytecode`. The proof uses only
`WellFormedBytecode.sentinelSafe`; the fill blocks are unused here. -/
theorem baseVerifier_extractsExecution_adaptive_wellFormed {A : AdaptiveAdversary} {δ : ℝ≥0∞}
    (hB : BlakeMisbehavesAdaptive A δ)
    (hwf : ∀ g ∈ support (runBlake2s (adaptiveGame verifyWith A)), WellFormedBytecode g.prog) :
    Pr{let g ← runBlake2s (adaptiveGame verifyWith A)}[
      verify g.prog g.input g.proof = true ∧ ¬ ∃ t,
        extractExecution g.prog g.input g.proof g.logA = some t ∧
          ValidExecution g.prog g.input t] ≤ δ :=
  (prEvent_mono_of_support _ _ _ fun g hg h ↦
    ⟨h.1, (hwf g hg).sentinelSafe, h.2⟩).trans (baseVerifier_extractsExecution_adaptive hB)

/-- **The headline for an adversary with coins that chooses the statement**, a distribution
`coins` over coin-free adaptive adversaries: `verify` accepts the drawn adversary's statement and
proof, the chosen program's sentinel slot is not a `JUMP`, and the extracted trace is no valid
execution, with probability at most `δ`, the probability over the coins that BLAKE2s misbehaves on
the drawn adversary's run. -/
theorem baseVerifier_extractsExecution_adaptive_coins {coins : ProbComp AdaptiveAdversary}
    {δ : ℝ≥0∞}
    (hB : Pr{let A ← coins; let g ← runBlake2s (adaptiveGame verifyWith A)}[
      HashMisbehavesFrom [] (rootsOf g.prog g.input)
        (leanVmReader.VerifierFlipFor (g.prog, g.input)) g.toRun] ≤ δ) :
    Pr{let A ← coins; let g ← runBlake2s (adaptiveGame verifyWith A)}[
      verify g.prog g.input g.proof = true ∧ SentinelSafe g.prog ∧ ¬ ∃ t,
        extractExecution g.prog g.input g.proof g.logA = some t ∧
          ValidExecution g.prog g.input t] ≤ δ := by
  have hw := baseVerifier_extractsWitness_adaptive_coins hB
  rw [← bind_assoc] at hw ⊢
  exact (prEvent_mono_of_support _ _ _ fun _ _ h ↦ ⟨h.1, noWitness h.2.1 h.2.2⟩).trans hw

/-! ## At a statement fixed before the adversary runs -/

/-- **Knowledge soundness in the random-oracle model, the constraint form**, at a statement fixed
before the adversary runs: `baseVerifier_extractsWitness_rom_adaptive` at the adversary that outputs
it. With the hash a uniformly random function and an adversary `A` of at most `Q` queries, the
game's verifier accepts `A`'s proof while the witness read off the stack the extractor reads off
`A`'s queries does not satisfy leanISA's constraint statement with probability at most `(Q +
13700)/2^128` (the challenges) plus `hashTerm 13700 Q` (collisions and hits). -/
theorem baseVerifier_extractsWitness_rom {prog : Program} {input : PublicInput} {A : Adversary}
    {Q : ℕ} (hQ : IsTotalQueryBound A Q) :
    Pr{let z ← runRandom (loggedGame verifyWith prog input A)}[
      z.1.ok = true ∧ ¬ ∃ e,
        extract Blake2sFlock.blake2sFlockSpec prog input z.1.proof z.1.logA = some e ∧
          SatisfiedBy prog input (witnessOf Blake2sFlock.blake2sFlockSpec prog e.1 e.2)] ≤
      ((Q + 13700 : ℕ) / 2 ^ 128 + hashTerm 13700 Q : ℝ≥0) := by
  have h := baseVerifier_extractsWitness_rom_adaptive
    (A := (fun proof ↦ (prog, input, proof)) <$> A) ((isQueryBound_map_iff _ _ _ _ _).mpr hQ)
  rwa [prEvent_runRandom_const] at h

/-- **The headline in the random-oracle model at a fixed statement.** For a program whose sentinel
slot is not a `JUMP`, with the hash a uniformly random function and an adversary `A` of at most `Q`
queries, the game's verifier accepts `A`'s proof while the trace extracted from `A`'s queries is no
valid execution of the program on the input with probability at most
`(Q + 13700)/2^128 + hashTerm 13700 Q`. -/
theorem baseVerifier_extractsExecution_rom {prog : Program} {input : PublicInput}
    {A : Adversary} {Q : ℕ} (hsafe : SentinelSafe prog) (hQ : IsTotalQueryBound A Q) :
    Pr{let z ← runRandom (loggedGame verifyWith prog input A)}[
      z.1.ok = true ∧ ¬ ∃ t, extractExecution prog input z.1.proof z.1.logA = some t ∧
        ValidExecution prog input t] ≤
      ((Q + 13700 : ℕ) / 2 ^ 128 + hashTerm 13700 Q : ℝ≥0) :=
  (prEvent_mono_of_support _ _ _ fun _ _ h ↦ ⟨h.1, noWitness hsafe h.2⟩).trans
    (baseVerifier_extractsWitness_rom hQ)

/-- **Knowledge soundness of the deployed verifier, the constraint form**, at a statement fixed
before the adversary runs: `baseVerifier_extractsWitness_adaptive` at the adversary that outputs it.
With BLAKE2s-256 answering the hash, `verify` accepts the adversary's proof while the witness read
off the stack the extractor reads off its queries does not satisfy leanISA's constraint statement
with probability at most `δ`, if BLAKE2s misbehaves on its run with probability at most `δ`. -/
theorem baseVerifier_extractsWitness {prog : Program} {input : PublicInput} {A : Adversary}
    {δ : ℝ≥0∞} (hB : BlakeMisbehaves prog input A δ) :
    Pr{let g ← runBlake2s (loggedGame verifyWith prog input A)}[
      verify prog input g.proof = true ∧ ¬ ∃ e,
        extract Blake2sFlock.blake2sFlockSpec prog input g.proof g.logA = some e ∧
          SatisfiedBy prog input (witnessOf Blake2sFlock.blake2sFlockSpec prog e.1 e.2)] ≤ δ := by
  have h := baseVerifier_extractsWitness_adaptive ((blakeMisbehavesAdaptive_const _ _ _ _).mpr hB)
  rwa [prEvent_runBlake2s_const] at h

/-- **Knowledge soundness for an adversary with coins, the constraint form**, at a statement fixed
before the coins are drawn.
An adversary with coins is a distribution `coins` over coin-free ones. With BLAKE2s-256 answering
the hash, `verify` accepts the proof of the adversary drawn from `coins` while the witness read off
the stack the extractor reads off its queries does not satisfy leanISA's constraint statement with
probability at most `δ`, if BLAKE2s misbehaves on the drawn adversary's run with probability at
most `δ`, a probability over the coins and no longer `0` or `1`. -/
theorem baseVerifier_extractsWitness_coins {prog : Program} {input : PublicInput}
    {coins : ProbComp Adversary} {δ : ℝ≥0∞}
    (hB : Pr{let A ← coins; let g ← runBlake2s (loggedGame verifyWith prog input A)}[
      HashMisbehavesFrom [] (rootsOf prog input) (leanVmReader.VerifierFlipFor (prog, input)) g] ≤
        δ) :
    Pr{let A ← coins; let g ← runBlake2s (loggedGame verifyWith prog input A)}[
      verify prog input g.proof = true ∧ ¬ ∃ e,
        extract Blake2sFlock.blake2sFlockSpec prog input g.proof g.logA = some e ∧
          SatisfiedBy prog input (witnessOf Blake2sFlock.blake2sFlockSpec prog e.1 e.2)] ≤ δ := by
  let : MeasurableSpace Adversary := ⊤
  rw [← bind_assoc, prEvent_bind_eq_lintegral_of_discrete] at hB ⊢
  exact (MeasureTheory.lintegral_mono fun _ ↦ baseVerifier_extractsWitness le_rfl).trans hB

/-- **The headline: knowledge soundness of the deployed verifier, for an execution**, at a
statement fixed before the adversary runs. For a program whose sentinel slot is not a `JUMP`, with
BLAKE2s-256 answering the hash, `verify` accepts the adversary's proof while the trace the extractor
reads off its queries is no valid execution of the program on the input with probability at most
`δ`, if BLAKE2s misbehaves on its run with probability at most `δ`. -/
theorem baseVerifier_extractsExecution {prog : Program} {input : PublicInput} {A : Adversary}
    {δ : ℝ≥0∞} (hsafe : SentinelSafe prog) (hB : BlakeMisbehaves prog input A δ) :
    Pr{let g ← runBlake2s (loggedGame verifyWith prog input A)}[
      verify prog input g.proof = true ∧ ¬ ∃ t,
        extractExecution prog input g.proof g.logA = some t ∧ ValidExecution prog input t] ≤ δ :=
  (prEvent_mono_of_support _ _ _ fun _ _ h ↦ ⟨h.1, noWitness hsafe h.2⟩).trans
    (baseVerifier_extractsWitness hB)

/-- **The headline for an adversary with coins** at a statement fixed before the coins are drawn.
For a program whose sentinel slot is not a `JUMP`, with BLAKE2s-256 answering the hash, `verify`
accepts the proof of the adversary drawn from `coins` while the extracted trace is no valid
execution with probability at most `δ`, the probability over the coins that BLAKE2s misbehaves on
the drawn adversary's run. -/
theorem baseVerifier_extractsExecution_coins {prog : Program} {input : PublicInput}
    {coins : ProbComp Adversary} {δ : ℝ≥0∞} (hsafe : SentinelSafe prog)
    (hB : Pr{let A ← coins; let g ← runBlake2s (loggedGame verifyWith prog input A)}[
      HashMisbehavesFrom [] (rootsOf prog input) (leanVmReader.VerifierFlipFor (prog, input)) g] ≤
        δ) :
    Pr{let A ← coins; let g ← runBlake2s (loggedGame verifyWith prog input A)}[
      verify prog input g.proof = true ∧ ¬ ∃ t,
        extractExecution prog input g.proof g.logA = some t ∧ ValidExecution prog input t] ≤ δ := by
  have hw := baseVerifier_extractsWitness_coins hB
  rw [← bind_assoc] at hw ⊢
  exact (prEvent_mono_of_support _ _ _ fun _ _ h ↦ ⟨h.1, noWitness hsafe h.2⟩).trans hw

/-- **The hypothesis from the comparison form** at a statement fixed before the adversary runs. If
misbehaving on the run of an adversary of at most `Q` queries, its flips those the verifier asked
for on the chain of `(prog, input)`, is at most `δ` likelier with BLAKE2s-256 answering than with a
uniformly random function, BLAKE2s misbehaves on it with probability at most the random-oracle bound
`(Q + 13700)/2^128 + hashTerm 13700 Q` plus `δ`. -/
theorem blakeMisbehaves_of_comparison {prog : Program} {input : PublicInput} {A : Adversary}
    {Q : ℕ} {δ : ℝ≥0∞} (hQ : IsTotalQueryBound A Q)
    (h : Blake2sActsAsRandomOracle (loggedGame verifyWith prog input A)
      (HashMisbehavesFrom [] (rootsOf prog input) (leanVmReader.VerifierFlipFor (prog, input))) δ) :
    BlakeMisbehaves prog input A (((Q + 13700 : ℕ) / 2 ^ 128 + hashTerm 13700 Q : ℝ≥0) + δ) :=
  h.trans (add_le_add_left ((prEvent_mono_of_support _ _ _ fun _ _ h ↦
    h.mono fun _ ↦ leanVmReader.flip_of_verifierFlipFor).trans
    (leanVm_misbehaves_rom_closed prog input A hQ)) δ)

/-! ## Completeness -/

/-- **The honest prover from an execution at a hash `H`** in a monad `m`: the witness generator
`witnessGen`, then `proveWith` on its witness; `none` when either returns none. -/
def proveExecutionWith {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (fuel : ℕ)
    (F : FlockSpec) (prog : Program) (input : PublicInput) (t : Trace prog) (ρ : ℕ) :
    m (Option (Proof PrunedMerklePaths)) :=
  match witnessGen prog input t with
  | some w => proveWith H fuel F prog input w ρ
  | none => pure none

/-- **leanVM's honest prover from an execution**: the witness generator `witnessGen`, then the
deployed prover `prove` on its witness, at `fuel` candidate nonces per grind and the WHIR rate
`ρ`; `none` when either returns none. It is `proveExecutionWith` at BLAKE2s-256 and the deployed
Flock specification, as `prove` is `proveWith`. -/
def proveExecution (fuel : ℕ) (prog : Program) (input : PublicInput) (t : Trace prog) (ρ : ℕ) :
    Option (Proof PrunedMerklePaths) :=
  proveExecutionWith (m := Id) blake2sBytes fuel Blake2sFlock.blake2sFlockSpec prog input t ρ

/-- The hypotheses of the random-oracle completeness from an execution, decided: first, in
constant time, a valid rate and the bounds a stack that fits puts on the memory, the bytecode
(`StackFits.bounds`) and the run (`StackFits.steps_le`), so that no check below reads a memory or
bytecode too large to fit or steps a run longer than such a stack allows; then well-formed
bytecode (`wellFormedB`), a valid execution (`checkTrace`) and a stack that fits
(`stackFitsB`). -/
def checkExecution (prog : Program) (input : PublicInput) (t : Trace prog) (ρ : ℕ) : Bool :=
  decide (t.κ ≤ 24 ∧ prog.logSize ≤ 27 ∧ t.steps ≤ 2 ^ 25 ∧ validRate ρ) && wellFormedB prog &&
    checkTrace prog input t && stackFitsB prog t

/-- **leanVM's honest prover from an execution, guarded**: `proveExecution` when the hypotheses
of completeness pass their checks (`checkExecution`), none otherwise. -/
def proveChecked (fuel : ℕ) (prog : Program) (input : PublicInput) (t : Trace prog) (ρ : ℕ) :
    Option (Proof PrunedMerklePaths) :=
  if checkExecution prog input t ρ then proveExecution fuel prog input t ρ else none

/-- **Completeness of the deployed pair, the constraint form**, from which
`proveExecution_complete` is proved. For a witness that satisfies leanISA's constraint
statement, `verify` accepts every proof `prove` returns: `Prove.baseProver_complete` at
BLAKE2s-256. When `prove` returns none is `prove_eq_none`. -/
theorem prove_complete (fuel : ℕ) {prog : Program} {input : PublicInput} {κ : ℕ}
    {w : EnsembleWitness (leanIsaEnsemble prog κ)} {ρ : ℕ} {proof : Proof PrunedMerklePaths}
    (hsat : SatisfiedBy prog input w) (hp : prove fuel prog input w ρ = some proof) :
    verify prog input proof = true :=
  Prove.baseProver_complete blake2sBytes fuel hsat hp

/-- **When the deployed prover returns no proof** for a witness of the constraint statement: the
witness has sizes, within the statement's caps, and either they put the stack above `2^maxMu`, or
the rate `ρ` is not valid, or a grind finds no nonce among its `fuel` candidates at a chain state
the prover's run reaches (`ProveReaches`, every round boundary of the run, so the grind named may
be one the run does not make). Nothing bounds how often the last happens. -/
theorem prove_eq_none (fuel : ℕ) {prog : Program} {input : PublicInput} {κ : ℕ}
    {w : EnsembleWitness (leanIsaEnsemble prog κ)} {ρ : ℕ} (hsat : SatisfiedBy prog input w)
    (h : prove fuel prog input w ρ = none) :
    ∃ s, Sizes.ofWitness w = some s ∧ (maxMu < leanIsaμ prog s ∨ ¬ validRate ρ ∨
      ∃ fs, ProveReaches fuel prog input w ρ fs ∧
        Id.run (fs.grind blake2sBytes fuel queryGrindingBits) = none) := by
  rcases Prove.proveWith_eq_none blake2sBytes fuel _ h with hn | ⟨s, hs, hc⟩
  · obtain ⟨s, hs⟩ := sizes_of_satisfiedBy hsat
    simp [hs] at hn
  · exact ⟨s, hs, hc.imp_left ((admissible_iff_of_satisfiedBy hsat hs).not.trans not_le).mp⟩

/-- **When the deployed prover returns a proof** for a witness of the constraint statement, at
its sizes `s`: when they put the stack within `2^maxMu`, the rate `ρ` is valid, and no grind runs
out of its `fuel` candidates at a chain state the prover's run reaches (`ProveReaches`): at
every round boundary of the run, which asks more than the grinds the run makes. -/
theorem prove_ne_none (fuel : ℕ) {prog : Program} {input : PublicInput} {κ : ℕ}
    {w : EnsembleWitness (leanIsaEnsemble prog κ)} {ρ : ℕ} {s : Sizes}
    (hsat : SatisfiedBy prog input w) (hs : Sizes.ofWitness w = some s)
    (hμ : leanIsaμ prog s ≤ maxMu) (hρ : validRate ρ)
    (hg : ∀ fs, ProveReaches fuel prog input w ρ fs →
      Id.run (fs.grind blake2sBytes fuel queryGrindingBits) ≠ none) :
    prove fuel prog input w ρ ≠ none :=
  Prove.proveWith_ne_none blake2sBytes fuel _ hs ((admissible_iff_of_satisfiedBy hsat hs).mpr hμ)
    hρ hg

/-- The honest run from an execution in the random-oracle model: the witness generator on `t`,
then the deployed prover on its witness with every hash a query to the oracle, then the verifier
on the proof, asking the same oracle; a generator or prover returning none is rejected. -/
def honestExecutionGame (fuel : ℕ) (prog : Program) (input : PublicInput) (t : Trace prog)
    (ρ : ℕ) : OracleComp hashSpec Bool := do
  match ← proveExecutionWith hashQuery fuel Blake2sFlock.blake2sFlockSpec prog input t ρ with
  | none => pure false
  | some proof => verifyWith hashQuery prog input proof

/-- On an execution whose stack fits, the honest run from the execution is the honest run of the
generated witness, which satisfies the constraint statement at sizes that keep the stack within
`2^maxMu`. -/
private theorem honestExecutionGame_eq {prog : Program} {input : PublicInput} {t : Trace prog}
    (hwf : WellFormedBytecode prog) (ht : ValidExecution prog input t)
    (hstack : StackFits prog t) :
    ∃ (w : EnsembleWitness (leanIsaEnsemble prog (t.κ + 1))) (s : Sizes),
      SatisfiedBy prog input w ∧ Sizes.ofWitness w = some s ∧ leanIsaμ prog s ≤ maxMu ∧
      ∀ fuel ρ, honestExecutionGame fuel prog input t ρ = honestGame fuel prog input w ρ := by
  obtain ⟨w, hw, hsat, -⟩ := witnessGen_correct hwf ht hstack.fits
  obtain ⟨τ, hτ, hs⟩ := sizes_witnessGen ht hw
  obtain ⟨τ', hτ', hμ⟩ := hstack
  obtain rfl := Option.some.inj (hτ.symm.trans hτ')
  refine ⟨w, _, hsat, hs, hμ, fun fuel ρ ↦ ?_⟩
  unfold honestExecutionGame proveExecutionWith honestGame
  rw [hw]
  rfl

/-- **The headline: completeness from an execution in the random-oracle model.**

*The game* (`honestExecutionGame`): the hash is a lazily sampled random function from byte strings
to 32-byte digests (`runRandom`). The witness generator runs on the execution `t`, the deployed
prover runs on its witness at `fuel` candidate nonces per grind and WHIR rate `ρ` with every hash a
query to that function, and the deployed verifier checks the proof, asking the same function.

*The bound*: the verifier rejects with probability at most
`(N + 1) · (1 - 2^-17)^min(fuel, 2^64) + N² / 2^256`, with `N = 264246250 + 6 · fuel` a bound on
the prover's queries; the first term is a grind running out of fuel, the second a collision.

*The assumptions*: `prog` is well-formed bytecode (its last slot no `JUMP`, the compiler's fill
blocks present), `t` is a valid execution of `prog` on `input` whose stack fits (`StackFits`,
which fails from `t.κ ≥ 25` on, and implies that `t` fits the caps, `StackFits.fits`), and `ρ` is
a valid rate. Each is decided by a computation: `wellFormedB`, `checkTrace`, `stackFitsB` (on a
valid execution), and the `Decidable` instance of `validRate`; `proveChecked` runs them. -/
theorem proveExecution_rom_complete (fuel : ℕ) {prog : Program} {input : PublicInput}
    {t : Trace prog} {ρ : ℕ} (hwf : WellFormedBytecode prog) (ht : ValidExecution prog input t)
    (hstack : StackFits prog t) (hρ : validRate ρ) :
    Pr{let z ← runRandom (honestExecutionGame fuel prog input t ρ)}[z.1 = false] ≤
      (((264246250 + 6 * fuel : ℕ) : ℝ≥0∞) + 1) *
          (1 - (2 ^ queryGrindingBits : ℝ≥0∞)⁻¹) ^ min fuel (2 ^ 64) +
        ((264246250 + 6 * fuel : ℕ) : ℝ≥0∞) * ((264246250 + 6 * fuel : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  obtain ⟨w, s, hsat, hs, hμ, hg⟩ := honestExecutionGame_eq hwf ht hstack
  rw [hg]
  exact honestGame_rom_rejects_le fuel hsat hs hμ hρ

/-- **Completeness from an execution in the random-oracle model at the default fuel `2^24`**: the
honest run of `proveExecution_rom_complete` is rejected with probability at most `2^-154`. -/
theorem proveExecution_rom_complete_default {prog : Program} {input : PublicInput}
    {t : Trace prog} {ρ : ℕ} (hwf : WellFormedBytecode prog) (ht : ValidExecution prog input t)
    (hstack : StackFits prog t) (hρ : validRate ρ) :
    Pr{let z ← runRandom (honestExecutionGame (2 ^ 24) prog input t ρ)}[z.1 = false] ≤
      (2 ^ 154 : ℝ≥0∞)⁻¹ := by
  obtain ⟨w, s, hsat, hs, hμ, hg⟩ := honestExecutionGame_eq hwf ht hstack
  rw [hg]
  exact honestGame_rom_rejects_le_default hsat hs hμ hρ

/-- **The headline: completeness of the deployed prover from an execution.** For well-formed
bytecode and a valid execution `t` that fits the caps, with `t'` the padded trace
`padTrace t (fillStarts prog)`, a valid execution with the same steps as `t`, its memory doubled
with the fill frames above `t`'s image, the witness generator returns a witness `w`, which
satisfies the constraint statement and represents `t'`. At every fuel and rate, `verify` accepts
every proof `proveExecution` returns; it returns none only when the stack does not fit
(`StackFits`), the rate is not valid, or a grind runs out of fuel at a chain state the prover's
run reaches; the last conjunct says the same as a sufficient condition for a proof. `Trace.Fits`
does not keep the stack within `2^maxMu`: the stack does not fit from `t.κ ≥ 25` on
(`not_stackFits_of_le`), and then `proveExecution` returns none
(`proveExecution_eq_none_of_not_stackFits`). At the witness's sizes the stack condition is
`leanIsaμ prog s ≤ maxMu` (`stackFits_iff`). -/
theorem proveExecution_complete {prog : Program} {input : PublicInput} {t : Trace prog}
    (hwf : WellFormedBytecode prog) (ht : ValidExecution prog input t) (hfit : t.Fits) :
    let t' := padTrace t (fillStarts prog)
    t'.PaddedFrom t ∧ ValidExecution prog input t' ∧
    ∃ w, witnessGen prog input t = some w ∧ SatisfiedBy prog input w ∧
      AssignmentRepresents w t' ∧ ∀ fuel ρ,
        (∀ proof, proveExecution fuel prog input t ρ = some proof →
          verify prog input proof = true) ∧
        (proveExecution fuel prog input t ρ = none → ¬ StackFits prog t ∨ ¬ validRate ρ ∨
          ∃ fs, ProveReaches fuel prog input w ρ fs ∧
            Id.run (fs.grind blake2sBytes fuel queryGrindingBits) = none) ∧
        (StackFits prog t → validRate ρ →
          (∀ fs, ProveReaches fuel prog input w ρ fs →
            Id.run (fs.grind blake2sBytes fuel queryGrindingBits) ≠ none) →
          proveExecution fuel prog input t ρ ≠ none) := by
  obtain ⟨w, hw, hsat, hrep⟩ := witnessGen_correct hwf ht hfit
  obtain ⟨τ, hτ, hs⟩ := sizes_witnessGen ht hw
  have hst : StackFits prog t ↔ leanIsaμ prog (execSizes t.κ t.runRows τ) ≤ maxMu :=
    ⟨fun ⟨_, hτ', hμ⟩ ↦ Option.some.inj (hτ.symm.trans hτ') ▸ hμ, fun hμ ↦ ⟨τ, hτ, hμ⟩⟩
  have hp : ∀ fuel ρ, proveExecution fuel prog input t ρ = prove fuel prog input w ρ :=
    fun _ _ ↦ by simp only [proveExecution, proveExecutionWith, hw]; rfl
  refine ⟨padTrace_from t _, (padTrace_from t _).valid hfit.room ht, w, hw, hsat, hrep,
    fun fuel ρ ↦ ?_⟩
  rw [hp, hst]
  refine ⟨fun _ ↦ prove_complete fuel hsat, fun h ↦ ?_, prove_ne_none fuel hsat hs⟩
  obtain ⟨s', hs', hc⟩ := prove_eq_none fuel hsat h
  obtain rfl := Option.some.inj (hs.symm.trans hs')
  exact hc.imp_left not_le.mpr

/-- **A stack that does not fit gets no proof**: on a valid execution whose stack does not fit,
`proveExecution` returns none at every fuel and rate, since the generated witness's sizes put the
stack above `2^maxMu` and `prove` checks them first. -/
theorem proveExecution_eq_none_of_not_stackFits (fuel : ℕ) {prog : Program} {input : PublicInput}
    {t : Trace prog} {ρ : ℕ} (ht : ValidExecution prog input t) (h : ¬ StackFits prog t) :
    proveExecution fuel prog input t ρ = none := by
  unfold proveExecution proveExecutionWith
  split
  · next w hw =>
    obtain ⟨τ, hτ, hs⟩ := sizes_witnessGen ht hw
    simp only [proveWith, proveFrom, hs]
    split_ifs with ha
    · exact absurd ⟨τ, hτ, ha.1.2.2.2.2⟩ h
    · rfl
  · rfl

/-- The checks of `checkExecution` decide the hypotheses of the random-oracle completeness from an
execution. -/
theorem checkExecution_eq_true_iff {prog : Program} {input : PublicInput} {t : Trace prog}
    {ρ : ℕ} : checkExecution prog input t ρ = true ↔ WellFormedBytecode prog ∧
      ValidExecution prog input t ∧ StackFits prog t ∧ validRate ρ := by
  simp only [checkExecution, Bool.and_eq_true, decide_eq_true_eq, wellFormedB_eq_true_iff,
    checkTrace_eq_true_iff]
  constructor
  · rintro ⟨⟨⟨⟨-, -, -, hρ⟩, hwf⟩, ht⟩, hst⟩
    exact ⟨hwf, ht, (stackFitsB_eq_true_iff ht).mp hst, hρ⟩
  · rintro ⟨hwf, ht, hst, hρ⟩
    exact ⟨⟨⟨⟨hst.bounds.1, hst.bounds.2, hst.steps_le ht.2, hρ⟩, hwf⟩, ht⟩,
      (stackFitsB_eq_true_iff ht).mpr hst⟩

/-- **Every proof the guarded prover returns is accepted**, with no hypothesis: it proves only
after its checks pass, and then `proveExecution_complete` applies. -/
theorem verify_proveChecked {fuel : ℕ} {prog : Program} {input : PublicInput} {t : Trace prog}
    {ρ : ℕ} {proof : Proof PrunedMerklePaths} (h : proveChecked fuel prog input t ρ = some proof) :
    verify prog input proof = true := by
  unfold proveChecked at h
  split_ifs at h with hc
  obtain ⟨hwf, ht, hst, -⟩ := checkExecution_eq_true_iff.mp hc
  obtain ⟨-, -, w, -, -, -, hall⟩ := proveExecution_complete hwf ht hst.fits
  exact (hall fuel ρ).1 proof h

/-- **Under the hypotheses of the random-oracle completeness the guarded prover is
`proveExecution`.** -/
theorem proveChecked_eq (fuel : ℕ) {prog : Program} {input : PublicInput} {t : Trace prog}
    {ρ : ℕ} (hwf : WellFormedBytecode prog) (ht : ValidExecution prog input t)
    (hstack : StackFits prog t) (hρ : validRate ρ) :
    proveChecked fuel prog input t ρ = proveExecution fuel prog input t ρ := by
  have hc : checkExecution prog input t ρ = true :=
    checkExecution_eq_true_iff.mpr ⟨hwf, ht, hstack, hρ⟩
  simp only [proveChecked, hc, ↓reduceIte]

end

end LeanerVM.Protocol
