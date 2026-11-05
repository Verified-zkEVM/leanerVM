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
public import LeanerVM.Protocol.Compile.Agree
public import LeanerVM.Protocol.AdaptiveGame
public import LeanerVM.Semantics.FillBlocks
public import LeanerVM.Protocol.Prove.RomComplete
public import LeanerVM.Protocol.Prove.Queries

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
(`Trace.PaddedFrom`); with `s` its sizes, at every fuel and rate `verify` accepts every proof
`proveExecution` returns, and `proveExecution` returns a proof unless the stack exceeds
`2^maxMu`, the rate is not valid, or a grind finds no nonce among its `fuel` candidates at a
chain state the prover's run reaches (`ProveReaches`: the state after the announcement and some
first rounds of the run, so every round boundary, a superset of the states the grinds start at).

## Completeness in the random-oracle model

`proveExecution_rom_complete`: for `WellFormedBytecode`, a valid execution `t` that fits the caps,
a generated witness whose stack fits (`StackFits`) and a valid rate, the honest run from the
execution (`honestExecutionGame`: the witness generator, the deployed prover with every hash a
query to one lazy random oracle, then the verifier on its proof at the same oracle) is rejected
with probability at most `(N + 1) (1 - 2^-17)^min(fuel, 2^64) + N^2 / 2^256`,
`N = 264246250 + 6 · fuel`; below `2^-154` at the default fuel `2^24`
(`proveExecution_rom_complete_default`). It is proved from the constraint form:
`honestGame_rom_rejects_le`: for a witness of the constraint statement whose sizes keep the stack
within `2^maxMu`, at a valid rate, the deployed prover and then the verifier on its proof, both
asking one lazy random oracle (`honestGame`), reject with probability at most
`(N + 1) (1 - 2^-17)^min(fuel, 2^64) + N^2 / 2^256` with `N = 264246250 + 6 · fuel`;
`prove_rom_eq_none_le` bounds the prover's failure alone. At the executable's default fuel `2^24`
both are below `2^-154` (`honestGame_rom_rejects_le_default`, `prove_rom_eq_none_le_default`).
The run is the deterministic run at the hash its final cache defines, where a failing grind leaves
an exhausted proof-of-work search in the cache (`Prove.exhausted_of_grind_eq_none`), which
`PowSearch.prEvent_exhausted_le` bounds given the prover's query count; the count
(`Prove.isTotalQueryBound_proveWith_closed`) is the verifier's phase by phase, with each
commitment's tree and each grind's candidates, maximised over the window of sizes.

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
is about a random function), and `Trace.Fits` does not keep the stack within `2^maxMu`. The padding
the proof picks has memory log-size `t.κ + 1`, so its four memory columns alone hold `2^(t.κ+3)`
cells, above `2^28` from `t.κ ≥ 26` on, where `proveExecution` returns none at every fuel and rate;
so it does whenever the filled tables exceed `2^28` cells. The generated witness represents the
padded trace, not the given one: the proof is of the same steps over a memory with the fill frames
above the image. -/

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
  (OracleComp.prEvent_mono_of_support _ fun _ hz h ↦
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
  (OracleComp.prEvent_mono_of_support _ fun _ _ h ↦ ⟨h.1, noWitness h.2.1 h.2.2⟩).trans
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
  (OracleComp.prEvent_mono_of_support _ fun z hz h ↦
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
    (OracleComp.prEvent_mono_of_support _ fun _ _ h ↦
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
  (OracleComp.prEvent_mono_of_support _ fun _ hg h ↦
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
  (OracleComp.prEvent_mono_of_support _ fun _ _ h ↦ ⟨h.1, noWitness h.2.1 h.2.2⟩).trans
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
  (OracleComp.prEvent_mono_of_support _ fun g hg h ↦
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
  exact (OracleComp.prEvent_mono_of_support _ fun _ _ h ↦ ⟨h.1, noWitness h.2.1 h.2.2⟩).trans hw

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
  (OracleComp.prEvent_mono_of_support _ fun _ _ h ↦ ⟨h.1, noWitness hsafe h.2⟩).trans
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
  (OracleComp.prEvent_mono_of_support _ fun _ _ h ↦ ⟨h.1, noWitness hsafe h.2⟩).trans
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
  exact (OracleComp.prEvent_mono_of_support _ fun _ _ h ↦ ⟨h.1, noWitness hsafe h.2⟩).trans hw

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
  h.trans (add_le_add_left ((OracleComp.prEvent_mono_of_support _ fun _ _ h ↦
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

/-- **The deployed prover in the random-oracle model returns a proof, except with small
probability.** For a witness of the constraint statement with sizes `s` that keep the stack within
`2^maxMu`, at a valid rate, the deployed prover with every hash a query to the lazy random oracle
returns no proof with probability at most `(N + 1) (1 - 2^-17)^min(fuel, 2^64) + N^2 / 2^256`,
where `N = 264246250 + 6 · fuel` bounds its queries (`Prove.isTotalQueryBound_proveWith_closed`). -/
theorem prove_rom_eq_none_le (fuel : ℕ) {prog : Program} {input : PublicInput} {κ : ℕ}
    {w : EnsembleWitness (leanIsaEnsemble prog κ)} {ρ : ℕ} {s : Sizes}
    (hsat : SatisfiedBy prog input w) (hs : Sizes.ofWitness w = some s)
    (hμ : leanIsaμ prog s ≤ maxMu) (hρ : validRate ρ) :
    Pr{let z ← runRandom (proveWith hashQuery fuel Blake2sFlock.blake2sFlockSpec prog input w ρ)}[
      z.1 = none] ≤
      (((264246250 + 6 * fuel : ℕ) : ℝ≥0∞) + 1) *
          (1 - (2 ^ queryGrindingBits : ℝ≥0∞)⁻¹) ^ min fuel (2 ^ 64) +
        ((264246250 + 6 * fuel : ℕ) : ℝ≥0∞) * ((264246250 + 6 * fuel : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  Prove.prEvent_proveWith_eq_none_le fuel _ hs ((admissible_iff_of_satisfiedBy hsat hs).mpr hμ)
    hρ (Prove.isTotalQueryBound_proveWith_closed fuel hsat hs hμ hρ)

/-- The honest run in the random-oracle model: the deployed prover's proof, then the verifier on
it, both asking the one hash oracle; a prover out of fuel is rejected. -/
def honestGame (fuel : ℕ) (prog : Program) (input : PublicInput) {κ : ℕ}
    (w : EnsembleWitness (leanIsaEnsemble prog κ)) (ρ : ℕ) : OracleComp hashSpec Bool := do
  match ← proveWith hashQuery fuel Blake2sFlock.blake2sFlockSpec prog input w ρ with
  | none => pure false
  | some proof => verifyWith hashQuery prog input proof

/-- **Completeness of the deployed pair in the random-oracle model.** For a witness of the
constraint statement with sizes `s` that keep the stack within `2^maxMu`, at a valid rate, the
honest run with the hash a lazy random oracle is rejected with probability at most
`(N + 1) (1 - 2^-17)^min(fuel, 2^64) + N^2 / 2^256`, `N = 264246250 + 6 · fuel`: every proof the
prover returns is accepted by the verifier asking the same oracle. -/
theorem honestGame_rom_rejects_le (fuel : ℕ) {prog : Program} {input : PublicInput} {κ : ℕ}
    {w : EnsembleWitness (leanIsaEnsemble prog κ)} {ρ : ℕ} {s : Sizes}
    (hsat : SatisfiedBy prog input w) (hs : Sizes.ofWitness w = some s)
    (hμ : leanIsaμ prog s ≤ maxMu) (hρ : validRate ρ) :
    Pr{let z ← runRandom (honestGame fuel prog input w ρ)}[z.1 = false] ≤
      (((264246250 + 6 * fuel : ℕ) : ℝ≥0∞) + 1) *
          (1 - (2 ^ queryGrindingBits : ℝ≥0∞)⁻¹) ^ min fuel (2 ^ 64) +
        ((264246250 + 6 * fuel : ℕ) : ℝ≥0∞) * ((264246250 + 6 * fuel : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  unfold runRandom honestGame
  rw [simulateQ_bind, StateT.run_bind]
  refine (prEvent_bind_le_add_iSup _ _ (fun z₁ ↦ z₁.1 = none) _).trans ?_
  refine le_of_le_of_eq (add_le_add (prove_rom_eq_none_le fuel hsat hs hμ hρ)
    (le_of_eq (ENNReal.iSup_eq_zero.mpr fun z₁ ↦ ENNReal.iSup_eq_zero.mpr fun hz₁ ↦
      ENNReal.iSup_eq_zero.mpr fun hne ↦ ?_)))
    (add_zero _)
  obtain ⟨p, c⟩ := z₁
  obtain ⟨proof, rfl⟩ := Option.ne_none_iff_exists'.mp hne
  refine (OracleComp.prEvent_eq_zero_iff _ _).mpr fun z hz hrej ↦ ?_
  set H : List UInt8 → Digest := fun t ↦ (z.2 t).getD Prove.zeroDigest
  have hagree : ∀ t u, z.2 t = some u → H t = u := fun t u h ↦ by simp [H, h]
  obtain ⟨hle, hver⟩ := run_simulateQ_pure_of_mem_support_randomOracle _ c hz H hagree
  have hpro := (run_simulateQ_pure_of_mem_support_randomOracle _ ∅ hz₁ H
    fun t u h ↦ hagree t u (hle h)).2
  have hp : proveWith (m := Id) H fuel Blake2sFlock.blake2sFlockSpec prog input w ρ =
      some proof :=
    (proveWith_simulateQ (r := Id) (fun t ↦ pure (H t)) fuel _ prog input w ρ).symm.trans hpro
  have hv : verifyWith (m := Id) H prog input proof = z.1 :=
    (verifyWith_simulateQ (r := Id) (fun t ↦ pure (H t)) prog input proof).symm.trans hver
  rw [Prove.baseProver_complete H fuel hsat hp] at hv
  rw [← hv] at hrej
  cases hrej

/-- The bound at the default fuel `2^24`, with `N = 364909546` queries, is below `2^-154`. -/
private theorem rom_bound_default (q : ℝ≥0∞) (hq : q ≤ (2 ^ 184 : ℝ≥0∞)⁻¹) :
    (((264246250 + 6 * 2 ^ 24 : ℕ) : ℝ≥0∞) + 1) * q +
      ((264246250 + 6 * 2 ^ 24 : ℕ) : ℝ≥0∞) * ((264246250 + 6 * 2 ^ 24 : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤
      (2 ^ 154 : ℝ≥0∞)⁻¹ := by
  refine (add_le_add (show (((264246250 + 6 * 2 ^ 24 : ℕ) : ℝ≥0∞) + 1) * q ≤
    (((264246250 + 6 * 2 ^ 24 : ℕ) : ℝ≥0∞) + 1) * (2 ^ 184 : ℝ≥0∞)⁻¹ by gcongr) le_rfl).trans ?_
  have h1 : (((264246250 + 6 * 2 ^ 24 : ℕ) : ℝ≥0∞) + 1) * (2 ^ 184 : ℝ≥0∞)⁻¹ =
      ENNReal.ofReal (364909547 / 2 ^ 184) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity)]
    norm_num [div_eq_mul_inv]
  have h2 : ((264246250 + 6 * 2 ^ 24 : ℕ) : ℝ≥0∞) * ((264246250 + 6 * 2 ^ 24 : ℕ) : ℝ≥0∞) /
      2 ^ 256 = ENNReal.ofReal (364909546 * 364909546 / 2 ^ 256) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity)]
    norm_num
  have h3 : (2 ^ 154 : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((2 ^ 154 : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos (by positivity)]
    norm_num
  rw [h1, h2, h3, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- **The deployed prover at the default fuel `2^24` in the random-oracle model** returns no proof
with probability below `2^-154`. -/
theorem prove_rom_eq_none_le_default {prog : Program} {input : PublicInput} {κ : ℕ}
    {w : EnsembleWitness (leanIsaEnsemble prog κ)} {ρ : ℕ} {s : Sizes}
    (hsat : SatisfiedBy prog input w) (hs : Sizes.ofWitness w = some s)
    (hμ : leanIsaμ prog s ≤ maxMu) (hρ : validRate ρ) :
    Pr{let z ← runRandom (proveWith hashQuery (2 ^ 24) Blake2sFlock.blake2sFlockSpec prog input
      w ρ)}[z.1 = none] ≤ (2 ^ 154 : ℝ≥0∞)⁻¹ :=
  (prove_rom_eq_none_le (2 ^ 24) hsat hs hμ hρ).trans
    (rom_bound_default _ Prove.one_sub_pow_fuel_le)

/-- **Completeness of the deployed pair at the default fuel `2^24` in the random-oracle model**:
the honest run is rejected with probability below `2^-154`. -/
theorem honestGame_rom_rejects_le_default {prog : Program} {input : PublicInput} {κ : ℕ}
    {w : EnsembleWitness (leanIsaEnsemble prog κ)} {ρ : ℕ} {s : Sizes}
    (hsat : SatisfiedBy prog input w) (hs : Sizes.ofWitness w = some s)
    (hμ : leanIsaμ prog s ≤ maxMu) (hρ : validRate ρ) :
    Pr{let z ← runRandom (honestGame (2 ^ 24) prog input w ρ)}[z.1 = false] ≤
      (2 ^ 154 : ℝ≥0∞)⁻¹ :=
  (honestGame_rom_rejects_le (2 ^ 24) hsat hs hμ hρ).trans
    (rom_bound_default _ Prove.one_sub_pow_fuel_le)

/-- **The stack of the generated witness fits**: the witness generator returns a witness for `t`,
and its sizes `s` (`Sizes.ofWitness`, determined by the witness) keep leanVM's stack within
`2^maxMu` cells (`leanIsaμ prog s ≤ maxMu`), which `prove` needs to return a proof. It is decided
by evaluating the generator. `Trace.Fits` does not imply it: the generator pads the memory to
log-size `t.κ + 1`, so its four memory columns alone hold `2^(t.κ+3)` cells, and from `t.κ ≥ 26`
on it fails. -/
def StackFits (prog : Program) (input : PublicInput) (t : Trace prog) : Prop :=
  ∃ s, (witnessGen prog input t).bind Sizes.ofWitness = some s ∧ leanIsaμ prog s ≤ maxMu

instance (prog : Program) (input : PublicInput) (t : Trace prog) :
    Decidable (StackFits prog input t) :=
  decidable_of_iff (((witnessGen prog input t).bind Sizes.ofWitness).any
    fun s ↦ decide (leanIsaμ prog s ≤ maxMu)) <| by
    unfold StackFits
    generalize (witnessGen prog input t).bind Sizes.ofWitness = o
    cases o <;> simp

/-- The honest run from an execution in the random-oracle model: the witness generator on `t`,
then the deployed prover on its witness with every hash a query to the oracle, then the verifier
on the proof, asking the same oracle; a generator or prover returning none is rejected. -/
def honestExecutionGame (fuel : ℕ) (prog : Program) (input : PublicInput) (t : Trace prog)
    (ρ : ℕ) : OracleComp hashSpec Bool := do
  match ← proveExecutionWith hashQuery fuel Blake2sFlock.blake2sFlockSpec prog input t ρ with
  | none => pure false
  | some proof => verifyWith hashQuery prog input proof

/-- **The headline: completeness from an execution in the random-oracle model.**

*The game* (`honestExecutionGame`): the hash is a lazily sampled random function from byte strings
to 32-byte digests (`runRandom`). The witness generator runs on the execution `t`, the deployed
prover runs on its witness at `fuel` candidate nonces per grind and WHIR rate `ρ` with every hash a
query to that function, and the deployed verifier checks the proof, asking the same function.

*The bound*: the verifier rejects with probability at most
`(N + 1) · (1 - 2^-17)^min(fuel, 2^64) + N² / 2^256`, with `N = 264246250 + 6 · fuel` a bound on
the prover's queries; the first term is a grind running out of fuel, the second a collision.

*The assumptions*: `prog` is well-formed bytecode (its last slot no `JUMP`, the compiler's fill
blocks present), `t` is a valid execution of `prog` on `input` that fits the caps (`Trace.Fits`),
the stack of the generated witness fits (`StackFits`, which fails from `t.κ ≥ 26` on), and `ρ` is
a valid rate. Each is decided by a computation: `wellFormedB`, `checkTrace`, `fitsB` (on a valid
execution), and the `Decidable` instances of `StackFits` and `validRate`. -/
theorem proveExecution_rom_complete (fuel : ℕ) {prog : Program} {input : PublicInput}
    {t : Trace prog} {ρ : ℕ} (hwf : WellFormedBytecode prog) (ht : ValidExecution prog input t)
    (hfit : t.Fits) (hstack : StackFits prog input t) (hρ : validRate ρ) :
    Pr{let z ← runRandom (honestExecutionGame fuel prog input t ρ)}[z.1 = false] ≤
      (((264246250 + 6 * fuel : ℕ) : ℝ≥0∞) + 1) *
          (1 - (2 ^ queryGrindingBits : ℝ≥0∞)⁻¹) ^ min fuel (2 ^ 64) +
        ((264246250 + 6 * fuel : ℕ) : ℝ≥0∞) * ((264246250 + 6 * fuel : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  obtain ⟨w, hw, hsat, -⟩ := witnessGen_correct hwf ht hfit
  obtain ⟨s, hs⟩ := sizes_of_satisfiedBy hsat
  have hb : (witnessGen prog input t).bind Sizes.ofWitness = some s := by
    rw [hw, Option.bind_some, hs]
  have hμ : leanIsaμ prog s ≤ maxMu := by
    obtain ⟨s', hs', hμ⟩ := hstack
    exact Option.some.inj (hb.symm.trans hs') ▸ hμ
  have hgame : honestExecutionGame fuel prog input t ρ = honestGame fuel prog input w ρ := by
    unfold honestExecutionGame proveExecutionWith honestGame
    rw [hw]
  rw [hgame]
  exact honestGame_rom_rejects_le fuel hsat hs hμ hρ

/-- **Completeness from an execution in the random-oracle model at the default fuel `2^24`**: the
honest run of `proveExecution_rom_complete` is rejected with probability below `2^-154`. -/
theorem proveExecution_rom_complete_default {prog : Program} {input : PublicInput}
    {t : Trace prog} {ρ : ℕ} (hwf : WellFormedBytecode prog) (ht : ValidExecution prog input t)
    (hfit : t.Fits) (hstack : StackFits prog input t) (hρ : validRate ρ) :
    Pr{let z ← runRandom (honestExecutionGame (2 ^ 24) prog input t ρ)}[z.1 = false] ≤
      (2 ^ 154 : ℝ≥0∞)⁻¹ :=
  (proveExecution_rom_complete (2 ^ 24) hwf ht hfit hstack hρ).trans
    (rom_bound_default _ Prove.one_sub_pow_fuel_le)

/-- **The headline: completeness of the deployed prover from an execution.** For well-formed
bytecode and a valid execution `t` that fits the caps, the witness generator returns a witness
`w`, which satisfies the constraint statement and represents the padded trace
`padTrace t (fillStarts prog)`: a valid execution with the same steps as `t`, its memory doubled
with the fill frames above `t`'s image. At every fuel and rate, `verify` accepts every proof
`proveExecution` returns; it returns none only when, at the witness's sizes `s`, the stack
exceeds `2^maxMu`, the rate is not valid, or a grind runs out of fuel at a chain state the
prover's run reaches; the last conjunct says the same as a sufficient condition for a proof.
`Trace.Fits` does not keep the stack within `2^maxMu`: from `t.κ ≥ 26` on it is not. -/
theorem proveExecution_complete {prog : Program} {input : PublicInput} {t : Trace prog}
    (hwf : WellFormedBytecode prog) (ht : ValidExecution prog input t) (hfit : t.Fits) :
    (padTrace t (fillStarts prog)).PaddedFrom t ∧
    ValidExecution prog input (padTrace t (fillStarts prog)) ∧
    ∃ w, witnessGen prog input t = some w ∧ SatisfiedBy prog input w ∧
      AssignmentRepresents w (padTrace t (fillStarts prog)) ∧
      ∃ s, Sizes.ofWitness w = some s ∧ ∀ fuel ρ,
        (∀ proof, proveExecution fuel prog input t ρ = some proof →
          verify prog input proof = true) ∧
        (proveExecution fuel prog input t ρ = none → maxMu < leanIsaμ prog s ∨ ¬ validRate ρ ∨
          ∃ fs, ProveReaches fuel prog input w ρ fs ∧
            Id.run (fs.grind blake2sBytes fuel queryGrindingBits) = none) ∧
        (leanIsaμ prog s ≤ maxMu → validRate ρ →
          (∀ fs, ProveReaches fuel prog input w ρ fs →
            Id.run (fs.grind blake2sBytes fuel queryGrindingBits) ≠ none) →
          proveExecution fuel prog input t ρ ≠ none) := by
  obtain ⟨w, hw, hsat, hrep⟩ := witnessGen_correct hwf ht hfit
  obtain ⟨s, hs⟩ := sizes_of_satisfiedBy hsat
  have hp : ∀ fuel ρ, proveExecution fuel prog input t ρ = prove fuel prog input w ρ :=
    fun _ _ ↦ by simp only [proveExecution, proveExecutionWith, hw]; rfl
  refine ⟨padTrace_from t _, (padTrace_from t _).valid hfit.room ht, w, hw, hsat, hrep, s, hs,
    fun fuel ρ ↦ ?_⟩
  rw [hp]
  refine ⟨fun _ ↦ prove_complete fuel hsat, fun h ↦ ?_, prove_ne_none fuel hsat hs⟩
  obtain ⟨s', hs', hc⟩ := prove_eq_none fuel hsat h
  exact Option.some.inj (hs.symm.trans hs') ▸ hc

end

end LeanerVM.Protocol
