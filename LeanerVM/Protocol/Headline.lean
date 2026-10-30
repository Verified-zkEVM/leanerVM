/-
  LeanerVM.Protocol.Headline

  leanVM's deployed prover and verifier against leanISA: an accepted proof, except with small
  probability, yields through the straight-line extractor a valid execution of the program on the
  public input, in the random-oracle model with no hypothesis and at BLAKE2s under one named
  hypothesis on the adversary's run; and a valid execution that fits the caps has a witness on
  which every proof the deployed prover returns is accepted.
-/

module

public import LeanerVM.Protocol.Core
public import LeanerVM.Protocol.LeanIsa.Sound
public import LeanerVM.Protocol.LeanIsa.Complete
public import LeanerVM.Arithmetization.Soundness
public import LeanerVM.Arithmetization.Completeness.Theorem
public import LeanerVM.Protocol.Compile.Agree
public import LeanerVM.Protocol.AdaptiveGame
public import LeanerVM.Semantics.FillBlocks

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
  `baseVerifier_extractsExecution_rom_adaptive_wellFormed`, and at a fixed statement
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

`prove_complete_of_execution`: for `WellFormedBytecode`, a valid execution that fits the caps
(`Trace.Fits`) has a padding with the same steps (`Trace.PaddedFrom`) and a witness of the
constraint statement representing the padding, with sizes `s`, on which, at every fuel and rate,
`verify` accepts every proof the deployed `prove` returns, and `prove` returns a proof unless the
stack exceeds `2^maxMu`, the rate is not valid, or a grind finds no nonce among its `fuel`
candidates at a chain state the prover's run reaches (`ProveReaches`: the state after the
announcement and some first rounds of the run). The witness exists; it is not computed, since
leanISA's padded witness reads the memory image through `MemImage.read`, a classical discrete
logarithm, and takes the fill blocks from the proposition `HasFillBlocks`.

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
  `13700 = 3 + 13697` queries. The event the theorems use, its flips restricted to the chosen
  statement's chain (`leanVmReader.FlipFor`), is smaller, so the bound holds for it.
* `BlakeMisbehavesAdaptive A δ`: with BLAKE2s answering, the adversary's run shows a collision or a
  hit on the whole joint log, or a flip on the chain of the statement it chose, with probability at
  most `δ`; `BlakeMisbehaves prog input A δ` is it at a fixed statement
  (`blakeMisbehavesAdaptive_const`). `blakeMisbehavesAdaptive_of_comparison`,
  `blakeMisbehaves_of_comparison`: if misbehaving is at most `δ` likelier under BLAKE2s than under
  a random function (`Blake2sActsAsRandomOracle`), the hypothesis holds at the random-oracle bound
  plus `δ`.

**The proofs.** A run under BLAKE2s, or under the lazy random oracle, is a possible run of the game
whose joint log is consistent (`mem_support_runBlake2s_adaptive`, `mem_support_runRandom_adaptive`);
under BLAKE2s its verdict is `verify`'s (`verifyWith_simulateQ`). A possible run of the adaptive
game is one of the game at the statement the prover chose (`mem_support_loggedGame_of_adaptive`).
On such a run, an accepted proof whose extraction fails puts the run inside `HashMisbehavesFrom`,
its flip on the chain of the statement (`Core.core_of_mem_support`), and `satisfiedBy_witnessOf`
turns the extracted stack's `M3Holds` into `SatisfiedBy` at the admissible sizes `extract`
returns; `TraceExtraction.valid` (leanISA's constraint soundness) turns that into a valid
execution. The random-oracle bound is `misbehaves_rom_of` on the adaptive game in two runs
(`adaptiveGame_eq_twoRunGame`), for flips on every statement's chain, which include those on the
chosen one (`SlotReader.flip_of_flipFor`). Completeness from an execution is leanISA's
`constraintCompleteness` followed by `prove_complete`, `prove_eq_none` and `prove_ne_none`.

**What they do not say.** An adversary with no coins has one run under BLAKE2s, so
`BlakeMisbehavesAdaptive` at `δ < 1` says that this run does not misbehave; an adversary with
coins gets the bound with `δ` the probability over its coins. The hypothesis is about one adversary
and is false for some: the replayer of a stored accepted proof fails it at every `δ < 1`, and so
does an adversary that hashes in its own code. No theorem shows it met by an adversary whose proof
is accepted. Completeness says that every proof `prove` returns is accepted, and when it returns
one, not that it does: nothing bounds how often a grind on the run runs out of fuel, and
`Trace.Fits` does not keep the stack within `2^maxMu`. The padding the proof picks has memory
log-size `t.κ + 1`, so its four memory columns alone hold `2^(t.κ+3)` cells, above `2^28` from
`t.κ ≥ 26` on, where `prove` returns none at every fuel and rate; so it does whenever the filled
tables exceed `2^28` cells. The completeness witness represents the padded trace, not the given
one, and its proof is about that witness, not about a prover that takes the trace.
-/

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
  (correlation intractability of the chain against a sparse relation). Chains of the log from the
  seeds of other statements are not read.

The protocol, its bad sets and the reader are those of leanVM, fixed inside this definition. With
no coins the run is one value, and the probability is `0` or `1`. -/
def BlakeMisbehavesAdaptive (A : AdaptiveAdversary) (δ : ℝ≥0∞) : Prop :=
  Pr{let g ← runBlake2s (adaptiveGame verifyWith A)}[
    HashMisbehavesFrom [] (rootsOf g.prog g.input) (leanVmReader.FlipFor (g.prog, g.input))
      g.toRun] ≤ δ

/-- **BLAKE2s misbehaves on this adversary's run with probability at most `δ`**, for the program
`prog` and the public input `input` fixed before the adversary runs: `BlakeMisbehavesAdaptive` at
the adversary that outputs them with its proof (`blakeMisbehavesAdaptive_const`), its flips those
on the chain of `(prog, input)`. -/
def BlakeMisbehaves (prog : Program) (input : PublicInput) (A : Adversary) (δ : ℝ≥0∞) : Prop :=
  Pr{let g ← runBlake2s (loggedGame verifyWith prog input A)}[
    HashMisbehavesFrom [] (rootsOf prog input) (leanVmReader.FlipFor (prog, input)) g] ≤ δ

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
through the adaptor means the hash misbehaves, a flip being one on the statement's chain. -/
private theorem misbehaves_of_escape {prog : Program} {input : PublicInput} {A : Adversary}
    {g : Run} (hg : g ∈ support (loggedGame verifyWith prog input A) ∧ QueryLog.Consistent g.log)
    (hok : g.ok = true)
    (hX : ¬ ∃ e, extract Blake2sFlock.blake2sFlockSpec prog input g.proof g.logA = some e ∧
      SatisfiedBy prog input (witnessOf Blake2sFlock.blake2sFlockSpec prog e.1 e.2)) :
    HashMisbehavesFrom [] (rootsOf prog input) (leanVmReader.FlipFor (prog, input)) g :=
  Core.core_of_mem_support hg.1 hg.2 hok fun ⟨s, q, he, hm⟩ ↦
    hX ⟨⟨s, q⟩, he, satisfiedBy_witnessOf _ prog s q (admissible_of_extract he) hm⟩

/-- On a possible run of the adaptive game with a consistent joint log whose verdict accepts, no
satisfying witness at the chosen statement means the hash misbehaves, a flip being one on that
statement's chain. -/
private theorem misbehaves_of_escape_run {A : AdaptiveAdversary} {g : AdaptiveRun}
    (hg : g ∈ support (adaptiveGame verifyWith A)) (hc : QueryLog.Consistent g.log)
    (hok : g.ok = true)
    (hX : ¬ ∃ e, extract Blake2sFlock.blake2sFlockSpec g.prog g.input g.proof g.logA = some e ∧
      SatisfiedBy g.prog g.input (witnessOf Blake2sFlock.blake2sFlockSpec g.prog e.1 e.2)) :
    HashMisbehavesFrom [] (rootsOf g.prog g.input) (leanVmReader.FlipFor (g.prog, g.input))
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
      fun _ ↦ leanVmReader.flip_of_flipFor).trans
    ((misbehaves_rom_adaptive hQ).trans (niError_closed Q))

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

/-- **The hypothesis from the comparison form.** If misbehaving on the run of an adaptive adversary
of at most `Q` queries, its flips on the chain of the statement it chose, is at most `δ` likelier
with BLAKE2s-256 answering than with a uniformly random function, BLAKE2s misbehaves on it with
probability at most the random-oracle bound `(Q + 13700)/2^128 + hashTerm 13700 Q` plus `δ`. -/
theorem blakeMisbehavesAdaptive_of_comparison {A : AdaptiveAdversary} {Q : ℕ} {δ : ℝ≥0∞}
    (hQ : IsTotalQueryBound A Q)
    (h : Blake2sActsAsRandomOracle (adaptiveGame verifyWith A)
      (fun g ↦ HashMisbehavesFrom [] (rootsOf g.prog g.input)
        (leanVmReader.FlipFor (g.prog, g.input)) g.toRun) δ) :
    BlakeMisbehavesAdaptive A (((Q + 13700 : ℕ) / 2 ^ 128 + hashTerm 13700 Q : ℝ≥0) + δ) := by
  have hR : Pr{let z ← runRandom (adaptiveGame verifyWith A)}[
      HashMisbehavesFrom [] (rootsOf z.1.prog z.1.input)
        (leanVmReader.FlipFor (z.1.prog, z.1.input)) z.1.toRun] ≤
      ((Q + 13700 : ℕ) / 2 ^ 128 + hashTerm 13700 Q : ℝ≥0) :=
    (OracleComp.prEvent_mono_of_support _ fun _ _ h ↦
      h.mono fun _ ↦ leanVmReader.flip_of_flipFor).trans
      ((misbehaves_rom_adaptive hQ).trans (niError_closed Q))
  exact h.trans (add_le_add_left hR δ)

/-! ## Knowledge soundness of the deployed verifier -/

/-- On a run of the adaptive game under BLAKE2s whose proof `verify` accepts, no satisfying
witness through the adaptor means the hash misbehaves, a flip being one on the chosen statement's
chain. -/
private theorem misbehaves_of_escape_adaptive {A : AdaptiveAdversary} {g : AdaptiveRun}
    (hg : g ∈ support (runBlake2s (adaptiveGame verifyWith A)))
    (hok : verify g.prog g.input g.proof = true)
    (hX : ¬ ∃ e, extract Blake2sFlock.blake2sFlockSpec g.prog g.input g.proof g.logA = some e ∧
      SatisfiedBy g.prog g.input (witnessOf Blake2sFlock.blake2sFlockSpec g.prog e.1 e.2)) :
    HashMisbehavesFrom [] (rootsOf g.prog g.input) (leanVmReader.FlipFor (g.prog, g.input))
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
      HashMisbehavesFrom [] (rootsOf g.prog g.input) (leanVmReader.FlipFor (g.prog, g.input))
        g.toRun] ≤ δ) :
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
      HashMisbehavesFrom [] (rootsOf g.prog g.input) (leanVmReader.FlipFor (g.prog, g.input))
        g.toRun] ≤ δ) :
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
      HashMisbehavesFrom [] (rootsOf prog input) (leanVmReader.FlipFor (prog, input)) g] ≤ δ) :
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
      HashMisbehavesFrom [] (rootsOf prog input) (leanVmReader.FlipFor (prog, input)) g] ≤ δ) :
    Pr{let A ← coins; let g ← runBlake2s (loggedGame verifyWith prog input A)}[
      verify prog input g.proof = true ∧ ¬ ∃ t,
        extractExecution prog input g.proof g.logA = some t ∧ ValidExecution prog input t] ≤ δ := by
  have hw := baseVerifier_extractsWitness_coins hB
  rw [← bind_assoc] at hw ⊢
  exact (OracleComp.prEvent_mono_of_support _ fun _ _ h ↦ ⟨h.1, noWitness hsafe h.2⟩).trans hw

/-- **The hypothesis from the comparison form** at a statement fixed before the adversary runs. If
misbehaving on the run of an adversary of at most `Q` queries, its flips on the chain of
`(prog, input)`, is at most `δ` likelier with BLAKE2s-256 answering than with a uniformly random
function, BLAKE2s misbehaves on it with probability at most the random-oracle bound
`(Q + 13700)/2^128 + hashTerm 13700 Q` plus `δ`. -/
theorem blakeMisbehaves_of_comparison {prog : Program} {input : PublicInput} {A : Adversary}
    {Q : ℕ} {δ : ℝ≥0∞} (hQ : IsTotalQueryBound A Q)
    (h : Blake2sActsAsRandomOracle (loggedGame verifyWith prog input A)
      (HashMisbehavesFrom [] (rootsOf prog input) (leanVmReader.FlipFor (prog, input))) δ) :
    BlakeMisbehaves prog input A (((Q + 13700 : ℕ) / 2 ^ 128 + hashTerm 13700 Q : ℝ≥0) + δ) :=
  h.trans (add_le_add_left ((OracleComp.prEvent_mono_of_support _ fun _ _ h ↦
    h.mono fun _ ↦ leanVmReader.flip_of_flipFor).trans
    (leanVm_misbehaves_rom_closed prog input A hQ)) δ)

/-! ## Completeness -/

/-- **Completeness of the deployed pair, the constraint form**, from which
`prove_complete_of_execution` is proved. For a witness that satisfies leanISA's constraint
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
the prover's run reaches (`ProveReaches`). Nothing bounds how often the last happens. -/
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
out of its `fuel` candidates at a chain state the prover's run reaches (`ProveReaches`). -/
theorem prove_ne_none (fuel : ℕ) {prog : Program} {input : PublicInput} {κ : ℕ}
    {w : EnsembleWitness (leanIsaEnsemble prog κ)} {ρ : ℕ} {s : Sizes}
    (hsat : SatisfiedBy prog input w) (hs : Sizes.ofWitness w = some s)
    (hμ : leanIsaμ prog s ≤ maxMu) (hρ : validRate ρ)
    (hg : ∀ fs, ProveReaches fuel prog input w ρ fs →
      Id.run (fs.grind blake2sBytes fuel queryGrindingBits) ≠ none) :
    prove fuel prog input w ρ ≠ none :=
  Prove.proveWith_ne_none blake2sBytes fuel _ hs ((admissible_iff_of_satisfiedBy hsat hs).mpr hμ)
    hρ hg

/-- **The headline: completeness of the deployed pair from an execution.** For well-formed
bytecode, a valid execution `t` that fits the caps has a padding `t'` with the same steps, itself a
valid execution, and a witness of the constraint statement representing `t'`, with sizes `s`, such
that at every fuel and rate `verify` accepts every proof `prove` returns on the witness, and
`prove` returns none only when the stack exceeds `2^maxMu`, the rate is not valid, or a grind
runs out of fuel at a chain state the prover's run reaches; the last conjunct says the same as a
sufficient condition for a proof. `Trace.Fits` does not keep the stack
within `2^maxMu`: from `t.κ ≥ 26` on it is not. The witness exists and is not computed:
leanISA's padded witness reads the image through the classical `MemImage.read` and takes the fill
blocks from `HasFillBlocks`. -/
theorem prove_complete_of_execution {prog : Program} {input : PublicInput} {t : Trace prog}
    (hwf : WellFormedBytecode prog) (ht : ValidExecution prog input t) (hfit : t.Fits) :
    ∃ t', t'.PaddedFrom t ∧ ValidExecution prog input t' ∧
      ∃ w : EnsembleWitness (leanIsaEnsemble prog t'.κ), SatisfiedBy prog input w ∧
        AssignmentRepresents w t' ∧ ∃ s, Sizes.ofWitness w = some s ∧ ∀ fuel ρ,
          (∀ proof, prove fuel prog input w ρ = some proof → verify prog input proof = true) ∧
          (prove fuel prog input w ρ = none → maxMu < leanIsaμ prog s ∨ ¬ validRate ρ ∨
            ∃ fs, ProveReaches fuel prog input w ρ fs ∧
              Id.run (fs.grind blake2sBytes fuel queryGrindingBits) = none) ∧
          (leanIsaμ prog s ≤ maxMu → validRate ρ →
            (∀ fs, ProveReaches fuel prog input w ρ fs →
              Id.run (fs.grind blake2sBytes fuel queryGrindingBits) ≠ none) →
            prove fuel prog input w ρ ≠ none) := by
  obtain ⟨t', hp, hv, w, hsat, hrep⟩ := constraintCompleteness hwf ht hfit
  obtain ⟨s, hs⟩ := sizes_of_satisfiedBy hsat
  refine ⟨t', hp, hv, w, hsat, hrep, s, hs, fun fuel _ ↦
    ⟨fun _ ↦ prove_complete fuel hsat, fun h ↦ ?_, prove_ne_none fuel hsat hs⟩⟩
  obtain ⟨s', hs', hc⟩ := prove_eq_none fuel hsat h
  exact Option.some.inj (hs.symm.trans hs') ▸ hc

end

end LeanerVM.Protocol
