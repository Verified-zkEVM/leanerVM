/-
  LeanerVM.Protocol.Headline

  The knowledge soundness of leanVM's deployed verifier: an accepted proof, except with small
  probability, yields through the straight-line extractor a witness of leanISA's constraint
  statement and a valid execution of the program; in the random-oracle model with no hypothesis,
  and at BLAKE2s under one named hypothesis on the adversary's run.
-/

module

public import LeanerVM.Protocol.Core
public import LeanerVM.Protocol.LeanIsa.Sound
public import LeanerVM.Arithmetization.Soundness
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
at a program whose sentinel slot is not a `JUMP`.

* `misbehaves_rom_adaptive`: with the hash a uniformly random function and an adaptive adversary of
  at most `Q` queries, the hash misbehaves on its run with probability at most
  `niError εquery 13700 Q`: a collision or a hit on the whole joint log, the proof's roots those at
  the statement it chose, or a flip on any statement's chain
  (`HashMisbehavesFrom [] (rootsOf prog input) leanVmReader.Flip`). No digest is in play at the
  start: the statement's seed is three queries of the hash, which the verifier asks
  (`FsState.seedWith`), and leanVM's reader reads the statement a chain starts from off the log
  (`leanVmReader`, `stmtOf`). So the bound counts the verifier's seed hashes,
  `13700 = 3 + 13697` queries. The event the headline theorems use, its flips restricted to the
  chosen statement's chain (`leanVmReader.FlipFor`), is smaller, so the bound holds for it.
* `baseVerifier_extractsWitness_rom_adaptive`: in the same model, the verifier accepts the chosen
  statement and proof while the extracted witness fails leanISA's constraint statement
  (`SatisfiedBy`) at it with probability at most `(Q + 13700)/2^128 + hashTerm 13700 Q`.
  `baseVerifier_extractsExecution_rom_adaptive`: the same for a valid execution, the event
  requiring that the chosen program's sentinel slot is not a `JUMP`;
  `baseVerifier_extractsExecution_rom_adaptive_wellFormed`: the same for an adversary whose
  programs are all `WellFormedBytecode`. The condition is needed by constraint soundness: some
  program with a sentinel `JUMP` has a witness of the constraint statement and no execution on any
  memory (the test `exists_satisfiedBy_without_execution`), and `verify` accepts every proof
  `prove` returns for it.
* `BlakeMisbehavesAdaptive A δ`: with BLAKE2s answering, the adversary's run shows a collision or a
  hit on the whole joint log, or a flip on the chain of the statement it chose, with probability at
  most `δ`.
  `blakeMisbehavesAdaptive_of_comparison`: if misbehaving is at most `δ` likelier under BLAKE2s
  than under a random function (`Blake2sActsAsRandomOracle`), `BlakeMisbehavesAdaptive` holds at
  the random-oracle bound plus `δ`.
* `baseVerifier_extractsWitness_adaptive`, `baseVerifier_extractsWitness_adaptive_coins`: the
  deployed `verify` accepts the chosen statement and proof while the extracted witness fails the
  constraint statement at it with probability at most `δ`, under `BlakeMisbehavesAdaptive A δ`;
  `baseVerifier_extractsExecution_adaptive` and `baseVerifier_extractsExecution_adaptive_wellFormed`
  for a valid execution.
* **At a fixed statement** the theorems are the adaptive ones at the adversary that outputs it,
  bound for bound: `baseVerifier_extractsWitness_rom`, `BlakeMisbehaves prog input A δ` (which is
  `BlakeMisbehavesAdaptive` there, `blakeMisbehavesAdaptive_const`), `baseVerifier_extractsWitness`,
  `baseVerifier_extractsWitness_coins`, `baseVerifier_extractsExecution`,
  `blakeMisbehaves_of_comparison`.
* `prove_complete`: for a witness of the constraint statement, `verify` accepts every proof the
  deployed prover `prove` returns.

**The proofs.** A run under BLAKE2s, or under the lazy random oracle, is a possible run of the game
whose joint log is consistent (`mem_support_runBlake2s_adaptive`, `mem_support_runRandom_adaptive`);
under BLAKE2s its verdict is `verify`'s (`verifyWith_simulateQ`). A possible run of the adaptive
game is one of the game at the statement the prover chose (`mem_support_loggedGame_of_adaptive`).
On such a run, an accepted proof whose extraction fails puts the run inside `HashMisbehavesFrom`,
its flip on the chain of the statement (`Core.core_of_mem_support`), and `satisfiedBy_witnessOf`
turns the extracted stack's `M3Holds` into `SatisfiedBy` at the admissible sizes `extract`
returns. The random-oracle bound is `misbehaves_rom_of` on the adaptive game in two runs
(`adaptiveGame_eq_twoRunGame`), for flips on every statement's chain, which include those on the
chosen one (`SlotReader.flip_of_flipFor`).

**What they do not say.** An adversary with no coins has one run under BLAKE2s, so
`BlakeMisbehavesAdaptive` at `δ < 1` says that this run does not misbehave; an adversary with
coins, a distribution over coin-free ones, gets the bound with `δ` the probability over its coins
(`baseVerifier_extractsWitness_adaptive_coins`). The hypothesis is about one adversary and is false
for some: the replayer of a stored accepted proof fails it at every `δ < 1`, and so does an
adversary that hashes in its own code. No theorem shows it met by an adversary whose proof is
accepted. The completeness direction is `prove_complete`, from a satisfying witness: every proof
`prove` returns is accepted, but nothing bounds how often its grinding runs out of fuel. None is
stated from an execution, since leanISA proves no trace-level constraint completeness.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization Blake2sHash LeanIsa
open OracleComp OracleSpec Verify ProofRoots LeanVmReader
open Air.Flat (EnsembleWitness)
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

/-- A satisfying extracted witness at a program whose sentinel slot is not a `JUMP` gives a valid
extracted execution. -/
private theorem execution_of_witness {prog : Program} {input : PublicInput}
    {proof : Proof PrunedMerklePaths} {log : hashSpec.QueryLog} (hsafe : SentinelSafe prog)
    {e : Σ s : Sizes, Column (leanIsaμ prog s)}
    (he : extract Blake2sFlock.blake2sFlockSpec prog input proof log = some e)
    (hsat : SatisfiedBy prog input (witnessOf Blake2sFlock.blake2sFlockSpec prog e.1 e.2)) :
    ∃ t, extractExecution prog input proof log = some t ∧ ValidExecution prog input t := by
  obtain ⟨t, ht, -, hvalid⟩ := (leanIsaTraceExtraction hsafe).valid _ _ _ hsat
  refine ⟨t, ?_, hvalid⟩
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

/-- **Adaptive knowledge soundness in the random-oracle model.** With the hash a uniformly random
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

/-- **Adaptive knowledge soundness in the random-oracle model, for an execution.** With the hash a
uniformly random function and an adaptive adversary `A` of at most `Q` queries, the game's verifier
accepts the statement and proof `A` outputs, the chosen program's sentinel slot is not a `JUMP`,
and the trace extracted from `A`'s queries is no valid execution of that program on that input,
with probability at most `(Q + 13700)/2^128 + hashTerm 13700 Q`. -/
theorem baseVerifier_extractsExecution_rom_adaptive {A : AdaptiveAdversary} {Q : ℕ}
    (hQ : IsTotalQueryBound A Q) :
    Pr{let z ← runRandom (adaptiveGame verifyWith A)}[z.1.ok = true ∧ SentinelSafe z.1.prog ∧
      ¬ ∃ t, extractExecution z.1.prog z.1.input z.1.proof z.1.logA = some t ∧
        ValidExecution z.1.prog z.1.input t] ≤
      ((Q + 13700 : ℕ) / 2 ^ 128 + hashTerm 13700 Q : ℝ≥0) :=
  (OracleComp.prEvent_mono_of_support _ fun _ _ h ↦
    ⟨h.1, fun ⟨_, he, hsat⟩ ↦ h.2.2 (execution_of_witness h.2.1 he hsat)⟩).trans
    (baseVerifier_extractsWitness_rom_adaptive hQ)

/-- **Adaptive knowledge soundness in the random-oracle model for well-formed programs**: the
execution form for an adversary whose programs, on its runs under the lazy random oracle, are all
`WellFormedBytecode`. -/
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

/-- **Adaptive knowledge soundness of the deployed verifier.** With BLAKE2s-256 answering the
hash, `verify` accepts the statement and proof the adversary outputs while the witness read off
the stack the extractor reads off its queries does not satisfy leanISA's constraint statement at
that statement with probability at most `δ`, if BLAKE2s misbehaves on its run with probability at
most `δ`. -/
theorem baseVerifier_extractsWitness_adaptive {A : AdaptiveAdversary} {δ : ℝ≥0∞}
    (hB : BlakeMisbehavesAdaptive A δ) :
    Pr{let g ← runBlake2s (adaptiveGame verifyWith A)}[
      verify g.prog g.input g.proof = true ∧ ¬ ∃ e,
        extract Blake2sFlock.blake2sFlockSpec g.prog g.input g.proof g.logA = some e ∧
          SatisfiedBy g.prog g.input (witnessOf Blake2sFlock.blake2sFlockSpec g.prog e.1 e.2)] ≤
      δ :=
  (OracleComp.prEvent_mono_of_support _ fun _ hg h ↦
    misbehaves_of_escape_adaptive hg h.1 h.2).trans hB

/-- **Adaptive knowledge soundness for an adversary with coins**, a distribution `coins` over
coin-free adaptive adversaries: the bound of `baseVerifier_extractsWitness_adaptive`, with `δ`
the probability over the coins that BLAKE2s misbehaves on the drawn adversary's run. -/
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

/-- **Adaptive knowledge soundness of the deployed verifier, for an execution.** With BLAKE2s-256
answering the hash, `verify` accepts the statement and proof the adversary outputs, the chosen
program's sentinel slot is not a `JUMP`, and the trace extracted from the adversary's queries is
no valid execution of that program on that input, with probability at most `δ`, if BLAKE2s
misbehaves on its run with probability at most `δ`. -/
theorem baseVerifier_extractsExecution_adaptive {A : AdaptiveAdversary} {δ : ℝ≥0∞}
    (hB : BlakeMisbehavesAdaptive A δ) :
    Pr{let g ← runBlake2s (adaptiveGame verifyWith A)}[
      verify g.prog g.input g.proof = true ∧ SentinelSafe g.prog ∧ ¬ ∃ t,
        extractExecution g.prog g.input g.proof g.logA = some t ∧
          ValidExecution g.prog g.input t] ≤ δ :=
  (OracleComp.prEvent_mono_of_support _ fun _ _ h ↦
    ⟨h.1, fun ⟨_, he, hsat⟩ ↦ h.2.2 (execution_of_witness h.2.1 he hsat)⟩).trans
    (baseVerifier_extractsWitness_adaptive hB)

/-- **Adaptive knowledge soundness for well-formed programs**: the execution form for an adversary
whose programs, on its runs under BLAKE2s, are all `WellFormedBytecode`. -/
theorem baseVerifier_extractsExecution_adaptive_wellFormed {A : AdaptiveAdversary} {δ : ℝ≥0∞}
    (hB : BlakeMisbehavesAdaptive A δ)
    (hwf : ∀ g ∈ support (runBlake2s (adaptiveGame verifyWith A)), WellFormedBytecode g.prog) :
    Pr{let g ← runBlake2s (adaptiveGame verifyWith A)}[
      verify g.prog g.input g.proof = true ∧ ¬ ∃ t,
        extractExecution g.prog g.input g.proof g.logA = some t ∧
          ValidExecution g.prog g.input t] ≤ δ :=
  (OracleComp.prEvent_mono_of_support _ fun g hg h ↦
    ⟨h.1, (hwf g hg).sentinelSafe, h.2⟩).trans (baseVerifier_extractsExecution_adaptive hB)

/-! ## At a statement fixed before the adversary runs -/

/-- **Knowledge soundness in the random-oracle model** at a statement fixed before the adversary
runs: `baseVerifier_extractsWitness_rom_adaptive` at the adversary that outputs it. With the hash a
uniformly random function and an adversary `A` of at most `Q` queries, the game's verifier accepts
`A`'s proof while the witness read off the stack the extractor reads off `A`'s queries does not
satisfy leanISA's constraint statement with probability at most `(Q + 13700)/2^128` (the
challenges) plus `hashTerm 13700 Q` (collisions and hits). -/
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

/-- **The headline: knowledge soundness of the deployed verifier** at a statement fixed before the
adversary runs: `baseVerifier_extractsWitness_adaptive` at the adversary that outputs it. With
BLAKE2s-256 answering the hash, `verify` accepts the adversary's proof while the witness read off
the stack the extractor reads off its queries does not satisfy leanISA's constraint statement with
probability at most `δ`, if BLAKE2s misbehaves on its run with probability at most `δ`. -/
theorem baseVerifier_extractsWitness {prog : Program} {input : PublicInput} {A : Adversary}
    {δ : ℝ≥0∞} (hB : BlakeMisbehaves prog input A δ) :
    Pr{let g ← runBlake2s (loggedGame verifyWith prog input A)}[
      verify prog input g.proof = true ∧ ¬ ∃ e,
        extract Blake2sFlock.blake2sFlockSpec prog input g.proof g.logA = some e ∧
          SatisfiedBy prog input (witnessOf Blake2sFlock.blake2sFlockSpec prog e.1 e.2)] ≤ δ := by
  have h := baseVerifier_extractsWitness_adaptive ((blakeMisbehavesAdaptive_const _ _ _ _).mpr hB)
  rwa [prEvent_runBlake2s_const] at h

/-- **The headline for an adversary with coins** at a statement fixed before the coins are drawn.
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

/-- **Knowledge soundness of the deployed verifier, for an execution**, at a statement fixed before
the adversary runs. For a program whose sentinel slot is not a `JUMP`, with BLAKE2s-256 answering
the hash, `verify` accepts the adversary's proof while the trace the extractor reads off its
queries (through leanISA's trace extraction) is no valid execution of the program on the input with
probability at most `δ`, if BLAKE2s misbehaves on its run with probability at most `δ`. -/
theorem baseVerifier_extractsExecution {prog : Program} {input : PublicInput} {A : Adversary}
    {δ : ℝ≥0∞} (hsafe : SentinelSafe prog) (hB : BlakeMisbehaves prog input A δ) :
    Pr{let g ← runBlake2s (loggedGame verifyWith prog input A)}[
      verify prog input g.proof = true ∧ ¬ ∃ t,
        extractTrace (leanIsaTraceExtraction hsafe) input g.proof g.logA = some t ∧
          ValidExecution prog input t] ≤ δ := by
  refine (OracleComp.prEvent_mono_of_support _ fun _ _ h ↦
    ⟨h.1, fun ⟨e, he, hsat⟩ ↦ h.2 ?_⟩).trans (baseVerifier_extractsWitness hB)
  obtain ⟨t, ht, -, hvalid⟩ := (leanIsaTraceExtraction hsafe).valid input _ _ hsat
  exact ⟨t, by rw [extractTrace, he, Option.bind_some, ht], hvalid⟩

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

/-- **Completeness of the deployed pair.** For a witness that satisfies leanISA's constraint
statement, `verify` accepts every proof `prove` returns: `Prove.baseProver_complete` at
BLAKE2s-256. `prove` returns no proof (`Prove.proveWith_eq_none`) only when the witness's memory
log-size is `0`, so that `Sizes.ofWitness` reads no sizes off it; when its sizes are not
admissible; when the rate `ρ` is not valid; or when a grind finds no nonce among its `fuel`
candidates at some chain state. Nothing bounds how often the last happens. -/
theorem prove_complete (fuel : ℕ) {prog : Program} {input : PublicInput} {κ : ℕ}
    {w : EnsembleWitness (leanIsaEnsemble prog κ)} {ρ : ℕ} {proof : Proof PrunedMerklePaths}
    (hsat : SatisfiedBy prog input w) (hp : prove fuel prog input w ρ = some proof) :
    verify prog input proof = true :=
  Prove.baseProver_complete blake2sBytes fuel hsat hp

end

end LeanerVM.Protocol
