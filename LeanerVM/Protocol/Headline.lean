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

/-!
# The headline theorems

An adversary (`Adversary`) is a cheating prover: a computation with no coins whose only access to
BLAKE2s-256 is the hash oracle, and which outputs a proof. The game (`loggedGame`) runs it with
its queries logged, then leanVM's verifier on its proof with the verifier's queries logged, for a
program `prog` and a public input `input` fixed before the adversary runs: every bound here is
selective. The extractor is straight-line and computable: `extract` reads the announced sizes off
the proof and the committed stack off the adversary's queries, `witnessOf` reads leanISA's witness
off the stack, and `extractTrace` reads an execution off the witness.

* `baseVerifier_extractsWitness_rom`: with the hash a uniformly random function and an adversary
  of at most `Q` queries, the verifier accepts while the extracted witness fails leanISA's
  constraint statement (`SatisfiedBy`) with probability at most
  `(Q + 13697)/2^128 + hashTerm 13697 Q`.
* `BlakeMisbehaves prog input A δ`: with BLAKE2s answering, the adversary's run shows a collision,
  a hit or a flip with probability at most `δ`.
* `baseVerifier_extractsWitness`: the deployed `verify` accepts while the extracted witness fails
  the constraint statement with probability at most `δ`, under `BlakeMisbehaves prog input A δ`.
* `baseVerifier_extractsExecution`: the same for a valid execution, read off the witness by
  leanISA's trace extraction, for a program whose sentinel slot is not a `JUMP`.
* `Blake2sActsAsRandomOracle`, `blakeMisbehaves_of_comparison`: if misbehaving is at most `δ`
  likelier under BLAKE2s than under a random function, `BlakeMisbehaves` holds at the
  random-oracle bound plus `δ`.

**The proofs.** A run under BLAKE2s, or under the lazy random oracle, is a possible run of the game
whose joint log is consistent (`mem_support_runBlake2s`, `mem_support_runRandom`); under BLAKE2s its
verdict is `verify`'s (`verifyWith_simulateQ`). On such a run, an accepted proof whose extraction
fails puts the run inside `HashMisbehaves` (`Core.core_of_mem_support`), and
`satisfiedBy_witnessOf` turns the extracted stack's `M3Holds` into `SatisfiedBy` at the admissible
sizes `extract` returns. The random-oracle bound is `leanVm_misbehaves_rom_closed`.

**What they do not say.** An adversary with no coins has one run under BLAKE2s, so
`BlakeMisbehaves` at `δ < 1` says that this run does not misbehave; for an adversary with coins, a
distribution over coin-free ones, `δ` is the probability over its coins. The hypothesis is about
one adversary and is false for some: the replayer of a stored accepted proof fails it at every
`δ < 1`, and so does an adversary that hashes in its own code. The completeness direction is
`baseProver_complete`, from a satisfying witness; none is stated from an execution, since leanISA
proves no trace-level constraint completeness.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization Blake2sHash LeanIsa
open OracleComp OracleSpec Verify ProofRoots LeanVmReader
open scoped NNReal ENNReal

@[expose] public section

/-! ## The hypotheses -/

/-- **BLAKE2s misbehaves on this adversary's run with probability at most `δ`.** Run the
adversary `A` with BLAKE2s-256 answering its hash queries, then leanVM's verifier on its proof, for
the program `prog` and the public input `input`; the joint log of the two runs' queries shows one
of:
- a *collision*: two different inputs with one digest (collision resistance);
- a *hit*: a query answered, at its input's first occurrence, by a digest already in play: the
  chain's first state (a digest of the statement), a 32-byte half of an earlier 64-byte input (the
  state or block of a chain step, a child of a Merkle node), or a digest a chain absorbed as two
  scalars (a Merkle root); for the verifier's queries, also a Merkle root the proof carries
  (unpredictability: no digest is known before it is computed);
- a *flip*: a Fiat–Shamir challenge, read off a chain of the log by leanVM's reader as a challenge
  of the deployed compiled protocol, that lies in the bad set of the transcript before it: the
  challenges that turn the protocol's state function from false to true, which have density at
  most `2^-128`, the query positions counted with their grinding (correlation intractability of
  the chain against a sparse relation).

The protocol, its bad sets and the reader are those of leanVM, fixed inside this definition. With
no coins the run is one value, and the probability is `0` or `1`. -/
def BlakeMisbehaves (prog : Program) (input : PublicInput) (A : Adversary) (δ : ℝ≥0∞) : Prop :=
  Pr{let g ← runBlake2s (loggedGame verifyWith prog input A)}[
    HashMisbehaves (rootsOf prog input) (leanVmReader prog input).Flip prog input g] ≤ δ

/-- **BLAKE2s acts as a random oracle** for the computation `G` and the event `bad`, up to `δ`:
`bad` is at most `δ` likelier with BLAKE2s-256 answering every query than with a uniformly random
function answering (the lazy random oracle). -/
def Blake2sActsAsRandomOracle {α : Type} (G : OracleComp hashSpec α) (bad : α → Prop)
    (δ : ℝ≥0∞) : Prop :=
  Pr{let x ← runBlake2s G}[bad x] ≤ Pr{let z ← runRandom G}[bad z.1] + δ

/-! ## The extraction -/

/-- **The extracted execution**: the stack `extract` reads off the log, the witness `witnessOf`
reads off the stack, and the trace a trace extraction `X` reads off the witness. Computable when
`X.traceOf` is. -/
def extractTrace {prog : Program} (X : TraceExtraction prog) (input : PublicInput)
    (proof : Proof PrunedMerklePaths) (log : hashSpec.QueryLog) : Option (Trace prog) :=
  (extract Blake2sFlock.blake2sFlockSpec prog input proof log).bind fun e ↦
    X.traceOf input (witnessOf Blake2sFlock.blake2sFlockSpec prog e.1 e.2)

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

/-- On a possible run with a consistent joint log whose verdict accepts, no satisfying witness
through the adaptor means the hash misbehaves. -/
private theorem misbehaves_of_escape {prog : Program} {input : PublicInput} {A : Adversary}
    {g : Run} (hg : g ∈ support (loggedGame verifyWith prog input A) ∧ QueryLog.Consistent g.log)
    (hok : g.ok = true)
    (hX : ¬ ∃ e, extract Blake2sFlock.blake2sFlockSpec prog input g.proof g.logA = some e ∧
      SatisfiedBy prog input (witnessOf Blake2sFlock.blake2sFlockSpec prog e.1 e.2)) :
    HashMisbehaves (rootsOf prog input) (leanVmReader prog input).Flip prog input g :=
  Core.core_of_mem_support hg.1 hg.2 hok fun ⟨s, q, he, hm⟩ ↦
    hX ⟨⟨s, q⟩, he, satisfiedBy_witnessOf _ prog s q (admissible_of_extract he) hm⟩

/-! ## The theorems -/

/-- **Knowledge soundness in the random-oracle model.** With the hash a uniformly random function
and an adversary `A` of at most `Q` queries, the game's verifier accepts `A`'s proof while the
witness read off the stack the extractor reads off `A`'s queries does not satisfy leanISA's
constraint statement with probability at most `(Q + 13697)/2^128` (the challenges) plus
`hashTerm 13697 Q` (collisions and hits). Selective: the program and the public input are fixed
before `A` runs. -/
theorem baseVerifier_extractsWitness_rom {prog : Program} {input : PublicInput} {A : Adversary}
    {Q : ℕ} (hQ : IsTotalQueryBound A Q) :
    Pr{let z ← runRandom (loggedGame verifyWith prog input A)}[
      z.1.ok = true ∧ ¬ ∃ e,
        extract Blake2sFlock.blake2sFlockSpec prog input z.1.proof z.1.logA = some e ∧
          SatisfiedBy prog input (witnessOf Blake2sFlock.blake2sFlockSpec prog e.1 e.2)] ≤
      ((Q + 13697 : ℕ) / 2 ^ 128 + hashTerm 13697 Q : ℝ≥0) :=
  (OracleComp.prEvent_mono_of_support _ fun _ hz h ↦
    misbehaves_of_escape (mem_support_runRandom hz) h.1 h.2).trans
    (leanVm_misbehaves_rom_closed prog input A hQ)

/-- **The headline: knowledge soundness of the deployed verifier.** With BLAKE2s-256 answering the
hash, `verify` accepts the adversary's proof while the witness read off the stack the extractor
reads off its queries does not satisfy leanISA's constraint statement with probability at most
`δ`, if BLAKE2s misbehaves on its run with probability at most `δ`. Selective: the program and
the public input are fixed before the adversary runs. -/
theorem baseVerifier_extractsWitness {prog : Program} {input : PublicInput} {A : Adversary}
    {δ : ℝ≥0∞} (hB : BlakeMisbehaves prog input A δ) :
    Pr{let g ← runBlake2s (loggedGame verifyWith prog input A)}[
      verify prog input g.proof = true ∧ ¬ ∃ e,
        extract Blake2sFlock.blake2sFlockSpec prog input g.proof g.logA = some e ∧
          SatisfiedBy prog input (witnessOf Blake2sFlock.blake2sFlockSpec prog e.1 e.2)] ≤ δ :=
  (OracleComp.prEvent_mono_of_support _ fun _ hg h ↦
    have ⟨hg', hc, hok⟩ := mem_support_runBlake2s hg
    misbehaves_of_escape ⟨hg', hc⟩ (hok.trans h.1) h.2).trans hB

/-- **Knowledge soundness of the deployed verifier, for an execution.** For a program whose
sentinel slot is not a `JUMP`, with BLAKE2s-256 answering the hash, `verify` accepts the
adversary's proof while the trace the extractor reads off its queries (through leanISA's trace
extraction) is no valid execution of the program on the input with probability at most `δ`, if
BLAKE2s misbehaves on its run with probability at most `δ`. Selective: the program and the public
input are fixed before the adversary runs. -/
theorem baseVerifier_extractsExecution {prog : Program} {input : PublicInput} {A : Adversary}
    {δ : ℝ≥0∞} (hsafe : SentinelSafe prog) (hB : BlakeMisbehaves prog input A δ) :
    Pr{let g ← runBlake2s (loggedGame verifyWith prog input A)}[
      verify prog input g.proof = true ∧ ¬ ∃ t,
        extractTrace (leanIsaTraceExtraction hsafe) input g.proof g.logA = some t ∧
          ValidExecution prog input t] ≤ δ := by
  refine (OracleComp.prEvent_mono_of_support _ fun _ _ h ↦
    ⟨h.1, fun ⟨e, he, hsat⟩ ↦ h.2 ?_⟩).trans (baseVerifier_extractsWitness hB)
  obtain ⟨t, ht, -, hvalid⟩ := (leanIsaTraceExtraction hsafe).valid input _ hsat
  exact ⟨t, by rw [extractTrace, he, Option.bind_some, ht], hvalid⟩

/-- **The hypothesis from the comparison form.** If misbehaving on the run of an adversary of at
most `Q` queries is at most `δ` likelier with BLAKE2s-256 answering than with a uniformly random
function, BLAKE2s misbehaves on it with probability at most the random-oracle bound
`(Q + 13697)/2^128 + hashTerm 13697 Q` plus `δ`. Selective: the program and the public input are
fixed before the adversary runs. -/
theorem blakeMisbehaves_of_comparison {prog : Program} {input : PublicInput} {A : Adversary}
    {Q : ℕ} {δ : ℝ≥0∞} (hQ : IsTotalQueryBound A Q)
    (h : Blake2sActsAsRandomOracle (loggedGame verifyWith prog input A)
      (HashMisbehaves (rootsOf prog input) (leanVmReader prog input).Flip prog input) δ) :
    BlakeMisbehaves prog input A (((Q + 13697 : ℕ) / 2 ^ 128 + hashTerm 13697 Q : ℝ≥0) + δ) :=
  h.trans (add_le_add_left (leanVm_misbehaves_rom_closed prog input A hQ) δ)

end

end LeanerVM.Protocol
