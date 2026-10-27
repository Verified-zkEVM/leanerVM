/-
  LeanerVM.Protocol.Prove

  leanVM's honest non-interactive prover: the compiled protocol's honest prover run against the
  Fiat–Shamir chain, its messages written to the proof, its challenges squeezed from what it has
  written, the grinding searched, the committed words opened at the queried positions; generic
  in how the hash is answered, deployed at BLAKE2s-256, and as an adversary of the random-oracle
  game.
-/

module

public import LeanerVM.Protocol.Prove.Compiled
public import LeanerVM.Protocol.Prove.Wire
public import LeanerVM.Protocol.ListBindingDeployed
public import LeanerVM.Protocol.RandomOracleGame

/-!
# The honest prover

`proveWith H fuel F prog input w ρ` proves that the witness `w` satisfies leanISA's constraint
statement for the program and the public input, at the WHIR rate `ρ`, every hash answered by `H`
in a monad `m`:

1. the sizes are read off the witness (`Sizes.ofWitness`) and must pass the setup checks with the
   rate (`Sizes.Admissible`, `validRate`), else `none`; they fix the leanISA instance at the Flock
   specification `F`, its stack (`stackOf`) and WHIR's deployed chain (`leanIsaChain`);
2. from the statement's seed, its three hashes answered by `H` (`FsState.seedWith`), the sizes
   and the rate are announced (`proveFrom` starts from the state a computation `seed` gives, run
   once the sizes and the rate pass);
3. the compiled protocol's honest prover (`compiledProver`, the stateful prover that runs as the
   honest prover of `listBindingDef`, `compiledProver_run`) runs round by round against the wire
   of its schedule (`compiledCodec`): each message written to the stream as the verifier reads it,
   each challenge squeezed from the chain, each committed word's rows committed under a Merkle root
   sent as two scalars, the grinding searched by `Writer.grind` with `fuel` candidate nonces
   (`none` when it runs out);
4. every committed word is opened at its level's positions (`merkleOpen`), in level order.

`prove` is `proveWith (m := Id) blake2sBytes` at the deployed Flock specification
(`Blake2sFlock.blake2sFlockSpec`), the one `verify` reads. `honestAdversary` is the prover in
the random-oracle game: every hash a query, an empty proof when the grinding runs out of fuel.

**Differences from the Rust prover** (`crates/lean_vm/src/cpu/mod.rs:520-640`, `prove`, at leanVM
`a386121f84292f6fa663aaa3e570c15bc0240ea2`). The stream is the same function of the messages and
the challenges, which are the oracle protocol's honest prover's: the Rust builds its witness from
an execution and runs its own provers, so the two agree on a proof only where the witnesses and the
honest messages agree. The grinding nonce is the smallest that clears the bits, as the Rust's
parallel search returns, but within `fuel` candidates. The Rust interleaves the openings with the
stream and hands them to the proof as each level is opened; they are a separate list in level
order either way. Single-threaded.

**Fuel.** A grind of 17 bits tries `2^17` candidates on average. In the random-oracle model a
search of `fuel = 2^24` candidates fails with probability `(1 − 2^-17)^(2^24) ≈ e^-128` per level,
three or four levels a proof. At BLAKE2s, a fixed function, an input on which no nonce below the
fuel clears the bits cannot be excluded; `prove` then returns `none`, never a proof the verifier
rejects. The Rust's search is unbounded over `u64` (`fiat_shamir/src/lib.rs:126-156`), so the
two nonces agree whenever the Rust's is below the fuel.

**Target.** Layer 13's honest prover: the executable artefact of T4's completeness direction.
Its theorem `baseProver_complete` (`LeanerVM.Protocol.Compile.Agree`) is
`baseProver_complete_of_agree` (`LeanerVM.Protocol.Prove.Complete`) with the agreement of the
executable verifier's phases with the oracle verifiers' (`Compile.phasesAgree`).
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization Blake2sHash LeanIsa Whir
open OracleComp OracleSpec
open Air.Flat (EnsembleWitness)

@[expose] public section

namespace Prove

/-- What the prover keeps beside the proof it writes: the commitments, in order, and each level's
query positions, in order. -/
structure Book where
  /-- The committed trees. -/
  commits : Array (Σ k, MerkleCommitment k)
  /-- Each level's positions. -/
  positions : Array (List ℕ)

/-- The prover's monad: the book and the transcript writer. -/
abbrev ProveM (m : Type → Type) : Type → Type := StateT Book (WriteM m PrunedMerklePaths)

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)

/-- The writer's primitives on the proof under construction, every hash answered by `H`: a scalar
sent and observed, a challenge squeezed, WHIR's query bits ground with `fuel` candidate nonces,
rows committed by `merkleCommitWithM` and the root sent, and a level's positions recorded. -/
def proveOps (fuel : ℕ) : WireOps (ProveM m) where
  send x := StateT.lift (Writer.addScalar H x)
  sample := StateT.lift (Writer.sample H)
  grind := StateT.lift (Writer.grind H fuel queryGrindingBits)
  commit depth leafWords rows := do
    let c ← (merkleCommitWithM H leafWords rows : m (MerkleCommitment depth))
    modify fun b ↦ { b with commits := b.commits.push ⟨depth, c⟩ }
    StateT.lift (Writer.addRoot H c.root)
  record ps := modify fun b ↦ { b with positions := b.positions.push ps }

/-- Every committed word opened at its level's positions, in level order. -/
def hintOpenings : ProveM m Unit := do
  let b ← get
  if b.commits.size ≠ b.positions.size then failure
  for (c, ps) in b.commits.toList.zip b.positions.toList do
    StateT.lift (Writer.hintOpening (merkleOpen c.2 ps))

/-- The proof's writer at admissible sizes, over the primitives `ops`: the announcement, the
compiled protocol's honest prover against the wire, every opening. -/
def writeProof (ops : WireOps (ProveM m)) (F : FlockSpec) (prog : Program) (s : Sizes)
    (hs : s.Admissible prog) (ρ : ℕ) (hρ : validRate ρ) (input : PublicInput)
    (q : Column (leanIsaμ prog s)) : ProveM m Unit := do
  StateT.lift (Writer.announce H s ρ)
  let _ ← Prover.runWith
    (compiledCodec ops (leanIsaInstance F prog s) (Verify.nLanes prog s)
      (leanIsaChain prog s hs ρ hρ).ladder)
    (compiledProver (leanIsaInstance F prog s) (leanIsa_conditions F prog s)
      (leanIsaChain_height F prog s hs ρ hρ) (leanIsaChain prog s hs ρ hρ).ladder
      ((leanIsaChain prog s hs ρ hρ).ladder.headPar (leanIsaChain prog s hs ρ hρ).pars).hb)
    (input, fun i ↦ i.elim0) q
  hintOpenings

/-- The proof of a writer run from the state `seed` computes, with an empty book; `none` when a
grind runs out of fuel. -/
def runProofFrom (seed : m FsState) (wr : ProveM m Unit) :
    m (Option (Proof PrunedMerklePaths)) := do
  let fs ← seed
  let r ← runWrite (wr.run' ⟨#[], #[]⟩) fs
  return r.map (·.2.proof)

/-- The proof of a writer run from the statement's seed with an empty book; `none` when a grind
runs out of fuel. -/
def runProof (prog : Program) (input : PublicInput) (wr : ProveM m Unit) :
    m (Option (Proof PrunedMerklePaths)) :=
  runProofFrom (pure (FsState.seed prog input)) wr

end Prove

open Prove

/-- **leanVM's honest prover from a computed start**, generic in how the hash `H` is answered and
in how the chain's first state is computed (`seed`): the sizes read off the witness and checked
with the rate, then, from `seed`'s state, the announcement, the compiled protocol's honest prover
run against the chain with `fuel` candidate nonces per grind, and the openings. `none` at
inadmissible sizes, when a grind runs out of fuel, or when the commitments and the positions
recorded differ in number (`hintOpenings`), which cannot happen: each level commits one word and
draws its positions once (`Prove.proveFrom_eq_none`). -/
def proveFrom {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (seed : m FsState)
    (fuel : ℕ) (F : FlockSpec) (prog : Program) (input : PublicInput)
    (w : EnsembleWitness (leanIsaEnsemble prog)) (ρ : ℕ) : m (Option (Proof PrunedMerklePaths)) :=
  match Sizes.ofWitness w with
  | none => pure none
  | some s =>
    if hs : s.Admissible prog ∧ validRate ρ then
      runProofFrom seed
        (writeProof H (proveOps H fuel) F prog s hs.1 ρ hs.2 input (stackOf F prog s w))
    else pure none

/-- **leanVM's honest prover**, generic in how the hash `H` is answered: `proveFrom` from the
statement's seed, its three hashes answered by `H`. -/
def proveWith {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (fuel : ℕ) (F : FlockSpec)
    (prog : Program) (input : PublicInput) (w : EnsembleWitness (leanIsaEnsemble prog)) (ρ : ℕ) :
    m (Option (Proof PrunedMerklePaths)) :=
  proveFrom H (FsState.seedWith H prog input) fuel F prog input w ρ

/-- **leanVM's honest prover** at the deployed hash, BLAKE2s-256, and the deployed Flock
specification, the one `verify` reads. -/
def prove (fuel : ℕ) (prog : Program) (input : PublicInput)
    (w : EnsembleWitness (leanIsaEnsemble prog)) (ρ : ℕ) : Option (Proof PrunedMerklePaths) :=
  proveWith (m := Id) blake2sBytes fuel Blake2sFlock.blake2sFlockSpec prog input w ρ

/-- **The honest prover as an adversary** of the random-oracle game: every hash a query; out of
fuel, the empty proof, which `verify` rejects. -/
def honestAdversary (fuel : ℕ) (prog : Program) (input : PublicInput)
    (w : EnsembleWitness (leanIsaEnsemble prog)) (ρ : ℕ) : Adversary := do
  match ← proveWith hashQuery fuel Blake2sFlock.blake2sFlockSpec prog input w ρ with
  | some proof => pure proof
  | none => pure ⟨[], []⟩

end
end LeanerVM.Protocol
