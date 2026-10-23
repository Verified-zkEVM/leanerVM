/-
  LeanerVM.Protocol.Verify.Setup

  The executable verifier's setup: the announced sizes and rate checked before any hash, the
  instance and the stack shape they fix, the commitment root, and the reading primitives of the
  chain walk.
-/

module

public import LeanerVM.Protocol.Proof
public import LeanerVM.Protocol.Merkle
public import LeanerVM.Protocol.FlockSpec
public import LeanerVM.Parameters.Whir

/-!
# The verifier's setup and the chain walk's primitives

The executable verifier `verifyWith` (`LeanerVM.Protocol.Verify`) runs in four stages: the
setup, the chain walk, the Merkle openings and the algebra. This module is the first stage and
the vocabulary of the second. Transcribed from the pinned leanVM
(`a386121f84292f6fa663aaa3e570c15bc0240ea2`): the stream order of
`crates/lean_vm/src/cpu/mod.rs:695-735` (`verify`), as the second verifier writes it out
(`python-verifier/verifier.py:1365-1407`, `verify_execution`).

**The setup** (`setup?`). The stream opens with the memory log-size, the six opcode tables'
log-heights and the WHIR rate, each a scalar with zero upper limbs (`read_public`,
`cpu/mod.rs:144-176`). The verifier reads them off the head of the stream and makes every check
`read_public` makes of them (`setupOk`) before the first hash, so that a proof with inadmissible
sizes costs no query. They fix the instance (`leanVm prog s`, the leanISA instance at the
deployed Flock specification), its stack (`stackMu`, `nLanes`) and the WHIR ladder
(`ladderOf`). The chain walk then observes the eight scalars and reads the commitment root, a
digest as two scalars whose top limbs are zero (`pcs::read_commitment`; `verifier.py:1381-1382`).

**The walk's primitives**, over the reader of `LeanerVM.Protocol.Proof` (`ReadM`): `samples n`
squeezes `n` challenges; `readRound d` reads the `d` wire coefficients of a round polynomial,
observing them, then squeezes its challenge, the order of every sumcheck of the bus and the
table phases (`verifier.py:452-459`); a round whose challenge comes first is WHIR's and is read
by its own walk. The walk records the wire scalars raw: the dropped coefficient is the
algebra's to derive (`RoundPoly.decode`), since the chain never reads it.

**Differences from the Rust.** None in what is accepted. The Rust checks each size as it reads
it; here the eight are checked before the walk starts, which rejects the same proofs earlier.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash LeanIsa

@[expose] public section

namespace Verify

/-! ## The setup -/

/-- The instance a proof of `prog` at the announced sizes `s` is about: leanISA's, at the
deployed Flock specification. -/
abbrev leanVm (prog : Program) (s : Sizes) : M3Instance :=
  leanIsaInstance Blake2sFlock.blake2sFlockSpec prog s

/-- The announced sizes and rate when they pass the setup checks, read off the head of the
stream without a hash; `none` otherwise (`read_public`, `cpu/mod.rs:144-176`). -/
def setup? {M : Type} (prog : Program) (p : Proof M) : Option (Sizes × ℕ) :=
  match p.announced? with
  | some (s, ρ) => if setupOk prog s ρ then some (s, ρ) else none
  | none => none

/-- The stack's number of variables at the announced sizes (`placements_of`,
`witness.rs:97`). -/
abbrev stackMu (prog : Program) (s : Sizes) : ℕ := leanIsaμ prog s

/-- The number of lanes of `2 ^ (μ - 6)` cells the committed columns occupy, at least one: the
level-0 rows carry only these, the rest of their leaf image being a zero prefix
(`witness.rs:97-101`, `StackShape::n_lanes`). -/
def nLanes (prog : Program) (s : Sizes) : ℕ :=
  max 1 (((LeanIsa.blocks prog s).total + 2 ^ (stackMu prog s - Whir.initialFold) - 1) /
    2 ^ (stackMu prog s - Whir.initialFold))

/-- The WHIR ladder of the stack at the announced rate (`derive_config`, `verifier.py:920-935`):
`none` outside the stacking and rate windows, which the setup checks exclude. -/
def ladderOf (prog : Program) (s : Sizes) (ρ : ℕ) : Option (List Whir.Level) :=
  Whir.ladder (stackMu prog s) ρ

/-! ## The chain walk's primitives -/

/-- The chain walk's monad: the transcript reader over the deployed proof, whose openings are
pruned Merkle paths. -/
abbrev Walk (m : Type → Type) : Type → Type := ReadM m PrunedMerklePaths

/-- One sumcheck round as read: the wire coefficients, low degree first with the dropped one
missing, and the challenge drawn after them. -/
structure Round where
  /-- The wire coefficients. -/
  wire : List E
  /-- The challenge. -/
  chal : E
  deriving Inhabited

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)

/-- `n` challenges, squeezed in order (`samples`). -/
def samples : ℕ → Walk m (List E)
  | 0 => pure []
  | n + 1 => do
    let x ← Reader.sample H
    let xs ← samples n
    return x :: xs

/-- A round whose `d` wire coefficients are read, and observed, before its challenge is
squeezed (`sumcheck`, `verifier.py:452-459`). -/
def readRound (d : ℕ) : Walk m Round := do
  let wire ← Reader.nextScalars H d
  let chal ← Reader.sample H
  return ⟨wire, chal⟩

/-- `n` rounds of `d` wire coefficients each. -/
def readRounds (d : ℕ) : ℕ → Walk m (List Round)
  | 0 => pure []
  | n + 1 => do
    let r ← readRound H d
    let rs ← readRounds d n
    return r :: rs

/-- The setup's reads: the eight announced scalars, observed, then the commitment root
(`read_public`, `read_commitment`). -/
def walkSetup : Walk m Digest := do
  let _ ← Reader.nextScalars H 8
  Reader.nextRoot H

/-! ## The rounds' decoding -/

/-- The round polynomials of a run of sumcheck rounds, decoded from their wires and the running
claim, each challenge evaluating the decoded polynomial into the next claim: the final claim and
the challenges, or `none` if a wire has the wrong length. `eq? j` is the equality weight of
round `j`, `none` for a plain round. -/
def replayRounds (d : ℕ) (eq? : ℕ → Option E) : ℕ → E → List Round → Option (E × List E)
  | _, claim, [] => some (claim, [])
  | j, claim, r :: rs => do
    let c ← RoundPoly.decode d claim (eq? j) r.wire
    let (final, cs) ← replayRounds d eq? (j + 1) (RoundPoly.eval c r.chal) rs
    return (final, r.chal :: cs)

end Verify

end
end LeanerVM.Protocol
