/-
  LeanerVM.Protocol.Verify

  leanVM's executable verifier: one function of the program, the public input and a proof, to
  `Bool`, generic in how the hash is answered, in four stages: the setup, the chain walk, the
  Merkle openings and the algebra.
-/

module

public import LeanerVM.Protocol.Verify.Whir

/-!
# The verifier

Written from the specification's unrolled protocol (§8.5,
`doc/leanvm/body/08-end-to-end-protocol.tex` at leanVM `a386121f84292f6fa663aaa3e570c15bc0240ea2`)
over the oracle verifiers of the phases, and transcribed for the stream order, the encodings and
the constants from the deployed verifiers: `crates/lean_vm/src/cpu/mod.rs:695-735` (`verify`)
and `python-verifier/verifier.py:1365-1407` (`verify_execution`).

`verifyWith H prog input proof` runs in four stages.

1. **The setup** (`setup?`, `openingsOk`): the announced sizes and rate, read off the head of the
   stream, pass `read_public`'s checks; the WHIR ladder of the stack exists; the openings have the
   number and shapes the ladder fixes. Nothing is hashed before these pass, and nothing at all on
   a proof they reject.
2. **The chain walk** (`walkChain`): from the statement's seed (`FsState.seed`, a constant of
   the statement), every chain step and grinding check in stream order: the eight sizes
   observed, the commitment root, the bus phase, the table sumcheck, the public input, the Flock
   phase, the opening's batching challenge `λ` and WHIR. It records the wire transcript
   (`Wire`): the scalars sent, raw, the challenges, the nonces, the roots and the positions.
3. **The Merkle openings** (`walkOpenings`): every level's pruned opening against its root at its
   positions, by `merkleVerifyWith H`; the rows. Then the stream and the openings must be fully
   consumed (`Reader.finish`).
4. **The algebra** (`algebra`), phase by phase, pure: the oracle verifiers' checks and outputs
   on the wire transcript (`leanVmBus`, `tableStep`, `pubStep`, `flockStep`), the opening's pool
   batched by the powers of `λ` (`Opening.poolList`: the ring-switched claim first, the column
   claims after, each through the stack's layout), and WHIR's sumcheck and terminal check
   (`whirCheck`).

The walk and the openings are `walkProof`, written over the walk's primitives (`ChainOps`) and run
here on the proof reader's, `readerOps H`; the same walk runs on any other reader of the chain.
`LeanerVM.Protocol.Verify.Hom` carries `verifyWith` along a monad morphism of the hash's monads
(`verifyWith_hom`, `verifyWith_simulateQ`, `verifyWith_pure`).

`verify := verifyWith (m := Id) blake2sBytes`. Every function is total and computable, by
structural recursion; a malformed proof is `false`.

**The fixed public polynomials.** Two public polynomials are evaluated, which a recursive
verifier defers instead (`VerifySummary`, `cpu/mod.rs:683-700`). The bytecode multilinear at the
bus point and the fingerprint challenges, `B̃(ζ_{<κ_bc}, α)`, is the program's share of the two
bytecode blocks' fingerprints (`bytecodeShare_eq`): `settleFixedClaims` evaluates it, and the bus
phase's totals take it in place of the entry columns (`leanVmBus`, `busOutWith`), so a recursive
verifier changes that one function. The Rust's native verifier evaluates the entry columns one by
one inside the totals (`leaf.rs:453`) and computes the multilinear too, handing it on unchecked
(`leaf.rs:627-637`); both give the same totals. The BLAKE2s circuit's matrices at the lincheck's
column weights are one forward walk of the circuit (`blake2sRows`), which the Flock step takes
for the lincheck's check.

**Differences from the Rust.** None in what is accepted. The Rust reads and checks each phase as
it goes and opens each WHIR level where its rows are needed; here the walk reads everything
first, the openings come after it and the algebra last, and the openings' number and shapes
are checked before any hash. Openings are not absorbed, so no challenge moves, and the same
proofs are rejected, some at another stage.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash LeanIsa CompPoly CMlPolynomialEval

@[expose] public section

namespace Verify

/-! ## The wire transcript -/

/-- Everything the chain walk reads and squeezes, phase by phase. -/
structure Wire where
  /-- The commitment root. -/
  root : Digest
  /-- The bus phase. -/
  bus : BusWire
  /-- The table sumcheck. -/
  table : TableWire
  /-- The public input. -/
  pub : PubWire
  /-- The Flock phase. -/
  flock : FlockWire
  /-- The opening's batching challenge `λ`. -/
  lam : E
  /-- The first round polynomial of WHIR's sumcheck. -/
  whirFirst : List E
  /-- WHIR's levels. -/
  whir : List WhirLevel
  deriving Inhabited

/-! ## The chain walk -/

section Walk

variable {n : Type → Type} [Monad n] (ops : ChainOps n)

/-- The chain walk on the instance of `prog` at the sizes `s`, with the opening's levels `shs`:
every phase's reads in stream order. -/
def walkChain (prog : Program) (s : Sizes) (input : PublicInput) (shs : List LevelShape) :
    n Wire := do
  let I := leanVm prog s
  let root ← walkSetup ops
  let bus ← walkBus ops I.μBus I.busClaims
  let table ← walkTables ops I.τmax I.tableColumns
  let pub ← walkPub ops (PublicInput.sentCount I (I.publicLines input))
  let flock ← walkFlock ops (s.τ 5)
  let lam ← ops.sample
  let (whirFirst, whir) ← walkWhir ops shs
  return ⟨root, bus, table, pub, flock, lam, whirFirst, whir⟩

/-- The verifier's reads in their stages: the whole chain walk, then every level's opening. -/
def walkProof (prog : Program) (s : Sizes) (input : PublicInput) (shs : List LevelShape) :
    n (Wire × List (List (List K))) := do
  let w ← walkChain ops prog s input shs
  let rows ← walkOpenings ops (nLanes prog s) true w.root shs w.whir
  return (w, rows)

end Walk

/-! ## The algebra -/

/-- The opening's weight and target: the pool's weights and values batched by the powers of
`λ` (`Opening.weight`, `Opening.values`), the pool built once. -/
def openingClaim (I : M3Instance) (s : I.Stmt × FlockOut I) (lam : E) : Weight E I.μ × E :=
  let pool := (Opening.poolList I s.2).toArray
  (Weight.batch (fun j : Fin pool.size ↦ pool[j].weight) lam,
    powerBatch (fun j : Fin pool.size ↦ pool[j].value) lam)

/-- The algebra on the wire transcript and the rows, phase by phase: the oracle verifiers'
checks and outputs (the bus phase's with the program's share settled, `leanVmBus`), the
opening's batch, and WHIR's sumcheck and terminal check. -/
def algebra (prog : Program) (s : Sizes) (input : PublicInput) (shs : List LevelShape)
    (w : Wire) (rows : List (List (List K))) : Bool :=
  let I := leanVm prog s
  match leanVmBus prog s input w.bus with
  | none => false
  | some b =>
    match tableStep I b w.table with
    | none => false
    | some t =>
      match pubStep I t w.pub with
      | none => false
      | some p =>
        match flockStep I (flockRegion prog s Blake2sFlock.blake2sFlockSpec) rfl blake2sRows p
          w.flock with
        | none => false
        | some f =>
          let (W, target) := openingClaim I f w.lam
          whirCheck I.μ shs W target w.whirFirst w.whir rows

/-! ## The verifier -/

/-- **leanVM's verifier**, generic in how the hash `H` is answered: the setup's checks before any
hash, the chain walk, the Merkle openings and the stream fully consumed, then the algebra. -/
def verifyWith {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (prog : Program)
    (input : PublicInput) (proof : Proof PrunedMerklePaths) : m Bool :=
  match setup? prog proof with
  | none => pure false
  | some (s, ρ) =>
    match ladderOf prog s ρ with
    | none => pure false
    | some levels =>
      let shs := levelShapes (stackMu prog s) levels
      if !openingsOk (nLanes prog s) true shs proof.merkle then pure false
      else do
        let r ← ((do
            let x ← walkProof (readerOps H) prog s input shs
            Reader.finish
            return x : Walk m (Wire × List (List (List K)))).run'
          ⟨FsState.seed prog input, proof.stream, proof.merkle⟩).run
        match r with
        | .error _ => pure false
        | .ok (w, rows) => pure (algebra prog s input shs w rows)

/-- **leanVM's verifier** at the deployed hash, BLAKE2s-256. -/
def verify (prog : Program) (input : PublicInput) (proof : Proof PrunedMerklePaths) : Bool :=
  verifyWith (m := Id) blake2sBytes prog input proof

/-- A proof the setup rejects is rejected without a hash, whatever answers it. -/
theorem verifyWith_of_setup {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)
    {prog : Program} {input : PublicInput} {proof : Proof PrunedMerklePaths}
    (h : setup? prog proof = none) : verifyWith H prog input proof = pure false := by
  simp only [verifyWith, h]

/-- A proof whose openings have another number or shape than the ladder fixes is rejected
without a hash, whatever answers it. -/
theorem verifyWith_of_openings {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)
    {prog : Program} {input : PublicInput} {proof : Proof PrunedMerklePaths} {s : Sizes} {ρ : ℕ}
    {levels : List Whir.Level} (hs : setup? prog proof = some (s, ρ))
    (hl : ladderOf prog s ρ = some levels)
    (ho : openingsOk (nLanes prog s) true (levelShapes (stackMu prog s) levels) proof.merkle =
      false) :
    verifyWith H prog input proof = pure false := by
  simp only [verifyWith, hs, hl, ho, Bool.not_false, ↓reduceIte]

end Verify

end
end LeanerVM.Protocol
