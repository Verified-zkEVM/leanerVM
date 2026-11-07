module

public import Statement.Prover.Run
public import Statement.Prover.Columns
public import Statement.Prover.Ntt
public import Statement.Prover.Bus
public import Statement.Prover.Table
public import Statement.Prover.Keccak
public import Statement.Prover.Whir

/-!
# The honest prover

`LeanVM.Prover.prove F prog input t ρ fuel`: leanVM's honest prover over the permutation `F` in any
monad, Keccak-256 the sponge over `F`. With Keccak-f[1600] in `Id` it is the executable
(`lake exe leanvm-prove`); with the model's permutation (`Common.queryPermutation`) it is the
prover the completeness statements name (`LeanVm.lean`, `LeanVmGuestCompleteness.lean`).

It computes the witness from the trace (`witness?`: one run of the program) and runs the honest
script, one executable prover per phase of `verify_execution`, against the verifier's own program
(`runScript`). Its only search is the proof-of-work nonce search, bounded by `fuel`; nothing
branches on a permutation answer except through the challenges the verifier's program samples.
The proof travels as its one encoding, `Proof.toBytes` (`crates/fiat_shamir/src/wire.rs`), which
hashes nothing.
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

/-- **The honest script** of an execution's witness `W` at the rate `ρ` and the public input
`publicInput`: the eight moves of `verify_execution` (`verifier.py:1463-1516`), each phase's
executable prover beside the verifier's phase (`Script.alongside`), which hands the next phase its
result. The public-input phase sends nothing; the output lanes' claims, on no committed column, do
not reach the stack (`ColumnClaim.onStack`). -/
def honestScript (W : Witness) (ρ : ℕ) (publicInput : Digest) : Script Unit :=
  let layout := W.layout
  (Script.sendList (W.announce ρ)).bind fun _ ↦
  (Script.commitS (stackWordFast layout.stackLog ρ W.stack)).bind fun _ ↦
  (Script.alongside (verifyBusBalance computedBytecodeValue layout) (busFast layout W.cols)).bind
    fun bus ↦
  (Script.alongside (tablePhase layout bus) (tableFast W.cols layout.tableLogHeights bus)).bind
    fun evaluations ↦
  (Script.alongside (publicInputPhase layout publicInput) Script.sampleE).bind fun publicClaims ↦
  (Script.alongside (keccakPhase layout evaluations) (KeccakGkr.keccakPhaseProve
    (layout.tableLogHeights.getD opKeccak 0) W.cols evaluations)).bind fun keccak ↦
  (ringFast keccak.2.1 keccak.2.2).bind fun r ↦
  let claims := (bus.claims ++ tableColumnClaims evaluations ++ publicClaims).filter
    (fun c ↦ c.column ∉ keccakOutputColumns) ++ keccak.1
  openingFast layout.stackLog ρ W.stack (r.claim layout :: claims.map (ClaimDesc.column layout))

/-! ## The proof's wire encoding (`Proof::to_bytes`, `crates/fiat_shamir/src/wire.rs:16-97`)

The one encoding of a proof, which `Proof.fromBytes` (`LeanVmVerifier.lean`) decodes. It hashes
nothing: a phase is pruned into the fewest siblings that authenticate all its paths together, a
sibling left out where another path's node gives it. The Rust asserts that the proof is within the
decoding's bounds and every count fits in 32 bits; here a count is written modulo `2^32`, and the
first path of a phase gives its height and leaf width (none for no path, where the Rust panics).
-/

open LeanVM.Protocol.KeccakHash in
/-- `write_u32`: the four little-endian bytes of a count, modulo `2^32` (`wire.rs:155-157`). -/
def u32Bytes (value : ℕ) : List UInt8 :=
  (List.range 4).map fun k ↦ UInt8.ofNat (value / 256 ^ k)

open LeanVM.Protocol.KeccakHash in
/-- `write_phase` (`wire.rs:61-97`): the queries' count and positions, in sampling order; the
height, the leaf width and the row width, the leaf width less the leading zero words every distinct
leaf has; the leaf at each distinct position, ascending (the first path at it), as its last
row-width words; then, level by level from the leaves, the sibling of each node the distinct paths
climb through (the first path's) whose sibling node is not one of them, left to right. -/
def phaseToBytes (paths : List Opening) : List UInt8 :=
  let height := (paths.head?.map fun path ↦ path.path.length).getD 0
  let leafWords := (paths.head?.map fun path ↦ path.leaf.length).getD 0
  let distinct := dedupByKey Opening.leafIndex
    (paths.mergeSort fun a b ↦ a.leafIndex ≤ b.leafIndex)
  let zeros := ((distinct.map fun path ↦
    (path.leaf.takeWhile fun word ↦ decide (word = 0)).length).min?).getD 0
  u32Bytes paths.length ++ paths.flatMap (fun path ↦ u32Bytes path.leafIndex) ++
    u32Bytes height ++ u32Bytes leafWords ++ u32Bytes (leafWords - zeros) ++
    distinct.flatMap (fun path ↦ (path.leaf.drop zeros).flatMap K.toBytes) ++
    (List.range height).flatMap fun level ↦
      let nodes := dedupByKey Prod.fst (distinct.map fun path ↦
        (path.leafIndex >>> level, path.path.getD level default))
      (nodes.filter fun (node, _) ↦ node ^^^ 1 ∉ nodes.map Prod.fst).flatMap
        fun (_, sibling) ↦ digestBytes sibling

/-- **The proof's one encoding** (`Proof::to_bytes`, `wire.rs:26-42`): the stream's length, then
each element as its three words; the number of phases, then each phase pruned (`phaseToBytes`). -/
def _root_.LeanVM.Protocol.Compile.Proof.toBytes (proof : Proof) : List UInt8 :=
  u32Bytes proof.stream.length ++ proof.stream.flatMap E.toBytes ++
    u32Bytes proof.openings.length ++ proof.openings.flatMap phaseToBytes

/-- **leanVM's honest prover.** The proof of the execution `t` of `prog` on `input` at the rate
`2^-ρ`, trying `fuel` nonces per proof of work; `none` for a trace that is no valid execution
within the cap, an invalid rate, or a proof-of-work search that finds no nonce. -/
def prove {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState) (prog : LeanIsaProgram)
    (input : PublicInput) (t : Execution prog) (ρ fuel : ℕ) : m (Option Proof) :=
  match witness? prog input t with
  | none => pure none
  | some W =>
    if 1 ≤ ρ ∧ ρ ≤ 4 then do
      let seed ← spongeSeedWith F (bytecodeWords prog) (publicInputDigest input)
      runScript F (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input))
        (honestScript W ρ (publicInputDigest input)) seed fuel
    else pure none

end LeanVM.Prover

end
