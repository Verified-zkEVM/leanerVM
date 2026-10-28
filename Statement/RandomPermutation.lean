module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection
public import VCVio.EvalDist.ProbabilityBounds
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.QueryTracking.WriterCost
public import VCVio.EvalDist.Monad.UniformTable

/-!
# Keccak and the random-permutation model

Read first (`Statement/README.md` states the model): Keccak-f[1600] as leanVM computes it, and
Keccak-256 over any permutation of its state (namespaces `LeanVM.*`), then the model (namespace
`Common`): `π` and `π⁻¹` lazily sampled, a cost bounded on every path, the oracles of the model
and a game's run (`KSpec`, `permCalls`, `runK`: Keccak-256 over `π`), and the SUF-CMA game of a
signature scheme (`SufCma`). The permutation's state is one type throughout, `KState`, `25` lanes
of `64` bits.
-/

@[expose] public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

set_option linter.unusedSectionVars false

/-!
## Keccak

Transcribed from `python-verifier/verifier.py` at leanVM
`94ee12ff6b2a3d42ba8328e22d09443692e4800b` (branch `main`): the round constants, rotation
offsets and lane permutation (`KECCAK_RC`, `KECCAK_RHO`, `KECCAK_PI`, `verifier.py:1207-1214`),
the permutation `keccak_f` (`verifier.py:360-375`), and the hash `keccak_hash`
(`verifier.py:191-209`) over any permutation `π` in any monad (`keccak256With`), the deployed one
over Keccak-f[1600] (`keccak256`): Keccak-256 as Ethereum computes it, rate `136` bytes, the
message padded with `0x01 ‖ 0^* ‖ 0x80` (FIPS 202's SHA3-256 would put `0x06` first). The Rust is
`crates/verifier/src/hash.rs` and `crates/primitives/src/hash.rs`.

A state is `25` lanes of `64` bits, lane `x + 5y` at index `x + 5y`.
-/

namespace LeanVM.Parameters

/-- `KECCAK_RC` (`verifier.py:1207-1212`): the round constants of the `24` rounds. -/
def keccakRC : List UInt64 := [
  0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
  0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- `KECCAK_RHO` (`verifier.py:1213`): the rotation of each lane, by index `x + 5y`. -/
def keccakRho : List ℕ :=
  [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]

/-- `KECCAK_PI` (`verifier.py:1214`): where lane `i = x + 5y` lands,
`i // 5 + 5 · ((2 · (i % 5) + 3 · (i // 5)) % 5)`. -/
def keccakPi (i : ℕ) : ℕ := i / 5 + 5 * ((2 * (i % 5) + 3 * (i / 5)) % 5)

end LeanVM.Parameters

namespace LeanVM.Semantics

open LeanVM.Parameters

/-! ### Keccak-f[1600] -/

/-- A Keccak state: `25` lanes of `64` bits, lane `x + 5y` at index `x + 5y`. -/
abbrev KState := Vector UInt64 25

namespace Keccak

/-- Lane `i` of a state, `0` past the end. -/
def lane (a : KState) (i : ℕ) : UInt64 := a.toArray.getD i 0

/-- `rot(x, n)`: rotate a lane left by `n < 64` bits (`verifier.py:364-365`). -/
def rot (x : UInt64) (n : ℕ) : UInt64 :=
  if n = 0 then x else (x <<< n.toUInt64) ||| (x >>> (64 - n).toUInt64)

/-- One round of `keccak_f` with the round constant `rc` (`verifier.py:368-374`): θ, then ρ and π
(`b[PI[i]] = rot(a[i], RHO[i])`), then χ and ι. -/
def round (a : KState) (rc : UInt64) : KState :=
  let c : Vector UInt64 5 := Vector.ofFn fun x ↦
    lane a x ^^^ lane a (x + 5) ^^^ lane a (x + 10) ^^^ lane a (x + 15) ^^^ lane a (x + 20)
  let cAt := fun x ↦ c.toArray.getD x 0
  -- θ: `a[i] ^ c[(i - 1) % 5] ^ rot(c[(i + 1) % 5], 1)`
  let a : KState := Vector.ofFn fun i ↦
    lane a i ^^^ cAt ((i.val + 4) % 5) ^^^ rot (cAt ((i.val + 1) % 5)) 1
  -- ρ and π
  let b : KState := (List.range 25).foldl
    (fun b i ↦ b.setIfInBounds (keccakPi i) (rot (lane a i) (keccakRho.getD i 0)))
    (Vector.replicate 25 0)
  -- χ
  let a : KState := Vector.ofFn fun i ↦
    lane b i ^^^ (~~~ lane b (i.val - i.val % 5 + (i.val + 1) % 5) &&&
      lane b (i.val - i.val % 5 + (i.val + 2) % 5))
  -- ι
  a.setIfInBounds 0 (lane a 0 ^^^ rc)

end Keccak

/-- **Keccak-f[1600]** (`keccak_f`, `verifier.py:360-375`): the `24` rounds. -/
def keccakF (a : KState) : KState := keccakRC.foldl Keccak.round a

end LeanVM.Semantics

namespace LeanVM.Protocol

open LeanVM.Parameters LeanVM.Semantics

/-- A Keccak-256 digest: its `32` bytes as four little-endian 64-bit words, the first four lanes of
the last state (`Digest.words`, `verifier.py:221-223`). -/
abbrev Digest := Vector UInt64 4

namespace KeccakHash

/-! ### Keccak-256 (`keccak_hash`, `verifier.py:191-209`) -/

/-- `RATE`: a block is `136` bytes, `17` lanes. -/
def rate : ℕ := 136

/-- `PAD_FIRST`: the padding's first byte, after the message. -/
def padFirst : UInt8 := 0x01

/-- `PAD_LAST`: the padding's last byte, the block's last. -/
def padLast : UInt8 := 0x80

/-- The little-endian 64-bit word of bytes `8i` to `8i + 7` of a byte string, missing bytes `0`
(`unpack("<17Q", ...)`). -/
def leLane (bytes : List UInt8) (i : ℕ) : UInt64 :=
  (List.range 8).foldl (fun acc k ↦ acc ||| ((bytes.getD (8 * i + k) 0).toUInt64 <<< (8 * k).toUInt64)) 0

section With

variable {m : Type → Type} [Monad m] (π : KState → m KState)

/-- Absorb one block of `136` bytes with the permutation `π`: XOR its `17` lanes into the rate,
then permute (`verifier.py:207-208`). -/
def absorbBlockWith (state : KState) (block : List UInt8) : m KState :=
  π (Vector.ofFn fun i ↦
    if i.val < 17 then Keccak.lane state i ^^^ leLane block i else Keccak.lane state i)

/-- The last block: the remaining `0` to `135` bytes, `PAD_FIRST` after them, zeros, and
`PAD_LAST` XORed into the block's last byte (one byte `0x81` when `135` bytes remain)
(`verifier.py:203-205`). -/
def padBlock (rest : List UInt8) : List UInt8 :=
  ((rest ++ List.replicate (rate - rest.length) 0).modify rest.length (· ^^^ padFirst)).modify
    (rate - 1) (· ^^^ padLast)

/-- Absorb `data` into `state` with `π`: `blocks` whole blocks of `136` bytes, then the padded
last block, which holds the remaining `0` to `135` bytes. -/
def absorbWith : (blocks : ℕ) → KState → List UInt8 → m KState
  | 0, state, data => absorbBlockWith π state (padBlock data)
  | blocks + 1, state, data => do
    let state ← absorbBlockWith π state (data.take rate)
    absorbWith blocks state (data.drop rate)

/-- **Keccak-256 over a permutation `π`**, in any monad (`keccak_hash`, `verifier.py:200-209`, with
`π` for Keccak-f[1600]): `⌊len/136⌋` whole blocks, then the padded last one, from the zero state;
the digest is the first four lanes. The Python pads the whole string first (`len // RATE + 1`
blocks); the blocks are the same. -/
def keccak256With (data : List UInt8) : m Digest := do
  let state ← absorbWith π (data.length / rate) (Vector.replicate 25 0) data
  pure #v[Keccak.lane state 0, Keccak.lane state 1, Keccak.lane state 2, Keccak.lane state 3]

end With

/-- **Keccak-256 of a byte string** (`keccak_hash`): Keccak-256 over Keccak-f[1600]. -/
def keccak256 (data : List UInt8) : Digest := Id.run (keccak256With (fun s ↦ pure (keccakF s)) data)

/-! ### Bytes of words and digests -/

/-- The eight little-endian bytes of a 64-bit word. -/
def wordBytes (w : UInt64) : List UInt8 :=
  (List.range 8).map fun k ↦ (w >>> (8 * k).toUInt64).toUInt8

/-- The 32 bytes of a digest: its words, little-endian (`Digest.value`, `verifier.py:209`). -/
def digestBytes (d : Digest) : List UInt8 := d.toList.flatMap wordBytes

end KeccakHash

/-- The 32 bytes of a digest as a vector: Keccak-256's output as the model's oracle answers it. -/
def Digest.toBytes (d : Digest) : Vector UInt8 32 :=
  ⟨(KeccakHash.digestBytes d).toArray, by
    obtain ⟨⟨l⟩, hl⟩ := d
    match l, hl with
    | [_, _, _, _], _ => rfl⟩

end LeanVM.Protocol

/-! ## The random permutation: `π` and `π⁻¹`, lazily sampled -/

namespace Common

/-- A query to a permutation `π` of `S`: forward `π x` or inverse `π⁻¹ y`. -/
inductive PermQuery (S : Type) where
  /-- The forward query `π x`. -/
  | fwd (x : S)
  /-- The inverse query `π⁻¹ y`. -/
  | inv (y : S)
  deriving DecidableEq

/-- The oracle specification of the random-permutation model: both kinds of query answer a state.
-/
abbrev permSpec (S : Type) : OracleSpec (PermQuery S) := PermQuery S →ₒ S

/-- The state of a lazily sampled permutation: the edges `(x, π x)` fixed so far, newest first. -/
abbrev PermLog (S : Type) := List (S × S)

variable {S : Type} [DecidableEq S]

/-- The recorded forward answer at `x`: the output of the first edge with input `x`. -/
def fwdLookup : PermLog S → S → Option S
  | [], _ => none
  | (a, b) :: E, x => if a = x then some b else fwdLookup E x

/-- The recorded inverse answer at `y`: the input of the first edge with output `y`. -/
def invLookup : PermLog S → S → Option S
  | [], _ => none
  | (a, b) :: E, y => if b = y then some a else invLookup E y

variable [Fintype S] [SampleableType S]

/-- A uniform draw from the points outside the list `l`, or from all of `S` when `l` covers
`S` (which the lazy permutation never needs: a full range is a full domain). -/
noncomputable def uniformAvoiding (l : List S) : ProbComp S :=
  if h : ∃ y, y ∉ l then
    letI : Nonempty {y // y ∉ l} := ⟨⟨h.choose, h.choose_spec⟩⟩
    letI : SampleableType {y // y ∉ l} := SampleableType.subtype S (· ∉ l)
    Subtype.val <$> ($ᵗ {y // y ∉ l})
  else $ᵗ S

/-- **The lazily sampled random permutation.** A recorded point is answered from the log; a
fresh forward query `π x` draws `π x` uniformly outside the current range and records `(x, π x)`;
a fresh inverse query `π⁻¹ y` draws `π⁻¹ y` uniformly outside the current domain and records
`(π⁻¹ y, y)`. -/
noncomputable def lazyPerm : QueryImpl (permSpec S) (StateT (PermLog S) ProbComp)
  | .fwd x => StateT.mk fun E =>
      match fwdLookup E x with
      | some y => pure (y, E)
      | none => (fun y ↦ (y, (x, y) :: E)) <$> uniformAvoiding (E.map Prod.snd)
  | .inv y => StateT.mk fun E =>
      match invLookup E y with
      | some x => pure (x, E)
      | none => (fun x ↦ (x, (x, y) :: E)) <$> uniformAvoiding (E.map Prod.fst)

/-! ## A cost bounded on every path of a computation -/

/-- A total weight bound: every path of `oa` makes queries of total weight at most `Q`, a query
`t` weighing `w t`. -/
def IsWeightBound {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type} (oa : OracleComp spec α)
    (w : ι → ℕ) (Q : ℕ) : Prop :=
  IsQueryBound oa Q (fun t b ↦ w t ≤ b) (fun t b ↦ b - w t)

/-- A byte as a residue. -/
def uInt8EquivFin : UInt8 ≃ Fin 256 where
  toFun b := b.toFin
  invFun f := UInt8.ofFin f
  left_inv _ := rfl
  right_inv _ := rfl

/-! ## The oracles of the model and a game's run -/

section

open LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- A 32-byte Keccak-256 digest. -/
abbrev KDigest := Vector UInt8 32

/-- **The oracles of the random-permutation model**: coins, Keccak-256 (its digest's 32 bytes),
`π` and `π⁻¹` on Keccak states. -/
abbrev KSpec := unifSpec + ((List UInt8 →ₒ KDigest) + permSpec KState)

/-- **Calls of the permutation**: a hash of `n` bytes costs `⌊n / 136⌋ + 1` (one per block of the
padded message), a call of `π` or `π⁻¹` one. -/
def permCalls : KSpec.Domain → ℕ
  | .inl _ => 0
  | .inr (.inl m) => m.length / 136 + 1
  | .inr (.inr _) => 1

/-- The model's answers: coins forwarded, Keccak-256 over the lazily sampled permutation, `π`
and `π⁻¹` the lazily sampled permutation. -/
noncomputable def kImpl : QueryImpl KSpec (StateT (PermLog KState) ProbComp)
  | .inl n => liftM (unifSpec.query n : ProbComp (Fin (n + 1)))
  | .inr (.inl m) => Digest.toBytes <$> keccak256With (fun x ↦ lazyPerm (.fwd x)) m
  | .inr (.inr q) => lazyPerm q

/-- **A game in the random-permutation model, run** against the lazily sampled random
permutation from no edge. -/
noncomputable def runK {α : Type} (G : OracleComp KSpec α) : ProbComp α :=
  (simulateQ kImpl G).run' []

end

/-! ## The SUF-CMA game of a hash-based signature scheme, in the random-permutation model -/

namespace SufCma

/-- **The digest bytes as a bit vector**, little endian: byte `i` is bits `8 i … 8 i + 7`
(`digestBitVec_extract`). -/
def digestBitVec : KDigest ≃ BitVec 256 :=
  (arrayVectorEquivFin UInt8 32).trans <|
    (Equiv.arrowCongr (Equiv.refl _) uInt8EquivFin).trans <|
      finFunctionFinEquiv.trans <| (finCongr (show 256 ^ 32 = 2 ^ 256 by norm_num)).trans
        ⟨BitVec.ofFin, BitVec.toFin, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- The hash of a signature scheme, `H : List UInt8 → BitVec 256`: in the model Keccak-256, its
digest read as a little-endian number (`digestBitVec`). -/
abbrev HSpec := List UInt8 →ₒ BitVec 256

/-- **A signature scheme** with the hash `H` (`HSpec`): a seed sampler, key generation from a
seed, the signer answering a request `Req` with `Resp`, the verifier of a claimed forgery `F`, and
the winning condition on the signing transcript and the forgery. -/
structure Scheme (Seed PK SK Req Resp F : Type) where
  /-- Sample the secret seed. -/
  sample : ProbComp Seed
  /-- Generate the keys from the seed. -/
  keygen : Seed → OracleComp HSpec (PK × SK)
  /-- Answer a signing request. -/
  sign : SK → Req → OracleComp HSpec Resp
  /-- Verify a claimed forgery. -/
  verify : PK → F → OracleComp HSpec Bool
  /-- The transcript and the forgery make a win (when the forgery verifies). -/
  win : QueryLog (Req →ₒ Resp) → F → Bool

variable {Seed PK SK Req Resp F : Type}

/-- The hash as Keccak-256 (`digestBitVec`), in the random-permutation model. -/
def hashK : QueryImpl HSpec (OracleComp KSpec) :=
  fun m ↦ digestBitVec <$> (liftM (KSpec.query (.inr (.inl m))) : OracleComp KSpec KDigest)

/-- The signing oracle in the random-permutation model. -/
def signingOracleK (S : Scheme Seed PK SK Req Resp F) (sk : SK) :
    QueryImpl (Req →ₒ Resp) (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp KSpec)) :=
  QueryImpl.withLogging fun r ↦ simulateQ hashK (S.sign sk r)

/-- **The RPM game**: the game with `H` Keccak-256 over the permutation, and an adversary that
also queries Keccak-256, `π` and `π⁻¹`. -/
noncomputable def rpmGame (S : Scheme Seed PK SK Req Resp F)
    (main : PK → OracleComp (KSpec + (Req →ₒ Resp)) F) : OracleComp KSpec Bool := do
  let seed ← liftM S.sample
  let (pk, sk) ← simulateQ hashK (S.keygen seed)
  let ((forgery, log) : F × QueryLog (Req →ₒ Resp)) ←
    (simulateQ (QueryImpl.ofLift KSpec (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp KSpec)) +
      signingOracleK S sk) (main pk)).run
  let verified ← simulateQ hashK (S.verify pk forgery)
  return S.win log forgery && verified

/-- **The RPM experiment**: the RPM game against the lazily sampled random permutation. -/
noncomputable def rpmExperiment (S : Scheme Seed PK SK Req Resp F)
    (main : PK → OracleComp (KSpec + (Req →ₒ Resp)) F) : ProbComp Bool :=
  runK (rpmGame S main)

/-- **`bits` bits of SUF-CMA security in the random-permutation model**: every adversary `main`
(coins, Keccak-256, `π`, `π⁻¹` and the signing oracle) whose game, key generation, the signer's
answers and the forgery's verification included, makes at most `Q ≥ 1` permutation calls on every
path wins with probability at most `(Q + 1) · 2^-bits`. -/
def RpmSecure (S : Scheme Seed PK SK Req Resp F) (bits : ℕ) : Prop :=
  ∀ Q, 1 ≤ Q → ∀ main : PK → OracleComp (KSpec + (Req →ₒ Resp)) F,
    IsWeightBound (rpmGame S main) permCalls Q →
      Pr{let b ← rpmExperiment S main}[b = true] ≤ ((Q : ℝ≥0∞) + 1) * (2 : ℝ≥0∞)⁻¹ ^ bits

end SufCma

end Common

end
