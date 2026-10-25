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

Read first. Keccak-f[1600] and Keccak-256 as leanVM computes them, and the random-permutation model
(RPM) every end statement with an adversary is stated in: one uniformly random permutation `π` of
the 1600-bit Keccak state, which every party queries forward (`π x`) and inverse (`π⁻¹ y`),
Keccak-256 the sponge over `π`.

* **Keccak as deployed** (namespaces `LeanVM.Parameters`, `LeanVM.Semantics`, `LeanVM.Protocol`):
  Keccak-f[1600] (`keccakF`) on `25` lanes of `64` bits, and Keccak-256 (`KeccakHash.keccak256`),
  transcribed from `python-verifier/verifier.py` at leanVM `94ee12ff6b2a3d42ba8328e22d09443692e4800b`.
* **The model** (namespace `Common`): a query to a permutation (`PermQuery`, `permSpec`), the
  lazily sampled uniform permutation (`lazyPerm`: a fresh answer uniform among the points not yet
  used), the sponge over any permutation on the 200-byte state (`spongeWith`, `KState`) with
  Keccak-256's padding (`keccakPadding`), the hash as the sponge over the lazily sampled
  permutation (`realImpl`, `realGame`), a bound on a cost along every path of a computation
  (`IsWeightBound`), the Keccak-256 evaluations a transcript of permutation queries contains
  (`pathsOf`), and the SUF-CMA game of a hash-based signature scheme (`SufCma.rpmGame`,
  `rpmExperiment`, its permutation calls `permCalls`).
* **Named by LeanDA's code-binding bound only** (the last sections): the two-oracle simulator
  (`simulator2`, `advS2`) and the duplex simulator (`Duplex.simImpl`), through which the bound's
  terms are the success probabilities of Wagner's reductions (`Statement/LeanDa.lean`). They are
  definitions of the proof's two-oracle random-oracle model, not statements in it.

Not definitions: `keccakPadding` carries the padding's laws, so the six lemmas before it
(`keccakPad_ne_nil`, `keccakUnpad_keccakPad` and what they use) are proved here.
-/

section

/-!
## Keccak

Transcribed from `python-verifier/verifier.py` at leanVM
`94ee12ff6b2a3d42ba8328e22d09443692e4800b` (branch `main`): the round constants, rotation
offsets and lane permutation (`KECCAK_RC`, `KECCAK_RHO`, `KECCAK_PI`, `verifier.py:1207-1214`),
the permutation `keccak_f` (`verifier.py:360-375`), and the hash `keccak_hash`
(`verifier.py:191-209`): Keccak-256 as Ethereum computes it, rate `136` bytes, the message padded
with `0x01 ‖ 0^* ‖ 0x80` (FIPS 202's SHA3-256 would put `0x06` first). The Rust is
`crates/verifier/src/hash.rs` and `crates/primitives/src/hash.rs`.

A state is `25` lanes of `64` bits, lane `x + 5y` at index `x + 5y`. A lane is a `UInt64` here
and a `K` word inside the machine (`K.ofLane`, `K.lane`: bit `i` of the lane is the coefficient
of `x^i`). Then the byte and field encodings the verifier hashes: a `K` word as eight
little-endian bytes, the Merkle leaf and node hashes, and a digest as two field elements.
-/

namespace LeanVM.Parameters

@[expose] public section

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

end
end LeanVM.Parameters

namespace LeanVM.Semantics

open LeanVM.Parameters

@[expose] public section

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

end
end LeanVM.Semantics

namespace LeanVM.Protocol

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-- A Keccak-256 digest: its `32` bytes as four little-endian 64-bit words, the first four lanes of
the last state (`Digest.words`, `verifier.py:221-223`). -/
abbrev Digest := Vector UInt64 4

/-- Digest equality decided on the word lists, usable from a module file, where core's
`DecidableEq` for `Vector` is not exposed. -/
def Digest.decEq : DecidableEq Digest := fun a b ↦
  decidable_of_iff (a.toList = b.toList) Vector.toList_inj

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

/-- Absorb one block of `136` bytes: XOR its `17` lanes into the rate, then permute
(`verifier.py:207-208`). -/
def absorbBlock (state : KState) (block : List UInt8) : KState :=
  keccakF (Vector.ofFn fun i ↦
    if i.val < 17 then Keccak.lane state i ^^^ leLane block i else Keccak.lane state i)

/-- The last block: the remaining `0` to `135` bytes, `PAD_FIRST` after them, zeros, and
`PAD_LAST` XORed into the block's last byte (one byte `0x81` when `135` bytes remain)
(`verifier.py:203-205`). -/
def padBlock (rest : List UInt8) : List UInt8 :=
  ((rest ++ List.replicate (rate - rest.length) 0).modify rest.length (· ^^^ padFirst)).modify
    (rate - 1) (· ^^^ padLast)

/-- Absorb `data` into `state`: `blocks` whole blocks of `136` bytes, then the padded last block,
which holds the remaining `0` to `135` bytes. -/
def absorb : (blocks : ℕ) → KState → List UInt8 → KState
  | 0, state, data => absorbBlock state (padBlock data)
  | blocks + 1, state, data => absorb blocks (absorbBlock state (data.take rate)) (data.drop rate)

/-- **Keccak-256 of a byte string** (`keccak_hash`, `verifier.py:200-209`): `⌊len/136⌋` whole
blocks, then the padded last one, from the zero state; the digest is the first four lanes. The
Python pads the whole string first (`len // RATE + 1` blocks); the blocks are the same. -/
def keccak256 (data : List UInt8) : Digest :=
  let state := absorb (data.length / rate) (Vector.replicate 25 0) data
  #v[Keccak.lane state 0, Keccak.lane state 1, Keccak.lane state 2, Keccak.lane state 3]

/-! ### Bytes of words and digests -/

/-- The eight little-endian bytes of a 64-bit word. -/
def wordBytes (w : UInt64) : List UInt8 :=
  (List.range 8).map fun k ↦ (w >>> (8 * k).toUInt64).toUInt8

/-- The 32 bytes of a digest: its words, little-endian (`Digest.value`, `verifier.py:209`). -/
def digestBytes (d : Digest) : List UInt8 := d.toList.flatMap wordBytes

/-! ### The Merkle node hash (`Transcript.merkle`, `verifier.py:433-445`) -/

/-- The digest of a node: Keccak-256 of the 64 bytes of its two children, left first. -/
def hashPair (left right : Digest) : Digest := keccak256 (digestBytes left ++ digestBytes right)

end KeccakHash

end
end LeanVM.Protocol

end

/-! ## The random permutation: `π` and `π⁻¹`, lazily sampled -/

@[expose] public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

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

variable {S : Type}

section Lookup

variable [DecidableEq S]

/-- The recorded forward answer at `x`: the output of the first edge with input `x`. -/
def fwdLookup : PermLog S → S → Option S
  | [], _ => none
  | (a, b) :: E, x => if a = x then some b else fwdLookup E x

/-- The recorded inverse answer at `y`: the input of the first edge with output `y`. -/
def invLookup : PermLog S → S → Option S
  | [], _ => none
  | (a, b) :: E, y => if b = y then some a else invLookup E y

end Lookup

section Sampling

variable [Fintype S] [DecidableEq S] [SampleableType S]

/-- A uniform draw from the points outside the list `l`, or from all of `S` when `l` covers
`S` (which the lazy permutation never needs: a full range is a full domain). -/
noncomputable def uniformAvoiding (l : List S) : ProbComp S :=
  if h : ∃ y, y ∉ l then
    letI : Nonempty {y // y ∉ l} := ⟨⟨h.choose, h.choose_spec⟩⟩
    letI : SampleableType {y // y ∉ l} := SampleableType.subtype S (· ∉ l)
    Subtype.val <$> ($ᵗ {y // y ∉ l})
  else $ᵗ S

end Sampling

section LazyPerm

variable [Fintype S] [DecidableEq S] [SampleableType S]

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

end LazyPerm

end Common

end

/-! ## The sponge over a permutation; Keccak-256's state, blocks and padding -/

@[expose] public section

namespace Common

/-- A type with an exclusive-or such that `a ^^^ (a ^^^ b) = b`: absorbing a block into a state
is invertible, and the block is recovered from the states before and after. -/
class XorCancel (α : Type) extends XorOp α where
  /-- XOR with `a` is an involution. -/
  xor_cancel : ∀ a b : α, a ^^^ (a ^^^ b) = b

/-- Byte vectors XOR bytewise. -/
instance (n : ℕ) : XorCancel (Vector UInt8 n) where
  xor a b := Vector.zipWith (· ^^^ ·) a b
  xor_cancel a b := by
    apply Vector.ext
    intro i hi
    change (Vector.zipWith (· ^^^ ·) a (Vector.zipWith (· ^^^ ·) a b))[i] = b[i]
    simp only [Vector.getElem_zipWith]
    rw [← UInt8.xor_assoc, UInt8.xor_self, UInt8.zero_xor]

variable {Dg E C : Type}

/-- The state of a sponge with digest part `Dg`, rest of the rate `E` and capacity `C`. -/
abbrev SpState (Dg E C : Type) := (Dg × E) × C

/-- The digest part of a state: the first component of the rate. -/
abbrev SpState.out (s : SpState Dg E C) : Dg := s.1.1

section Xor

variable [XorCancel Dg] [XorCancel E]

/-- XOR on the rate, componentwise. -/
def rxor (a b : Dg × E) : Dg × E := (a.1 ^^^ b.1, a.2 ^^^ b.2)

/-- Absorbing a block: XOR it into the rate, keep the capacity. -/
def absorb (s : SpState Dg E C) (B : Dg × E) : SpState Dg E C := (rxor s.1 B, s.2)

/-- The block that takes the state `s` to the state `x` with the same capacity. -/
def blockTo (s x : SpState Dg E C) : Dg × E := rxor s.1 x.1

/-- Absorb the blocks `bs` from the state `s`: XOR each into the rate and permute with `π`. -/
def absorbAll {m : Type → Type} [Monad m] (π : SpState Dg E C → m (SpState Dg E C)) :
    SpState Dg E C → List (Dg × E) → m (SpState Dg E C)
  | s, [] => pure s
  | s, B :: bs => do
    let y ← π (absorb s B)
    absorbAll π y bs

end Xor

/-- A sponge padding: an injective map from messages to nonempty lists of blocks, with a decoder
that recognises exactly the padded messages. -/
structure Padding (Msg Blk : Type) where
  /-- The padded message, as a list of blocks. -/
  pad : Msg → List Blk
  /-- The decoder: the message whose padding is the given block list, if any. -/
  unpad : List Blk → Option Msg
  /-- The decoder recognises exactly the paddings. -/
  unpad_eq_some_iff : ∀ β m, unpad β = some m ↔ pad m = β
  /-- A padded message has at least one block. -/
  pad_ne_nil : ∀ m, pad m ≠ []

variable [XorCancel Dg] [XorCancel E]

/-- **The sponge.** Absorb the padded message from the initial state `iv` with `π`, and output the
digest part of the final state. -/
def spongeWith {Msg : Type} {m : Type → Type} [Monad m] (P : Padding Msg (Dg × E))
    (iv : SpState Dg E C) (π : SpState Dg E C → m (SpState Dg E C)) (msg : Msg) : m Dg :=
  SpState.out <$> absorbAll π iv (P.pad msg)

/-- A 32-byte Keccak-256 digest. -/
abbrev KDigest := Vector UInt8 32

/-- The rate bytes of the Keccak state after the digest: bytes 32 to 135. -/
abbrev KRest := Vector UInt8 104

/-- The capacity of the Keccak state: bytes 136 to 199 (512 bits). -/
abbrev KCap := Vector UInt8 64

/-- The Keccak-f[1600] state as 200 bytes, split into digest, rest of the rate and capacity.
Byte `i` of the state is byte `i % 8` of lane `i / 8`, little-endian, as in `keccak_hash`. -/
abbrev KState := SpState KDigest KRest KCap

/-- A Keccak-256 block: the 136 rate bytes. -/
abbrev KBlock := KDigest × KRest

/-- The 200 bytes of a Keccak state, in order. -/
def KState.toBytes (s : KState) : List UInt8 := s.1.1.toList ++ s.1.2.toList ++ s.2.toList

/-- The Keccak state of 200 bytes (missing bytes read as zero). -/
def KState.ofBytes (bs : List UInt8) : KState :=
  ((Vector.ofFn fun i : Fin 32 ↦ bs.getD i 0, Vector.ofFn fun i : Fin 104 ↦ bs.getD (32 + i) 0),
    Vector.ofFn fun i : Fin 64 ↦ bs.getD (136 + i) 0)

/-- The all-zero initial state. -/
def KState.zero : KState := ((Vector.replicate 32 0, Vector.replicate 104 0), Vector.replicate 64 0)

/-- The block of the 136 bytes `bs` (missing bytes read as zero). -/
def KBlock.ofBytes (bs : List UInt8) : KBlock :=
  (Vector.ofFn fun i : Fin 32 ↦ bs.getD i 0, Vector.ofFn fun i : Fin 104 ↦ bs.getD (32 + i) 0)

/-- The 136 bytes of a block. -/
def KBlock.toBytes (B : KBlock) : List UInt8 := B.1.toList ++ B.2.toList

/-- The padded message: `msg ‖ 0x01 ‖ 0^* ‖ 0x80`, with `0x01` and `0x80` merged into `0x81` when
`msg` leaves one byte in its last block; the length is the next multiple of 136. -/
def keccakPadBytes (msg : List UInt8) : List UInt8 :=
  if msg.length % 136 = 135 then msg ++ [0x81]
  else msg ++ [0x01] ++ List.replicate (134 - msg.length % 136) 0 ++ [0x80]

/-- Split a byte list into 136-byte blocks. -/
def toBlocks : List UInt8 → List KBlock
  | [] => []
  | b :: bs => KBlock.ofBytes ((b :: bs).take 136) :: toBlocks ((b :: bs).drop 136)
termination_by l => l.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

/-- The bytes of a block list. -/
def blocksToBytes (β : List KBlock) : List UInt8 := β.flatMap KBlock.toBytes

/-- Undo the padding of a padded byte list (arbitrary on other inputs). -/
def stripPad (bs : List UInt8) : List UInt8 :=
  match bs.reverse with
  | 0x81 :: rest => rest.reverse
  | _ :: rest => (((rest.dropWhile (· = 0)).drop 1)).reverse
  | [] => []

/-- The Keccak-256 padding of a message into blocks. -/
def keccakPad (msg : List UInt8) : List KBlock := toBlocks (keccakPadBytes msg)

/-- The Keccak-256 decoder: strip the padding, and accept when it pads back. -/
def keccakUnpad (β : List KBlock) : Option (List UInt8) :=
  let msg := stripPad (blocksToBytes β)
  if keccakPad msg = β then some msg else none

/-- The bytes of a block made of 136 bytes are those bytes. -/
theorem KBlock.toBytes_ofBytes {bs : List UInt8} (h : bs.length = 136) :
    (KBlock.ofBytes bs).toBytes = bs := by
  apply List.ext_getElem
  · simp [KBlock.toBytes, KBlock.ofBytes, h]
  intro i h1 h2
  simp only [KBlock.toBytes, KBlock.ofBytes] at h1 ⊢
  rw [List.getElem_append]
  split_ifs with hi
  · simp only [Vector.toList_ofFn, List.getElem_ofFn]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  · simp only [Vector.toList_ofFn, List.getElem_ofFn, List.length_ofFn]
    simp only [Vector.toList_ofFn, List.length_ofFn] at hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    congr 1
    omega

/-- Splitting a list whose length is a multiple of 136 into blocks and back gives the list. -/
theorem blocksToBytes_toBlocks (bs : List UInt8) (h : bs.length % 136 = 0) :
    blocksToBytes (toBlocks bs) = bs := by
  induction bs using toBlocks.induct with
  | case1 => simp [toBlocks, blocksToBytes]
  | case2 b bs ih =>
    rw [toBlocks]
    simp only [blocksToBytes, List.flatMap_cons] at ih ⊢
    have hlen : 136 ≤ (b :: bs).length := by
      have : 0 < (b :: bs).length := by simp
      omega
    rw [KBlock.toBytes_ofBytes (by simp only [List.length_take]; omega),
      ih (by simp only [List.length_drop]; omega), List.take_append_drop]

/-- The padded bytes have a length that is a positive multiple of 136. -/
theorem keccakPadBytes_length (msg : List UInt8) :
    (keccakPadBytes msg).length = 136 * (msg.length / 136 + 1) := by
  unfold keccakPadBytes
  split_ifs with h
  · simp; omega
  · simp; omega

/-- Stripping the padding recovers the message. -/
theorem stripPad_keccakPadBytes (msg : List UInt8) : stripPad (keccakPadBytes msg) = msg := by
  unfold keccakPadBytes
  split_ifs with h
  · simp [stripPad]
  · have hz : ∀ k, List.dropWhile (· = (0 : UInt8)) (List.replicate k 0 ++ (1 :: msg.reverse)) =
        1 :: msg.reverse := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => simp [List.replicate_succ, ih]
    simp only [stripPad, List.append_assoc, List.cons_append, List.nil_append,
      List.reverse_append, List.reverse_cons, List.reverse_nil, List.reverse_replicate]
    simp [hz]

/-- Padded block lists are never empty. -/
theorem keccakPad_ne_nil (msg : List UInt8) : keccakPad msg ≠ [] := by
  unfold keccakPad
  have hlen := keccakPadBytes_length msg
  cases h : keccakPadBytes msg with
  | nil => rw [h] at hlen; simp at hlen
  | cons b bs => rw [toBlocks]; exact List.cons_ne_nil _ _

/-- The decoder inverts the padding. -/
theorem keccakUnpad_keccakPad (msg : List UInt8) : keccakUnpad (keccakPad msg) = some msg := by
  have hb : blocksToBytes (keccakPad msg) = keccakPadBytes msg :=
    blocksToBytes_toBlocks _ (by rw [keccakPadBytes_length]; omega)
  simp [keccakUnpad, hb, stripPad_keccakPadBytes]

/-- **The Keccak-256 padding**, with its decoder. -/
def keccakPadding : Padding (List UInt8) KBlock where
  pad := keccakPad
  unpad := keccakUnpad
  unpad_eq_some_iff β m := by
    constructor
    · intro h
      simp only [keccakUnpad] at h
      split_ifs at h with hp
      · cases h; exact hp
    · rintro rfl
      exact keccakUnpad_keccakPad m
  pad_ne_nil := keccakPad_ne_nil

end Common

end

/-! ## A cost bounded on every path of a computation -/

@[expose] public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Common

universe u

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {σ α : Type}

/-- A total weight bound: every path of `oa` makes queries of total weight at most `Q`, a query
`t` weighing `w t`. -/
def IsWeightBound (oa : OracleComp spec α) (w : ι → ℕ) (Q : ℕ) : Prop :=
  IsQueryBound oa Q (fun t b ↦ w t ≤ b) (fun t b ↦ b - w t)

end Common

end

/-! ## Bytes as `Fin 256` -/

@[expose] public section

open OracleComp OracleSpec

namespace Common

/-- A byte as a residue. -/
def uInt8EquivFin : UInt8 ≃ Fin 256 where
  toFun b := b.toFin
  invFun f := UInt8.ofFin f
  left_inv _ := rfl
  right_inv _ := rfl

end Common

end

/-! ## A hash query -/

@[expose] public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Common

variable {ι : Type} [DecidableEq ι] {hs : OracleSpec.{0, 0} ι}
  [∀ t : hs.Domain, SampleableType (hs.Range t)] {α : Type}

/-- A hash query, in the random-oracle-model computations over `unifSpec + hs`. -/
abbrev hq (t : ι) : OracleComp (unifSpec + hs) (hs.Range t) := hs.query t

end Common

end

/-! ## Keccak-256 over the random permutation -/

@[expose] public section

open OracleComp OracleSpec

namespace Common

/-- The random oracle `Msg → Dg`. -/
abbrev roSpec (Msg Dg : Type) : OracleSpec Msg := Msg →ₒ Dg

/-- The distinguisher's oracles: uniform coins, the hash `H : Msg → Dg`, and the permutation
`π` and its inverse. -/
abbrev dSpec (Msg Dg St : Type) := unifSpec + (roSpec Msg Dg + permSpec St)

section Setting

variable {Dg E C Msg : Type}
  [XorCancel Dg] [XorCancel E]
  [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [Fintype Dg] [Fintype E] [Fintype C]
  [SampleableType Dg] [SampleableType E] [SampleableType C]

/-- The real world: coins forwarded, `H` the sponge over the lazy random permutation, `π` and
`π⁻¹` the lazy random permutation. -/
noncomputable def realImpl (P : Padding Msg (Dg × E)) (iv : SpState Dg E C) :
    QueryImpl (dSpec Msg Dg (SpState Dg E C)) (StateT (PermLog (SpState Dg E C)) ProbComp)
  | .inl n => liftM (unifSpec.query n : ProbComp (Fin (n + 1)))
  | .inr (.inl m) => spongeWith P iv (fun x ↦ lazyPerm (.fwd x)) m
  | .inr (.inr q) => lazyPerm q

/-- **The real world** run of a distinguisher, from the empty permutation. -/
noncomputable def realGame (P : Padding Msg (Dg × E)) (iv : SpState Dg E C) {α : Type}
    (D : OracleComp (dSpec Msg Dg (SpState Dg E C)) α) : ProbComp α :=
  (simulateQ (realImpl P iv) D).run' []

/-- The simulator's state: the edges it has answered, newest first, and the rooted states with
their paths, newest first, ending with the initial state and the empty path. -/
structure SimState (Dg E C : Type) where
  /-- The answered edges `(x, π x)`, newest first. -/
  edges : PermLog (SpState Dg E C)
  /-- The rooted states with their block paths, newest first. -/
  chains : List (SpState Dg E C × List (Dg × E))

/-- The initial simulator state: no edges, and the initial state rooted at the empty path. -/
def SimState.init (iv : SpState Dg E C) : SimState Dg E C := ⟨[], [(iv, [])]⟩

/-- The rooted state whose capacity is that of `x`, with its path: the first such chain. -/
def chainOf (VC : List (SpState Dg E C × List (Dg × E))) (x : SpState Dg E C) :
    Option (SpState Dg E C × List (Dg × E)) :=
  VC.find? fun p ↦ decide (p.1.2 = x.2)

end Setting

end Common

end

/-! ## The Keccak-256 evaluations a transcript of permutation queries contains -/

@[expose] public section

set_option linter.unusedSectionVars false

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Common

section Setting

variable {Dg E C Msg : Type}
  [XorCancel Dg] [XorCancel E]
  [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [Fintype Dg] [Fintype E] [Fintype C]
  [SampleableType Dg] [SampleableType E] [SampleableType C]
  (P : Padding Msg (Dg × E)) (iv : SpState Dg E C)

/-- One step of the simulator's bookkeeping, replayed from a query and its answer. -/
def replayStep (σ : SimState Dg E C) :
    PermQuery (SpState Dg E C) × SpState Dg E C → SimState Dg E C
  | (.fwd x, y) =>
    match fwdLookup σ.edges x with
    | some _ => σ
    | none =>
      match chainOf σ.chains x with
      | some (s, β) => ⟨(x, y) :: σ.edges, (y, β ++ [blockTo s x]) :: σ.chains⟩
      | none => ⟨(x, y) :: σ.edges, σ.chains⟩
  | (.inv y, x) =>
    match invLookup σ.edges y with
    | some _ => σ
    | none => ⟨(x, y) :: σ.edges, σ.chains⟩

/-- The simulator's bookkeeping replayed from a transcript of permutation queries and answers,
oldest first. -/
def replay (log : List (PermQuery (SpState Dg E C) × SpState Dg E C)) : SimState Dg E C :=
  log.foldl replayStep (SimState.init iv)

/-- The hash queries whose whole sponge paths a simulator state has rooted, with the digests of
the paths' ends. -/
def simPaths (σ : SimState Dg E C) : List (Msg × Dg) :=
  σ.chains.filterMap fun p ↦ (P.unpad p.2).map fun m ↦ (m, p.1.1.1)

/-- **The hash queries of a permutation transcript**: the messages whose whole padded sponge path
the transcript (oldest first) contains as a chain of forward queries from the initial state,
each with the digest part of the path's last answer. -/
def pathsOf (log : List (PermQuery (SpState Dg E C) × SpState Dg E C)) : List (Msg × Dg) :=
  simPaths P (replay iv log)

end Setting

end Common

end

/-! ## The SUF-CMA game of a hash-based signature scheme, in the random-permutation model -/

@[expose] public section

set_option linter.unusedSectionVars false

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Common.SufCma

/-- **The digest bytes as a bit vector**, little endian: byte `i` is bits `8 i … 8 i + 7`
(`digestBitVec_extract`). -/
def digestBitVec : KDigest ≃ BitVec 256 :=
  (arrayVectorEquivFin UInt8 32).trans <|
    (Equiv.arrowCongr (Equiv.refl _) uInt8EquivFin).trans <|
      finFunctionFinEquiv.trans <| (finCongr (show 256 ^ 32 = 2 ^ 256 by norm_num)).trans
        ⟨BitVec.ofFin, BitVec.toFin, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- The oracles of the random-permutation model: coins, Keccak-256 `H`, `π` and `π⁻¹`. -/
abbrev KSpec := dSpec (List UInt8) KDigest KState

/-- A hash `List UInt8 → D`. -/
abbrev HSpec (D : Type) := List UInt8 →ₒ D

/-- **A signature scheme** with hash `H : List UInt8 → D`: a seed sampler, key generation from a
seed, the signer answering a request `Req` with `Resp`, the verifier of a claimed forgery `F`, and
the winning condition on the signing transcript and the forgery. -/
structure Scheme (D Seed PK SK Req Resp F : Type) where
  /-- Sample the secret seed. -/
  sample : ProbComp Seed
  /-- Generate the keys from the seed. -/
  keygen : Seed → OracleComp (HSpec D) (PK × SK)
  /-- Answer a signing request. -/
  sign : SK → Req → OracleComp (HSpec D) Resp
  /-- Verify a claimed forgery. -/
  verify : PK → F → OracleComp (HSpec D) Bool
  /-- The transcript and the forgery make a win (when the forgery verifies). -/
  win : QueryLog (Req →ₒ Resp) → F → Bool

variable {D Seed PK SK Req Resp F : Type}

variable [SampleableType D]

variable (e : KDigest ≃ D)

/-- The hash as Keccak-256 read through `e`, in the random-permutation model. -/
def hashK : QueryImpl (HSpec D) (OracleComp KSpec) :=
  fun m ↦ e <$> (liftM (KSpec.query (.inr (.inl m))) : OracleComp KSpec KDigest)

/-- The signing oracle in the random-permutation model. -/
def signingOracleK (S : Scheme D Seed PK SK Req Resp F) (sk : SK) :
    QueryImpl (Req →ₒ Resp) (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp KSpec)) :=
  QueryImpl.withLogging fun r ↦ simulateQ (hashK e) (S.sign sk r)

/-- **The RPM game**: the game with `H` Keccak-256 over the permutation, read through `e`, and
an adversary that also queries Keccak-256, `π` and `π⁻¹`. -/
noncomputable def rpmGame (S : Scheme D Seed PK SK Req Resp F)
    (main : PK → OracleComp (KSpec + (Req →ₒ Resp)) F) : OracleComp KSpec Bool := do
  let seed ← liftM S.sample
  let (pk, sk) ← simulateQ (hashK e) (S.keygen seed)
  let ((forgery, log) : F × QueryLog (Req →ₒ Resp)) ←
    (simulateQ (QueryImpl.ofLift KSpec (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp KSpec)) +
      signingOracleK e S sk) (main pk)).run
  let verified ← simulateQ (hashK e) (S.verify pk forgery)
  return S.win log forgery && verified

/-- **The RPM experiment**: the RPM game against the lazily sampled random permutation. -/
noncomputable def rpmExperiment (S : Scheme D Seed PK SK Req Resp F)
    (main : PK → OracleComp (KSpec + (Req →ₒ Resp)) F) : ProbComp Bool :=
  realGame keccakPadding KState.zero (rpmGame e S main)

/-- **Calls of the permutation**: a hash of `n` bytes costs `⌊n / 136⌋ + 1` (one per block of the
padded message), a call of `π` or `π⁻¹` one. -/
def permCalls : KSpec.Domain → ℕ
  | .inl _ => 0
  | .inr (.inl m) => m.length / 136 + 1
  | .inr (.inr _) => 1

end Common.SufCma

end

/-! ## Named by LeanDA's code-binding bound: the two-oracle simulator -/

@[expose] public section

set_option linter.unusedSectionVars false

open OracleComp OracleSpec

namespace Common

/-- The random function of the two-oracle model: states to states. -/
abbrev fSpec (St : Type) : OracleSpec St := St →ₒ St

/-- The random oracles of the two-oracle model: `H` and `F`. -/
abbrev hfSpec (Msg Dg St : Type) := roSpec Msg Dg + fSpec St

/-- The game's oracles in the two-oracle model: coins, `H`, `π` and `π⁻¹`, and `F`. -/
abbrev dSpec2 (Msg Dg St : Type) := unifSpec + (roSpec Msg Dg + (permSpec St + fSpec St))

section Setting

variable {Dg E C Msg : Type}
  [XorCancel Dg] [XorCancel E]
  [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [Fintype Dg] [Fintype E] [Fintype C]
  [SampleableType Dg] [SampleableType E] [SampleableType C]
  (P : Padding Msg (Dg × E)) (iv : SpState Dg E C)

/-- The game's direct calls become permutation queries. -/
def toOne : QueryImpl (dSpec2 Msg Dg (SpState Dg E C))
    (OracleComp (dSpec Msg Dg (SpState Dg E C)))
  | .inl n => liftM ((dSpec Msg Dg (SpState Dg E C)).query (.inl n))
  | .inr (.inl m) => liftM ((dSpec Msg Dg (SpState Dg E C)).query (.inr (.inl m)))
  | .inr (.inr (.inl q)) => liftM ((dSpec Msg Dg (SpState Dg E C)).query (.inr (.inr q)))
  | .inr (.inr (.inr x)) => liftM ((dSpec Msg Dg (SpState Dg E C)).query (.inr (.inr (.fwd x))))

/-- **The real world** of the two-oracle model: `F` is the random permutation. -/
noncomputable def realGame2 {α : Type} (D : OracleComp (dSpec2 Msg Dg (SpState Dg E C)) α) :
    ProbComp α :=
  realGame P iv (simulateQ (toOne (E := E) (C := C)) D)

/-- An `H` query of the two-oracle ROM. -/
abbrev hQuery (m : Msg) : OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) Dg :=
  hq (hs := hfSpec Msg Dg (SpState Dg E C)) (.inl m)

/-- An `F` query of the two-oracle ROM. -/
abbrev fQuery (x : SpState Dg E C) :
    OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) (SpState Dg E C) :=
  hq (hs := hfSpec Msg Dg (SpState Dg E C)) (.inr x)

/-- The answer of the two-oracle simulator at a fresh rooted node `x` with path `β`: when `β`
pads a message `m`, `H m` completed by uniform bits; otherwise `F x`. -/
noncomputable def rootedAnswer2 (β : List (Dg × E)) (x : SpState Dg E C) :
    OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) (SpState Dg E C) :=
  match P.unpad β with
  | some m => do
    let d ← hQuery (E := E) (C := C) m
    let ec ← (liftM ($ᵗ (E × C)) : OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) _)
    pure ((d, ec.1), ec.2)
  | none => fQuery (Dg := Dg) x

/-- **The two-oracle simulator**: answers `π` and `π⁻¹` with oracle access to `H` and `F`. -/
noncomputable def simulator2 : QueryImpl (permSpec (SpState Dg E C))
    (StateT (SimState Dg E C) (OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C))))
  | .fwd x => StateT.mk fun σ ↦
      match fwdLookup σ.edges x with
      | some y => pure (y, σ)
      | none =>
        match chainOf σ.chains x with
        | some (s, β) => do
          let y ← rootedAnswer2 P (β ++ [blockTo s x]) x
          pure (y, ⟨(x, y) :: σ.edges, (y, β ++ [blockTo s x]) :: σ.chains⟩)
        | none => do
          let y ← fQuery (Dg := Dg) x
          pure (y, ⟨(x, y) :: σ.edges, σ.chains⟩)
  | .inv y => StateT.mk fun σ ↦
      match invLookup σ.edges y with
      | some x => pure (x, σ)
      | none => do
        let x ← (liftM ($ᵗ (SpState Dg E C)) :
          OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) _)
        pure (x, ⟨(x, y) :: σ.edges, σ.chains⟩)

end Setting

end Common

end

/-! ## Named by LeanDA's code-binding bound: the simulated adversary -/

@[expose] public section

set_option linter.unusedSectionVars false

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Common

section Setting

variable {Dg E C Msg : Type}
  [XorCancel Dg] [XorCancel E]
  [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [Fintype Dg] [Fintype E] [Fintype C]
  [SampleableType Dg] [SampleableType E] [SampleableType C]
  (P : Padding Msg (Dg × E)) (iv : SpState Dg E C)

/-- An honest computation with coins and `H` as a game computation. -/
def hEmbed2 : QueryImpl (unifSpec + roSpec Msg Dg)
    (OracleComp (dSpec2 Msg Dg (SpState Dg E C)))
  | .inl n => liftM ((dSpec2 Msg Dg (SpState Dg E C)).query (.inl n))
  | .inr m => liftM ((dSpec2 Msg Dg (SpState Dg E C)).query (.inr (.inl m)))

/-- An honest computation with coins, `H` and `F` as a game computation. -/
def hfEmbed : QueryImpl (unifSpec + hfSpec Msg Dg (SpState Dg E C))
    (OracleComp (dSpec2 Msg Dg (SpState Dg E C)))
  | .inl n => liftM ((dSpec2 Msg Dg (SpState Dg E C)).query (.inl n))
  | .inr (.inl m) => liftM ((dSpec2 Msg Dg (SpState Dg E C)).query (.inr (.inl m)))
  | .inr (.inr x) => liftM ((dSpec2 Msg Dg (SpState Dg E C)).query (.inr (.inr (.inr x))))

/-- An RPM adversary (coins, `H`, `π`, `π⁻¹`) as a game computation. -/
def advEmbed : QueryImpl (dSpec Msg Dg (SpState Dg E C))
    (OracleComp (dSpec2 Msg Dg (SpState Dg E C)))
  | .inl n => liftM ((dSpec2 Msg Dg (SpState Dg E C)).query (.inl n))
  | .inr (.inl m) => liftM ((dSpec2 Msg Dg (SpState Dg E C)).query (.inr (.inl m)))
  | .inr (.inr q) => liftM ((dSpec2 Msg Dg (SpState Dg E C)).query (.inr (.inr (.inl q))))

/-- **The two-oracle game**: an honest part with `H`, the adversary with `H`, `π`, `π⁻¹`, an
honest part with `H` and `F`. -/
def rpmGame2 {β γ δ : Type} (pre : OracleComp (unifSpec + roSpec Msg Dg) β)
    (A : β → OracleComp (dSpec Msg Dg (SpState Dg E C)) γ)
    (post : β → γ → OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) δ) :
    OracleComp (dSpec2 Msg Dg (SpState Dg E C)) δ :=
  simulateQ (hEmbed2 (E := E) (C := C)) pre >>= fun x ↦
    simulateQ (advEmbed (Msg := Msg)) (A x) >>= fun a ↦ simulateQ (hfEmbed (Msg := Msg)) (post x a)

/-- The adversary's oracles in the two-oracle ROM: coins, `H`, and `π`, `π⁻¹` answered by the
simulator `simulator2` (which queries `H` and `F`). -/
noncomputable def advImpl2 : QueryImpl (dSpec Msg Dg (SpState Dg E C))
    (StateT (SimState Dg E C) (OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C))))
  | .inl n => liftM (liftM (unifSpec.query n : ProbComp (Fin (n + 1))) :
      OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) _)
  | .inr (.inl m) => liftM (hQuery (Msg := Msg) (Dg := Dg) (E := E) (C := C) m)
  | .inr (.inr q) => simulator2 P q

/-- **The ROM adversary of an RPM adversary** in the two-oracle model. -/
noncomputable def advS2 {α : Type} (A : OracleComp (dSpec Msg Dg (SpState Dg E C)) α) :
    OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) α :=
  (simulateQ (advImpl2 P) A).run' (SimState.init iv)

end Setting

end Common

end

/-! ## Named by LeanDA's code-binding bound: the duplex and its simulator -/

@[expose] public section

set_option linter.unusedSectionVars false

open OracleComp OracleSpec

namespace Common.Duplex

/-- **A duplex challenge derivation** with `n` challenges: the label and the initial state, the
absorption of a root (`first`), the step (`next`), the answers as a challenge and the rest
(`build`), the capacity of the rest (`capW`), and the recognition of absorbed roots (`dec`). -/
structure DuplexSpec (Msg Dg St Root Z W Cp : Type) (n : ℕ) where
  /-- The label whose hash seeds the initial state. -/
  label : Msg
  /-- The initial state from the label's hash. -/
  init : Dg → St
  /-- The state absorbing a root after the answer `y₀`. -/
  first : Root → St → St
  /-- The state after an answer, absorbing nothing. -/
  next : St → St
  /-- An answer from its challenge and its rest. -/
  build : Z × W ≃ St
  /-- The capacity of a rest. -/
  capW : W → Cp
  /-- The root a state absorbs after `y₀`, if any. -/
  dec : St → St → Option Root
  dec_iff : ∀ y x r, dec y x = some r ↔ first r y = x
  /-- There is at least one challenge. -/
  n_pos : 0 < n
  /-- Absorbing a root keeps the capacity. -/
  cap_first : ∀ r y, capW (build.symm (first r y)).2 = capW (build.symm y).2
  /-- A step keeps the capacity. -/
  cap_next : ∀ y, capW (build.symm (next y)).2 = capW (build.symm y).2

variable {Msg Dg St Root Z W Cp : Type} {n : ℕ}

namespace DuplexSpec

variable (D : DuplexSpec Msg Dg St Root Z W Cp n)

/-- The capacity of a state. -/
def cap (x : St) : Cp := D.capW (D.build.symm x).2

end DuplexSpec

/-- The two-oracle random-oracle model: coins, `H` and `F`. -/
abbrev Rom2 (Msg Dg St : Type) := unifSpec + hfSpec Msg Dg St

section Programs

variable [DecidableEq Msg] [DecidableEq St]

/-- An `H` query. -/
abbrev hQ (m : Msg) : OracleComp (Rom2 Msg Dg St) Dg :=
  liftM ((Rom2 Msg Dg St).query (.inr (.inl m)))

variable (D : DuplexSpec Msg Dg St Root Z W Cp n)

end Programs

/-- The simulator's state: the answered states with their answers and the challenge they were
programmed with, newest first; the registered steps of the challenge chains; the initial state
and its answer once known; the collision flag. -/
structure SimSt (St Root : Type) (n : ℕ) where
  log : List (St × St × Option (Root × Fin n))
  lab : List (St × (Root × Fin n))
  x0 : Option St
  y0 : Option St
  bad : Bool

/-- The initial simulator state. -/
def SimSt.init : SimSt St Root n := ⟨[], [], none, none, false⟩

section Sim

variable [DecidableEq St] [DecidableEq Root] [DecidableEq Cp]
  (D : DuplexSpec Msg Dg St Root Z W Cp n)

/-- The recorded answer at a state. -/
def SimSt.answer (s : SimSt St Root n) (x : St) : Option St :=
  (s.log.find? (·.1 = x)).map (·.2.1)

/-- The challenges used for programming. -/
def SimSt.used (s : SimSt St Root n) : List (Root × Fin n) := s.log.filterMap (·.2.2)

/-- The registered challenge of a chain state. -/
def SimSt.labOf (s : SimSt St Root n) (x : St) : Option (Root × Fin n) :=
  (s.lab.find? (·.1 = x)).map (·.2)

/-- **The challenge a fresh state would be programmed with**: none at the initial state; `(r, 0)`
at `first r y₀`; else its registered one. -/
def efflab (s : SimSt St Root n) (x : St) : Option (Root × Fin n) :=
  if s.x0 = some x then none
  else match s.y0 with
    | some v => match D.dec v x with
      | some r => some (r, ⟨0, D.n_pos⟩)
      | none => s.labOf x
    | none => s.labOf x

/-- The capacities seen: of the answered states, of their answers, and of the initial state. -/
def forb (s : SimSt St Root n) : Finset Cp :=
  (s.log.map (D.cap ·.1) ++ s.log.map (D.cap ·.2.1) ++ s.x0.toList.map D.cap).toFinset

/-- The state after answering the fresh state `x` with `y`, programmed with `lbl`. -/
def SimSt.record (s : SimSt St Root n) (x y : St) (lbl : Option (Root × Fin n)) :
    SimSt St Root n where
  log := (x, y, lbl) :: s.log
  lab := match lbl with
    | some (r, j) =>
      if h : j.val + 1 < n then
        if s.labOf (D.next y) = none then (D.next y, (r, ⟨j.val + 1, h⟩)) :: s.lab else s.lab
      else s.lab
    | none => s.lab
  x0 := s.x0
  y0 := if s.x0 = some x then some y else s.y0
  bad := s.bad || decide (D.cap y ∈ insert (D.cap x) (forb D s))

variable {ι' : Type} {hs' : OracleSpec ι'} [SampleableType St] [SampleableType W]
  (hQ' : Msg → OracleComp (unifSpec + hs') Dg) (ga : Root → Fin n → OracleComp (unifSpec + hs') Z)

/-- The answer and challenge of a fresh state. -/
noncomputable def freshAns (s : SimSt St Root n) (x : St) :
    OracleComp (unifSpec + hs') (St × Option (Root × Fin n)) :=
  match efflab D s x with
  | some (r, j) =>
    if (r, j) ∈ s.used then (·, none) <$> (liftM ($ᵗ St) : OracleComp (unifSpec + hs') St)
    else do
      let z ← ga r j
      let w ← (liftM ($ᵗ W) : OracleComp (unifSpec + hs') W)
      pure (D.build (z, w), some (r, j))
  | none => (·, none) <$> (liftM ($ᵗ St) : OracleComp (unifSpec + hs') St)

/-- **The simulator** of `F`, forwarding coins and `H` (and recording the initial state when the
label is hashed). -/
noncomputable def simImpl [DecidableEq Msg] :
    QueryImpl (Rom2 Msg Dg St) (StateT (SimSt St Root n) (OracleComp (unifSpec + hs')))
  | .inl k => liftM (liftM (unifSpec.query k : ProbComp (Fin (k + 1))) :
      OracleComp (unifSpec + hs') (Fin (k + 1)))
  | .inr (.inl m) => StateT.mk fun s ↦ do
      let d ← hQ' m
      pure (d, if m = D.label then { s with x0 := some (D.init d) } else s)
  | .inr (.inr x) => StateT.mk fun s ↦
      match s.answer x with
      | some y => pure (y, s)
      | none => do
        let a ← freshAns D ga s x
        pure (a.1, s.record D x a.1 a.2)

end Sim

end Common.Duplex

end

/-! ## Named by LeanDA's code-binding bound: the challenges as a random oracle -/

@[expose] public section

set_option linter.unusedSectionVars false

open OracleComp OracleSpec

namespace Common.Duplex

variable {Msg Dg St Root Z W Cp : Type} {n : ℕ}
  [DecidableEq Msg] [DecidableEq St] [DecidableEq Root] [DecidableEq Cp]
  [SampleableType Dg] [SampleableType St] [SampleableType Z] [SampleableType W]
  [Fintype St] [Fintype Z] [Fintype W]
  (D : DuplexSpec Msg Dg St Root Z W Cp n)

/-- The oracles of the simulated world: coins, `H`, and the challenges `G` on `(r, j)`. -/
abbrev GSpec (Msg Dg Root Z : Type) (n : ℕ) := roSpec Msg Dg + (Root × Fin n →ₒ Z)

/-- `H` in the simulated world. -/
abbrev hP (m : Msg) : OracleComp (unifSpec + GSpec Msg Dg Root Z n) Dg :=
  liftM ((unifSpec + GSpec Msg Dg Root Z n).query (.inr (.inl m)))

/-- A challenge in the simulated world. -/
abbrev gaP (r : Root) (j : Fin n) : OracleComp (unifSpec + GSpec Msg Dg Root Z n) Z :=
  liftM ((unifSpec + GSpec Msg Dg Root Z n).query (.inr (.inr (r, j))))

end Common.Duplex

end

/-! ## Named by LeanDA's code-binding bound: the challenges as one random oracle of vectors -/

@[expose] public section

set_option linter.unusedSectionVars false

open OracleComp OracleSpec
open scoped ENNReal

namespace Common

section Swap

variable {ι₁ ι₂ : Type} [DecidableEq ι₁] [DecidableEq ι₂] {hs₁ : OracleSpec.{0, 0} ι₁}
  {hs₂ : OracleSpec.{0, 0} ι₂} [∀ t : hs₁.Domain, SampleableType (hs₁.Range t)]
  [∀ t : hs₂.Domain, SampleableType (hs₂.Range t)]

/-- The oracles of a sum, in the other order. -/
def swapImpl : QueryImpl (unifSpec + (hs₁ + hs₂)) (OracleComp (unifSpec + (hs₂ + hs₁)))
  | .inl k => liftM ((unifSpec + (hs₂ + hs₁)).query (.inl k))
  | .inr (.inl t) => liftM ((unifSpec + (hs₂ + hs₁)).query (.inr (.inr t)))
  | .inr (.inr t) => liftM ((unifSpec + (hs₂ + hs₁)).query (.inr (.inl t)))

end Swap

end Common

namespace Common.Duplex

variable {Msg Dg Root Z : Type} {n : ℕ}
  [DecidableEq Msg] [DecidableEq Root] [SampleableType Dg] [SampleableType Z]
  [Fintype Z] [Fintype Root] [Nonempty Z]

/-- `H`, and the challenges as one random oracle of vectors. -/
abbrev VSpec (Msg Dg Root Z : Type) (n : ℕ) := roSpec Msg Dg + (Root →ₒ (Fin n → Z))

/-- The challenge `(r, j)` read as component `j` of the vector of `r`. -/
def toV : QueryImpl (unifSpec + GSpec Msg Dg Root Z n) (OracleComp (unifSpec + VSpec Msg Dg Root Z n))
  | .inl k => liftM ((unifSpec + VSpec Msg Dg Root Z n).query (.inl k))
  | .inr (.inl m) => liftM ((unifSpec + VSpec Msg Dg Root Z n).query (.inr (.inl m)))
  | .inr (.inr rj) =>
      (fun v ↦ v rj.2) <$> liftM ((unifSpec + VSpec Msg Dg Root Z n).query (.inr (.inr rj.1)))

end Common.Duplex

end
