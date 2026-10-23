/-
  LeanVM.Spec.Keccak

  Keccak: the permutation Keccak-f[1600], which the ISA's `KECCAK` instruction computes and the
  verifier's Fiat-Shamir sponge runs on, and Keccak-256 over byte strings (Ethereum's), the hash
  of the verifier's Merkle trees and digests.
-/

module

public import LeanVM.Spec.Field

/-!
# Keccak

Transcribed from `python-verifier/verifier.py` at leanVM
`3375f7a137c50b803f3416f6466b5d4e0719708a` (branch `keccak-gkr`): the round constants, rotation
offsets and lane permutation (`KECCAK_RC`, `KECCAK_RHO`, `KECCAK_PI`, `verifier.py:1191-1198`),
the permutation `keccak_f` (`verifier.py:361-376`), and the hash `keccak_hash`
(`verifier.py:191-207`): Keccak-256 as Ethereum computes it, rate `136` bytes, the message padded
with `0x01 ‖ 0^* ‖ 0x80` (FIPS 202's SHA3-256 would put `0x06` first). The Rust is
`crates/verifier/src/hash.rs` and `crates/primitives/src/hash/`.

A state is `25` lanes of `64` bits, lane `x + 5y` at index `x + 5y`. A lane is a `UInt64` here
and a `K` word inside the machine (`K.ofLane`, `K.lane`: bit `i` of the lane is the coefficient
of `x^i`). Then the byte and field encodings the verifier hashes: a `K` word as eight
little-endian bytes, the Merkle leaf and node hashes, and a digest as two field elements.
-/

namespace LeanVM.Parameters

@[expose] public section

/-- `KECCAK_RC` (`verifier.py:1191-1196`): the round constants of the `24` rounds. -/
def keccakRC : List UInt64 := [
  0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
  0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- `KECCAK_RHO` (`verifier.py:1197`): the rotation of each lane, by index `x + 5y`. -/
def keccakRho : List ℕ :=
  [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]

/-- `KECCAK_PI` (`verifier.py:1198`): where lane `i = x + 5y` lands,
`i // 5 + 5 · ((2 · (i % 5) + 3 · (i // 5)) % 5)`. -/
def keccakPi (i : ℕ) : ℕ := i / 5 + 5 * ((2 * (i % 5) + 3 * (i / 5)) % 5)

/-- A `K` word from a 64-bit lane: bit `i` of the lane is the coefficient of `x^i`. -/
def K.ofLane (w : UInt64) : K := BF64.ofBitVec w.toBitVec

/-- The 64-bit lane of a `K` word (`K.__index__`). -/
def K.lane (a : K) : UInt64 := ⟨a.toBitVec⟩

end
end LeanVM.Parameters

namespace LeanVM.Semantics

open LeanVM.Parameters

@[expose] public section

/-! ## Keccak-f[1600] -/

/-- A Keccak state: `25` lanes of `64` bits, lane `x + 5y` at index `x + 5y`. -/
abbrev KState := Vector UInt64 25

namespace Keccak

/-- Lane `i` of a state, `0` past the end. -/
def lane (a : KState) (i : ℕ) : UInt64 := a.toArray.getD i 0

/-- `rot(x, n)`: rotate a lane left by `n < 64` bits (`verifier.py:365-366`). -/
def rot (x : UInt64) (n : ℕ) : UInt64 :=
  if n = 0 then x else (x <<< n.toUInt64) ||| (x >>> (64 - n).toUInt64)

/-- One round of `keccak_f` with the round constant `rc` (`verifier.py:369-375`): θ, then ρ and π
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

/-- **Keccak-f[1600]** (`keccak_f`, `verifier.py:361-376`): the `24` rounds. -/
def keccakF (a : KState) : KState := keccakRC.foldl Keccak.round a

end
end LeanVM.Semantics

namespace LeanVM.Protocol

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-- A Keccak-256 digest: its `32` bytes as four little-endian 64-bit words, the first four lanes of
the last state (`Digest.words`, `verifier.py:219-221`). -/
abbrev Digest := Vector UInt64 4

/-- Digest equality decided on the word lists, usable from a module file, where core's
`DecidableEq` for `Vector` is not exposed. -/
def Digest.decEq : DecidableEq Digest := fun a b ↦
  decidable_of_iff (a.toList = b.toList) Vector.toList_inj

namespace KeccakHash

/-! ## Keccak-256 (`keccak_hash`, `verifier.py:191-207`) -/

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
(`verifier.py:205-206`). -/
def absorbBlock (state : KState) (block : List UInt8) : KState :=
  keccakF (Vector.ofFn fun i ↦
    if i.val < 17 then Keccak.lane state i ^^^ leLane block i else Keccak.lane state i)

/-- The last block: the remaining `0` to `135` bytes, `PAD_FIRST` after them, zeros, and
`PAD_LAST` XORed into the block's last byte (one byte `0x81` when `135` bytes remain)
(`verifier.py:201-203`). -/
def padBlock (rest : List UInt8) : List UInt8 :=
  ((rest ++ List.replicate (rate - rest.length) 0).modify rest.length (· ^^^ padFirst)).modify
    (rate - 1) (· ^^^ padLast)

/-- Absorb `data` into `state`: `blocks` whole blocks of `136` bytes, then the padded last block,
which holds the remaining `0` to `135` bytes. -/
def absorb : (blocks : ℕ) → KState → List UInt8 → KState
  | 0, state, data => absorbBlock state (padBlock data)
  | blocks + 1, state, data => absorb blocks (absorbBlock state (data.take rate)) (data.drop rate)

/-- **Keccak-256 of a byte string** (`keccak_hash`, `verifier.py:198-207`): `⌊len/136⌋` whole
blocks, then the padded last one, from the zero state; the digest is the first four lanes. The
Python pads the whole string first (`len // RATE + 1` blocks); the blocks are the same. -/
def keccak256 (data : List UInt8) : Digest :=
  let state := absorb (data.length / rate) (Vector.replicate 25 0) data
  #v[Keccak.lane state 0, Keccak.lane state 1, Keccak.lane state 2, Keccak.lane state 3]

/-! ## Bytes of words and digests -/

/-- The eight little-endian bytes of a 64-bit word. -/
def wordBytes (w : UInt64) : List UInt8 :=
  (List.range 8).map fun k ↦ (w >>> (8 * k).toUInt64).toUInt8

/-- The 32 bytes of a digest: its words, little-endian (`Digest.value`, `verifier.py:207`). -/
def digestBytes (d : Digest) : List UInt8 := d.toList.flatMap wordBytes

/-- The eight little-endian bytes of a `K` word (`K.to_bytes`, `verifier.py:50-52`). -/
def kBytes (a : K) : List UInt8 := wordBytes a.lane

/-! ## The Merkle hashes (`Transcript.merkle`, `verifier.py:434-446`) -/

/-- The digest of a leaf: Keccak-256 of its words as bytes. -/
def hashWords (words : List K) : Digest := keccak256 (words.flatMap kBytes)

/-- The digest of a node: Keccak-256 of the 64 bytes of its two children, left first. -/
def hashPair (left right : Digest) : Digest := keccak256 (digestBytes left ++ digestBytes right)

/-! ## The digest encoding (`Digest.halves`, `Digest.from_halves`, `verifier.py:223-231`) -/

/-- A digest as the two field elements a transcript carries it in, its 128-bit halves
`E(w0, w1)`, `E(w2, w3)` (`halves`). -/
def digestScalars (d : Digest) : E × E :=
  (E.ofLimbs (K.ofLane d[0]) (K.ofLane d[1]) 0, E.ofLimbs (K.ofLane d[2]) (K.ofLane d[3]) 0)

/-- The digest two field elements encode, or `none` if either has a nonzero top limb
(`from_halves`). -/
def digestOfScalars (s : E × E) : Option Digest :=
  if IsCanonical128 s.1 ∧ IsCanonical128 s.2 then
    some #v[(s.1.limb 0).lane, (s.1.limb 1).lane, (s.2.limb 0).lane, (s.2.limb 1).lane]
  else none

end KeccakHash

end
end LeanVM.Protocol
