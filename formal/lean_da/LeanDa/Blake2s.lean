module

public import Mathlib.Data.Vector.Basic

/-!
# BLAKE2s-256

RFC 7693, as `crates/primitives/src/hash/mod.rs` computes it at leanVM `b64b3d41f`: the
constants (`IV`, `SIGMA`, lines 31-61), the compression function (`compress`, lines 91-117), the
unkeyed initial chaining value (`PARAM_IV`, lines 78-83), and the one-shot hash of a byte string
(`Hasher::update` and `finalize`, lines 157-193): every 64-byte block but the last compressed at
the byte count including it, then the last, zero-padded, at the total length with the final flag.
The empty string is one zero block at counter `0`. The digest is the chaining value's eight words,
little-endian (`state_bytes`, lines 126-132).

The security statements of this project hold for every hash function; BLAKE2s enters only as the
function a collision is found for.
-/

namespace LeanDa.Blake2s

@[expose] public section

/-- `IV[i] = ⌊2^32 · frac(√pᵢ₊₁)⌋` for the first eight primes (`IV`). -/
def iv : Vector UInt32 8 := #v[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- `sigma[r]` permutes the sixteen message words of round `r` (`SIGMA`). -/
def sigma : Vector (Vector (Fin 16) 16) 10 := #v[
  #v[ 0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15],
  #v[14, 10,  4,  8,  9, 15, 13,  6,  1, 12,  0,  2, 11,  7,  5,  3],
  #v[11,  8, 12,  0,  5,  2, 15, 13, 10, 14,  3,  6,  7,  1,  9,  4],
  #v[ 7,  9,  3,  1, 13, 12, 11, 14,  2,  6,  5, 10,  4,  0, 15,  8],
  #v[ 9,  0,  5,  7,  2,  4, 10, 15, 14,  1, 11, 12,  6,  8,  3, 13],
  #v[ 2, 12,  6, 10,  0, 11,  8,  3,  4, 13,  7,  5, 15, 14,  1,  9],
  #v[12,  5,  1, 15, 14, 13,  4, 10,  0,  7,  6,  3,  9,  2,  8, 11],
  #v[13, 11,  7, 14, 12,  1,  3,  9,  5,  0, 15,  4,  8,  6,  2, 10],
  #v[ 6, 15, 14,  9, 11,  3,  0,  8, 12,  2, 13,  7,  1,  4, 10,  5],
  #v[10,  2,  8,  4,  7,  6,  1,  5, 15, 11,  9, 14,  3, 12, 13,  0]]

/-- Rotate right by `n` bits. -/
def rotr (x : UInt32) (n : ℕ) : UInt32 := ⟨x.toBitVec.rotateRight n⟩

/-- The mixing function `G` on lanes `a, b, c, d` with message words `x, y`. -/
def mix (v : Vector UInt32 16) (a b c d : Fin 16) (x y : UInt32) : Vector UInt32 16 :=
  let va := v[a] + v[b] + x
  let vd := rotr (v[d] ^^^ va) 16
  let vc := v[c] + vd
  let vb := rotr (v[b] ^^^ vc) 12
  let va := va + vb + y
  let vd := rotr (vd ^^^ va) 8
  let vc := vc + vd
  let vb := rotr (vb ^^^ vc) 7
  (((v.set a va).set b vb).set c vc).set d vd

/-- One round: four column and four diagonal mixes (`G_LANES`), message words chosen by `s`. -/
def round (v m : Vector UInt32 16) (s : Vector (Fin 16) 16) : Vector UInt32 16 :=
  let v := mix v 0 4 8 12 m[s[0]] m[s[1]]
  let v := mix v 1 5 9 13 m[s[2]] m[s[3]]
  let v := mix v 2 6 10 14 m[s[4]] m[s[5]]
  let v := mix v 3 7 11 15 m[s[6]] m[s[7]]
  let v := mix v 0 5 10 15 m[s[8]] m[s[9]]
  let v := mix v 1 6 11 12 m[s[10]] m[s[11]]
  let v := mix v 2 7 8 13 m[s[12]] m[s[13]]
  mix v 3 4 9 14 m[s[14]] m[s[15]]

/-- The compression of block `m` into the chaining value `h` at byte counter `t`, with the
final-block flag when `last` (`compress`). -/
def compress (h : Vector UInt32 8) (m : Vector UInt32 16) (t : UInt64) (last : Bool) :
    Vector UInt32 8 :=
  let v : Vector UInt32 16 := h ++ iv
  let v := v.set 12 (v[12] ^^^ t.toUInt32)
  let v := v.set 13 (v[13] ^^^ (t >>> 32).toUInt32)
  let v := if last then v.set 14 (~~~ v[14]) else v
  let v := sigma.foldl (fun v s ↦ round v m s) v
  Vector.ofFn fun i : Fin 8 ↦ h[i] ^^^ v[i] ^^^ v[i.val + 8]

/-- The initial chaining value of unkeyed BLAKE2s-256: `iv` with the parameter block
`0x01010020` (digest length 32, key length 0, fanout 1, depth 1) in word 0 (`PARAM_IV`). -/
def paramIv : Vector UInt32 8 := iv.set 0 (iv[0] ^^^ 0x01010020)

/-- A little-endian word from four bytes. -/
def leWord (b0 b1 b2 b3 : UInt8) : UInt32 :=
  b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)

/-- The sixteen little-endian words of a block of at most 64 bytes, zero-padded
(`block_words`). -/
def blockWords (block : List UInt8) : Vector UInt32 16 :=
  Vector.ofFn fun i : Fin 16 ↦
    leWord (block.getD (4 * i) 0) (block.getD (4 * i + 1) 0) (block.getD (4 * i + 2) 0)
      (block.getD (4 * i + 3) 0)

/-- Absorb `data` into `h` after `t` bytes: `blocks` more blocks of 64 bytes, each compressed at
the count including it without the flag, then the rest as the final block. -/
def absorb (h : Vector UInt32 8) (t : ℕ) : (blocks : ℕ) → List UInt8 → Vector UInt32 8
  | 0, data => compress h (blockWords data) (t + data.length).toUInt64 true
  | blocks + 1, data =>
    absorb (compress h (blockWords (data.take 64)) (t + 64).toUInt64 false) (t + 64) blocks
      (data.drop 64)

/-- The 32 bytes of a chaining value, its words little-endian (`state_bytes`). -/
def stateBytes (h : Vector UInt32 8) : Vector UInt8 32 :=
  Vector.ofFn fun i : Fin 32 ↦ (h[i.val / 4]'(by omega) >>> (8 * (i.val % 4)).toUInt32).toUInt8

end

end LeanDa.Blake2s

namespace LeanDa

@[expose] public section

/-- A BLAKE2s-256 digest (`fiat_shamir::merkle::Hash`, `[u8; 32]`). -/
abbrev Digest := Vector UInt8 32

/-- **BLAKE2s-256 of a byte string** (`primitives::hash::hash`): `⌈len/64⌉ - 1` non-final
blocks, then the final one. -/
def blake2s (data : List UInt8) : Digest :=
  Blake2s.stateBytes (Blake2s.absorb Blake2s.paramIv 0 ((data.length - 1) / 64) data)

end

end LeanDa
