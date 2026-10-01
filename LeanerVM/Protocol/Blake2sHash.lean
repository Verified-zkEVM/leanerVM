/-
  LeanerVM.Protocol.Blake2sHash

  BLAKE2s-256 over byte strings, the hash every digest of the proof system is computed with: the
  Merkle leaves and nodes, the transcript's chain and seed. With it, the leaf and node hashes of
  leanVM's Merkle trees and the encoding of a digest as two field elements.
-/

module

public import LeanerVM.Semantics.Blake2s

/-!
# The BLAKE2s byte hasher and the digest encoding

Category B. `blake2sBytes` is RFC 7693 §3.3 over the compression function `compress` of
`LeanerVM.Semantics.Blake2s`: the unkeyed parameter block folded into the first word of `iv`,
every block but the last compressed at the byte count so far with no flag, and the last block,
zero-padded, at the total length with the last-block flag; the empty message is one zero block.
The pinned leanVM computes exactly this (`crates/primitives/src/hash.rs:66-224`, `init_state`,
`Hasher`, `hash`, at `a386121f84292f6fa663aaa3e570c15bc0240ea2`), never setting the last-node
flag, which the `BLAKE2S` opcode alone takes as an input.

The Merkle hashes are those of `crates/fiat_shamir/src/merkle.rs:40-67`: a leaf is the hash of
its `K` words as little-endian bytes (`hash_words`), a node the hash of the 64 bytes of its two
children (`hash_pair`). The digest encoding is `merkle.rs:14-36`: a digest travels as two
elements of `E`, each holding sixteen bytes in its two low limbs with the top limb `0`
(`hash_to_scalars`), and the decoder rejects a nonzero top limb (`scalars_to_hash`), since the
two halves come off the proof stream.

A digest is its eight chaining words; `digestBytes` is its byte form.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics

@[expose] public section

/-- A BLAKE2s-256 digest, as the eight chaining words of its last compression. -/
abbrev Digest := Vector UInt32 8

/-- Digest equality decided on the word lists, usable from a module file, where core's
`DecidableEq` for `Vector` is not exposed. -/
def Digest.decEq : DecidableEq Digest := fun a b ↦
  decidable_of_iff (a.toList = b.toList) Vector.toList_inj

namespace Blake2sHash

/-! ## RFC 7693 §3.3 -/

/-- The last-block flag word. -/
def lastBlock : UInt32 := 0xFFFFFFFF

/-- The initial chaining value of an unkeyed BLAKE2s-256: `iv` with the parameter block
`0x01010020` (digest length 32, key length 0, fanout 1, depth 1; RFC 7693 §2.8) XORed into word 0
(`hash.rs:66-81`, `init_state`, `PARAM_IV`). -/
def paramIv : Vector UInt32 8 := iv.set 0 (iv[0] ^^^ 0x01010020)

/-- A little-endian word from four bytes. -/
def leWord (b0 b1 b2 b3 : UInt8) : UInt32 :=
  b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)

/-- The sixteen little-endian words of a block of at most 64 bytes, zero-padded
(`hash.rs:118-120`, `block_words`). -/
def blockWords (block : List UInt8) : Vector UInt32 16 :=
  let b := fun i ↦ block.getD i 0
  #v[leWord (b 0) (b 1) (b 2) (b 3), leWord (b 4) (b 5) (b 6) (b 7),
     leWord (b 8) (b 9) (b 10) (b 11), leWord (b 12) (b 13) (b 14) (b 15),
     leWord (b 16) (b 17) (b 18) (b 19), leWord (b 20) (b 21) (b 22) (b 23),
     leWord (b 24) (b 25) (b 26) (b 27), leWord (b 28) (b 29) (b 30) (b 31),
     leWord (b 32) (b 33) (b 34) (b 35), leWord (b 36) (b 37) (b 38) (b 39),
     leWord (b 40) (b 41) (b 42) (b 43), leWord (b 44) (b 45) (b 46) (b 47),
     leWord (b 48) (b 49) (b 50) (b 51), leWord (b 52) (b 53) (b 54) (b 55),
     leWord (b 56) (b 57) (b 58) (b 59), leWord (b 60) (b 61) (b 62) (b 63)]

/-- Absorb `data` into the chaining value `h` after `t` bytes: `blocks` more non-final blocks of
64 bytes, each compressed at the byte count including it with no flag, then the rest as the
final block, zero-padded, compressed at the total length with the last-block flag
(RFC 7693 §3.3; `hash.rs:176-199`, `Hasher.update` and `finalize`). -/
def absorb (h : Vector UInt32 8) (t : ℕ) : (blocks : ℕ) → List UInt8 → Digest
  | 0, data => compress h (blockWords data) (t + data.length).toUInt64 lastBlock 0
  | blocks + 1, data =>
    absorb (compress h (blockWords (data.take 64)) (t + 64).toUInt64 0 0) (t + 64) blocks
      (data.drop 64)

/-- BLAKE2s-256 of a byte string (`hash.rs:209-224`, `hash`): `⌈len/64⌉ - 1` non-final blocks,
then the final one; the empty string is one zero block at counter `0`. -/
def blake2sBytes (data : List UInt8) : Digest :=
  absorb paramIv 0 ((data.length - 1) / 64) data

/-! ## Bytes of words and digests -/

/-- The four little-endian bytes of a word. -/
def wordBytes (w : UInt32) : List UInt8 :=
  [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8, (w >>> 24).toUInt8]

/-- The 32 bytes of a digest: its words, little-endian (`hash.rs:124-130`, `state_bytes`). -/
def digestBytes (d : Digest) : List UInt8 := d.toList.flatMap wordBytes

/-- The eight little-endian bytes of a `K` word (`merkle.rs:61-67`, `hash_words`). -/
def kBytes (a : K) : List UInt8 := wordBytes (lowWord a) ++ wordBytes (highWord a)

/-! ## The Merkle hashes -/

/-- The digest of a leaf: BLAKE2s-256 of its words as bytes (`merkle.rs:61-67`, `hash_words`). -/
def hashWords (words : List K) : Digest := blake2sBytes (words.flatMap kBytes)

/-- The digest of a node: BLAKE2s-256 of the 64 bytes of its two children, left first
(`merkle.rs:46-51`, `hash_pair`). -/
def hashPair (left right : Digest) : Digest :=
  blake2sBytes (digestBytes left ++ digestBytes right)

/-! ## The digest encoding (`merkle.rs:14-36`) -/

/-- A digest as the two field elements a transcript carries it in: bytes `0..16` and `16..32`,
each as a canonical 128-bit cell (`hash_to_scalars`). -/
def digestScalars (d : Digest) : E × E :=
  (wordsCell #v[d[0], d[1], d[2], d[3]], wordsCell #v[d[4], d[5], d[6], d[7]])

/-- The digest two field elements encode, or `none` if either has a nonzero top limb
(`scalars_to_hash`, `Error::NonCanonicalEncoding`). -/
def digestOfScalars (s : E × E) : Option Digest :=
  if IsCanonical128 s.1 ∧ IsCanonical128 s.2 then some (cellWords s.1 ++ cellWords s.2) else none

/-! ## Load-bearing lemmas -/

theorem lowWord_ofWords (lo hi : UInt32) : lowWord (ofWords lo hi) = lo := by
  apply UInt32.toBitVec_inj.mp
  simp only [lowWord, ofWords, UInt32.toBitVec_ofBitVec, BF64.toBitVec_ofBitVec]
  exact BitVec.extractLsb'_append_eq_right

theorem highWord_ofWords (lo hi : UInt32) : highWord (ofWords lo hi) = hi := by
  apply UInt32.toBitVec_inj.mp
  simp only [highWord, ofWords, UInt32.toBitVec_ofBitVec, BF64.toBitVec_ofBitVec]
  exact BitVec.extractLsb'_append_eq_left

/-- A four-word vector is the vector of its four words. -/
private theorem vector4_eta {α : Type} (v : Vector α 4) : #v[v[0], v[1], v[2], v[3]] = v := by
  ext i hi
  rcases i with _ | _ | _ | _ | i <;> first | rfl | omega

/-- Reading the words of the cell built from four words gives the words back. -/
theorem cellWords_wordsCell (w : Vector UInt32 4) : cellWords (wordsCell w) = w := by
  simp only [cellWords, wordsCell, limb_ofLimbs, lowWord_ofWords, highWord_ofWords,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  exact vector4_eta w

/-- The cell built from four words is canonical. -/
theorem isCanonical128_wordsCell (w : Vector UInt32 4) : IsCanonical128 (wordsCell w) := by
  show (E.ofLimbs _ _ 0).limb 2 = 0
  rw [limb_ofLimbs]; rfl

/-- Decoding the encoding of a digest gives the digest back. -/
theorem digestOfScalars_digestScalars (d : Digest) :
    digestOfScalars (digestScalars d) = some d := by
  simp only [digestOfScalars, digestScalars, isCanonical128_wordsCell, and_self, ↓reduceIte,
    cellWords_wordsCell, Option.some.injEq]
  ext i hi
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;> first | rfl | omega

/-- The first four words of the concatenation of two four-word vectors. -/
private theorem append_left4 {α : Type} (x y : Vector α 4) :
    #v[(x ++ y)[0], (x ++ y)[1], (x ++ y)[2], (x ++ y)[3]] = x := by
  rw [Vector.getElem_append_left (show 0 < 4 by decide),
    Vector.getElem_append_left (show 1 < 4 by decide),
    Vector.getElem_append_left (show 2 < 4 by decide),
    Vector.getElem_append_left (show 3 < 4 by decide)]
  exact vector4_eta x

/-- The last four words of the concatenation of two four-word vectors. -/
private theorem append_right4 {α : Type} (x y : Vector α 4) :
    #v[(x ++ y)[4], (x ++ y)[5], (x ++ y)[6], (x ++ y)[7]] = y := by
  rw [Vector.getElem_append_right (show 4 < 4 + 4 by decide) (show 4 ≤ 4 by decide),
    Vector.getElem_append_right (show 5 < 4 + 4 by decide) (show 4 ≤ 5 by decide),
    Vector.getElem_append_right (show 6 < 4 + 4 by decide) (show 4 ≤ 6 by decide),
    Vector.getElem_append_right (show 7 < 4 + 4 by decide) (show 4 ≤ 7 by decide)]
  exact vector4_eta y

/-- Encoding a decoded pair gives the pair back: the encoding is a bijection between digests and
pairs of canonical cells. -/
theorem digestScalars_digestOfScalars {s : E × E} {d : Digest}
    (h : digestOfScalars s = some d) : digestScalars d = s := by
  obtain ⟨a, b⟩ := s
  unfold digestOfScalars at h
  split at h
  · rename_i hc
    have ha : IsCanonical128 a := hc.1
    have hb : IsCanonical128 b := hc.2
    rw [Option.some.injEq] at h
    subst h
    show (wordsCell _, wordsCell _) = (a, b)
    rw [append_left4, append_right4, wordsCell_cellWords ha, wordsCell_cellWords hb]
  · exact absurd h (by simp)

end Blake2sHash

end
end LeanerVM.Protocol
