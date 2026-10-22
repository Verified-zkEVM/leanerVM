/-
  LeanerVM.Protocol.Blake2sHash

  BLAKE2s-256 over byte strings, the hash every digest of the proof system is computed with: the
  Merkle leaves and nodes, the transcript's chain and seed. With it, the leaf and node hashes of
  leanVM's Merkle trees and the encoding of a digest as two field elements.
-/

module

public import LeanerVM.Semantics.Blake2s
public import LeanerVM.Semantics.Blake2sFast

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
  Vector.ofFn fun j ↦ leWord (b (4 * j)) (b (4 * j + 1)) (b (4 * j + 2)) (b (4 * j + 3))

/-- Absorb `data` into the chaining value `h` after `t` bytes: `blocks` more non-final blocks of
64 bytes, each compressed at the byte count including it with no flag, then the rest as the
final block, zero-padded, compressed at the total length with the last-block flag
(RFC 7693 §3.3; `hash.rs:176-199`, `Hasher.update` and `finalize`). It hashes `data` only when
`blocks` is `(data.length - 1) / 64`, the count `blake2sBytes` passes; with fewer, the final
block is truncated to 64 bytes. -/
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

/-- The digest whose bytes begin a byte string: eight little-endian words, missing bytes read as
zero. It inverts `digestBytes` (`digestOfBytes_digestBytes`). -/
def digestOfBytes (b : List UInt8) : Digest :=
  Vector.ofFn fun j : Fin 8 ↦
    leWord (b.getD (4 * j) 0) (b.getD (4 * j + 1) 0) (b.getD (4 * j + 2) 0) (b.getD (4 * j + 3) 0)

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

/-! ## The encoding round trip -/

private theorem lowWord_ofWords (lo hi : UInt32) : lowWord (ofWords lo hi) = lo := by
  apply UInt32.toBitVec_inj.mp
  simp only [lowWord, ofWords, UInt32.toBitVec_ofBitVec, BF64.toBitVec_ofBitVec]
  exact BitVec.extractLsb'_append_eq_right

private theorem highWord_ofWords (lo hi : UInt32) : highWord (ofWords lo hi) = hi := by
  apply UInt32.toBitVec_inj.mp
  simp only [highWord, ofWords, UInt32.toBitVec_ofBitVec, BF64.toBitVec_ofBitVec]
  exact BitVec.extractLsb'_append_eq_left

/-- A four-word vector is the vector of its four words. -/
private theorem vector4_eta {α : Type} (v : Vector α 4) : #v[v[0], v[1], v[2], v[3]] = v := by
  ext i hi
  rcases i with _ | _ | _ | _ | i <;> first | rfl | omega

/-- Reading the words of the cell built from four words gives the words back. -/
private theorem cellWords_wordsCell (w : Vector UInt32 4) : cellWords (wordsCell w) = w := by
  simp only [cellWords, wordsCell, limb_ofLimbs, lowWord_ofWords, highWord_ofWords,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  exact vector4_eta w

/-- The cell built from four words is canonical. -/
private theorem isCanonical128_wordsCell (w : Vector UInt32 4) :
    IsCanonical128 (wordsCell w) := by
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
    cases h
    show (wordsCell _, wordsCell _) = (a, b)
    rw [append_left4, append_right4, wordsCell_cellWords hc.1, wordsCell_cellWords hc.2]
  · cases h

/-! ## The byte round trip -/

/-- A word read back from its four little-endian bytes. -/
private theorem leWord_wordBytes (w : UInt32) :
    leWord w.toUInt8 (w >>> 8).toUInt8 (w >>> 16).toUInt8 (w >>> 24).toUInt8 = w := by
  apply UInt32.toBitVec_inj.mp
  simp only [leWord, UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, UInt8.toBitVec_toUInt32,
    UInt32.toBitVec_toUInt8, UInt32.toBitVec_shiftRight]
  ext i hi
  simp [BitVec.getElem_or, BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight]
  rw [← BitVec.getLsbD_eq_getElem]
  by_cases h1 : i < 8
  · simp only [h1, decide_true, Bool.true_and, Bool.not_true, Bool.false_and, Bool.or_false,
      show i < 16 by omega, show i < 24 by omega]
  by_cases h2 : i < 16
  · simp only [h1, h2, decide_true, decide_false, Bool.true_and, Bool.not_true, Bool.not_false,
      Bool.false_and, Bool.or_false, Bool.false_or, show i < 24 by omega,
      show i - 8 < 8 by omega, show 8 + (i - 8) = i by omega]
  by_cases h3 : i < 24
  · simp only [h1, h2, h3, decide_true, decide_false, Bool.true_and, Bool.not_false,
      Bool.not_true, Bool.false_and, Bool.or_false, Bool.false_or, show ¬ i - 8 < 8 by omega,
      show i - 16 < 8 by omega, show 16 + (i - 16) = i by omega]
  · simp only [h1, h2, h3, decide_true, decide_false, Bool.true_and, Bool.not_false,
      Bool.false_and, Bool.false_or, show ¬ i - 8 < 8 by omega, show ¬ i - 16 < 8 by omega,
      show i - 24 < 8 by omega, show 24 + (i - 24) = i by omega]

/-- Byte `4j + r` of the bytes of a word list is byte `r` of word `j`. -/
private theorem getD_flatMap_wordBytes :
    ∀ (l : List UInt32) (j r : ℕ) (hj : j < l.length), r < 4 →
      (l.flatMap wordBytes).getD (4 * j + r) 0 = (wordBytes l[j]).getD r 0
  | [], _, _, h, _ => absurd h (by simp)
  | w :: l, 0, r, _, hr => by
    have hlen : (wordBytes w).length = 4 := rfl
    simp only [Nat.mul_zero, Nat.zero_add]
    rw [List.flatMap_cons, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [hlen]; omega), ← List.getD_eq_getElem?_getD]
    rfl
  | w :: l, j + 1, r, h, hr => by
    have hlen : (wordBytes w).length = 4 := rfl
    rw [List.flatMap_cons, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [hlen]; omega), hlen,
      show 4 * (j + 1) + r - 4 = 4 * j + r by omega, ← List.getD_eq_getElem?_getD,
      getD_flatMap_wordBytes l j r (by simpa using h) hr]
    rfl

/-- A digest has 32 bytes. -/
theorem length_digestBytes (d : Digest) : (digestBytes d).length = 32 := by
  simp [digestBytes, wordBytes, List.length_flatMap]

/-- Reading the bytes of a digest gives the digest back. -/
theorem digestOfBytes_digestBytes (d : Digest) : digestOfBytes (digestBytes d) = d := by
  ext j hj
  simp only [digestOfBytes, digestBytes, Vector.getElem_ofFn]
  have hl : j < d.toList.length := by simpa using hj
  have h0 := getD_flatMap_wordBytes _ j 0 hl (by omega)
  rw [Nat.add_zero] at h0
  rw [h0, getD_flatMap_wordBytes _ j 1 hl (by omega), getD_flatMap_wordBytes _ j 2 hl (by omega),
    getD_flatMap_wordBytes _ j 3 hl (by omega)]
  simp only [wordBytes, List.getD_cons_zero, List.getD_cons_succ, Vector.getElem_toList]
  exact leWord_wordBytes d[j]

end Blake2sHash

end
end LeanerVM.Protocol
