/-
  LeanerVM.Protocol.Blake2sHashFast

  The byte hasher and the Merkle node hash without the quadratic byte reads, proved equal to
  `blake2sBytes`, `hashWords` and `hashPair` and registered for compiled code.
-/

module

public import LeanerVM.Protocol.Blake2sHash

/-!
# Faster byte hashing

`blockWords` reads its bytes with `List.getD`, so a block costs a quadratic number of list steps,
and `hashPair` writes two digests out as 64 bytes only for `blockWords` to read them back.
`blockWordsFast` reads through an array, and `hashPairFast` compresses the sixteen digest words
directly: the bytes of a word, read back little-endian, are the word (`leWord_wordBytes`). The
`@[csimp]` theorems substitute `blake2sBytesFast`, `hashWordsFast` and `hashPairFast` in code
compiled after this module, such as `merkleRoot`. The specifications are unchanged.
-/

namespace LeanerVM.Protocol.Blake2sHash

open LeanerVM.Parameters LeanerVM.Semantics

@[expose] public section

/-- The bytes of a word, read back little-endian, are the word. -/
theorem leWord_wordBytes (w : UInt32) :
    leWord w.toUInt8 (w >>> 8).toUInt8 (w >>> 16).toUInt8 (w >>> 24).toUInt8 = w := by
  apply UInt32.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [leWord, UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32,
    UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, Nat.testBit_or, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  have hw : w.toNat.testBit j = (decide (j < 32) && w.toNat.testBit j) := by
    by_cases h : j < 32
    · simp [h]
    · simp [h, Nat.testBit_lt_two_pow (w.toNat_lt.trans_le (Nat.pow_le_pow_right (by norm_num)
        (by omega : 32 ≤ j)))]
  rw [hw]
  rcases (by omega : j < 8 ∨ (8 ≤ j ∧ j < 16) ∨ (16 ≤ j ∧ j < 24) ∨ (24 ≤ j ∧ j < 32) ∨ 32 ≤ j)
    with h | h | h | h | h
  · simp [h, show j < 32 by omega, show ¬ 8 ≤ j by omega, show ¬ 16 ≤ j by omega,
      show ¬ 24 ≤ j by omega]
  · simp [h, show j < 32 by omega, show ¬ j < 8 by omega, show ¬ 16 ≤ j by omega,
      show ¬ 24 ≤ j by omega, show j - 8 < 8 by omega, show 8 + (j - 8) = j by omega]
  · simp [h, show j < 32 by omega, show ¬ j < 8 by omega, show ¬ 24 ≤ j by omega,
      show 8 ≤ j by omega, show ¬ j - 8 < 8 by omega, show j - 16 < 8 by omega,
      show 16 + (j - 16) = j by omega]
  · simp [h, show ¬ j < 8 by omega, show 8 ≤ j by omega, show 16 ≤ j by omega,
      show ¬ j - 8 < 8 by omega, show ¬ j - 16 < 8 by omega, show j - 24 < 8 by omega,
      show 24 + (j - 24) = j by omega]
  · simp [show ¬ j < 32 by omega, show ¬ j < 8 by omega]

private theorem getD_toArray (l : List UInt8) (i : ℕ) : l.toArray.getD i 0 = l.getD i 0 := by
  simp only [Array.getD, List.getD_eq_getElem?_getD, List.size_toArray]
  split_ifs with h
  · simp [h]
  · simp [h]

/-- `blockWords` reading its bytes through an array. -/
def blockWordsFast (block : List UInt8) : Vector UInt32 16 :=
  let a := block.toArray
  let b := fun i ↦ a.getD i 0
  Vector.ofFn fun j ↦ leWord (b (4 * j)) (b (4 * j + 1)) (b (4 * j + 2)) (b (4 * j + 3))

/-- `blockWordsFast` is `blockWords`. -/
theorem blockWordsFast_eq : blockWordsFast = blockWords := by
  funext block
  simp only [blockWordsFast, blockWords, getD_toArray]

/-- `absorb` over `blockWordsFast`. -/
def absorbFast (h : Vector UInt32 8) (t : ℕ) : (blocks : ℕ) → List UInt8 → Digest
  | 0, data => compress h (blockWordsFast data) (t + data.length).toUInt64 lastBlock 0
  | blocks + 1, data =>
    absorbFast (compress h (blockWordsFast (data.take 64)) (t + 64).toUInt64 0 0) (t + 64) blocks
      (data.drop 64)

/-- `absorbFast` is `absorb`. -/
theorem absorbFast_eq : absorbFast = absorb := by
  funext h t blocks data
  induction blocks generalizing h t data with
  | zero => simp only [absorbFast, absorb, blockWordsFast_eq]
  | succ n ih => simp only [absorbFast, absorb, blockWordsFast_eq, ih]

/-- `blake2sBytes` over `absorbFast`. -/
def blake2sBytesFast (data : List UInt8) : Digest :=
  absorbFast paramIv 0 ((data.length - 1) / 64) data

/-- Compiled code hashes bytes through `blake2sBytesFast`. -/
@[csimp] theorem blake2sBytes_eq_blake2sBytesFast : @blake2sBytes = @blake2sBytesFast := by
  funext data
  simp only [blake2sBytes, blake2sBytesFast, absorbFast_eq]

/-- `hashWords` over `blake2sBytesFast`. -/
def hashWordsFast (words : List K) : Digest := blake2sBytesFast (words.flatMap kBytes)

/-- Compiled code hashes Merkle leaves through `hashWordsFast`. -/
@[csimp] theorem hashWords_eq_hashWordsFast : @hashWords = @hashWordsFast := by
  funext words
  simp only [hashWords, hashWordsFast, ← blake2sBytes_eq_blake2sBytesFast]

/-- Byte `4j + t` of the little-endian bytes of a word list is byte `t` of word `j`. -/
private theorem getD_flatMap_wordBytes (L : List UInt32) (j t : ℕ) (ht : t < 4)
    (hj : j < L.length) :
    (L.flatMap wordBytes).getD (4 * j + t) 0 = (wordBytes (L.getD j 0)).getD t 0 := by
  induction L generalizing j with
  | nil => simp at hj
  | cons w L ih =>
    rw [List.flatMap_cons]
    cases j with
    | zero =>
      rw [List.getD_append _ _ _ _ (by simp [wordBytes]; omega)]
      simp
    | succ j =>
      rw [List.getD_append_right _ _ _ _ (by simp [wordBytes]; omega)]
      simp only [List.length_cons] at hj
      rw [show 4 * (j + 1) + t - (wordBytes w).length = 4 * j + t by simp [wordBytes]; omega,
        ih j (by omega)]
      simp

/-- The Merkle node hash on words: one compression of the two digests' sixteen words. -/
def hashPairFast (left right : Digest) : Digest := compress paramIv (left ++ right) 64 lastBlock 0

/-- Compiled code hashes Merkle nodes through `hashPairFast`. -/
@[csimp] theorem hashPair_eq_hashPairFast : @hashPair = @hashPairFast := by
  funext left right
  have hbytes :
      digestBytes left ++ digestBytes right = (left ++ right).toList.flatMap wordBytes := by
    simp only [digestBytes, Vector.toList_append, List.flatMap_append]
  have hlen : (digestBytes left ++ digestBytes right).length = 64 := by
    simp [hbytes, wordBytes, List.length_flatMap]
  simp only [hashPair, hashPairFast, blake2sBytes, hlen]
  simp only [show (64 - 1) / 64 = 0 from rfl, absorb, hlen]
  congr 1
  apply Vector.ext
  intro j hj
  simp only [blockWords, Vector.getElem_ofFn, hbytes]
  have hL : j < (left ++ right).toList.length := by simp; omega
  have h0 := getD_flatMap_wordBytes _ j 0 (by norm_num) hL
  simp only [Nat.add_zero] at h0
  rw [h0, getD_flatMap_wordBytes _ j 1 (by norm_num) hL,
    getD_flatMap_wordBytes _ j 2 (by norm_num) hL, getD_flatMap_wordBytes _ j 3 (by norm_num) hL]
  simp only [wordBytes, List.getD_cons_zero, List.getD_cons_succ]
  rw [leWord_wordBytes, List.getD_eq_getElem _ _ hL, Vector.getElem_toList]

end
end LeanerVM.Protocol.Blake2sHash
