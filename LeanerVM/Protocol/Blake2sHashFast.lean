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
`absorb` copies each block out with `List.take`, and `hashWords` and `hashPair` write words out as
bytes only for `blockWords` to read them back. `blake2sBytesFast` turns the bytes into an array
once and reads every block in place (`blockWordsAt`, `absorbAt`); `hashWordsFast` absorbs the
leaf's words themselves (`absorbWords`) and `hashPairFast` compresses the sixteen digest words,
since the bytes of a word, read back little-endian, are the word (`leWord_wordBytes`). The `@[csimp]` theorems substitute
`blake2sBytesFast`, `hashWordsFast` and `hashPairFast` in code compiled after this module, such as
`merkleRoot`. The specifications are unchanged.
-/

namespace LeanerVM.Protocol.Blake2sHash

open LeanerVM.Parameters LeanerVM.Semantics

@[expose] public section

/-- The sixteen little-endian words of the 64 bytes of `a` from `off`, zero-padded past its end:
`blockWords` reading in place. -/
def blockWordsAt (a : Array UInt8) (off : ℕ) : Vector UInt32 16 :=
  let w := fun j : ℕ ↦ leWord (a.getD (off + 4 * j) 0) (a.getD (off + 4 * j + 1) 0)
    (a.getD (off + 4 * j + 2) 0) (a.getD (off + 4 * j + 3) 0)
  #v[w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7, w 8, w 9, w 10, w 11, w 12, w 13, w 14, w 15]

private theorem getElem_blockWordsAt (a : Array UInt8) (off j : ℕ) (hj : j < 16) :
    (blockWordsAt a off)[j] = leWord (a.getD (off + 4 * j) 0) (a.getD (off + 4 * j + 1) 0)
      (a.getD (off + 4 * j + 2) 0) (a.getD (off + 4 * j + 3) 0) := by
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j <;>
    first | rfl | omega

/-- `blockWordsAt` reads the bytes from `off`. -/
private theorem blockWordsAt_eq (l : List UInt8) (off : ℕ) :
    blockWordsAt l.toArray off = blockWords (l.drop off) := by
  refine Vector.ext fun j hj ↦ ?_
  simp only [getElem_blockWordsAt _ _ _ hj, blockWords, Vector.getElem_ofFn,
    Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD,
    List.getElem?_drop, Nat.add_assoc]

/-- `blockWords` reads the first 64 bytes only. -/
private theorem blockWords_take (l : List UInt8) : blockWords (l.take 64) = blockWords l := by
  refine Vector.ext fun j hj ↦ ?_
  simp only [blockWords, Vector.getElem_ofFn, List.getD_eq_getElem?_getD]
  rw [List.getElem?_take_of_lt (by omega), List.getElem?_take_of_lt (by omega),
    List.getElem?_take_of_lt (by omega), List.getElem?_take_of_lt (by omega)]

/-- `blockWords` reading its bytes through an array. -/
def blockWordsFast (block : List UInt8) : Vector UInt32 16 := blockWordsAt block.toArray 0

/-- `blockWordsFast` is `blockWords`. -/
theorem blockWordsFast_eq : blockWordsFast = blockWords := by
  funext block
  rw [blockWordsFast, blockWordsAt_eq, List.drop_zero]

/-- `absorb` over the bytes of `a` from `off`, read in place. -/
def absorbAt (a : Array UInt8) (h : Vector UInt32 8) (t : ℕ) : (blocks : ℕ) → (off : ℕ) → Digest
  | 0, off => compress h (blockWordsAt a off) (t + (a.size - off)).toUInt64 lastBlock 0
  | blocks + 1, off =>
    absorbAt a (compress h (blockWordsAt a off) (t + 64).toUInt64 0 0) (t + 64) blocks (off + 64)

/-- `absorbAt` absorbs the bytes from `off`. -/
private theorem absorbAt_eq (l : List UInt8) (h : Vector UInt32 8) (t blocks off : ℕ) :
    absorbAt l.toArray h t blocks off = absorb h t blocks (l.drop off) := by
  induction blocks generalizing h t off with
  | zero => simp [absorbAt, absorb, blockWordsAt_eq]
  | succ n ih => rw [absorbAt, absorb, ih, blockWords_take, blockWordsAt_eq, List.drop_drop]

/-- `absorb` over `absorbAt`. -/
def absorbFast (h : Vector UInt32 8) (t blocks : ℕ) (data : List UInt8) : Digest :=
  absorbAt data.toArray h t blocks 0

/-- `absorbFast` is `absorb`. -/
theorem absorbFast_eq : absorbFast = absorb := by
  funext h t blocks data
  rw [absorbFast, absorbAt_eq, List.drop_zero]

/-- `blake2sBytes` over `absorbAt`. -/
def blake2sBytesFast (data : List UInt8) : Digest :=
  let a := data.toArray
  absorbAt a paramIv 0 ((a.size - 1) / 64) 0

/-- Compiled code hashes bytes through `blake2sBytesFast`. -/
@[csimp] theorem blake2sBytes_eq_blake2sBytesFast : @blake2sBytes = @blake2sBytesFast := by
  funext data
  rw [blake2sBytes, blake2sBytesFast, absorbAt_eq, List.size_toArray, List.drop_zero]

/-- Word `j` read back from the little-endian bytes of a word list is word `j`, zero past the
end. -/
private theorem leWord_flatMap_wordBytes (L : List UInt32) (j : ℕ) :
    leWord ((L.flatMap wordBytes).getD (4 * j) 0) ((L.flatMap wordBytes).getD (4 * j + 1) 0)
      ((L.flatMap wordBytes).getD (4 * j + 2) 0) ((L.flatMap wordBytes).getD (4 * j + 3) 0) =
      L.getD j 0 := by
  induction L generalizing j with
  | nil => simp only [List.flatMap_nil, List.getD_nil]; rfl
  | cons w L ih =>
    cases j with
    | zero => simpa [wordBytes] using leWord_wordBytes w
    | succ j => simpa [wordBytes, Nat.mul_add] using ih j

/-- The sixteen words of `a` from `off`, zero past its end. -/
def wordsAt (a : Array UInt32) (off : ℕ) : Vector UInt32 16 :=
  let w := fun j : ℕ ↦ a.getD (off + j) 0
  #v[w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7, w 8, w 9, w 10, w 11, w 12, w 13, w 14, w 15]

private theorem getElem_wordsAt (a : Array UInt32) (off j : ℕ) (hj : j < 16) :
    (wordsAt a off)[j] = a.getD (off + j) 0 := by
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j <;>
    first | rfl | omega

/-- `absorb` over the little-endian bytes of the words of `a` from `off`, read as words. -/
def absorbWords (a : Array UInt32) (h : Vector UInt32 8) (t : ℕ) :
    (blocks : ℕ) → (off : ℕ) → Digest
  | 0, off => compress h (wordsAt a off) (t + 4 * (a.size - off)).toUInt64 lastBlock 0
  | blocks + 1, off =>
    absorbWords a (compress h (wordsAt a off) (t + 64).toUInt64 0 0) (t + 64) blocks (off + 16)

/-- The block of the bytes of a word list from word `off` is its sixteen words from `off`. -/
private theorem blockWords_drop_flatMap (L : List UInt32) (off : ℕ) :
    blockWords ((L.flatMap wordBytes).drop (4 * off)) = wordsAt L.toArray off := by
  refine Vector.ext fun j hj ↦ ?_
  have := leWord_flatMap_wordBytes L (off + j)
  simp only [List.getD_eq_getElem?_getD, Nat.mul_add, Nat.add_assoc] at this
  simp only [blockWords, Vector.getElem_ofFn, getElem_wordsAt _ _ _ hj, List.getD_eq_getElem?_getD,
    List.getElem?_drop, Array.getD_eq_getD_getElem?, List.getElem?_toArray, this]

private theorem length_flatMap_wordBytes (L : List UInt32) :
    (L.flatMap wordBytes).length = 4 * L.length := by
  induction L with
  | nil => rfl
  | cons w L ih => simp [ih, wordBytes]; omega

/-- `absorbWords` absorbs the bytes of the words from `off`. -/
private theorem absorbWords_eq (L : List UInt32) (h : Vector UInt32 8) (t blocks off : ℕ) :
    absorbWords L.toArray h t blocks off =
      absorb h t blocks ((L.flatMap wordBytes).drop (4 * off)) := by
  induction blocks generalizing h t off with
  | zero =>
    simp only [absorbWords, absorb, blockWords_drop_flatMap, List.length_drop,
      length_flatMap_wordBytes, List.size_toArray, Nat.mul_sub]
  | succ n ih =>
    rw [absorbWords, absorb, ih, blockWords_take, blockWords_drop_flatMap, List.drop_drop,
      show 4 * off + 64 = 4 * (off + 16) by omega]

/-- `hashWords` over the sixteen words of each block, without the bytes. -/
def hashWordsFast (words : List K) : Digest :=
  let a := (words.flatMap fun x ↦ [lowWord x, highWord x]).toArray
  absorbWords a paramIv 0 ((4 * a.size - 1) / 64) 0

/-- Compiled code hashes Merkle leaves through `hashWordsFast`. -/
@[csimp] theorem hashWords_eq_hashWordsFast : @hashWords = @hashWordsFast := by
  funext words
  have hb : words.flatMap kBytes = (words.flatMap fun x ↦ [lowWord x, highWord x]).flatMap
      wordBytes := by
    simp only [List.flatMap_assoc, List.flatMap_cons, List.flatMap_nil, List.append_nil]; rfl
  rw [hashWords, hashWordsFast, blake2sBytes, hb, length_flatMap_wordBytes, absorbWords_eq,
    List.size_toArray, Nat.mul_zero, List.drop_zero]

/-- The Merkle node hash on words: one compression of the two digests' sixteen words. -/
def hashPairFast (left right : Digest) : Digest := compress paramIv (left ++ right) 64 lastBlock 0

/-- Compiled code hashes Merkle nodes through `hashPairFast`. -/
@[csimp] theorem hashPair_eq_hashPairFast : @hashPair = @hashPairFast := by
  funext left right
  have hbytes :
      digestBytes left ++ digestBytes right = (left ++ right).toList.flatMap wordBytes := by
    simp only [digestBytes, Vector.toList_append, List.flatMap_append]
  have hlen : (digestBytes left ++ digestBytes right).length = 64 := by
    rw [hbytes, length_flatMap_wordBytes]; simp
  simp only [hashPair, hashPairFast, blake2sBytes, hlen, show (64 - 1) / 64 = 0 from rfl, absorb]
  refine congrArg (compress paramIv · 64 lastBlock 0) (Vector.ext fun j hj ↦ ?_)
  simp only [blockWords, Vector.getElem_ofFn, hbytes, leWord_flatMap_wordBytes]
  rw [List.getD_eq_getElem _ _ (by simp; omega), Vector.getElem_toList]

end
end LeanerVM.Protocol.Blake2sHash
