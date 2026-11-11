import LeanerVM.Semantics.Blake2sFast

/-!
# Differential tests of the compiled compression

`compress` compiles to `compressFast` (`LeanerVM.Semantics.Blake2sFast`), proved equal to it;
these `#guard`s compare it on random-looking words with `compress` assembled from
`Blake2s.round`, which no `@[csimp]` theorem replaces, with and without both flags, and one
round on the working words with `Blake2s.round`.
-/

namespace LeanerVMTests.Semantics.Blake2sFast

open LeanerVM.Parameters LeanerVM.Semantics

/-- A xorshift step. -/
private def xs (s : UInt64) : UInt64 :=
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  s ^^^ (s <<< 17)

/-- Edge words, then random-looking ones. -/
private def words : List UInt64 :=
  [0, 1, 0xFFFFFFFF, 0x8000000000000000, 0xFFFFFFFFFFFFFFFF] ++
    (List.range 24).map fun i ↦ Nat.iterate xs (i + 1) 0x9E3779B97F4A7C15

/-- `n` words from a seed. -/
private def wordsOf (n : ℕ) (seed : ℕ) : Vector UInt32 n :=
  Vector.ofFn fun i ↦ (words.getD ((i.val + seed) % words.length) 0).toUInt32

/-- `compress` assembled from `Blake2s.round`. -/
private def compressSpec (h : Vector UInt32 8) (m : Vector UInt32 16) (t : UInt64)
    (f0 f1 : UInt32) : Vector UInt32 8 :=
  let v := sigma.foldl (fun v s ↦ Blake2s.round v m s) (Blake2s.initialState h t f0 f1)
  Vector.ofFn fun i : Fin 8 ↦ h[i] ^^^ v[i] ^^^ v[i.val + 8]

#guard (List.range 8).all fun s ↦
  (compress (wordsOf 8 s) (wordsOf 16 (s + 3)) (words.getD s 0) 0 0).toList ==
    (compressSpec (wordsOf 8 s) (wordsOf 16 (s + 3)) (words.getD s 0) 0 0).toList

#guard (compress (wordsOf 8 1) (wordsOf 16 2) 64 0xFFFFFFFF 0xFFFFFFFF).toList ==
  (compressSpec (wordsOf 8 1) (wordsOf 16 2) 64 0xFFFFFFFF 0xFFFFFFFF).toList

-- One round on the working words, under every schedule row.
#guard (List.range 10).all fun r ↦
  (Blake2s.roundFast (wordsOf 16 r) (wordsOf 16 (r + 5)) (sigma.toList.getD r sigma[0])).toList ==
    (Blake2s.round (wordsOf 16 r) (wordsOf 16 (r + 5)) (sigma.toList.getD r sigma[0])).toList

-- Each rotation, against `BitVec.rotateRight`.
#guard words.all fun w ↦
  Blake2s.rotr16 w.toUInt32 == Blake2s.rotr w.toUInt32 16 &&
    Blake2s.rotr12 w.toUInt32 == Blake2s.rotr w.toUInt32 12 &&
    Blake2s.rotr8 w.toUInt32 == Blake2s.rotr w.toUInt32 8 &&
    Blake2s.rotr7 w.toUInt32 == Blake2s.rotr w.toUInt32 7

end LeanerVMTests.Semantics.Blake2sFast
