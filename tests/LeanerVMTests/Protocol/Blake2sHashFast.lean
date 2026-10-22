import LeanerVM.Protocol.Blake2sHashFast

/-!
# Differential tests of the compiled byte hasher

`blake2sBytes`, `hashWords` and `hashPair` compile to the functions of
`LeanerVM.Protocol.Blake2sHashFast`, proved equal to them; these `#guard`s check them against
`hashlib.blake2s` digests (as in the `Blake2sHash` tests), against `absorb`, which no `@[csimp]`
theorem replaces, and the node hash against RFC 7693's one-compression form of 64 bytes.
-/

namespace LeanerVMTests.Protocol.Blake2sHashFast

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol LeanerVM.Protocol.Blake2sHash

/-- The bytes `0, 1, …, n - 1`. -/
private def ramp (n : ℕ) : List UInt8 := (List.range n).map Nat.toUInt8

/-- `compress` assembled from `Blake2s.round`. -/
private def compressSpec (h : Vector UInt32 8) (m : Vector UInt32 16) (t : UInt64)
    (f0 f1 : UInt32) : Vector UInt32 8 :=
  let v := sigma.foldl (fun v s ↦ Blake2s.round v m s) (Blake2s.initialState h t f0 f1)
  Vector.ofFn fun i : Fin 8 ↦ h[i] ^^^ v[i] ^^^ v[i.val + 8]

/-- Eight words from a seed. -/
private def digestOf (seed : ℕ) : Digest :=
  Vector.ofFn fun i ↦ (i.val * 0x9E3779B9 + seed * 0x85EBCA6B).toUInt32

#guard (blake2sBytes (ramp 64)).toList ==
  [0x8b4ef356, 0x907e5596, 0x524bf2c1, 0x519dc8d0, 0x1bcf6a08, 0xcf34f600, 0x3392de1d, 0x3eaaeab8]
#guard (blake2sBytes (ramp 128)).toList ==
  [0xde77a81f, 0x199d2567, 0x342a3a86, 0x2a96c6bc, 0xbffc252b, 0x7ecdbe5c, 0xa31f8fde, 0x96a78866]
#guard (hashWords [K.ofBits 1, K.ofBits 2]).toList ==
  [0x6b8928f2, 0x12389f83, 0xe4753c2b, 0x44f83b7f, 0x926dae68, 0xa0cb51b5, 0x1828562e, 0x44a89c61]

-- Every length from 0 to 69 bytes: one, two and the empty block.
#guard ((List.range 70).map ramp).all fun d ↦
  (blake2sBytesFast d).toList == (absorb paramIv 0 ((d.length - 1) / 64) d).toList

-- A node is one compression of its children's sixteen words.
#guard (List.range 4).all fun s ↦
  (hashPair (digestOf s) (digestOf (s + 7))).toList ==
    (compressSpec paramIv (digestOf s ++ digestOf (s + 7)) 64 lastBlock 0).toList

end LeanerVMTests.Protocol.Blake2sHashFast
