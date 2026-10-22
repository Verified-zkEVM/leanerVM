import LeanerVM.Protocol.Merkle

/-!
# Differential tests of the compiled fast paths

The word arithmetic of `LeanerVM.Parameters.ToCompPoly.BF64Fast`, the degree-three product and
inverse of `LeanerVM.Parameters.ToCompPoly.ExtensionFast`, the compression of
`LeanerVM.Semantics.Blake2sFast` and the hasher of `LeanerVM.Protocol.Blake2sHashFast` are
proved equal to their specifications; these `#guard`s run both on random-looking inputs and on
edge words, and the hasher on `hashlib.blake2s` digests, as a check of the compiled code. The
specification side calls functions compiled before the `@[csimp]` theorems were registered
(`BF64.mul`, `BF64.invItohTsujii`, `Blake2s.round`), which the substitution does not touch. Two
mutations show the conditions the product and the reduction depend on.
-/

namespace LeanerVMTests.Protocol.FastArithmetic

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol LeanerVM.Parameters.FastBF64

/-- A xorshift step. -/
private def xs (s : UInt64) : UInt64 :=
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  s ^^^ (s <<< 17)

/-- Edge words, then random-looking ones. -/
private def words : List UInt64 :=
  [0, 1, 2, 0x1B, 0x8000000000000000, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFF, 0x100000000] ++
    (List.range 24).map fun i ↦ Nat.iterate xs (i + 1) 0x9E3779B97F4A7C15

/-- `E` elements from consecutive words. -/
private def elems : List E :=
  (List.range 10).map fun i ↦
    E.ofLimbs (ofWord (words.getD i 0)) (ofWord (words.getD (i + 7) 0))
      (ofWord (words.getD (i + 14) 0))

/-! ## `K` -/

-- The word product against CompPoly's `BF64.mul`, on every pair.
#guard words.all fun a ↦ words.all fun b ↦ ofWord (mulWord a b) == BF64.mul (ofWord a) (ofWord b)

-- `*` on `K` compiles to `mulFast` through `BF64.instMul`.
#guard words.all fun a ↦ words.all fun b ↦ ofWord a * ofWord b == BF64.mul (ofWord a) (ofWord b)

-- The inverse against CompPoly's addition chain.
#guard (words.take 12).all fun a ↦ invFast (ofWord a) == BF64.invItohTsujii (ofWord a)

-- `⁻¹` and `/` on `K`.
#guard (words.drop 1 |>.take 8).all fun a ↦ BF64.mul (ofWord a) (ofWord a)⁻¹ == 1
#guard (words.take 8).all fun a ↦ ofWord a / ofWord 3 == BF64.mul (ofWord a) (ofWord 3)⁻¹

-- Powers against repeated `BF64.mul`.
#guard (words.take 6).all fun a ↦ (List.range 9).all fun n ↦
  ofWord a ^ n == (List.replicate n (ofWord a)).foldl BF64.mul 1
#guard (words.take 6).all fun a ↦ ofWord a ^ (2 ^ 64 - 1) == if a = 0 then 0 else 1

/-! ## `E` -/

/-- The product by its limbs over `BF64.mul` (`mul_limbs`). -/
private def mulLimbs (x z : E) : E :=
  let m := BF64.mul
  let (a0, a1, a2) := (x.limb 0, x.limb 1, x.limb 2)
  let (b0, b1, b2) := (z.limb 0, z.limb 1, z.limb 2)
  E.ofLimbs (m a0 b0 + m a1 b2 + m a2 b1)
    (m a0 b1 + m a1 b0 + m a1 b2 + m a2 b1 + m a2 b2) (m a0 b2 + m a1 b1 + m a2 b0 + m a2 b2)

#guard elems.all fun x ↦ elems.all fun z ↦ x * z == mulLimbs x z

-- The table product CompPoly compiles `Ext.mul` to, against Karatsuba.
#guard elems.all fun x ↦ elems.all fun z ↦
  CompPoly.Extension.Ext.mulTbl x z == LeanerVM.Parameters.FastExt.mulFast x z

#guard (elems.take 3).all fun x ↦ x * x⁻¹ == 1

/-- The inverse through a field dictionary: Cramer's rule in `fieldFast`. -/
private def fieldInv {R : Type} [Field R] (x : R) : R := x⁻¹

#guard elems.all fun x ↦ x * fieldInv x == 1
#guard elems.all fun x ↦ fieldInv x == x⁻¹
#guard fieldInv (0 : E) == 0
#guard (elems.take 3).all fun x ↦ x ^ 5 == mulLimbs x (mulLimbs x (mulLimbs x (mulLimbs x x)))
#guard (0 : E)⁻¹ == 0

/-! ## BLAKE2s -/

/-- `compress` assembled from `Blake2s.round`, which no `@[csimp]` theorem replaces. -/
private def compressSpec (h : Vector UInt32 8) (m : Vector UInt32 16) (t : UInt64)
    (f0 f1 : UInt32) : Vector UInt32 8 :=
  let v := sigma.foldl (fun v s ↦ Blake2s.round v m s) (Blake2s.initialState h t f0 f1)
  Vector.ofFn fun i : Fin 8 ↦ h[i] ^^^ v[i] ^^^ v[i.val + 8]

/-- Words from a seed. -/
private def wordsOf (n : ℕ) (seed : ℕ) : Vector UInt32 n :=
  Vector.ofFn fun i ↦ (words.getD ((i.val + seed) % words.length) 0).toUInt32

#guard (List.range 6).all fun s ↦
  (compress (wordsOf 8 s) (wordsOf 16 (s + 3)) (words.getD s 0) 0 0).toList ==
    (compressSpec (wordsOf 8 s) (wordsOf 16 (s + 3)) (words.getD s 0) 0 0).toList
#guard (compress (wordsOf 8 1) (wordsOf 16 2) 64 0xFFFFFFFF 0xFFFFFFFF).toList ==
  (compressSpec (wordsOf 8 1) (wordsOf 16 2) 64 0xFFFFFFFF 0xFFFFFFFF).toList

-- A Merkle node over the fast compression, against RFC 7693's unkeyed hash of 64 bytes.
#guard (Blake2sHash.hashPair (wordsOf 8 0) (wordsOf 8 5)).toList ==
  (compressSpec Blake2sHash.paramIv (wordsOf 8 0 ++ wordsOf 8 5) 64 Blake2sHash.lastBlock 0).toList

/-- The bytes `0, 1, …, n - 1`. -/
private def ramp (n : ℕ) : List UInt8 := (List.range n).map Nat.toUInt8

-- The hasher over `blockWordsFast`, against `hashlib.blake2s` (as in the `Blake2sHash` tests).
#guard (Blake2sHash.blake2sBytes (ramp 64)).toList ==
  [0x8b4ef356, 0x907e5596, 0x524bf2c1, 0x519dc8d0, 0x1bcf6a08, 0xcf34f600, 0x3392de1d, 0x3eaaeab8]
#guard (Blake2sHash.blake2sBytes (ramp 128)).toList ==
  [0xde77a81f, 0x199d2567, 0x342a3a86, 0x2a96c6bc, 0xbffc252b, 0x7ecdbe5c, 0xa31f8fde, 0x96a78866]
#guard (Blake2sHash.hashWords [K.ofBits 1, K.ofBits 2]).toList ==
  [0x6b8928f2, 0x12389f83, 0xe4753c2b, 0x44f83b7f, 0x926dae68, 0xa0cb51b5, 0x1828562e, 0x44a89c61]
#guard ((List.range 70).map ramp).all fun d ↦
  (Blake2sHash.blake2sBytesFast d).toList == (Blake2sHash.absorb Blake2sHash.paramIv 0
    ((d.length - 1) / 64) d).toList

/-! ## Mutations -/

-- Without the masks, the integer product carries: it is not the carry-less product.
#guard words.any fun a ↦ words.any fun b ↦ (a &&& 0xFFFFFFFF) * (b &&& 0xFFFFFFFF) !=
  clmul32 a b

-- One fold of the high word is not enough: the bits it pushes past `X^63` are lost.
#guard words.any fun a ↦ words.any fun b ↦
  let hl := clmul64 a b
  hl.2 ^^^ hl.1 ^^^ (hl.1 <<< 1) ^^^ (hl.1 <<< 3) ^^^ (hl.1 <<< 4) != mulWord a b

end LeanerVMTests.Protocol.FastArithmetic
