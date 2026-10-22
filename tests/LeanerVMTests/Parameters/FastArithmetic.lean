import LeanerVM.Parameters.Field

/-!
# Differential tests of the compiled field arithmetic

The word arithmetic of `LeanerVM.Parameters.ToCompPoly.BF64Fast` and the degree-three product,
inverse and powers of `LeanerVM.Parameters.ToCompPoly.ExtensionFast` are proved equal to their
specifications; these `#guard`s run both on edge words and on random-looking ones, as a check of
the compiled code itself. The specification side calls functions compiled before the
`@[csimp]` theorems were registered (`BF64.mul`, `BF64.invItohTsujii`, `Ext.mulTbl`), which the
substitution does not touch. Two mutations show the conditions the product and the reduction
depend on.
-/

namespace LeanerVMTests.Parameters.FastArithmetic

open LeanerVM.Parameters LeanerVM.Parameters.FastBF64

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

/-- The inverse through a field dictionary, as generic code reaches it. -/
private def fieldInv {R : Type} [Field R] (x : R) : R := x⁻¹

/-- Division through a field dictionary. -/
private def fieldDiv {R : Type} [Field R] (x y : R) : R := x / y

/-! ## `K` -/

-- The word product against CompPoly's `BF64.mul`, on every pair.
#guard words.all fun a ↦ words.all fun b ↦ ofWord (mulWord a b) == BF64.mul (ofWord a) (ofWord b)

-- `*` on `K` compiles to `mulFast` through `BF64.instMul`.
#guard words.all fun a ↦ words.all fun b ↦ ofWord a * ofWord b == BF64.mul (ofWord a) (ofWord b)

-- The inverse against CompPoly's addition chain.
#guard (words.take 12).all fun a ↦ invFast (ofWord a) == BF64.invItohTsujii (ofWord a)

-- `⁻¹` and `/` on `K`, zero included.
#guard (words.drop 1 |>.take 8).all fun a ↦ BF64.mul (ofWord a) (ofWord a)⁻¹ == 1
#guard (words.take 8).all fun a ↦ ofWord a / ofWord 3 == BF64.mul (ofWord a) (ofWord 3)⁻¹
#guard (0 : K)⁻¹ == 0
#guard (words.take 8).all fun a ↦ ofWord a / 0 == 0
#guard fieldInv (0 : K) == 0
#guard (words.take 8).all fun a ↦ fieldDiv (ofWord a) 0 == 0

-- Powers against repeated `BF64.mul`, and integer powers.
#guard (words.take 6).all fun a ↦ (List.range 9).all fun n ↦
  ofWord a ^ n == (List.replicate n (ofWord a)).foldl BF64.mul 1
#guard (words.take 6).all fun a ↦ ofWord a ^ (2 ^ 64 - 1) == if a = 0 then 0 else 1
#guard (words.take 6).all fun a ↦
  ofWord a ^ (-3 : ℤ) == BF64.invItohTsujii (BF64.mul (ofWord a) (BF64.mul (ofWord a) (ofWord a)))
#guard (words.take 6).all fun a ↦ ofWord a ^ (4 : ℤ) == ofWord a ^ 4

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

-- The ring-level inverse `x ^ (q^3 - 2)` and Cramer's rule through a field dictionary.
#guard (elems.take 3).all fun x ↦ x * x⁻¹ == 1
#guard elems.all fun x ↦ x * fieldInv x == 1
#guard elems.all fun x ↦ fieldInv x == x⁻¹
#guard (0 : E)⁻¹ == 0
#guard fieldInv (0 : E) == 0
#guard (elems.take 3).all fun x ↦ x / 0 == 0
#guard elems.all fun x ↦ fieldDiv x 0 == 0

-- Natural and integer powers.
#guard (elems.take 3).all fun x ↦ x ^ 5 == mulLimbs x (mulLimbs x (mulLimbs x (mulLimbs x x)))
#guard elems.all fun x ↦ x ^ (-2 : ℤ) * mulLimbs x x == 1
#guard elems.all fun x ↦ x ^ (3 : ℤ) == mulLimbs x (mulLimbs x x)

/-! ## Mutations -/

-- Without the masks, the integer product carries: it is not the carry-less product.
#guard words.any fun a ↦ words.any fun b ↦ (a &&& 0xFFFFFFFF) * (b &&& 0xFFFFFFFF) !=
  clmul32 a b

-- One fold of the high word is not enough: the bits it pushes past `X^63` are lost.
#guard words.any fun a ↦ words.any fun b ↦
  let hl := clmul64 a b
  hl.2 ^^^ hl.1 ^^^ (hl.1 <<< 1) ^^^ (hl.1 <<< 3) ^^^ (hl.1 <<< 4) != mulWord a b

end LeanerVMTests.Parameters.FastArithmetic
