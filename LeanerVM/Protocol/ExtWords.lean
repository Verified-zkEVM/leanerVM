/-
  LeanerVM.Protocol.ExtWords

  Sums and products of `E` on its limbs' machine words, proved to be `E`'s, for compiled code
  that names them in place of the field operations.
-/

module

public import LeanerVM.Parameters.Field
public import LeanerVM.Parameters.ToCompPoly.ExtensionFast
public import Mathlib.Algebra.CharP.Two

/-!
# `E` on words

`E`'s operations run through its `Ring` instance over `K`'s, whose elements are bit vectors: a sum
of limbs and every product converts each operand to a machine word and back. `addW` and `mulW`
convert each limb once: `addW` is three `xor`s, `mulW` Karatsuba's six word products with the
modulus `y^3 = y + 1` folded in by `xor`s (`addW_eq`, `mulW_eq`). They are functions, not
instances: code that wants them names them, with the equations as its proofs.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly FastBF64

@[expose] public section

namespace ExtWords

/-- The words of an element's limbs. -/
@[inline] def w0 (x : E) : UInt64 := toWord (x.limb 0)

@[inline, inherit_doc w0] def w1 (x : E) : UInt64 := toWord (x.limb 1)

@[inline, inherit_doc w0] def w2 (x : E) : UInt64 := toWord (x.limb 2)

/-- The element of three limb words. -/
@[inline] def ofW (a b c : UInt64) : E := E.ofLimbs (ofWord a) (ofWord b) (ofWord c)

/-- `E`'s sum on words. -/
def addW (x y : E) : E := ofW (w0 x ^^^ w0 y) (w1 x ^^^ w1 y) (w2 x ^^^ w2 y)

/-- `E`'s product on words: Karatsuba's six products, `y^3 = y + 1` folded in. -/
def mulW (x y : E) : E :=
  let a0 := w0 x
  let a1 := w1 x
  let a2 := w2 x
  let b0 := w0 y
  let b1 := w1 y
  let b2 := w2 y
  let p00 := mulWord a0 b0
  let p11 := mulWord a1 b1
  let p22 := mulWord a2 b2
  let c1 := mulWord (a0 ^^^ a1) (b0 ^^^ b1) ^^^ p00 ^^^ p11
  let c2 := mulWord (a0 ^^^ a2) (b0 ^^^ b2) ^^^ p00 ^^^ p22 ^^^ p11
  let c3 := mulWord (a1 ^^^ a2) (b1 ^^^ b2) ^^^ p11 ^^^ p22
  ofW (p00 ^^^ c3) (c1 ^^^ p22 ^^^ c3) (c2 ^^^ p22)

/-- The element of a `xor` is the sum of the elements. -/
private theorem ofWord_xor (a b : UInt64) : ofWord (a ^^^ b) = ofWord a + ofWord b := by
  rw [BF64.add_def]
  rfl

/-- `addW` is the sum. -/
theorem addW_eq (x y : E) : addW x y = x + y := by
  apply E.ext
  intro i
  rw [limb_add]
  fin_cases i <;> simp [addW, ofW, w0, w1, w2, ofWord_xor]

/-- `mulW` is the product. -/
theorem mulW_eq (x y : E) : mulW x y = x * y := by
  rw [← FastExt.mulDeg3_eq (P := BF64.ext3Params) rfl x y]
  apply E.ext
  intro i
  fin_cases i
  · show ofWord _ = x.limb 0 * y.limb 0 - (((x.limb 1 + x.limb 2) * (y.limb 1 + y.limb 2) -
      x.limb 1 * y.limb 1 - x.limb 2 * y.limb 2) - x.limb 2 * y.limb 2 * 0) * 1
    simp only [ofWord_xor, ofWord_mulWord, w0, w1, w2, ofWord_toWord, CharTwo.sub_eq_add]
    ring
  · show ofWord _ = ((x.limb 0 + x.limb 1) * (y.limb 0 + y.limb 1) - x.limb 0 * y.limb 0 -
      x.limb 1 * y.limb 1) - x.limb 2 * y.limb 2 * 1 -
      (((x.limb 1 + x.limb 2) * (y.limb 1 + y.limb 2) - x.limb 1 * y.limb 1 -
      x.limb 2 * y.limb 2) - x.limb 2 * y.limb 2 * 0) * 1
    simp only [ofWord_xor, ofWord_mulWord, w0, w1, w2, ofWord_toWord, CharTwo.sub_eq_add]
    ring
  · show ofWord _ = ((x.limb 0 + x.limb 2) * (y.limb 0 + y.limb 2) - x.limb 0 * y.limb 0 -
      x.limb 2 * y.limb 2 + x.limb 1 * y.limb 1) - x.limb 2 * y.limb 2 * 1 -
      (((x.limb 1 + x.limb 2) * (y.limb 1 + y.limb 2) - x.limb 1 * y.limb 1 -
      x.limb 2 * y.limb 2) - x.limb 2 * y.limb 2 * 0) * 0
    simp only [ofWord_xor, ofWord_mulWord, w0, w1, w2, ofWord_toWord, CharTwo.sub_eq_add]
    ring

end ExtWords

end

end LeanerVM.Protocol
