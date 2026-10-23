/-
  LeanerVM.Semantics.Blake2sFast

  The BLAKE2s compression function on native word rotations and unboxed working words, proved
  equal to `compress` and registered for compiled code.
-/

module

public import LeanerVM.Semantics.Blake2s

/-!
# BLAKE2s compression on native rotations

`compress` rotates through `BitVec.rotateRight`, which compiles to arithmetic on natural numbers,
and keeps its sixteen working words in an array. `compressFast` is the same function with each
rotation by `16`, `12`, `8` or `7` written as two `UInt32` shifts (`rotr_sixteen` through
`rotr_seven`) and the working words held in the sixteen fields of `Words` across a round, which
compiled code keeps unboxed. The `@[csimp]` theorem `compress_eq_compressFast` makes every compiled
call of `compress` after this module run `compressFast`; `instDecidableCompressCells_eq` does the
same for the decision of `CompressCells`, whose instance was compiled before this module. Nothing
here is trusted beyond the two equations; the specification is `compress`.
-/

namespace LeanerVM.Semantics

open LeanerVM.Parameters

@[expose] public section

namespace Blake2s

/-- Rotate right by 16. -/
@[inline] def rotr16 (x : UInt32) : UInt32 := (x >>> 16) ||| (x <<< 16)

/-- Rotate right by 12. -/
@[inline] def rotr12 (x : UInt32) : UInt32 := (x >>> 12) ||| (x <<< 20)

/-- Rotate right by 8. -/
@[inline] def rotr8 (x : UInt32) : UInt32 := (x >>> 8) ||| (x <<< 24)

/-- Rotate right by 7. -/
@[inline] def rotr7 (x : UInt32) : UInt32 := (x >>> 7) ||| (x <<< 25)

/-- Rotation by 16 is two shifts. -/
theorem rotr_sixteen (x : UInt32) : rotr x 16 = rotr16 x := by
  apply UInt32.toBitVec_inj.mp; simp [rotr, rotr16, BitVec.rotateRight_def]

/-- Rotation by 12 is two shifts. -/
theorem rotr_twelve (x : UInt32) : rotr x 12 = rotr12 x := by
  apply UInt32.toBitVec_inj.mp; simp [rotr, rotr12, BitVec.rotateRight_def]

/-- Rotation by 8 is two shifts. -/
theorem rotr_eight (x : UInt32) : rotr x 8 = rotr8 x := by
  apply UInt32.toBitVec_inj.mp; simp [rotr, rotr8, BitVec.rotateRight_def]

/-- Rotation by 7 is two shifts. -/
theorem rotr_seven (x : UInt32) : rotr x 7 = rotr7 x := by
  apply UInt32.toBitVec_inj.mp; simp [rotr, rotr7, BitVec.rotateRight_def]

/-- `mix` on native rotations. -/
@[inline] def mixFast (v : Vector UInt32 16) (a b c d : Fin 16) (x y : UInt32) :
    Vector UInt32 16 :=
  let va := v[a] + v[b] + x
  let vd := rotr16 (v[d] ^^^ va)
  let vc := v[c] + vd
  let vb := rotr12 (v[b] ^^^ vc)
  let va := va + vb + y
  let vd := rotr8 (vd ^^^ va)
  let vc := vc + vd
  let vb := rotr7 (vb ^^^ vc)
  (((v.set a va).set b vb).set c vc).set d vd

/-- `mixFast` is `mix`. -/
theorem mixFast_eq : mixFast = mix := by
  funext v a b c d x y
  simp only [mixFast, mix, rotr_sixteen, rotr_twelve, rotr_eight, rotr_seven]

/-- `G` on four words with native rotations: the new `(a, b, c, d)`. -/
@[inline] def mixWords (a b c d x y : UInt32) : UInt32 × UInt32 × UInt32 × UInt32 :=
  let a := a + b + x
  let d := rotr16 (d ^^^ a)
  let c := c + d
  let b := rotr12 (b ^^^ c)
  let a := a + b + y
  let d := rotr8 (d ^^^ a)
  let c := c + d
  let b := rotr7 (b ^^^ c)
  (a, b, c, d)

/-- The sixteen working words of `F`, one field each: `w0` through `w15`. -/
structure Words where
  (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : UInt32)

/-- The working words as a vector. -/
def Words.toVector (w : Words) : Vector UInt32 16 :=
  #v[w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6, w.w7, w.w8, w.w9, w.w10, w.w11, w.w12, w.w13,
    w.w14, w.w15]

/-- The working words of a vector. -/
def Words.ofVector (v : Vector UInt32 16) : Words :=
  ⟨v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8], v[9], v[10], v[11], v[12], v[13], v[14],
    v[15]⟩

/-- `round` on the working words: the four column and the four diagonal `mixWords`. -/
@[inline] def roundWords (v : Words) (m : Vector UInt32 16) (s : Vector (Fin 16) 16) : Words :=
  let x := fun i : Fin 16 ↦ m[s[i]]
  let r0 := mixWords v.w0 v.w4 v.w8 v.w12 (x 0) (x 1)
  let r1 := mixWords v.w1 v.w5 v.w9 v.w13 (x 2) (x 3)
  let r2 := mixWords v.w2 v.w6 v.w10 v.w14 (x 4) (x 5)
  let r3 := mixWords v.w3 v.w7 v.w11 v.w15 (x 6) (x 7)
  let r4 := mixWords r0.1 r1.2.1 r2.2.2.1 r3.2.2.2 (x 8) (x 9)
  let r5 := mixWords r1.1 r2.2.1 r3.2.2.1 r0.2.2.2 (x 10) (x 11)
  let r6 := mixWords r2.1 r3.2.1 r0.2.2.1 r1.2.2.2 (x 12) (x 13)
  let r7 := mixWords r3.1 r0.2.1 r1.2.2.1 r2.2.2.2 (x 14) (x 15)
  ⟨r4.1, r5.1, r6.1, r7.1, r7.2.1, r4.2.1, r5.2.1, r6.2.1, r6.2.2.1, r7.2.2.1, r4.2.2.1, r5.2.2.1,
    r5.2.2.2, r6.2.2.2, r7.2.2.2, r4.2.2.2⟩

private theorem toVector_ofVector (v : Vector UInt32 16) : (Words.ofVector v).toVector = v := by
  ext i hi
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;>
    first | rfl | omega

private theorem mixFast_toVector_0 (v : Words) (x y : UInt32) :
    mixFast v.toVector 0 4 8 12 x y = (let r := mixWords v.w0 v.w4 v.w8 v.w12 x y
      { v with w0 := r.1, w4 := r.2.1, w8 := r.2.2.1, w12 := r.2.2.2 }).toVector := rfl

private theorem mixFast_toVector_1 (v : Words) (x y : UInt32) :
    mixFast v.toVector 1 5 9 13 x y = (let r := mixWords v.w1 v.w5 v.w9 v.w13 x y
      { v with w1 := r.1, w5 := r.2.1, w9 := r.2.2.1, w13 := r.2.2.2 }).toVector := rfl

private theorem mixFast_toVector_2 (v : Words) (x y : UInt32) :
    mixFast v.toVector 2 6 10 14 x y = (let r := mixWords v.w2 v.w6 v.w10 v.w14 x y
      { v with w2 := r.1, w6 := r.2.1, w10 := r.2.2.1, w14 := r.2.2.2 }).toVector := rfl

private theorem mixFast_toVector_3 (v : Words) (x y : UInt32) :
    mixFast v.toVector 3 7 11 15 x y = (let r := mixWords v.w3 v.w7 v.w11 v.w15 x y
      { v with w3 := r.1, w7 := r.2.1, w11 := r.2.2.1, w15 := r.2.2.2 }).toVector := rfl

private theorem mixFast_toVector_4 (v : Words) (x y : UInt32) :
    mixFast v.toVector 0 5 10 15 x y = (let r := mixWords v.w0 v.w5 v.w10 v.w15 x y
      { v with w0 := r.1, w5 := r.2.1, w10 := r.2.2.1, w15 := r.2.2.2 }).toVector := rfl

private theorem mixFast_toVector_5 (v : Words) (x y : UInt32) :
    mixFast v.toVector 1 6 11 12 x y = (let r := mixWords v.w1 v.w6 v.w11 v.w12 x y
      { v with w1 := r.1, w6 := r.2.1, w11 := r.2.2.1, w12 := r.2.2.2 }).toVector := rfl

private theorem mixFast_toVector_6 (v : Words) (x y : UInt32) :
    mixFast v.toVector 2 7 8 13 x y = (let r := mixWords v.w2 v.w7 v.w8 v.w13 x y
      { v with w2 := r.1, w7 := r.2.1, w8 := r.2.2.1, w13 := r.2.2.2 }).toVector := rfl

private theorem mixFast_toVector_7 (v : Words) (x y : UInt32) :
    mixFast v.toVector 3 4 9 14 x y = (let r := mixWords v.w3 v.w4 v.w9 v.w14 x y
      { v with w3 := r.1, w4 := r.2.1, w9 := r.2.2.1, w14 := r.2.2.2 }).toVector := rfl

/-- `roundWords` is `round` on the working words. -/
private theorem toVector_roundWords (v : Words) (m : Vector UInt32 16) (s : Vector (Fin 16) 16) :
    (roundWords v m s).toVector = round v.toVector m s := by
  rw [round, ← mixFast_eq]
  simp only [mixFast_toVector_0, mixFast_toVector_1, mixFast_toVector_2, mixFast_toVector_3,
    mixFast_toVector_4, mixFast_toVector_5, mixFast_toVector_6, mixFast_toVector_7]
  rfl

/-- `round` through `roundWords`. -/
def roundFast (v m : Vector UInt32 16) (s : Vector (Fin 16) 16) : Vector UInt32 16 :=
  (roundWords (.ofVector v) m s).toVector

/-- `roundFast` is `round`. -/
theorem roundFast_eq : roundFast = round := by
  funext v m s
  rw [roundFast, toVector_roundWords, toVector_ofVector]

end Blake2s

/-- `compress` on native rotations and unboxed working words. -/
def compressFast (h : Vector UInt32 8) (m : Vector UInt32 16) (t : UInt64) (f0 f1 : UInt32) :
    Vector UInt32 8 :=
  let v := (sigma.foldl (fun v s ↦ Blake2s.roundWords v m s)
    (.ofVector (Blake2s.initialState h t f0 f1))).toVector
  #v[h[0] ^^^ v[0] ^^^ v[8], h[1] ^^^ v[1] ^^^ v[9], h[2] ^^^ v[2] ^^^ v[10],
     h[3] ^^^ v[3] ^^^ v[11], h[4] ^^^ v[4] ^^^ v[12], h[5] ^^^ v[5] ^^^ v[13],
     h[6] ^^^ v[6] ^^^ v[14], h[7] ^^^ v[7] ^^^ v[15]]

/-- The rounds of `compress` are those of `compressFast`. -/
private theorem foldl_words (h : Vector UInt32 8) (m : Vector UInt32 16) (t : UInt64)
    (f0 f1 : UInt32) :
    sigma.foldl (fun v s ↦ Blake2s.round v m s) (Blake2s.initialState h t f0 f1) =
      (sigma.foldl (fun v s ↦ Blake2s.roundWords v m s)
        (.ofVector (Blake2s.initialState h t f0 f1))).toVector := by
  conv_lhs => rw [← Blake2s.toVector_ofVector (Blake2s.initialState h t f0 f1)]
  exact Vector.foldl_hom _ fun v s ↦ (Blake2s.toVector_roundWords v m s).symm

/-- Compiled code compresses through `compressFast`. -/
@[csimp] theorem compress_eq_compressFast : @compress = @compressFast := by
  funext h m t f0 f1
  exact congrArg (fun v : Vector UInt32 16 ↦
    #v[h[0] ^^^ v[0] ^^^ v[8], h[1] ^^^ v[1] ^^^ v[9], h[2] ^^^ v[2] ^^^ v[10],
      h[3] ^^^ v[3] ^^^ v[11], h[4] ^^^ v[4] ^^^ v[12], h[5] ^^^ v[5] ^^^ v[13],
      h[6] ^^^ v[6] ^^^ v[14], h[7] ^^^ v[7] ^^^ v[15]]) (foldl_words h m t f0 f1)

/-- The decision of `CompressCells` through `compressFast`. -/
@[instance_reducible] def decidableCompressCellsFast {m : Fin 4 → E} {cv0 cv1 out0 out1 md : E} :
    Decidable (CompressCells m cv0 cv1 out0 out1 md) :=
  decidable_of_iff
    ((∀ i, IsCanonical128 (m i)) ∧ IsCanonical128 cv0 ∧ IsCanonical128 cv1 ∧
      IsCanonical128 out0 ∧ IsCanonical128 out1 ∧ IsCanonical128 md ∧
      (cellWords out0 ++ cellWords out1).toList =
        (compressFast (cellWords cv0 ++ cellWords cv1) (messageWords m) (unpackMetadata md).1
          (unpackMetadata md).2.1 (unpackMetadata md).2.2).toList)
    (by simp only [CompressCells, ← compress_eq_compressFast, Vector.toList_inj])

/-- Compiled code decides `CompressCells` through `compressFast`. -/
@[csimp] theorem instDecidableCompressCells_eq :
    @instDecidableCompressCells = @decidableCompressCellsFast := by
  funext m cv0 cv1 out0 out1 md
  exact Subsingleton.elim _ _

end
end LeanerVM.Semantics
