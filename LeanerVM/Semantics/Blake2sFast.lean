/-
  LeanerVM.Semantics.Blake2sFast

  The BLAKE2s compression function on native word rotations, proved equal to `compress` and
  registered for compiled code.
-/

module

public import LeanerVM.Semantics.Blake2s

/-!
# BLAKE2s compression on native rotations

`compress` rotates through `BitVec.rotateRight`, which compiles to arithmetic on natural numbers.
`compressFast` is the same function with each rotation by `16`, `12`, `8` or `7` written as two
`UInt32` shifts (`rotr_sixteen` through `rotr_seven`), and `compressFast_eq` proves the two equal.
The `@[csimp]` theorem `compress_eq_compressFast` makes every compiled call of `compress` after
this module run `compressFast`; `instDecidableCompressCells_eq` does the same for the decision of
`CompressCells`, whose instance was compiled before this module. Nothing here is trusted beyond
the two equations; the specification is `compress`.
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

/-- `round` on native rotations. -/
def roundFast (v m : Vector UInt32 16) (s : Vector (Fin 16) 16) : Vector UInt32 16 :=
  let v := mixFast v 0 4 8 12 m[s[0]] m[s[1]]
  let v := mixFast v 1 5 9 13 m[s[2]] m[s[3]]
  let v := mixFast v 2 6 10 14 m[s[4]] m[s[5]]
  let v := mixFast v 3 7 11 15 m[s[6]] m[s[7]]
  let v := mixFast v 0 5 10 15 m[s[8]] m[s[9]]
  let v := mixFast v 1 6 11 12 m[s[10]] m[s[11]]
  let v := mixFast v 2 7 8 13 m[s[12]] m[s[13]]
  mixFast v 3 4 9 14 m[s[14]] m[s[15]]

/-- `roundFast` is `round`. -/
theorem roundFast_eq : roundFast = round := by
  funext v m s
  simp only [roundFast, round, mixFast_eq]

end Blake2s

/-- `compress` on native rotations. -/
def compressFast (h : Vector UInt32 8) (m : Vector UInt32 16) (t : UInt64) (f0 f1 : UInt32) :
    Vector UInt32 8 :=
  let v := sigma.foldl (fun v s ↦ Blake2s.roundFast v m s) (Blake2s.initialState h t f0 f1)
  #v[h[0] ^^^ v[0] ^^^ v[8], h[1] ^^^ v[1] ^^^ v[9], h[2] ^^^ v[2] ^^^ v[10],
     h[3] ^^^ v[3] ^^^ v[11], h[4] ^^^ v[4] ^^^ v[12], h[5] ^^^ v[5] ^^^ v[13],
     h[6] ^^^ v[6] ^^^ v[14], h[7] ^^^ v[7] ^^^ v[15]]

/-- Compiled code compresses through `compressFast`. -/
@[csimp] theorem compress_eq_compressFast : @compress = @compressFast := by
  funext h m t f0 f1
  simp only [compress, compressFast, Blake2s.roundFast_eq]

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
