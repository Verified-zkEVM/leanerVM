module

public import Statement.SufCma

/-!
# `digestBitVec`, compiled fast

`Common.SufCma.digestBitVec`, the digest's bytes as a little-endian number, compiles as a fold
(`digestBitVec_eq_digestBitVecFast`, `@[csimp]`): proved, for speed only.
-/

namespace LeanVM.Fast.SufCma

@[expose] public section

/-! ## A digest's bytes as a number -/

/-- `Common.SufCma.digestBitVec`, the bytes' little-endian number by a fold. -/
def digestBitVecFold (d : Common.DigestBytes) : BitVec 256 :=
  BitVec.ofNat 256 (d.toList.foldr (fun b acc ↦ b.toNat + 256 * acc) 0)

/-- The little-endian number of a list of bytes is the sum of its bytes' weights. -/
theorem foldr_bytes_eq_sum : ∀ l : List UInt8,
    l.foldr (fun b acc ↦ b.toNat + 256 * acc) 0 =
      ∑ i ∈ Finset.range l.length, (l.getD i 0).toNat * 256 ^ i
  | [] => rfl
  | b :: l => by
    rw [List.foldr_cons, foldr_bytes_eq_sum l, List.length_cons, Finset.sum_range_succ',
      Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring

/-- **`digestBitVec` is the fold.** -/
theorem digestBitVec_eq_digestBitVecFold (d : Common.DigestBytes) :
    Common.SufCma.digestBitVec d = digestBitVecFold d := by
  have hval : (Common.SufCma.digestBitVec d).toNat =
      ∑ i : Fin 32, (d[(i : ℕ)]).toNat * 256 ^ (i : ℕ) := by
    change ((finFunctionFinEquiv
      (fun i : Fin 32 ↦ Common.uInt8EquivFin (d[(i : ℕ)])) : Fin (256 ^ 32)) : ℕ) = _
    rw [finFunctionFinEquiv_apply]
    rfl
  have hsum : ∑ i : Fin 32, (d[(i : ℕ)]).toNat * 256 ^ (i : ℕ) =
      ∑ i ∈ Finset.range d.toList.length, (d.toList.getD i 0).toNat * 256 ^ i := by
    rw [Vector.length_toList,
      ← Fin.sum_univ_eq_sum_range (fun i ↦ (d.toList.getD i 0).toNat * 256 ^ i)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [List.getD_eq_getElem?_getD]
  apply BitVec.eq_of_toNat_eq
  rw [digestBitVecFold, BitVec.toNat_ofNat, foldr_bytes_eq_sum, ← hsum, ← hval,
    Nat.mod_eq_of_lt (Common.SufCma.digestBitVec d).isLt]

/-- `Common.SufCma.digestBitVec` with the fold for its function. -/
def digestBitVecFast : Common.DigestBytes ≃ BitVec 256 where
  toFun := digestBitVecFold
  invFun := Common.SufCma.digestBitVec.symm
  left_inv d := by rw [← digestBitVec_eq_digestBitVecFold, Equiv.symm_apply_apply]
  right_inv b := by rw [← digestBitVec_eq_digestBitVecFold, Equiv.apply_symm_apply]

/-- `Common.SufCma.digestBitVec` compiles as `digestBitVecFast`. -/
@[csimp] theorem digestBitVec_eq_digestBitVecFast :
    @Common.SufCma.digestBitVec = @digestBitVecFast :=
  Equiv.ext digestBitVec_eq_digestBitVecFold

end

end LeanVM.Fast.SufCma
