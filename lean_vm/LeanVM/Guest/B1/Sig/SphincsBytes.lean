/-
  LeanVM.Guest.B1.Sig.SphincsBytes

  `sp_from_bytes` (`lean_ethereum.py:3528-3544`) is sound: on a memory image of at most `2^32`
  words holding the byte table, its value is a word below the bound its marks' range checks give.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsKec
public import LeanVM.Guest.B1.Sig.Interface

/-!
# `sp_from_bytes`, sound

* `range_sound`: a range check against `g^(K-1)` passes only for `x = g^e`, `e < K`, on a memory of
  at most `2^32` words (`rangeCheck_iff`'s soundness half, for any `K ≤ 2^32`);
* `sByte_sound`: a byte mark range checked below `K ≤ 256` and read off the byte table is the word
  `e < K`;
* `sFromBytesRest_sound`, `sFromBytes_sound`: the folded value is a word below
  `K · 256^(bytes - 1)`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

variable {σ : Val}

/-- **A range check, sound**: against `g^(K-1)`, on a memory image of at most `2^32` words, the
value is `g^e` for some `e < K`. -/
theorem range_sound {κ : Nat} (hκ : κ ≤ 32) (L : MemImage κ) {x y t1 t2 : E} {K : Nat}
    (hK : 1 ≤ K) (hK' : K ≤ 2 ^ 32) (h1 : LoadHolds L.read x 0 t1) (hk : ofK (gpow (K - 1)) = x * y)
    (h2 : LoadHolds L.read y 0 t2) : ∃ e < K, x = ofK (gpow e) := by
  have hκ64 : κ < 64 := by omega
  have h32 : 2 ^ κ ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) hκ
  obtain ⟨hx, h1⟩ := h1
  obtain ⟨hy, h2⟩ := h2
  rw [gpow, pow_zero, mul_one] at h1 h2
  obtain ⟨i, hi, -⟩ := (read_some_iff hκ64 L _ _).mp h1
  obtain ⟨j, hj, -⟩ := (read_some_iff hκ64 L _ _).mp h2
  have ex : x = ofK (gpow i) := by rw [eq_ofK_limb hx, hi]
  have ey : y = ofK (gpow j) := by rw [eq_ofK_limb hy, hj]
  rw [ex, ey, ← ofK_mul, gpow, gpow, ← pow_add] at hk
  have hij := gpow_injOn (by have := i.isLt; have := j.isLt; simp only [Set.mem_Iio]; omega)
    (by simp only [Set.mem_Iio]; omega) (ofK_injective hk).symm
  exact ⟨i, by omega, ex⟩

theorem g255W_eq : g255W = ofK (gpow 255) := by
  rw [g255W, word, Value.ofBits_zero, ← ofK_eq_ofLimbs]
  exact congrArg ofK (by decide +kernel)

theorem g63W_eq : g63W = ofK (gpow 63) := by
  rw [g63W, word, Value.ofBits_zero, ← ofK_eq_ofLimbs]
  exact congrArg ofK (by decide +kernel)

theorem g15W_eq : g15W = ofK (gpow 15) := by
  rw [g15W, word, Value.ofBits_zero, ← ofK_eq_ofLimbs]
  exact congrArg ofK (by decide +kernel)

theorem g7W_eq : g7W = ofK (gpow 7) := by
  rw [g7W, word, Value.ofBits_zero, ← ofK_eq_ofLimbs]
  exact congrArg ofK (by decide +kernel)

/-- **A byte, sound**: a mark range checked below `K ≤ 256` and read off the byte table at
`σ (.n 1)` is the word of its exponent. -/
theorem sByte_sound {κ : Nat} (hκ : κ ≤ 32) {L : MemImage κ} {mark : V} {bound : E} {b K : Nat}
    (hK : 1 ≤ K) (hK256 : K ≤ 256) (hbound : bound = ofK (gpow (K - 1)))
    (hbb : ByteBits L.read (σ (.n 1))) (h : AtomsHold L.read σ (sByte mark bound b)) :
    ∃ e < K, σ (.n (b + 5)) = eOfNat e := by
  have c : σ (.n b) = bound := h.atom (a := .const (.n b) bound) (by simp [sByte, rangeS, cst])
  have r := h.atom (a := .rangeCheck mark (.n (b + 1)) (.n (b + 2)) (.n (b + 3)) (.n b))
    (by simp [sByte, rangeS])
  have m : σ (.n (b + 4)) = σ (.n 1) * σ mark :=
    h.atom (a := .mul (.n (b + 4)) (.n 1) mark) (by simp [sByte, mulS])
  have l : LoadHolds L.read (σ (.n (b + 4))) 0 (σ (.n (b + 5))) :=
    h.atom (a := .load (.n (b + 5)) (.n (b + 4)) 0) (by simp [sByte, loadS])
  obtain ⟨r1, r2, r3⟩ := r
  rw [c, hbound] at r2
  obtain ⟨e, he, hm⟩ := range_sound hκ L hK (by omega) r1 r2 r3
  obtain ⟨hbbK, hbbv⟩ := hbb e (by omega)
  obtain ⟨-, hl⟩ := l
  have hp : σ (.n (b + 4)) = ofK ((σ (.n 1)).limb 0 * gpow e) := by
    rw [m, hm, ofK_mul, ← eq_ofK_limb hbbK]
  have hl0 : (ofK ((σ (.n 1)).limb 0 * gpow e)).limb 0 = (σ (.n 1)).limb 0 * gpow e := by simp
  rw [hp, hl0] at hl
  simp only [gpow, pow_zero, mul_one] at hl hbbv
  refine ⟨e, he, ?_⟩
  rw [hbbv] at hl
  rw [← word_eq_eOfNat]
  exact (Option.some.inj hl).symm

theorem word256_eq : word 256 0 0 = eOfNat (2 ^ 8) := word_eq_eOfNat 256

/-- **The bytes after the top one, folded**: from a word below `M`, a word below `M · 256^n`. -/
theorem sFromBytesRest_sound {κ : Nat} (hκ : κ ≤ 32) {L : MemImage κ}
    (hbb : ByteBits L.read (σ (.n 1))) :
    ∀ (ms : List V) (b : Nat) (val : V) (N M : Nat), σ val = eOfNat N → N < M →
      M * 256 ^ ms.length ≤ 2 ^ 64 → AtomsHold L.read σ (sFromBytesRest ms b val).1 →
      ∃ N', σ (sFromBytesRest ms b val).2.2 = eOfNat N' ∧ N' < M * 256 ^ ms.length
  | [], _, _, N, M, hv, hN, _, _ => ⟨N, hv, by simpa using hN⟩
  | m :: ms, b, val, N, M, hv, hN, hM, h => by
      have h' : AtomsHold L.read σ (sByte m g255W b ++ [cst (b + 6) (word 256 0 0),
          mulS (.n (b + 7)) val (.n (b + 6)), addS (.n (b + 8)) (.n (b + 5)) (.n (b + 7))] ++
          (sFromBytesRest ms (b + 9) (.n (b + 8))).1) := h
      obtain ⟨e, he, hb⟩ := sByte_sound hκ (K := 256) (by norm_num) (by norm_num) g255W_eq hbb h'.left.left
      have c : σ (.n (b + 6)) = word 256 0 0 :=
        h'.left.right.atom (a := .const (.n (b + 6)) _) (by simp [cst])
      have mu : σ (.n (b + 7)) = σ val * σ (.n (b + 6)) :=
        h'.left.right.atom (a := .mul (.n (b + 7)) val (.n (b + 6))) (by simp [mulS])
      have ad : σ (.n (b + 8)) = σ (.n (b + 5)) + σ (.n (b + 7)) :=
        h'.left.right.atom (a := .add (.n (b + 8)) (.n (b + 5)) (.n (b + 7))) (by simp [addS])
      have hpow : 256 ^ (ms.length + 1) = 256 ^ ms.length * 256 := pow_succ _ _
      have hM1 : 1 ≤ 256 ^ ms.length := Nat.one_le_pow _ _ (by norm_num)
      have hM256 : M * 256 ≤ 2 ^ 64 := by
        simp only [List.length_cons, hpow] at hM
        nlinarith
      have hv8 : σ (.n (b + 8)) = eOfNat (2 ^ 8 * N + e) := by
        rw [ad, mu, c, hv, hb, word256_eq, mul_comm, eOfNat_two_pow_mul (by omega), add_comm,
          Value.eOfNat_add_of_lt (by omega)]
      obtain ⟨N', h1, h2⟩ := sFromBytesRest_sound hκ hbb ms (b + 9) (.n (b + 8)) (2 ^ 8 * N + e)
        (M * 256) hv8 (by omega) (by simp only [List.length_cons, hpow] at hM; linarith) h'.right
      refine ⟨N', h1, ?_⟩
      simp only [List.length_cons, hpow]
      linarith

/-- **`sp_from_bytes`, sound**: the top byte range checked below `K`, the value is a word below
`K · 256^n`, `n` the bytes after it. -/
theorem sFromBytes_sound {κ : Nat} (hκ : κ ≤ 32) {L : MemImage κ} (hbb : ByteBits L.read (σ (.n 1)))
    {top : V} {rest : List V} {bound : E} {b K : Nat} (hK : 1 ≤ K) (hK256 : K ≤ 256)
    (hbound : bound = ofK (gpow (K - 1))) (hM : K * 256 ^ rest.length ≤ 2 ^ 64)
    (h : AtomsHold L.read σ (sFromBytes top rest bound b).1) :
    ∃ N, σ (sFromBytes top rest bound b).2.2 = eOfNat N ∧ N < K * 256 ^ rest.length := by
  have h' : AtomsHold L.read σ (sByte top bound b ++ (sFromBytesRest rest (b + 6) (.n (b + 5))).1) := h
  obtain ⟨e, he, hb⟩ := sByte_sound hκ hK hK256 hbound hbb h'.left
  exact sFromBytesRest_sound hκ hbb rest (b + 6) (.n (b + 5)) e K hb he hM h'.right

end
end LeanVM.Guest.B1.Sig
