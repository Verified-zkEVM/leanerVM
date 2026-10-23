/-
  LeanVM.Guest.B1.KeccakGkr.VkHead

  `verify_keccak`'s head (G:2784-2827): `pack_g`, `y`'s bits, `half_g`, `odd_g`, `y_last`.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkT

/-!
# `y` in the exponent

With the table's height `τ` (`tau_g = g^τ`), `pack_g = g^(τ - 4)` and `y_g = g^(τ - 3)`; the
hinted bits of `y = τ - 3`, pinned boolean, give `half_g = g^(y / 2)`, `odd_g = g^(y % 2)` and
`y_last = g^(y/2 + y % 2)`, which `assert half_g·y_last = y_g` ties back to `y`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- `INV_GEN^4`, as the data writes it, is `g⁻⁴`. -/
theorem word_ginv4_mul : word 8070450532247928836 0 0 * gen ^ 4 = 1 := by
  rw [show gen ^ 4 = ofK (K.ofBits 16) by rw [← word_two_pow (a := 4) (by decide)]; exact word_eOfNat _,
    show word 8070450532247928836 0 0 = ofK (K.ofBits 8070450532247928836) from word_eOfNat _,
    ← ofK_mul, show K.ofBits 8070450532247928836 * K.ofBits 16 = 1 by decide +kernel, ofK_one]

theorem bool_of_mul_self {b : E} (h : b * b = b) : b = 0 ∨ b = 1 := by
  have h' : b * (b - 1) = 0 := by rw [mul_sub, h, mul_one, sub_self]
  rcases mul_eq_zero.mp h' with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

/-- **`y` in the exponent** (G:2788-2804). -/
theorem vkBits_holds {τ : ℕ} (hτ1 : 9 ≤ τ) (hτ2 : τ ≤ 28) (htg : σ (.n 6) = gen ^ τ)
    {next : Prop} {kret : List E → Prop} (h : Stmt.HoldsList C rd σ vkBitsT next kret) :
    σ (.n 17) = gen ^ (τ - 4) ∧ σ (.n 19) = gen ^ (τ - 3) ∧
      σ (.n 43) = gen ^ ((τ - 3) / 2) ∧ σ (.n 47) = gen ^ ((τ - 3) % 2) ∧
      σ (.n 48) = gen ^ ((τ - 3) / 2 + (τ - 3) % 2) ∧ next := by
  simp only [vkBitsT, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨e16, e17, e18, e19, -, b0, b1, e25, e26, e27, e28, b2, e29, e30, e31, e32, e33, b3, e34,
    e35, e36, e37, e38, b4, e39, e40, e41, e42, e43, e44, e45, e46, e47, e48, e49, e50, e51, heq,
    hn⟩ := h
  have h17 : σ (.n 17) = gen ^ (τ - 4) := by
    rw [e17, htg, e16, show τ = τ - 4 + 4 by omega, pow_add, mul_assoc, mul_comm (gen ^ 4),
      word_ginv4_mul, mul_one]
    congr 1
  have h19 : σ (.n 19) = gen ^ (τ - 3) := by
    rw [e19, h17, e18, word_gen, ← pow_succ]; congr 1; omega
  -- the half chain is a product over the bits 1 .. 4
  set c : ℕ → E := fun k ↦ σ (.n (21 + k)) with hc
  have hcb : ∀ k < 4, c k * c k = c k := by
    intro k hk
    interval_cases k
    · exact b1.symm
    · exact b2.symm
    · exact b3.symm
    · exact b4.symm
  have hprod := prod_gen_pow_of_bool hcb
  have h43 : σ (.n 43) = ∏ j ∈ Finset.range 4, (1 + c j * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, hc]
    rw [e43, e42, e41, e40, e39, e38, e37, e36, e35, e34, e33, e32, e31, e30, e29, e28, e27, e26,
      e25]
    simp only [word_one, Nat.reduceAdd]
    rw [show word 3 0 0 = gen ^ 2 ^ 0 + 1 by
          rw [word_eOfNat, show (3 : ℕ) = 2 ^ 1 ^^^ 1 from rfl, eOfNat_xor, eOfNat_one,
            ← word_eOfNat, word_two_pow (by decide)]; simp,
      show word 5 0 0 = gen ^ 2 ^ 1 + 1 by
          rw [word_eOfNat, show (5 : ℕ) = 2 ^ 2 ^^^ 1 from rfl, eOfNat_xor, eOfNat_one,
            ← word_eOfNat, word_two_pow (by decide)]; norm_num,
      show word 17 0 0 = gen ^ 2 ^ 2 + 1 by
          rw [word_eOfNat, show (17 : ℕ) = 2 ^ 4 ^^^ 1 from rfl, eOfNat_xor, eOfNat_one,
            ← word_eOfNat, word_two_pow (by decide)]; norm_num,
      show word 257 0 0 = gen ^ 2 ^ 3 + 1 by
          rw [word_eOfNat, show (257 : ℕ) = 2 ^ 8 ^^^ 1 from rfl, eOfNat_xor, eOfNat_one,
            ← word_eOfNat, word_two_pow (by decide)]; norm_num]
  rw [hprod] at h43
  set H := bitsVal (fun j ↦ decide (c j = 1)) 4 with hH
  have hHlt : H < 16 := bitsVal_lt _ 4
  -- the odd bit
  have hb0 := bool_of_mul_self b0.symm
  set o : ℕ := if σ (.n 20) = 1 then 1 else 0 with ho
  have h47 : σ (.n 47) = gen ^ o := by
    rw [e47, e46, e45, e44, word_one]
    rcases hb0 with h0 | h1
    · simp [ho, h0]
    · rw [show o = 1 by simp [ho, h1], h1, show word 3 0 0 = gen + 1 by
        rw [word_eOfNat, show (3 : ℕ) = 2 ^ 1 ^^^ 1 from rfl, eOfNat_xor, eOfNat_one,
          ← word_eOfNat, word_two_pow (by decide), pow_one]]
      rw [one_mul, pow_one, ← add_assoc, add_comm (1 : E) gen, add_assoc, e_add_self, add_zero]
  have ho1 : o < 2 := by simp only [ho]; split <;> omega
  -- the check
  have hchk : gen ^ (2 * H + o) = gen ^ (τ - 3) := by
    have := eq_of_add_eq_zero' heq
    rw [e49, e48, h43, h47, e51, e50, h17, word_gen, ← pow_succ, ← pow_add, ← pow_add] at this
    rw [show 2 * H + o = H + (H + o) by ring, this]; congr 1; omega
  have hy := gen_pow_inj (by omega) (by omega) hchk
  refine ⟨h17, h19, ?_, ?_, ?_, hn⟩
  · rw [h43]; congr 1; omega
  · rw [h47]; congr 1; omega
  · rw [e48, h43, h47, ← pow_add]; congr 1; omega

end
end LeanVM.Guest.B1.VerifySub
