/-
  LeanVM.Guest.B1.Tables.Vt.ZcCert

  `verify_tables`' table sumcheck's round count: the hinted `g^n` is `g^(max τ_t)`, below the bus
  point's length.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Fresh

/-!
# The table sumcheck's rounds (G:2183-2194)

`g_zc_n` is hinted; every `τ_t` is at most `n` (a range-checked quotient), some `τ_t` is `n` (the
product of `g^n + g^τ_t` is zero), and `n ≤ μ` (`vt_zc_n`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- `g^32`, as the data writes it. -/
abbrev vtW32 : E := word 4294967296 0 0

theorem vtW32_eq : vtW32 = ofK (Parameters.gpow 32) := by
  rw [vtW32, show (4294967296 : ℕ) = 2 ^ 32 by norm_num, tb_word_two_pow (by norm_num),
    gen_pow_eq_ofK]

section
variable {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemImage μ)
include hμ

/-- **The round count.** -/
theorem vt_zc_n {σ : Val} (h : VtH Lm.read σ) {τ : ℕ → ℕ} (hτ : ∀ t < 6, τ t < 29)
    (hdim : ∀ t < 6, LoadHolds Lm.read (σ (.n 10)) (t + 1) (gen ^ τ t)) {m : ℕ} (hm : m < 33)
    (hmu : σ (.n 9) = gen ^ m) :
    ∃ n, σ (.n 5817) = gen ^ n ∧ (∀ t < 6, τ t ≤ n) ∧ (∃ t < 6, τ t = n) ∧ n ≤ m := by
  have a5153 := h.atom 5153 (.load (.n 5818) (.n 10) 1) (by decide +kernel)
  have a5154 := h.atom 5154 (.const (.n 5819) (word 4294967296 0 0)) (by decide +kernel)
  have a5155 := h.atom 5155 (.mul (.n 5817) (.n 5820) (.n 5818)) (by decide +kernel)
  have a5156 := h.atom 5156 (.rangeCheck (.n 5820) (.n 5821) (.n 5822) (.n 5823) (.n 5819)) (by decide +kernel)
  have a5157 := h.atom 5157 (.add (.n 5824) (.n 5817) (.n 5818)) (by decide +kernel)
  have a5158 := h.atom 5158 (.load (.n 5825) (.n 10) 2) (by decide +kernel)
  have a5159 := h.atom 5159 (.const (.n 5826) (word 4294967296 0 0)) (by decide +kernel)
  have a5160 := h.atom 5160 (.mul (.n 5817) (.n 5827) (.n 5825)) (by decide +kernel)
  have a5161 := h.atom 5161 (.rangeCheck (.n 5827) (.n 5828) (.n 5829) (.n 5830) (.n 5826)) (by decide +kernel)
  have a5162 := h.atom 5162 (.add (.n 5831) (.n 5817) (.n 5825)) (by decide +kernel)
  have a5163 := h.atom 5163 (.mul (.n 5832) (.n 5824) (.n 5831)) (by decide +kernel)
  have a5164 := h.atom 5164 (.load (.n 5833) (.n 10) 3) (by decide +kernel)
  have a5165 := h.atom 5165 (.const (.n 5834) (word 4294967296 0 0)) (by decide +kernel)
  have a5166 := h.atom 5166 (.mul (.n 5817) (.n 5835) (.n 5833)) (by decide +kernel)
  have a5167 := h.atom 5167 (.rangeCheck (.n 5835) (.n 5836) (.n 5837) (.n 5838) (.n 5834)) (by decide +kernel)
  have a5168 := h.atom 5168 (.add (.n 5839) (.n 5817) (.n 5833)) (by decide +kernel)
  have a5169 := h.atom 5169 (.mul (.n 5840) (.n 5832) (.n 5839)) (by decide +kernel)
  have a5170 := h.atom 5170 (.load (.n 5841) (.n 10) 4) (by decide +kernel)
  have a5171 := h.atom 5171 (.const (.n 5842) (word 4294967296 0 0)) (by decide +kernel)
  have a5172 := h.atom 5172 (.mul (.n 5817) (.n 5843) (.n 5841)) (by decide +kernel)
  have a5173 := h.atom 5173 (.rangeCheck (.n 5843) (.n 5844) (.n 5845) (.n 5846) (.n 5842)) (by decide +kernel)
  have a5174 := h.atom 5174 (.add (.n 5847) (.n 5817) (.n 5841)) (by decide +kernel)
  have a5175 := h.atom 5175 (.mul (.n 5848) (.n 5840) (.n 5847)) (by decide +kernel)
  have a5176 := h.atom 5176 (.load (.n 5849) (.n 10) 5) (by decide +kernel)
  have a5177 := h.atom 5177 (.const (.n 5850) (word 4294967296 0 0)) (by decide +kernel)
  have a5178 := h.atom 5178 (.mul (.n 5817) (.n 5851) (.n 5849)) (by decide +kernel)
  have a5179 := h.atom 5179 (.rangeCheck (.n 5851) (.n 5852) (.n 5853) (.n 5854) (.n 5850)) (by decide +kernel)
  have a5180 := h.atom 5180 (.add (.n 5855) (.n 5817) (.n 5849)) (by decide +kernel)
  have a5181 := h.atom 5181 (.mul (.n 5856) (.n 5848) (.n 5855)) (by decide +kernel)
  have a5182 := h.atom 5182 (.load (.n 5857) (.n 10) 6) (by decide +kernel)
  have a5183 := h.atom 5183 (.const (.n 5858) (word 4294967296 0 0)) (by decide +kernel)
  have a5184 := h.atom 5184 (.mul (.n 5817) (.n 5859) (.n 5857)) (by decide +kernel)
  have a5185 := h.atom 5185 (.rangeCheck (.n 5859) (.n 5860) (.n 5861) (.n 5862) (.n 5858)) (by decide +kernel)
  have a5186 := h.atom 5186 (.add (.n 5863) (.n 5817) (.n 5857)) (by decide +kernel)
  have a5187 := h.atom 5187 (.mul (.n 5864) (.n 5856) (.n 5863)) (by decide +kernel)
  have a5188 := h.atom 5188 (.const (.n 5865) (word 0 0 0)) (by decide +kernel)
  have a5189 := h.atom 5189 (.assertEq (.n 5864) (.n 5865)) (by decide +kernel)
  have a5190 := h.atom 5190 (.const (.n 5866) (word 4294967296 0 0)) (by decide +kernel)
  have a5191 := h.atom 5191 (.mul (.n 9) (.n 5867) (.n 5817)) (by decide +kernel)
  have a5192 := h.atom 5192 (.rangeCheck (.n 5867) (.n 5868) (.n 5869) (.n 5870) (.n 5866)) (by decide +kernel)
  simp only [Atom.Holds] at a5153 a5154 a5155 a5157 a5158 a5159 a5160 a5162 a5163 a5164
  simp only [Atom.Holds] at a5165 a5166 a5168 a5169 a5170 a5171 a5172 a5174 a5175 a5176
  simp only [Atom.Holds] at a5177 a5178 a5180 a5181 a5182 a5183 a5184 a5186 a5187 a5188 a5189
  simp only [Atom.Holds] at a5190 a5191
  have v0 := tb_loadHolds_unique a5153 (hdim 0 (by norm_num))
  have v1 := tb_loadHolds_unique a5158 (hdim 1 (by norm_num))
  have v2 := tb_loadHolds_unique a5164 (hdim 2 (by norm_num))
  have v3 := tb_loadHolds_unique a5170 (hdim 3 (by norm_num))
  have v4 := tb_loadHolds_unique a5176 (hdim 4 (by norm_num))
  have v5 := tb_loadHolds_unique a5182 (hdim 5 (by norm_num))
  have rc := fun {x y t1 t2 k : V} (hk : σ k = vtW32)
      (hh : (Atom.rangeCheck x y t1 t2 k).Holds Lm.read σ) =>
    vt_rc hμ Lm (K := 33) (by omega) (by norm_num) (by rw [hk, vtW32_eq]) hh
  obtain ⟨d0, hd0, r0⟩ := rc a5154 a5156
  obtain ⟨d1, hd1, r1⟩ := rc a5159 a5161
  obtain ⟨d2, hd2, r2⟩ := rc a5165 a5167
  obtain ⟨d3, hd3, r3⟩ := rc a5171 a5173
  obtain ⟨d4, hd4, r4⟩ := rc a5177 a5179
  obtain ⟨d5, hd5, r5⟩ := rc a5183 a5185
  obtain ⟨d6, hd6, r6⟩ := rc a5190 a5192
  have hb := fun t (ht : t < 6) => hτ t ht
  rw [r0, v0, ← pow_add] at a5155
  rw [r1, v1, ← pow_add] at a5160
  rw [r2, v2, ← pow_add] at a5166
  rw [r3, v3, ← pow_add] at a5172
  rw [r4, v4, ← pow_add] at a5178
  rw [r5, v5, ← pow_add] at a5184
  have hb0 := hb 0 (by norm_num); have hb1 := hb 1 (by norm_num); have hb2 := hb 2 (by norm_num)
  have hb3 := hb 3 (by norm_num); have hb4 := hb 4 (by norm_num); have hb5 := hb 5 (by norm_num)
  have i1 := gen_pow_inj (by omega) (by omega) (a5155.symm.trans a5160)
  have i2 := gen_pow_inj (by omega) (by omega) (a5155.symm.trans a5166)
  have i3 := gen_pow_inj (by omega) (by omega) (a5155.symm.trans a5172)
  have i4 := gen_pow_inj (by omega) (by omega) (a5155.symm.trans a5178)
  have i5 := gen_pow_inj (by omega) (by omega) (a5155.symm.trans a5184)
  rw [hmu, r6, a5155, ← pow_add] at a5191
  have im := gen_pow_inj (by omega) (by omega) a5191
  refine ⟨d0 + τ 0, a5155, fun t ht => ?_, ?_, by omega⟩
  · interval_cases t <;> omega
  · rw [tb_word_zero] at a5188
    have hz : σ (.n 5864) = 0 := by rw [← a5188]; exact e_add_eq_zero_iff.mp a5189
    rw [a5187, a5181, a5175, a5169, a5163, a5157, a5162, a5168, a5174, a5180, a5186] at hz
    have key : ∀ t < 6, ∀ v : E, v = gen ^ τ t → σ (.n 5817) + v = 0 → τ t = d0 + τ 0 :=
      fun t ht v hv h0 => by
        rw [a5155, hv] at h0
        exact (gen_pow_inj (by omega) (by have := hb t ht; omega)
          (e_add_eq_zero_iff.mp h0)).symm
    rcases mul_eq_zero.mp hz with hz | h5
    · rcases mul_eq_zero.mp hz with hz | h4
      · rcases mul_eq_zero.mp hz with hz | h3
        · rcases mul_eq_zero.mp hz with hz | h2
          · rcases mul_eq_zero.mp hz with h0 | h1
            · exact ⟨0, by norm_num, key 0 (by norm_num) _ v0 h0⟩
            · exact ⟨1, by norm_num, key 1 (by norm_num) _ v1 h1⟩
          · exact ⟨2, by norm_num, key 2 (by norm_num) _ v2 h2⟩
        · exact ⟨3, by norm_num, key 3 (by norm_num) _ v3 h3⟩
      · exact ⟨4, by norm_num, key 4 (by norm_num) _ v4 h4⟩
    · exact ⟨5, by norm_num, key 5 (by norm_num) _ v5 h5⟩
end

end
end LeanVM.Guest.B1.Tables
