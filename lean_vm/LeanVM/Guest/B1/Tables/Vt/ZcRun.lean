/-
  LeanVM.Guest.B1.Tables.Vt.ZcRun

  `verify_tables`' table sumcheck from its target: the batching challenge's powers, the target
  from the three sides' totals, the first record, the rounds, the last record, the challenges'
  running products and the prefix equality weights.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Rounds
public import LeanVM.Guest.B1.Eq.EqPrefix

/-!
# The table sumcheck (G:2183-2230)

`vt_zc_run`: with `ξ = zc_xi` and the sides' totals `T_s`, the target `ξ²·T_0 + ξ³·T_1 + ξ⁴·T_2`
runs `n` plain rounds from the sponge after the bus words, reading `3n` words after the five; the
last record holds the sponge, the cursor and the final claim; the challenges are in `chi` from
its top; `cprod[g^j]` is the product of the first `j`; `peq` holds the prefix equality weights of
`chi` against `1 + ζ`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem vt_chi_index {n j : ℕ} {y : E} (hj : j < n) (hy : gen ^ n * vtWInvGen = y * gen ^ j) :
    y = gen ^ (n - 1 - j) := by
  have h1 : gen ^ n * vtWInvGen * gen = gen ^ n := by rw [mul_assoc, vtWInvGen_mul, mul_one]
  rw [hy, mul_assoc, ← pow_succ] at h1
  have e : y * gen ^ (j + 1) = gen ^ (n - 1 - j) * gen ^ (j + 1) := by
    rw [h1, ← pow_add, show n - 1 - j + (j + 1) = n by omega]
  exact mul_right_cancel₀ (pow_ne_zero _ gen_ne_zero) e

set_option maxHeartbeats 1000000 in
/-- **The table sumcheck.** -/
theorem vt_zc_run {rd : Reader} {σ : Val} (h : VtH rd σ) {n : ℕ} (hn : n < 33)
    (hgn : σ (.n 5817) = gen ^ n) :
    σ (.n 5905) = σ (.n 5895) ^ 2 * σ (.n 4411) + σ (.n 5895) ^ 3 * σ (.n 4924) +
      σ (.n 5895) ^ 4 * σ (.n 5816) ∧
    ∃ (xs pts : List E) (claimN : E),
      RunsTo (sumcheck (σ (.n 5905)) 4 (List.replicate n none))
        ⟨(List.range 5).map fun k ↦ σ (.n (5884 + k)), []⟩ xs (pts, claimN)
        ⟨(List.range 5).map fun k ↦ σ (.n (5927 + k)), []⟩ ∧
      ReadsAt rd (σ (.n 5) * gen ^ 5) xs ∧ xs.length = 3 * n ∧ pts.length = n ∧
      σ (.n 5932) = σ (.n 5) * gen ^ 5 * gen ^ (3 * n) ∧ σ (.n 5933) = claimN ∧
      (∀ i < n, LoadHolds rd (σ (.n 18)) (n - 1 - i) (pts.getD i 0)) ∧
      (∀ j ≤ n, LoadHolds rd (σ (.n 5915)) j ((pts.take j).prod)) ∧
      EqPrefix rd (σ (.n 5936)) 1 (σ (.n 18)) (σ (.n 2767)) n := by
  have a5207 := h.atom 5207 (.const (.n 5896) (word 1 0 0)) (by decide +kernel)
  have a5208 := h.atom 5208 (.mul (.n 5897) (.n 5896) (.n 5895)) (by decide +kernel)
  have a5209 := h.atom 5209 (.mul (.n 5898) (.n 5897) (.n 5895)) (by decide +kernel)
  have a5210 := h.atom 5210 (.mul (.n 5899) (.n 5898) (.n 5895)) (by decide +kernel)
  have a5211 := h.atom 5211 (.mul (.n 5900) (.n 5899) (.n 5895)) (by decide +kernel)
  have a5212 := h.atom 5212 (.mul (.n 5901) (.n 5898) (.n 4411)) (by decide +kernel)
  have a5213 := h.atom 5213 (.mul (.n 5902) (.n 5899) (.n 4924)) (by decide +kernel)
  have a5214 := h.atom 5214 (.add (.n 5903) (.n 5901) (.n 5902)) (by decide +kernel)
  have a5215 := h.atom 5215 (.mul (.n 5904) (.n 5900) (.n 5816)) (by decide +kernel)
  have a5216 := h.atom 5216 (.add (.n 5905) (.n 5903) (.n 5904)) (by decide +kernel)
  have a5217 := h.atom 5217 (.const (.n 5906) (word 2 0 0)) (by decide +kernel)
  have a5218 := h.atom 5218 (.mul (.n 5907) (.n 5817) (.n 5906)) (by decide +kernel)
  have a5219 := h.atom 5219 (.mul (.n 5908) (.n 5907) (.n 5907)) (by decide +kernel)
  have a5220 := h.atom 5220 (.mul (.n 5909) (.n 5908) (.n 5907)) (by decide +kernel)
  have a5221 := h.atom 5221 (.mul (.n 5910) (.n 5909) (.n 5909)) (by decide +kernel)
  have a5222 := h.atom 5222 (.mul (.n 5911) (.n 5910) (.n 5907)) (by decide +kernel)
  have a5224 := h.atom 5224 (.const (.n 5913) (word 2 0 0)) (by decide +kernel)
  have a5225 := h.atom 5225 (.mul (.n 5914) (.n 5817) (.n 5913)) (by decide +kernel)
  have a5227 := h.atom 5227 (.load (.n 5884) (.n 5912) 0) (by decide +kernel)
  have a5228 := h.atom 5228 (.load (.n 5885) (.n 5912) 1) (by decide +kernel)
  have a5229 := h.atom 5229 (.load (.n 5886) (.n 5912) 2) (by decide +kernel)
  have a5230 := h.atom 5230 (.load (.n 5887) (.n 5912) 3) (by decide +kernel)
  have a5231 := h.atom 5231 (.load (.n 5888) (.n 5912) 4) (by decide +kernel)
  have a5232 := h.atom 5232 (.const (.n 5916) (word 32 0 0)) (by decide +kernel)
  have a5233 := h.atom 5233 (.mul (.n 5917) (.n 5) (.n 5916)) (by decide +kernel)
  have a5234 := h.atom 5234 (.load (.n 5917) (.n 5912) 5) (by decide +kernel)
  have a5235 := h.atom 5235 (.load (.n 5905) (.n 5912) 6) (by decide +kernel)
  have a5236 := h.atom 5236 (.const (.n 5918) (word 1 0 0)) (by decide +kernel)
  have a5237 := h.atom 5237 (.load (.n 5918) (.n 5915) 0) (by decide +kernel)
  have a5238 := h.atom 5238 (.const (.n 5919) (word 1 0 0)) (by decide +kernel)
  have a5239 := h.atom 5239 (.add (.n 5920) (.n 5919) (.n 5817)) (by decide +kernel)
  have a5240 := h.atom 5240 (.const (.n 5921) (word 1 0 0)) (by decide +kernel)
  have a5242 := h.atom 5242 (.mul (.n 5922) (.n 5817) (.n 5817)) (by decide +kernel)
  have a5243 := h.atom 5243 (.mul (.n 5923) (.n 5922) (.n 5817)) (by decide +kernel)
  have a5244 := h.atom 5244 (.mul (.n 5924) (.n 5923) (.n 5923)) (by decide +kernel)
  have a5245 := h.atom 5245 (.mul (.n 5925) (.n 5924) (.n 5817)) (by decide +kernel)
  have a5246 := h.atom 5246 (.mul (.n 5926) (.n 5912) (.n 5925)) (by decide +kernel)
  have a5247 := h.atom 5247 (.load (.n 5927) (.n 5926) 0) (by decide +kernel)
  have a5248 := h.atom 5248 (.load (.n 5928) (.n 5926) 1) (by decide +kernel)
  have a5249 := h.atom 5249 (.load (.n 5929) (.n 5926) 2) (by decide +kernel)
  have a5250 := h.atom 5250 (.load (.n 5930) (.n 5926) 3) (by decide +kernel)
  have a5251 := h.atom 5251 (.load (.n 5931) (.n 5926) 4) (by decide +kernel)
  have a5252 := h.atom 5252 (.load (.n 5932) (.n 5926) 5) (by decide +kernel)
  have a5253 := h.atom 5253 (.load (.n 5933) (.n 5926) 6) (by decide +kernel)
  have a5254 := h.atom 5254 (.const (.n 5934) (word 2 0 0)) (by decide +kernel)
  have a5255 := h.atom 5255 (.mul (.n 5935) (.n 5817) (.n 5934)) (by decide +kernel)
  have a5257 := h.atom 5257 (.const (.n 5937) (word 1 0 0)) (by decide +kernel)
  have hloop := h.callIf 5241 (.n 5920) "__loop10" [.n 5921, .n 5817, .n 5912, .n 18, .n 5817,
    .n 5915] (by decide +kernel)
  have hchain := h.call 5258 "eq_prefix_chain" [.n 5936, .n 5937, .n 18, .n 2767, .n 5817] []
    (by decide +kernel)
  simp only [Atom.Holds] at a5207 a5208 a5209 a5210 a5211 a5212 a5213 a5214 a5215 a5216
  simp only [Atom.Holds] at a5217 a5218 a5219 a5220 a5221 a5222 a5224 a5225 a5227 a5228
  simp only [Atom.Holds] at a5229 a5230 a5231 a5232 a5233 a5234 a5235 a5236 a5237 a5238
  simp only [Atom.Holds] at a5239 a5240 a5242 a5243 a5244 a5245 a5246 a5247 a5248 a5249
  simp only [Atom.Holds] at a5250 a5251 a5252 a5253 a5254 a5255 a5257
  simp only [List.map_cons, List.map_nil] at hloop hchain
  refine ⟨by rw [a5216, a5214, a5212, a5213, a5215, a5211, a5210, a5209, a5208, a5207,
    tb_word_one]; ring, ?_⟩
  have hB : ∀ j < n, L10B rd (σ (.n 5912)) (σ (.n 18)) (gen ^ n) (σ (.n 5915)) (gen ^ j) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · intro j hj; omega
    · have hne : σ (.n 5920) ≠ 0 := by
        rw [a5239, a5238, tb_word_one, hgn]
        intro h0
        have := gen_pow_inj (by omega) (by omega)
          ((e_add_eq_zero_iff.mp h0).symm.trans (pow_zero gen).symm)
        omega
      have hr := hloop.2 hne
      rw [a5240, tb_word_one, hgn] at hr
      exact l10_loop hn0 (by omega) hr
  have hc0 : CapAt rd (σ (.n 5912) * gen ^ (7 * 0)) 0 1
      ((List.range 5).map fun k ↦ σ (.n (5884 + k))) := by
    refine ⟨by simp, fun j hj => ?_⟩
    simp only [List.length_map, List.length_range] at hj
    simp only [Nat.mul_zero, pow_zero, mul_one, Nat.zero_add, List.getElem_map,
      List.getElem_range]
    interval_cases j
    · exact a5227
    · exact a5228
    · exact a5229
    · exact a5230
    · exact a5231
  have hcur0 : LoadHolds rd (σ (.n 5912) * gen ^ (7 * 0)) 5 (σ (.n 5) * gen ^ 5) := by
    rw [Nat.mul_zero, pow_zero, mul_one, ← tb_word_two_pow (by norm_num),
      show (2 : ℕ) ^ 5 = 32 by norm_num, ← a5232, ← a5233]
    exact a5234
  have hcl0 : LoadHolds rd (σ (.n 5912) * gen ^ (7 * 0)) 6 (σ (.n 5905)) := by
    rw [Nat.mul_zero, pow_zero, mul_one]; exact a5235
  obtain ⟨xs, pts, claimN, capN, hrun, hxs, hxl, hpl, hcN, hcurN, hclN, hchi⟩ :=
    l10_chain (by omega) hB n le_rfl 0 (by omega) _ _ _ hc0 hcur0 hcl0
  have e5926 : σ (.n 5926) = σ (.n 5912) * gen ^ (7 * n) := by
    rw [a5246, a5245, a5244, a5243, a5242, hgn]; ring
  have hcF : CapAt rd (σ (.n 5912) * gen ^ (7 * n)) 0 1
      ((List.range 5).map fun k ↦ σ (.n (5927 + k))) := by
    refine ⟨by simp, fun j hj => ?_⟩
    simp only [List.length_map, List.length_range] at hj
    simp only [Nat.zero_add, mul_one, List.getElem_map, List.getElem_range, ← e5926]
    interval_cases j
    · exact a5247
    · exact a5248
    · exact a5249
    · exact a5250
    · exact a5251
  obtain rfl := capAt_unique' hcN hcF
  rw [← e5926] at hcurN hclN
  refine ⟨xs, pts, claimN, hrun, by simpa using hxs, hxl, hpl,
    tb_loadHolds_unique a5252 hcurN, tb_loadHolds_unique a5253 hclN,
    fun i hi => by simpa using hchi i hi, ?_, ?_⟩
  · intro j hj
    induction j with
    | zero =>
      rw [a5236, tb_word_one] at a5237
      simpa using a5237
    | succ j ih =>
      obtain ⟨-, -, -, -, rk, -, -, -, -, -, ⟨y, hy, hrk⟩, cp, hcp, hcp1⟩ := hB j (by omega)
      rw [vt_chi_index (by omega) hy, tb_loadHolds_mul_gen_pow, Nat.add_zero] at hrk
      have erk : rk = pts.getD j 0 := tb_loadHolds_unique hrk (by simpa using hchi j (by omega))
      rw [tb_loadHolds_mul_gen_pow, Nat.add_zero] at hcp
      rw [tb_loadHolds_mul_gen_pow] at hcp1
      rw [tb_loadHolds_unique hcp (ih (by omega)), erk] at hcp1
      rw [List.prod_take_succ _ _ (by omega), ← List.getD_eq_getElem _ 0 (by omega)]
      exact hcp1
  · have hm := (eq_prefix_chain_holds rd _ _).mp hchain
    simp only [MeaningEqPrefixChain] at hm
    obtain ⟨-, -, n', hn', hn'v, hep⟩ := hm
    rw [hgn] at hn'v
    obtain rfl := gen_pow_inj (by omega) (by omega) hn'v
    rw [a5257, tb_word_one] at hep
    exact hep

end
end LeanVM.Guest.B1.Tables
