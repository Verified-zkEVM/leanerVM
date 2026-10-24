/-
  LeanVM.Guest.B1.Selectors.SharedVals

  `shared_selector_tables`' loop end and dispatch selector on every valuation satisfying its body:
  functions of its length argument alone.
-/

module

public import LeanVM.Guest.B1.Selectors.SharedTables

/-!
# `shared_selector_tables`' loop end

On every valuation satisfying the body's statements before its loop (any memory, any call
relation), with `len_g = g^n`, `n < 64`: the hinted bits rebuild `q_g = g^(n / 4)` (`σ 39`, the
end `__loop9` runs to) and `r_g = g^(n % 4)` (`σ 20`, the dispatch's selector), the loop's
condition is `1 + g^(n / 4)` and its start `1` (`ss_body_vals`). No load or unpinned hint enters:
the bits are pinned Boolean and their value by `q_g^4·r_g = len_g`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **The loop end and the selector are the length's.** -/
theorem ss_body_vals {C : CallRel} {rd : Reader} {σ : Val} {next : Prop}
    {kret : List E → Prop} (h : Stmt.HoldsList C rd σ ssPre next kret) {n : ℕ} (hn : n < 64)
    (h5 : σ (.n 5) = gen ^ n) :
    σ (.n 39) = gen ^ (n / 4) ∧ σ (.n 20) = gen ^ (n % 4) ∧
      σ (.n 44) = 1 + gen ^ (n / 4) ∧ σ (.n 45) = 1 := by
  simp only [ssPre, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and] at h
  obtain ⟨p6, p7, p8, p9, p10, p11, c12, c13, m14, a15, c16, c17, m18, a19, m20, c21, c22, m23,
    a24, c25, c26, m27, a28, m29, c30, c31, m32, a33, m34, c35, c36, m37, a38, m39, m40, m41, m42,
    e42, c43, a44, c45, -⟩ := h
  let f : ℕ → Bool := fun k ↦ decide (σ (.n (6 + k)) = 1)
  have pin : ∀ k < 6, σ (.n (6 + k)) * σ (.n (6 + k)) = σ (.n (6 + k)) := by
    intro k hk
    interval_cases k
    · exact p6.symm
    · exact p7.symm
    · exact p8.symm
    · exact p9.symm
    · exact p10.symm
    · exact p11.symm
  let r := bitsVal f 2
  let q := bitsVal (fun k ↦ f (k + 2)) 4
  have hr4 : r < 4 := bitsVal_lt f 2
  have hq16 : q < 16 := bitsVal_lt _ 4
  have hrg : σ (.n 20) = gen ^ r := by
    have := ss_prod (b := fun j ↦ σ (.n (6 + j))) (n := 2) (by norm_num)
      (fun j hj => pin j (by omega))
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, Nat.reduceAdd] at this
    rw [m20, a15, a19, c12, c16, m14, m18, c13, c17, tb_word_one, this]
  have hqg : σ (.n 39) = gen ^ q := by
    have := ss_prod (b := fun j ↦ σ (.n (6 + (j + 2)))) (n := 4) le_rfl
      (fun j hj => pin (j + 2) (by omega))
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, Nat.reduceAdd] at this
    rw [m39, m34, m29, a24, a28, a33, a38, c21, c25, c30, c35, m23, m27, m32, m37, c22, c26, c31,
      c36, tb_word_one, this]
  have hq4 : σ (.n 41) = gen ^ (4 * q) := by rw [m41, m40, hqg]; ring
  have hn' : 4 * q + r = n := by
    have e : gen ^ (4 * q + r) = gen ^ n := by
      rw [← h5, ← e_add_eq_zero_iff.mp e42, m42, hq4, hrg, ← pow_add]
    exact gen_pow_inj (by omega) (by omega) e
  have hq : q = n / 4 := by omega
  have hr : r = n % 4 := by omega
  refine ⟨by rw [hqg, hq], by rw [hrg, hr], by rw [a44, c43, tb_word_one, hqg, hq],
    by rw [c45, tb_word_one]⟩

end
end LeanVM.Guest.B1.Tables
