/-
  LeanVM.Guest.B1.Tables.Vt.Fw

  `verify_tables`' framework claims: the memory and bytecode index extensions, the five column
  values stored in the claim pool with their `g^|point|`, and the pull side's reloads of them.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Fresh
public import LeanVM.Guest.B1.Selectors.IndexMle

/-!
# The framework's claims (G:2082-2118)

`vt_fw`: `index_mle` at `log_mem` and at `19` (the bytecode's log-size) give the index extensions
of the point's prefixes; the memory's three values, the final memory count and the final bytecode
count are `claim_pool[0 .. 4]`, with `claim_cplen_g` the `block_kappa` cells of their blocks; the
pull side reloads the index values and the memory values from where the push side left them.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

theorem vt_index_arm {rd : Reader} {σ : Val} {v r : ℕ} {point : List E} {κ : ℕ}
    (hz : TbReadsAt rd (σ (.n 8)) point) (hκ : κ ≤ point.length) (hκ34 : κ < 34)
    (hv : σ (.n v) = gen ^ κ)
    (hd : ∃ (j : ℕ) (h : j < vtImNames.length), σ (.n v) = ofK (Parameters.gpow j) ∧
      coreProgram.Rel rd vtImNames[j] ([V.n 8].map σ) ([V.n r].map σ)) :
    σ (.n r) = indexMle (point.take κ) := by
  obtain ⟨j, hj, hjv, hrel⟩ := hd
  have hj34 : j < 34 := by simpa [vtImNames] using hj
  rw [hv, ← gen_pow_eq_ofK] at hjv
  obtain rfl := gen_pow_inj (by omega) (by omega) hjv
  simp only [vtImNames, List.getElem_map, List.getElem_range, List.map_cons, List.map_nil] at hrel
  obtain ⟨zs, hzl, hzr, hval⟩ := index_mle_holds κ hκ34 _ _ _ hrel
  rw [hval, tbReadsAt_unique hzr (tbReadsAt_take hz κ) (by simp; omega)]

/-- **The framework's claims.** -/
theorem vt_fw {rd : Reader} {σ : Val} (h : VtH rd σ) {point : List E}
    (hz : TbReadsAt rd (σ (.n 8)) point) {lm : ℕ} (hlm : lm ≤ point.length) (hlm34 : lm < 34)
    (h19 : 19 ≤ point.length) (hk1 : LoadHolds rd (σ (.n 12)) 1 (gen ^ lm))
    (hk2 : LoadHolds rd (σ (.n 12)) 2 (gen ^ 19)) :
    σ (.n 2908) = indexMle (point.take lm) ∧ σ (.n 4440) = σ (.n 2908) ∧
      σ (.n 2983) = indexMle (point.take 19) ∧ σ (.n 4485) = σ (.n 2983) ∧
      σ (.n 4457) = σ (.n 2914) ∧ σ (.n 4461) = σ (.n 2927) ∧ σ (.n 4465) = σ (.n 2940) ∧
      LoadHolds rd (σ (.n 16)) 0 (σ (.n 2914)) ∧ LoadHolds rd (σ (.n 16)) 1 (σ (.n 2927)) ∧
      LoadHolds rd (σ (.n 16)) 2 (σ (.n 2940)) ∧ LoadHolds rd (σ (.n 16)) 3 (σ (.n 4444)) ∧
      LoadHolds rd (σ (.n 16)) 4 (σ (.n 4502)) ∧ LoadHolds rd (σ (.n 17)) 0 (gen ^ lm) ∧
      LoadHolds rd (σ (.n 17)) 1 (gen ^ lm) ∧ LoadHolds rd (σ (.n 17)) 2 (gen ^ lm) ∧
      LoadHolds rd (σ (.n 17)) 3 (σ (.n 4430)) ∧ LoadHolds rd (σ (.n 17)) 4 (σ (.n 4475)) ∧
      LoadHolds rd (σ (.n 12)) 55 (σ (.n 4430)) ∧ LoadHolds rd (σ (.n 12)) 56 (σ (.n 4475)) := by
  have a2434 := h.atom 2434 (.load (.n 2884) (.n 12) 1) (by decide +kernel)
  have a2510 := h.atom 2510 (.load (.n 2959) (.n 12) 2) (by decide +kernel)
  have d2455 := h.dispatch 2455 (.n 2884) vtImNames [.n 8] [.n 2908] (by decide +kernel)
  have d2531 := h.dispatch 2531 (.n 2959) vtImNames [.n 8] [.n 2983] (by decide +kernel)
  have a2456 := h.atom 2456 (.load (.n 2908) (.n 2851) 1) (by decide +kernel)
  have a2532 := h.atom 2532 (.load (.n 2983) (.n 2851) 2) (by decide +kernel)
  have a3934 := h.atom 3934 (.load (.n 4440) (.n 2851) 1) (by decide +kernel)
  have a3978 := h.atom 3978 (.load (.n 4485) (.n 2851) 2) (by decide +kernel)
  have a2471 := h.atom 2471 (.load (.n 2914) (.n 16) 0) (by decide +kernel)
  have a2485 := h.atom 2485 (.load (.n 2927) (.n 16) 1) (by decide +kernel)
  have a2499 := h.atom 2499 (.load (.n 2940) (.n 16) 2) (by decide +kernel)
  have a3947 := h.atom 3947 (.load (.n 4444) (.n 16) 3) (by decide +kernel)
  have a3992 := h.atom 3992 (.load (.n 4502) (.n 16) 4) (by decide +kernel)
  have a3952 := h.atom 3952 (.load (.n 4457) (.n 16) 0) (by decide +kernel)
  have a3956 := h.atom 3956 (.load (.n 4461) (.n 16) 1) (by decide +kernel)
  have a3960 := h.atom 3960 (.load (.n 4465) (.n 16) 2) (by decide +kernel)
  have a2472 := h.atom 2472 (.load (.n 2884) (.n 17) 0) (by decide +kernel)
  have a2486 := h.atom 2486 (.load (.n 2884) (.n 17) 1) (by decide +kernel)
  have a2500 := h.atom 2500 (.load (.n 2884) (.n 17) 2) (by decide +kernel)
  have a3948 := h.atom 3948 (.load (.n 4430) (.n 17) 3) (by decide +kernel)
  have a3993 := h.atom 3993 (.load (.n 4475) (.n 17) 4) (by decide +kernel)
  have a3926 := h.atom 3926 (.load (.n 4430) (.n 12) 55) (by decide +kernel)
  have a3970 := h.atom 3970 (.load (.n 4475) (.n 12) 56) (by decide +kernel)
  simp only [Atom.Holds] at a2434 a2510 a2456 a2532 a3934 a3978 a2471 a2485 a2499 a3947 a3992
  simp only [Atom.Holds] at a3952 a3956 a3960 a2472 a2486 a2500 a3948 a3993 a3926 a3970
  have e2884 := tb_loadHolds_unique a2434 hk1
  have e2959 := tb_loadHolds_unique a2510 hk2
  rw [e2884] at a2472 a2486 a2500
  exact ⟨vt_index_arm hz hlm hlm34 e2884 d2455, tb_loadHolds_unique a3934 a2456,
    vt_index_arm hz h19 (by norm_num) e2959 d2531, tb_loadHolds_unique a3978 a2532,
    tb_loadHolds_unique a3952 a2471, tb_loadHolds_unique a3956 a2485,
    tb_loadHolds_unique a3960 a2499, a2471, a2485, a2499, a3947, a3992, a2472, a2486, a2500,
    a3948, a3993, a3926, a3970⟩

end
end LeanVM.Guest.B1.Tables
