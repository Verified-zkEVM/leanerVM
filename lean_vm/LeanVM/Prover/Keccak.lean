/-
  LeanVM.Prover.Keccak

  The executable Keccak phase makes the moves of the specification's `hKeccakPhase`.
-/

module

public import LeanVM.Prover.Keccak.Reduction
public import LeanVM.Protocol.EndToEnd.Complete.KeccakPhase

/-!
# The Keccak phase

`corr_keccakPhase`: given the instance's columns as arrays indexed by the verifier's column
numbers (`cols`, the witness's), and claims whose output lanes' point has the `KECCAK` table's
`τ` coordinates, the executable phase `keccakPhaseProve (s.τ 5) cols claims` makes the moves of
`hKeccakPhase prog s q claims` and returns its result. `q_keccak`'s column of `cols` agrees with
the honest stack's `q_keccak` words (`qkH`) on its `2^(τ + 6)` words (`colAgree_qk`).

The modules: `Keccak/Tables` (loops, equality tables, folded tables, coefficient lists, bits),
`Keccak/States` (the masks are the bits entering χ), `Keccak/Product` (`G`'s coefficients),
`Keccak/Rounds` (the bounded stateful sumcheck, the openings' products), `Keccak/Pack`,
`Keccak/Position`, `Keccak/Layer`, `Keccak/Open`, `Keccak/Reduction`.
-/

namespace LeanVM.Prover.KeccakGkr

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakGkr
open LeanVM.Protocol LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.EndToEnd.Complete

@[expose] public section

variable (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s))

theorem tau_sub_add : s.τ 5 - 4 + 4 = s.τ 5 := by
  have := s.minSteps_le
  simp only [keccakMinStepsLog] at this
  omega

/-- **`q_keccak`'s column of the witness's arrays is the honest stack's `q_keccak`**, on its
words. -/
theorem colAgree_qk (cols : Array (Array K))
    (hcols : ∀ c : Col, cols.getD (pyCol c) #[] = ((inst prog s).column q c).values.toArray) :
    ColAgree (s.τ 5 - 4) (fun n ↦ (cols.getD qkeccak #[]).getD n 0) (qkH prog s q) := by
  intro n hn
  have hn' : n < 2 ^ (s.τ 5 + 6) := by
    have e : s.τ 5 - 4 + 10 = s.τ 5 + 6 := by have := tau_sub_add s; omega
    rwa [e] at hn
  have h := keccakCol_getD prog s (fromI prog s q) hn'
  rw [toI_fromI, qkOf_fromI] at h
  rw [← h, ← pyCol_keccakCol, hcols keccakCol]
  rfl

/-- **The executable Keccak phase makes the moves of `hKeccakPhase`**, and returns its result. -/
theorem corr_keccakPhase (cols : Array (Array K))
    (hcols : ∀ c : Col, cols.getD (pyCol c) #[] = ((inst prog s).column q c).values.toArray)
    (claims : List ColumnClaim) (hlen : ((lanesOf claims).headD default).point.length = s.τ 5) :
    Corr (· = ·) (keccakPhaseProve (s.τ 5) cols claims) (hKeccakPhase prog s q claims) := by
  unfold keccakPhaseProve hKeccakPhase
  rw [Script.ret_bind]
  refine Corr.bind (fun a b h ↦ ?_) _ _ (corr_keccak (colAgree_qk prog s q cols hcols)
    (by rw [hlen, tau_sub_add]) _)
  subst h
  exact corr_ret rfl

end
end LeanVM.Prover.KeccakGkr
