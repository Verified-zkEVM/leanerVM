/-
  LeanVM.Guest.B1.Main.AggEqtreeCS

  `AggEqtreeC.lean` under any semantics of `BLAKE2S` (`S : BlakeSem`).
-/

module

public import LeanVM.Guest.B1.Main.AggEqtreeC
public import LeanVM.Guest.B1.Main.AggStepsCS

/-!
# `AggEqtreeC.lean` under any `BLAKE2S` semantics

Each definition and lemma of `AggEqtreeC.lean` that mentions the semantics, with `S : BlakeSem` a
parameter and a `S` in its name.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

variable {S : BlakeSem}

variable {C : CallRel} {rd : Reader}

/-- **`eqtree`, backward**: on a valuation with `eqtree`'s values from `b`, the block holds once
the coordinates are at `pt·g^off` and the equality kernel's layers in `out`. -/
theorem eqtreeS_complete {σ : Val} (pt out : V) (off b : ℕ) (kret : List E → Prop) (rs : List E)
    (hl : rs.length = 6) (hv : EtVals σ b rs)
    (hr : ∀ t < 6, LoadHolds rd (σ pt) (off + t) (rs.getD t 0))
    (hout : ∀ t < 6, ∀ i < 2 ^ (t + 1), LoadHolds rd (σ out) (2 ^ (t + 1) - 2 + i) (etK rs (t + 1) i)) :
    Stmt.HoldsListB S C rd σ (eqtreeT pt off out b) True kret := by
  rw [eqtreeT, holdsListB_append,
    holdsListB_flatten_range 5 (fun t => etLayer pt off out b (t + 1)) (fun _ => noRetList_etLayer ..)]
  simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, word_one]
  obtain ⟨e0, e1, e2, eL⟩ := hv
  have k0 := etK_succ_lo rs 0 0 (by omega) (by norm_num)
  have k1 := etK_succ_hi rs 0 0 (by omega) (by norm_num)
  simp only [etK, List.take_zero, show eqKernel [] = [1] from rfl, List.getD_cons_zero, one_mul,
    pow_zero, Nat.add_zero, zero_add] at k0 k1
  refine ⟨by rw [e0]; simpa using hr 0 (by omega), e1, by rw [e2, e1, e0], ?_, ?_,
    fun t ht => ?_, trivial⟩
  · have := hout 0 (by norm_num) 0 (by norm_num)
    rw [etK, k0] at this
    rw [e2]; simpa using this
  · have := hout 0 (by norm_num) 1 (by norm_num)
    rw [etK, k1] at this
    rw [e0]; simpa using this
  rw [etLayer, holdsListB_append, holdsListB_flatten_range _ (etEntry out b (t + 1)) (fun _ => rfl)]
  simp only [etEntry, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, word_one]
  obtain ⟨f0, f1, f2, fE⟩ := eL t ht
  refine ⟨by rw [f0]; exact hr _ (by omega), f1, by rw [f2, f1, f0], fun i hi => ?_, trivial⟩
  obtain ⟨g0, g1, g2⟩ := fE i hi
  have hp : 2 ^ (t + 1) ≤ 2 ^ (t + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hp2 : 2 ^ (t + 1 + 1) = 2 * 2 ^ (t + 1) := by rw [pow_succ]; ring
  rw [show etBase b (t + 1) + 4 + 3 * i = etBase b (t + 1) + 3 + 3 * i + 1 by omega,
    show etBase b (t + 1) + 5 + 3 * i = etBase b (t + 1) + 3 + 3 * i + 2 by omega]
  refine ⟨by rw [g0]; exact hout t (by omega) i hi, by rw [g1, g0, f2], ?_, by rw [g2, g0, f0], ?_,
    trivial⟩
  · rw [g1, ← etK_succ_lo rs (t + 1) i (by omega) hi]
    exact hout (t + 1) (by omega) i (by omega)
  · rw [g2, ← etK_succ_hi rs (t + 1) i (by omega) hi,
      show 2 ^ (t + 1 + 1) - 2 + 2 ^ (t + 1) + i = 2 ^ (t + 1 + 1) - 2 + (2 ^ (t + 1) + i) by omega]
    exact hout (t + 1) (by omega) _ (by omega)

end
end LeanVM.Guest.B1.Main
