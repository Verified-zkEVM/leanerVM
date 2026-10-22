/-
  LeanVM.E2E.Complete.Count.FinalWitness

  T6-det under the deployed limits is not vacuous: the leaf of `Witness.lean` meets its
  hypotheses.
-/

module

public import LeanVM.E2E.Complete.Count.Final
public import LeanVM.E2E.Complete.Witness

/-!
# The leaf, under the deployed limits

The leaf `wTree` (`Witness.lean`: one leanXMSS claim held directly, the constant hash `wH`, the
rate `1`, the fuel `1`) meets every hypothesis of `idealVerify_complete_final` together
(`hyps_final_wTree`), its limits now without the count; so V_I accepts its honest idealized proof
(`idealVerify_complete_final_wTree`).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Blake2sHash LeanVM.Node LeanVM.Guest LeanVM.Protocol.LeanIsa

@[expose] public section

/-- **T6-det's hypotheses under the deployed limits hold together** at the leaf `wTree`. -/
theorem hyps_final_wTree : validRate 1 ∧ wTree.Valid wH ∧ wTree.WithinLimitsBudget wH 1 1 ∧
    wTree.PowFound wH 1 1 ∧ wTree.WeightsNonzero wH 1 1 ∧ wTree.RootsInjAt wH 1 1 ∧
    wTree.size ≤ 1 := by
  obtain ⟨hρ, hv, hlim, hpow, hw, hroots, hfuel⟩ := hyps_wTree
  exact ⟨hρ, hv, HonestTree.withinLimitsBudget_of' wH 1 1 hlim, hpow, hw, hroots, hfuel⟩

/-- **T6-det under the deployed limits, on the leaf**: V_I accepts the honest idealized proof
of `wTree` with every hash answered by `wH`. -/
theorem idealVerify_complete_final_wTree :
    ∃ s ip, honestIdeal wH 1 1 wTree = some (s, ip) ∧ s.claims = wClaims ∧
      idealVerify (m := Id) (fun x ↦ (pure (wH x) : Id Digest)) guest ip 1 s = true := by
  obtain ⟨hρ, hv, hlim, hpow, hw, hroots, hfuel⟩ := hyps_final_wTree
  exact idealVerify_complete_final wH 1 1 wTree hρ hv hlim hpow hw hroots hfuel

end
end LeanVM.E2E.Complete
