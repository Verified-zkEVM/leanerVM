/-
  LeanVM.Guest.B1.Sig.ArmCostB2CS

  `ArmCostB2C.lean` under any semantics of `BLAKE2S` (`S : BlakeSem`).
-/

module

public import LeanVM.Guest.B1.Sig.ArmCostB2C
public import LeanVM.Guest.B1.Sig.ArmCostS
public import LeanVM.Guest.B2C.CntWeightB

/-!
# `ArmCostB2C.lean` under any `BLAKE2S` semantics

Each definition and lemma of `ArmCostB2C.lean` that mentions the semantics, with `S : BlakeSem` a
parameter and a `S` in its name.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B2C

@[expose] public section

variable {S : BlakeSem}


/-- **`verify_lean_xmss`'s separately counted arms**, at opcode `op` on a valid instance: at most
the matches' bases plus `136` steps, against a table bounded per arm by a base per match and `B`
per chain step. -/
theorem xmssS_costW_le (acs : List (ℕ × List (List ℕ))) (op : Opcode) (A : ℕ → ℕ) (B : ℕ)
    (hA : ∀ q ∈ xMatches, ∀ k < q.2,
      ((tabOp acs op q.1.idx).map fun l => l.getD k 0).getD 0 ≤ A q.1.idx + B * armSteps q.2 k)
    {rd : Reader} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Memory.Tree} {args rets : List E}
    (hv : (Memory.Tree.node f σ bufs kids).ValidB S coreProgram rd args rets) (hf : f = "verify_lean_xmss") :
    costW acs σ (coreOf 17).body op ≤ (xMatches.map fun q => A q.1.idx).sum + 136 * B := by
  rw [show (coreOf 17).body = Data.core16.body from rfl, costW_eq]
  exact xmssS_cw_valid _ A B hA hv hf

/-! ## At the generated table -/

theorem xmssArmCS_spec : ∀ op σ bufs kids rd args rets,
    (Memory.Tree.node "verify_lean_xmss" σ bufs kids).ValidB S coreProgram rd args rets →
      costW (nth Data.cplArms 17 []) σ (coreOf 17).body op ≤ xmssArmC op :=
  fun op _ _ _ _ _ _ hv => xmssS_costW_le _ op _ _ (xmssArm_hA op) hv rfl

end
end LeanVM.Guest.B1.Sig
