/-
  LeanVM.Guest.B1.Comp.Da.CalleeC

  `da_verify` as a callee of `main` over a completeness model: `CalleesAtC`'s `da_verify` field
  (`CalleesOpenC`'s, at the deployed frame sizes, certificates and callee bounds).
-/

module

public import LeanVM.Guest.B1.Comp.Da.CompleteAtC
public import LeanVM.Guest.B1.Main.CalleesAtC
public import LeanVM.Guest.B1.Main.CalleesProved

/-!
# `da_verify`, as `main`'s callee, over a completeness model

`da_verify_calleeC H CM`: on the hypotheses `H : CalleesHyps fs cert bytecode` (their `dvc20`,
`dvc4`), `da_verify` is complete under `CM.sem`, placed at `κ = 16`, for a witness opening the
claim over `CM.H` and the guest's padding digests, within `calleeBd fs H`'s `daVerify` words and
`daVerifyW` weights: the `da_verify` field of `CalleesAtC CM.H CM.sem fs cert 16 _ (calleeBd fs H)`
(at `B2C.calleesHyps_b2c`, `CalleesOpenC CM _`'s). `da_verify_callee_of_comp`: at
`CompModel.deployed`, `calleesAt_proved`'s `da_verify` field.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.E2E.Complete
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Node
open LeanVM.Guest.B1 (Returns LowDef completeAtWS_deployed)

@[expose] public section

/-- **`da_verify` as `main`'s callee over a completeness model**: `CalleesAtC`'s `da_verify`
field at `calleeBd fs H`. -/
theorem da_verify_calleeC {fs : String → ℕ} {cert : String → V → ℕ} {bytecode : List K}
    (H : CalleesHyps fs cert bytecode) (CM : CompModel) :
    ∀ (wt : Da.Witness) (root vd : Digest), wt.OpensWith CM.H daPadCell daPadRow root vd →
    ∀ (args rets : List E) (Lin : Layout),
    (∀ rd, LowDef 16 rd → MemL rd Lin → DaVerifyPreAt root vd rd args rets) →
    CompleteAtWS CM.sem fs cert (fun θ : String → ℕ => θ) 16 "da_verify" Lin args (Returns rets)
      ((calleeBd fs H).daVerify wt.rows.length) fun θ => (calleeBd fs H).daVerifyW θ wt.rows.length :=
  fun wt root vd hw args rets Lin hpre =>
    Digest.da_verify_completeRelAtWC fs cert le_rfl H.dvc20 H.dvc4 wt root vd hw args rets Lin
      fun rd h1 h2 => cp_dv (hpre rd h1 h2)

/-- **At the deployed model**, the deployed `da_verify` field (`calleesAt_proved`'s). -/
theorem da_verify_callee_of_comp {fs : String → ℕ} {cert : String → V → ℕ} {bytecode : List K}
    (H : CalleesHyps fs cert bytecode) :
    ∀ (wt : Da.Witness) (root vd : Digest), wt.Opens root vd → ∀ (args rets : List E) (Lin : Layout),
    (∀ rd, LowDef 16 rd → MemL rd Lin → DaVerifyPreAt root vd rd args rets) →
    CompleteAtW fs cert (fun θ : String → ℕ => θ) 16 "da_verify" Lin args (Returns rets)
      ((calleeBd fs H).daVerify wt.rows.length) fun θ => (calleeBd fs H).daVerifyW θ wt.rows.length :=
  fun wt root vd hw args rets Lin hpre =>
    completeAtWS_deployed.mp (da_verify_calleeC H CompModel.deployed wt root vd
      ((Digest.opensWith_deployed_iff root vd wt).mpr hw) args rets Lin hpre)

end
end LeanVM.Guest.B1.Main
