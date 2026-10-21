/-
  LeanVM.Guest.B1.Main.CalleesModel

  `main`'s callees over every completeness model, from group B1's merged completeness lemmas over
  `CompModel` (`B1/Comp/**`), at the deployed frame sizes, certificates and callee bounds; the
  pieces not yet placed over a model collected in `CalleesOpenC`.
-/

module

public import LeanVM.Guest.B1.Main.CalleesAtC
public import LeanVM.Guest.B1.Main.CalleesProved
public import LeanVM.Guest.B1.Comp.Sig.CompleteAtC
public import LeanVM.Guest.B1.Comp.VerifySub.Placed
public import LeanVM.Guest.Memory.GuestBoundsAtB
public import LeanVM.Guest.B2C.CalleesHyps
public import LeanVM.Guest.B1.Comp.Tables.CalleesC
public import LeanVM.Guest.B1.Comp.Da.CalleeC

/-!
# The callees of `main` over a completeness model

`CalleesAtC CM.H CM.sem B2C.fs B2C.cert 16 (VsGoodC CM CapOk) (calleeBd B2C.fs B2C.calleesHyps_b2c)`
field by field, `calleesAtC_of_open`:

* from B1's lemmas over `CompModel`, their trees' bounds the pure callees' `TotalLeB` at `B2C.fs`
  (`Memory/GuestBoundsAtB.lean`): `verify_lean_xmss` (`verify_lean_xmss_completeRelBS`),
  `verify_sig_lean_sphincs` (`verify_sig_lean_sphincs_completeRelBS`), `statement_digest`
  (`Digest.sd_completeRelBS`), `da_list_digest` (`Digest.dl_completeRelBS`), `cover_da_root`
  (`Digest.cover_completeRelBS`), `claim_list_digest` (`Digest.cld_completeRelBS`),
  `child_claim_list_digest` (`Digest.ccld_completeRelBS`) and `da_verify` (`da_verify_calleeC`);
* `verify_sub` at every good run over the model (`VsGoodC CM CapOk`: a run record the model
  answers, the run within the limits over the model, the tables' context and the cap's agreement
  `CapOk`) by B1's `VerifySub.verify_sub_completeAtWSC`, its blake-free callees the deployed
  `certify_placement` and `check_opening_terminal`, `verify_bus_gkr`, `verify_tables` and
  `verify_flock` B1's over every model (`B2C.gkrC_b2c`, `B2C.tablesC_b2c`, `B2C.flockC_b2c`);
* the rest, `CalleesOpenC CM CapOk`: `open_stacked` placed over the model, bounded, at the cap's
  agreement `CapOk`.

At `CompModel.deployed` the open part is the deployed lemmas' (`calleesOpenC_deployed`, in
`E2E/Complete/GuestModelDeployed.lean`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node LeanVM.E2E.Complete
open LeanVM.Guest.B1 (CompleteRelBS LowDef Returns)

@[expose] public section

/-- **A good run of `verify_sub` over a completeness model**, at its run record `R`: the model
answers `R` (`R.Ans CM D`), the run is within the deployed limits over the model (`D.OkC`), the
tables' context holds (`D.TOk`), and the cap's agreement `CapOk` holds at the run record's batching
state and target. -/
def VsGoodC (CM : CompModel) (CapOk : ℕ → ℕ → Digest → Digest → List E → List Compile.Opening → E → Prop)
    (D : VerifySub.VsData) (R : VerifySub.VsRunC) : Prop :=
  R.Ans CM D ∧ D.OkC CM End.bytecode R ∧ D.TOk End.bytecode ∧
    CapOk (VerifySub.layoutOf End.bytecode D.logMem D.rows).stackLog D.rate D.root R.cvL D.xsW D.os
      (R.target D)

/-- **The piece of `main`'s callees not yet placed over a completeness model**: `verify_sub`'s
`open_stacked` within the deployed bound at the cap's agreement `CapOk`, over `CM` at the deployed
frame sizes, certificates and bounds. -/
structure CalleesOpenC (CM : CompModel)
    (CapOk : ℕ → ℕ → Digest → Digest → List E → List Compile.Opening → E → Prop) : Prop where
  open_stacked : VerifySub.CompleteOpenAtBC CM B2C.fs B2C.cert 16 CapOk B2C.calleesHyps_b2c.Bop

/-- **`main`'s callees over a completeness model**: all but `verify_sub`'s `open_stacked` from B1's
lemmas over every model, that from `CalleesOpenC`. -/
theorem calleesAtC_of_open {CM : CompModel}
    {CapOk : ℕ → ℕ → Digest → Digest → List E → List Compile.Opening → E → Prop}
    (h : CalleesOpenC CM CapOk) :
    CalleesAtC CM.H CM.sem B2C.fs B2C.cert 16 (VsGoodC CM CapOk)
      (calleeBd B2C.fs B2C.calleesHyps_b2c) where
  verify_lean_xmss := verify_lean_xmss_completeRelBS B2C.fs B2C.cert
    (verifyB_lean_xmss_totalLe_at B2C.fsAgree_fs) (by norm_num)
  verify_sig_lean_sphincs := verify_sig_lean_sphincs_completeRelBS B2C.fs B2C.cert
    (verifyB_sig_lean_sphincs_totalLe_at B2C.fsAgree_fs) (by norm_num)
  statement_digest sig cells := Digest.sd_completeRelBS B2C.fs B2C.cert sig cells
    (statementB_digest_totalLe_at B2C.fsAgree_fs)
  da_list_digest claims := Digest.dl_completeRelBS B2C.fs B2C.cert claims
    (daB_list_digest_totalLe_at B2C.fsAgree_fs)
  cover_da_root i args rets Lin hpre := Digest.cover_completeRelBS B2C.fs B2C.cert (by norm_num) i
    args rets Lin fun rd h1 h2 => cp_cover (hpre rd h1 h2)
  claim_list_digest cs := Digest.cld_completeRelBS B2C.fs B2C.cert (by norm_num) cs
    (fun e => logG e * 482) (fun t => ctBound[t]!) 147 (loop86B_totalLeOn_at B2C.fsAgree_fs)
    (fun t ht => by rw [B2C.ctNames_eq_ctList]; exact ctB_totalLe_at B2C.fsAgree_fs t ht)
    (scaledB_log_L6_totalLe_at B2C.fsAgree_fs)
  child_claim_list_digest off cs := Digest.ccld_completeRelBS B2C.fs B2C.cert (by norm_num) off cs
    147 147 (scaledB_log_L11_totalLe_at B2C.fsAgree_fs) (scaledB_log_L6_totalLe_at B2C.fsAgree_fs)
  da_verify := da_verify_calleeC B2C.calleesHyps_b2c CM
  verify_sub D R hD lpA sqA outA _ w c hc :=
    VerifySub.verify_sub_completeAtWSC (CM := CM) (fs := B2C.fs) (cert := B2C.cert) (by norm_num)
      (VerifySub.VsWeightHypsS.ofStat c hc)
      (Bsw := ⟨fun θ => VerifySub.vtcGkrBoundW (w θ), fun θ => VerifySub.vtTablesBoundW (w θ),
        fun θ => flockBoundW (w θ), fun θ => termBoundW (w θ)⟩)
      (Bs := calleeVsB B2C.fs B2C.calleesHyps_b2c) (B2C.gkrC_b2c CM w) (B2C.tablesC_b2c CM w)
      (B2C.flockC_b2c CM w)
      (certify_placement_completeAtB B2C.fs B2C.cert (by norm_num)) h.open_stacked
      (check_opening_terminal_completeAtW B2C.fs B2C.cert w 16) End.bytecode_length hD.1 hD.2.1
      hD.2.2.1 hD.2.2.2 lpA sqA outA

end
end LeanVM.Guest.B1.Main
