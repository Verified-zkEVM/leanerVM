/-
  LeanVM.E2E.Complete.DecodeHV

  `main`'s callees in tree form over every completeness model, at the deployed sizes: `verify_sub`
  by trees decoding the child's run (`VsRootTreeE`), the child-claim and statement digests by trees
  loading their reads with their preconditions, `cover_da_root` by trees loading its slot.
-/

module

public import LeanVM.E2E.Complete.DecodeStmtTree
public import LeanVM.E2E.Complete.GuestModelAll
public import LeanVM.Guest.B1.Comp.Tables.CalleesCL

/-!
# `main`'s callees in tree form over a completeness model

The hypotheses `mainCompleteC_ofT` takes, at `calleesAtC_of_open`'s callees:

* `vs_completeT`: `verify_sub` complete at every good run by trees satisfying `VsRootTreeE` at the
  Whir side's opening predicate `OsQ` (`verify_sub_completeAtWCE`, the transcript callees loading
  their words, `gkrCL_b2c`, `tablesCL_b2c`, `flockCL_b2c`, `open_stacked_completeAtBCL_b2c`);
* `ccl_completeT`, `sd_completeT`: the child-claim and statement digests by trees loading their
  reads, their preconditions kept at the reader (`CclQP`, `SdQP`);
* `cover_completeT`: `cover_da_root` by trees loading its slot.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
open LeanVM.Guest.B1.Main (calleeBd vsExtLR VsGoodC)

@[expose] public section

/-- **`verify_sub` over a completeness model, by trees decoding the child's run.** -/
theorem vs_completeT (CM : CompModel) {OsQ : ℕ → ℕ → List Opening → ℕ → Memory.Tree → Prop}
    (hO : B1.VerifySub.CompleteOpenAtBCL CM B2C.fs B2C.cert 16 (B1.VerifySub.CapAgreesC CM)
      B2C.calleesHyps_b2c.Bop OsQ) :
    ∀ (D : B1.VerifySub.VsData) (R : B1.VerifySub.VsRunC), VsGoodC CM (B1.VerifySub.CapAgreesC CM) D R →
      ∀ lpA sqA outA : ℕ, ∀ {Θ : Type} (w : Θ → String → ℕ) (c : Θ → B1.VerifySub.VsStat),
      (∀ θ, B1.VerifySub.VsStatOkS CM.sem (w θ) (c θ)) →
      B1.CompleteAtWST CM.sem B2C.fs B2C.cert w 16 "verify_sub" (vsExtLR lpA sqA outA D R)
        [(digestScalars D.pi).1, (digestScalars D.pi).2, (digestScalars D.seed).1,
          (digestScalars D.seed).2, ofK (gpow lpA), ofK (gpow sqA), ofK (gpow outA)] (B1.Returns [])
        (calleeBd B2C.fs B2C.calleesHyps_b2c).vs
        (fun θ => (calleeBd B2C.fs B2C.calleesHyps_b2c).vsW (w θ) (c θ))
        (fun fp _ t => B1.VerifySub.VsRootTreeE CM.sem OsQ End.bytecode D R B2C.fs B2C.cert fp t) :=
  fun D R hD lpA sqA outA _ w c hc =>
    B1.VerifySub.verify_sub_completeAtWCE (CM := CM) (fs := B2C.fs) (cert := B2C.cert) (by norm_num)
      (B1.VerifySub.VsWeightHypsS.ofStat c hc)
      (Bsw := ⟨fun θ => B1.VerifySub.vtcGkrBoundW (w θ), fun θ => B1.VerifySub.vtTablesBoundW (w θ),
        fun θ => B1.flockBoundW (w θ), fun θ => B1.termBoundW (w θ)⟩)
      (Bs := B1.Main.calleeVsB B2C.fs B2C.calleesHyps_b2c) (B2C.gkrCL_b2c CM w) (B2C.tablesCL_b2c CM w)
      (B2C.flockCL_b2c CM w)
      (B1.certify_placement_completeAtB B2C.fs B2C.cert (by norm_num))
      hO
      (B1.check_opening_terminal_completeAtW B2C.fs B2C.cert w 16) End.bytecode_length hD.1
      hD.2.1 hD.2.2.1 hD.2.2.2 lpA sqA outA


/-- **The child-claim digests by trees loading their reads, their precondition kept.** -/
theorem ccl_completeT (CM : CompModel) :
    ∀ (off : ℕ → ℕ) (cs args rets : List E) (Lin' : B1.Main.Layout),
      (∀ rd, B1.LowDef 16 rd → B1.Main.MemL rd Lin' → B1.Digest.CclPreAtC CM.H off cs rd args rets) →
      B1.CompleteAtBST CM.sem B2C.fs B2C.cert 16 "child_claim_list_digest" Lin' args (B1.Returns rets)
        ((calleeBd B2C.fs B2C.calleesHyps_b2c).ccl (cs.length / 4))
        (fun b rd t => B1.Digest.CclLoadsQ off cs args rets b rd t ∧
          B1.Digest.CclPreAtC CM.H off cs rd args rets) :=
  fun off cs args rets Lin' hpre =>
    B1.Main.CompleteAtBST.qmono_rd (B1.Digest.ccld_completeRelBST B2C.fs B2C.cert (by norm_num) off cs
      147 147 (scaledB_log_L11_totalLe_at B2C.fsAgree_fs) (scaledB_log_L6_totalLe_at B2C.fsAgree_fs)
      args rets Lin' hpre) fun _ rd _ hl hL hq => ⟨hq, hpre rd hl hL⟩

/-- **The statement digests by trees loading their reads, their precondition kept.** -/
theorem sd_completeT (CM : CompModel) :
    ∀ (sig : Digest) (cells args rets : List E) (Lin' : B1.Main.Layout),
      (∀ rd, B1.LowDef 16 rd → B1.Main.MemL rd Lin' → B1.Digest.SdPreAtC CM.H sig cells rd args rets) →
      B1.CompleteAtBST CM.sem B2C.fs B2C.cert 16 "statement_digest" Lin' args (B1.Returns rets)
        (calleeBd B2C.fs B2C.calleesHyps_b2c).sd
        (fun b rd t => B1.Digest.SdLoadsQ sig cells args rets b rd t ∧
          B1.Digest.SdPreAtC CM.H sig cells rd args rets) :=
  fun sig cells args rets Lin' hpre =>
    B1.Main.CompleteAtBST.qmono_rd (B1.Digest.sd_completeRelBST B2C.fs B2C.cert (κ := 16) sig cells
      (statementB_digest_totalLe_at B2C.fsAgree_fs) args rets Lin' hpre)
      fun _ rd _ hl hL hq => ⟨hq, hpre rd hl hL⟩

/-- **`cover_da_root` by trees loading its slot.** -/
theorem cover_completeT (CM : CompModel) :
    ∀ i, B1.CompleteRelBST CM.sem B2C.fs B2C.cert 16 "cover_da_root" (B1.Main.CoverPreAt i)
      (calleeBd B2C.fs B2C.calleesHyps_b2c).cover (B1.Digest.CoverLoadsQ i) :=
  fun i args rets Lin hpre =>
    B1.Digest.cover_completeRelBST B2C.fs B2C.cert (by norm_num) i args rets Lin
      fun rd h1 h2 => B1.Main.cp_cover (hpre rd h1 h2)

end
end LeanVM.E2E.Complete
