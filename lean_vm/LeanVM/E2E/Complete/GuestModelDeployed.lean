/-
  LeanVM.E2E.Complete.GuestModelDeployed

  At the deployed completeness model every fact `B1CompHyps` names is its deployed lemma, and the
  model theorem re-derives the deployed completeness.
-/

module

public import LeanVM.E2E.Complete.GuestModel
public import LeanVM.Guest.EndKnowB
public import LeanVM.E2E.Runs
public import LeanVM.Guest.B1.Comp.VsInv.Caps

/-!
# The deployed model

* `completeAtBS_blakeDeployed`, `completeRelBS_blakeDeployed`, `relAtInWS_blakeDeployed`, `completeAtWS_blakeDeployed`,
  `vsStatOkS_blakeDeployed`: at `blakeDeployed` the placed completeness forms under a semantics are the
  deployed ones;
* `clPreAtC_someBlake`, `cclPreAtC_someBlake`, `sdPreAtC_someBlake`, `daListPreAtC_someBlake`,
  `meaning_verify_lean_xmssWith_some`, `meaning_verify_sig_lean_sphincsWith_some`: over BLAKE2s
  answering everything the callees' preconditions are the deployed ones;
* `calleesAtC_deployed`: `CalleesAt` gives `CalleesAtC` at the deployed model;
* `calleesOpenC_deployed`, `b1CompHyps_deployed : B1CompHyps CompModel.deployed`: `open_stacked`
  at `CapAgreesC CompModel.deployed` from the deployed `CompleteOpenAtB` at `CapAgrees`
  (`capAgreesC_deployed`);
* `guest_complete_of_model : End.GuestCompleteWithin B2C.b2cBudget'`: the deployed `guest_complete`
  re-derived from `guestCompleteModelExec_at` at `CompModel.deployed` (`nodeRelWith_deployed`,
  `capsAgreeWith_blake2s`, `validExecutionB_deployed`, `committedSizeB_deployed`).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Node LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1 LeanVM.Guest.B1.Main

@[expose] public section

/-! ## The placed forms at the deployed semantics -/

section Placed

variable {fs : String → ℕ} {cert : String → V → ℕ}

theorem completeAtBS_blakeDeployed {k : ℕ} {f : String} {Lin : Main.Layout} {args : List E}
    {Out : List E → Main.Layout → Prop} {B : ℕ} :
    CompleteAtBS blakeDeployed fs cert k f Lin args Out B ↔ CompleteAtB fs cert k f Lin args Out B := by
  simp only [CompleteAtBS, CompleteAtB, relAtInB_deployed]

theorem completeRelBS_blakeDeployed {k : ℕ} {f : String} {Pre : Reader → List E → List E → Prop}
    {B : ℕ} : CompleteRelBS blakeDeployed fs cert k f Pre B ↔ CompleteRelB fs cert k f Pre B := by
  simp only [CompleteRelBS, CompleteRelB, completeAtBS_blakeDeployed]

theorem relAtInWS_blakeDeployed {Θ : Type} (w : Θ → String → ℕ) (rd : Reader) (R D : ℕ → Prop)
    (fp n : ℕ) (f : String) (args rets : List E) (Bw : Θ → ℕ) :
    RelAtInWS blakeDeployed fs cert w rd R D fp n f args rets Bw ↔
      RelAtInW fs cert w rd R D fp n f args rets Bw := by
  simp only [RelAtInWS, RelAtInW, validB_deployed]

theorem completeAtWS_blakeDeployed {Θ : Type} {w : Θ → String → ℕ} {κ : ℕ} {f : String} {Lin : Main.Layout}
    {args : List E} {Out : List E → Main.Layout → Prop} {B : ℕ} {Bw : Θ → ℕ} :
    CompleteAtWS blakeDeployed fs cert w κ f Lin args Out B Bw ↔
      CompleteAtW fs cert w κ f Lin args Out B Bw := by
  simp only [CompleteAtWS, CompleteAtW, relAtInWS_blakeDeployed]

theorem vsStatOkS_blakeDeployed (ω : String → ℕ) (c : VerifySub.VsStat) :
    VerifySub.VsStatOkS blakeDeployed ω c ↔ VerifySub.VsStatOk ω c := by
  constructor
  · intro h
    exact ⟨(weightLeB_deployed _ _ _).mp h.gpw, (weightLeB_deployed _ _ _).mp h.l2a,
      (weightLeB_deployed _ _ _).mp h.l2b, (weightLeB_deployed _ _ _).mp h.ac,
      (weightLeB_deployed _ _ _).mp h.pl,
      fun μ r h1 h2 h3 h4 => (weightLeB_deployed _ _ _).mp (h.os μ r h1 h2 h3 h4)⟩
  · intro h
    exact ⟨(weightLeB_deployed _ _ _).mpr h.gpw, (weightLeB_deployed _ _ _).mpr h.l2a,
      (weightLeB_deployed _ _ _).mpr h.l2b, (weightLeB_deployed _ _ _).mpr h.ac,
      (weightLeB_deployed _ _ _).mpr h.pl,
      fun μ r h1 h2 h3 h4 => (weightLeB_deployed _ _ _).mpr (h.os μ r h1 h2 h3 h4)⟩

end Placed

/-! ## The preconditions over BLAKE2s -/

section Pre

theorem clPreAtC_someBlake (cs : List E) (rd : Reader) (a r : List E) :
    Digest.ClPreAtC Value.someBlake cs rd a r ↔ ClPreAt cs rd a r := by
  match a, r with
  | [_, _, _], [_, _] => simp [Digest.ClPreAtC, ClPreAt]
  | [], _ | [_], _ | [_, _], _ | _ :: _ :: _ :: _ :: _, _ => exact Iff.rfl
  | [_, _, _], [] | [_, _, _], [_] | [_, _, _], _ :: _ :: _ :: _ => exact Iff.rfl

theorem cclPreAtC_someBlake (off : ℕ → ℕ) (cs : List E) (rd : Reader) (a r : List E) :
    Digest.CclPreAtC Value.someBlake off cs rd a r ↔ CclPreAt off cs rd a r := by
  match a, r with
  | [_, _, _, _, _, _, _], [_, _] => simp [Digest.CclPreAtC, CclPreAt]
  | [], _ | [_], _ | [_, _], _ | [_, _, _], _ | [_, _, _, _], _ | [_, _, _, _, _], _
  | [_, _, _, _, _, _], _ | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, _ => exact Iff.rfl
  | [_, _, _, _, _, _, _], [] | [_, _, _, _, _, _, _], [_]
  | [_, _, _, _, _, _, _], _ :: _ :: _ :: _ => exact Iff.rfl

theorem sdPreAtC_someBlake (sig : Digest) (cells : List E) (rd : Reader) (a r : List E) :
    Digest.SdPreAtC Value.someBlake sig cells rd a r ↔ SdPreAt sig cells rd a r := by
  match a, r with
  | [_, _, _, _, _, _], [_, _] =>
    simp only [Digest.SdPreAtC, SdPreAt, Digest.stmtDigestOfWith, Value.someBlake, Option.some.injEq,
      exists_eq_left']
    rfl
  | [], _ | [_], _ | [_, _], _ | [_, _, _], _ | [_, _, _, _], _ | [_, _, _, _, _], _
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, _ => exact Iff.rfl
  | [_, _, _, _, _, _], [] | [_, _, _, _, _, _], [_]
  | [_, _, _, _, _, _], _ :: _ :: _ :: _ => exact Iff.rfl

theorem daListPreAtC_someBlake (claims : List DaClaim) (rd : Reader) (a r : List E) :
    Digest.DaListPreAtC Value.someBlake claims rd a r ↔ DaListPreAt claims rd a r := by
  match a, r with
  | [_, _], [_, _] =>
    simp only [Digest.DaListPreAtC, DaListPreAt, daListDigestWith, Value.someBlake, Option.some.injEq,
      exists_eq_left']
    rfl
  | [], _ | [_], _ | _ :: _ :: _ :: _, _ => exact Iff.rfl
  | [_, _], [] | [_, _], [_] | [_, _], _ :: _ :: _ :: _ => exact Iff.rfl

theorem meaning_verify_lean_xmssWith_some (rd : Reader) (args rets : List E) :
    Meaning_verify_lean_xmssWith Value.someBlake rd args rets ↔
      Meaning_verify_lean_xmss rd args rets := by
  simp only [Meaning_verify_lean_xmssWith, Meaning_verify_lean_xmss,
    E2E.xmssVerifyWith_some_blake2s, Option.some.injEq]

theorem meaning_verify_sig_lean_sphincsWith_some (rd : Reader) (args rets : List E) :
    Meaning_verify_sig_lean_sphincsWith Value.someBlake rd args rets ↔
      Meaning_verify_sig_lean_sphincs rd args rets := by
  simp only [Meaning_verify_sig_lean_sphincsWith, Meaning_verify_sig_lean_sphincs,
    E2E.sphincsVerifyWith_some_blake2s, Option.some.injEq]

end Pre

/-! ## The callees at the deployed model -/

/-- At the run record of the deployed run, the caller's words are `vsExtL`'s. -/
theorem vsExtLR_ofD (lpA sqA outA : ℕ) (D : VerifySub.VsData) :
    vsExtLR lpA sqA outA D (VerifySub.VsRunC.ofD D) = VerifySub.vsExtL lpA sqA outA D := by
  simp only [vsExtLR, VerifySub.vsExtL, VerifySub.VsRunC.fresh_ofD]

/-- **`CalleesAt` is `CalleesAtC` at the deployed model.** -/
theorem calleesAtC_deployed {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}
    {VsGood : VerifySub.VsData → Prop} {Bd : CalleeBounds} (H : CalleesAt fs cert κ VsGood Bd) :
    CalleesAtC Value.someBlake blakeDeployed fs cert κ
      (fun D R => VsGood D ∧ R = VerifySub.VsRunC.ofD D) Bd where
  verify_lean_xmss args rets Lin hpre := completeAtBS_blakeDeployed.mpr
    (H.verify_lean_xmss args rets Lin fun rd h1 h2 =>
      (meaning_verify_lean_xmssWith_some rd args rets).mp (hpre rd h1 h2))
  verify_sig_lean_sphincs args rets Lin hpre := completeAtBS_blakeDeployed.mpr
    (H.verify_sig_lean_sphincs args rets Lin fun rd h1 h2 =>
      (meaning_verify_sig_lean_sphincsWith_some rd args rets).mp (hpre rd h1 h2))
  statement_digest sig cells args rets Lin hpre := completeAtBS_blakeDeployed.mpr
    (H.statement_digest sig cells args rets Lin fun rd h1 h2 =>
      (sdPreAtC_someBlake sig cells rd args rets).mp (hpre rd h1 h2))
  da_list_digest claims args rets Lin hpre := completeAtBS_blakeDeployed.mpr
    (H.da_list_digest claims args rets Lin fun rd h1 h2 =>
      (daListPreAtC_someBlake claims rd args rets).mp (hpre rd h1 h2))
  cover_da_root i args rets Lin hpre := completeAtBS_blakeDeployed.mpr (H.cover_da_root i args rets Lin hpre)
  claim_list_digest cs args rets Lin hpre := completeAtBS_blakeDeployed.mpr
    (H.claim_list_digest cs args rets Lin fun rd h1 h2 =>
      (clPreAtC_someBlake cs rd args rets).mp (hpre rd h1 h2))
  child_claim_list_digest off cs args rets Lin hpre := completeAtBS_blakeDeployed.mpr
    (H.child_claim_list_digest off cs args rets Lin fun rd h1 h2 =>
      (cclPreAtC_someBlake off cs rd args rets).mp (hpre rd h1 h2))
  da_verify wt root vd ho args rets Lin hpre := completeAtWS_blakeDeployed.mpr
    (H.da_verify wt root vd ((Digest.opensWith_deployed_iff root vd wt).mp ho) args rets Lin hpre)
  verify_sub D R hD lpA sqA outA _ w c hc := by
    obtain ⟨hD, rfl⟩ := hD
    rw [vsExtLR_ofD]
    exact completeAtWS_blakeDeployed.mpr
      (H.verify_sub D hD lpA sqA outA w c fun θ => (vsStatOkS_blakeDeployed _ _).mp (hc θ))

/-- **The callees not yet placed over a model, at the deployed model**: the deployed
`calleesAt_proved`'s. -/
theorem calleesOpenC_deployed :
    CalleesOpenC CompModel.deployed (VerifySub.CapAgreesC CompModel.deployed) where
  open_stacked μ r h1 h2 h3 h4 root cv xs os w cv' roots' target c Lin hrun hcap hm :=
    B2C.calleesHyps_b2c.op.toC μ r h1 h2 h3 h4 root cv xs os w cv' roots' target c Lin hrun
      ((VerifySub.capAgreesC_deployed _ _ _ _ _ _ _).mp hcap) hm

/-- **At the deployed model what group B1 still owes is its deployed lemma.** -/
theorem b1CompHyps_deployed : B1CompHyps CompModel.deployed := ⟨calleesOpenC_deployed⟩

/-- **The deployed completeness, re-derived from the model theorem** (`End.guest_complete`'s
statement): at the deployed model the node relation answered by BLAKE2s is `NodeRel`, the caps
under BLAKE2s are `CapsAgree`, and a valid execution under the deployed semantics within its
committed size is a valid execution within the deployed committed size. -/
theorem guest_complete_of_model : End.GuestCompleteWithin B2C.b2cBudget' := by
  intro seed s w hrel hlim hcap hbudget
  obtain ⟨t, hv, hsz⟩ := guestCompleteModelExec_at CompModel.deployed b1CompHyps_deployed
    blake2sBytes (fun x d h => (Option.some.inj h).symm) seed s w (statementDigest seed s)
    (Value.statementDigestWith_some seed s) ((End.nodeRelWith_deployed _ seed s w).mpr hrel) hlim
    ((capsAgreeWith_blake2s seed w).mpr hcap) hbudget
  refine ⟨t, (validExecutionB_deployed _ _ t).mp hv, ?_⟩
  rw [← committedSizeB_deployed]
  exact hsz

end
end LeanVM.E2E.Complete
