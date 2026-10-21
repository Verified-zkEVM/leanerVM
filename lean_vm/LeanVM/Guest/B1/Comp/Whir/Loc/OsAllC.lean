/-
  LeanVM.Guest.B1.Comp.Whir.Loc.OsAllC

  `open_stacked` complete, placed, over every completeness model, at `main`'s frame sizes.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.Loc.G1C3
public import LeanVM.Guest.B1.Comp.Whir.Loc.PureC
public import LeanVM.Guest.B1.Comp.Whir.Loc.OsInstAllB
public import LeanVM.Guest.B2C.CalleesHyps

/-!
# `open_stacked` over every completeness model

`osCalleesAtBCOf CM fs h cert k hc`: group 1's callees of `open_stacked` over `CM` at the bounds of
the deployed `osCalleesAtB … (g1BoundsOf fs h)`; `osCalleesMaxOfC`: their maxima, the deployed
constants (`osCalleesMaxOf`). `open_stacked_completeAtBC_of`: `open_stacked_completeAtB_of` over
every model, at the caps' agreement `CapAgreesC CM`; its bound is the deployed one
(`osBopC_eq`), so at `main`'s frame sizes and certificates it is `CalleesOpenC`'s field
(`open_stacked_completeAtBC_b2c`: `CompleteOpenAtBC CM B2C.fs B2C.cert 16 (CapAgreesC CM)
B2C.calleesHyps_b2c.Bop`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub
open LeanVM.E2E.Complete

@[expose] public section

set_option maxRecDepth 100000 in
/-- **Group 1's callees of `open_stacked`, placed, over a completeness model**, at the deployed
bounds. -/
noncomputable def osCalleesAtBCOf (CM : CompModel) (fs : String → ℕ) (h : FsAgree fs) (cert : String → V → ℕ)
    (k : ℕ) (hc : G1Certs fs cert) : OsCalleesAtBC CM fs cert k where
  foldB := fun _ => 68
  fold := opening_fold_completeRelBC fs cert k _ (openingB_fold_totalLe_at h)
  canonicalB := fun _ => fs "assert_canonical"
  canonical := fun a r L hp => completeAtBS_of_freeOn (by decide +kernel) (List.mem_singleton_self _)
    ((osCalleesAtB fs cert k hc (g1BoundsOf fs h)).canonical a r L hp)
  oodB := fun args => fs "opening_ood_point" + (2 * logG (args.getD 3 0) + 2) +
    max (logG (args.getD 3 0) * 78) (fs "__loop9")
  ood := opening_ood_point_completeRelBC fs cert k (fun x => logG x * 78) (loop9B_totalLeOn_at h)
  grindB := fun args => fs "grind_check" + max (logG (args.getD 3 0) * 32) (fs "__loop6")
  grind := grind_check_completeRelBC fs cert k hc.grind (fun x => logG x * 32) (loop6B_totalLeOn_at h)
  finalMsg4B := fun _ => 72
  finalMsg4 := ofm_L4_completeMemBC fs cert k _ (openingB_final_message_L4_totalLe_at h)
  finalMsg8B := fun _ => 124
  finalMsg8 := ofm_L8_completeMemBC fs cert k _ (openingB_final_message_L8_totalLe_at h)
  finalMsg16B := fun _ => 228
  finalMsg16 := ofm_L16_completeMemBC fs cert k _ (openingB_final_message_L16_totalLe_at h)
  finalMsg32B := fun _ => 436
  finalMsg32 := ofm_L32_completeMemBC fs cert k _ (openingB_final_message_L32_totalLe_at h)
  rowWeights4B := fun _ => 57
  rowWeights4 := fun a r L hp => completeAtBS_of_freeOn (by decide +kernel) (List.mem_singleton_self _)
    ((osCalleesAtB fs cert k hc (g1BoundsOf fs h)).rowWeights4 a r L hp)
  rowWeights6B := fun _ => 205
  rowWeights6 := fun a r L hp => completeAtBS_of_freeOn (by decide +kernel) (List.mem_singleton_self _)
    ((osCalleesAtB fs cert k hc (g1BoundsOf fs h)).rowWeights6 a r L hp)
  foldFinal2B := fun _ => 92
  foldFinal2 := fun a r L hp => completeAtBS_of_freeOn (by decide +kernel) (List.mem_singleton_self _)
    ((osCalleesAtB fs cert k hc (g1BoundsOf fs h)).foldFinal2 a r L hp)
  foldFinal3B := fun _ => 137
  foldFinal3 := fun a r L hp => completeAtBS_of_freeOn (by decide +kernel) (List.mem_singleton_self _)
    ((osCalleesAtB fs cert k hc (g1BoundsOf fs h)).foldFinal3 a r L hp)
  foldFinal4B := fun _ => 194
  foldFinal4 := fun a r L hp => completeAtBS_of_freeOn (by decide +kernel) (List.mem_singleton_self _)
    ((osCalleesAtB fs cert k hc (g1BoundsOf fs h)).foldFinal4 a r L hp)
  foldFinal5B := fun _ => 275
  foldFinal5 := fun a r L hp => completeAtBS_of_freeOn (by decide +kernel) (List.mem_singleton_self _)
    ((osCalleesAtB fs cert k hc (g1BoundsOf fs h)).foldFinal5 a r L hp)
  decode := fun p hp => osDecodeAtDC_of fs cert k (osDq_freeOn p hp) ((osCalleesAtB fs cert k hc (g1BoundsOf fs h)).decode p hp)

noncomputable def osCalleesMaxOfC (CM : CompModel) (fs' : String → ℕ) (h : FsAgree fs') (cert : String → V → ℕ) (k : ℕ)
    (hc : G1Certs fs' cert) : OsCalleesMaxC CM (osCalleesAtBCOf CM fs' h cert k hc) where
  foldMax := 68
  fold := fun _ => le_rfl
  canonicalMax := fs' "assert_canonical"
  canonical := fun _ => le_rfl
  oodMax := fs' "opening_ood_point" + 46 + max (22 * 78) (fs' "__loop9")
  ood := fun a m ha hm => by
    show fs' "opening_ood_point" + (2 * logG (a.getD 3 0) + 2) +
      max (logG (a.getD 3 0) * 78) (fs' "__loop9") ≤ _
    rw [ha]
    have h := (LeanVM.Guest.logG_gen_pow_le m).trans hm
    exact Nat.add_le_add (Nat.add_le_add_left (by omega) _)
      (max_le_max (Nat.mul_le_mul_right _ h) le_rfl)
  grindMax := fs' "grind_check" + max (17 * 32) (fs' "__loop6")
  grind := fun a ha => by
    show fs' "grind_check" + max (logG (a.getD 3 0) * 32) (fs' "__loop6") ≤ _
    rw [ha]
    exact Nat.add_le_add_left (max_le_max (Nat.mul_le_mul_right _
      (LeanVM.Guest.logG_gen_pow_le Whir.queryGrindingBits)) le_rfl) _
  finalMsg4Max := 72
  finalMsg4 := fun _ => le_rfl
  finalMsg8Max := 124
  finalMsg8 := fun _ => le_rfl
  finalMsg16Max := 228
  finalMsg16 := fun _ => le_rfl
  finalMsg32Max := 436
  finalMsg32 := fun _ => le_rfl
  rowWeights4Max := 57
  rowWeights4 := fun _ => le_rfl
  rowWeights6Max := 205
  rowWeights6 := fun _ => le_rfl
  foldFinal2Max := 92
  foldFinal2 := fun _ => le_rfl
  foldFinal3Max := 137
  foldFinal3 := fun _ => le_rfl
  foldFinal4Max := 194
  foldFinal4 := fun _ => le_rfl
  foldFinal5Max := 275
  foldFinal5 := fun _ => le_rfl

theorem osBopC_eq (CM : CompModel) (fs : String → ℕ) (h : FsAgree fs) (cert : String → V → ℕ) (k : ℕ)
    (hc : G1Certs fs cert) :
    osBopC CM fs (osCalleesMaxOfC CM fs h cert k hc) (osPureSizesC CM fs) =
      osBop fs (osCalleesMaxOf fs h cert k hc) (osPureSizes fs) := by
  have hg : osG1PairsC CM (osCalleesMaxOfC CM fs h cert k hc) = osG1Pairs (osCalleesMaxOf fs h cert k hc) := rfl
  have hl : ∀ lv f, osLvBdC CM fs (osPureSizesC CM fs) lv f = osLvBd fs (osPureSizes fs) lv f := fun _ _ => rfl
  have hbd : ∀ cfg, osBdC CM fs (osCalleesMaxOfC CM fs h cert k hc) (osPureSizesC CM fs) cfg =
      osBd fs (osCalleesMaxOf fs h cert k hc) (osPureSizes fs) cfg := by
    intro cfg; funext f
    simp only [osBdC, osBd, hg, hl]
  have hcb : ∀ cfg name, osCfgBoundC CM fs (osCalleesMaxOfC CM fs h cert k hc) (osPureSizesC CM fs) cfg name =
      osCfgBound fs (osCalleesMaxOf fs h cert k hc) (osPureSizes fs) cfg name := by
    intro cfg name
    simp only [osCfgBoundC, osCfgBound, hbd]
  simp only [osBopC, osBop, hcb]

/-- **`open_stacked` is complete, placed, over every completeness model**, at frame sizes agreeing
with `fsOf` but at `main`, at the caps' agreement over the model, within the deployed bound. -/
theorem open_stacked_completeAtBC_of (CM : CompModel) (fs : String → ℕ) (h : FsAgree fs) (cert : String → V → ℕ)
    (k : ℕ) (hc : G1Certs fs cert) (hq : OsOqFits fs cert) :
    CompleteOpenAtBC CM fs cert k (CapAgreesC CM) (osBop fs (osCalleesMaxOf fs h cert k hc) (osPureSizes fs)) := by
  rw [← osBopC_eq CM fs h cert k hc]
  exact open_stacked_completeAtBC fs cert k (osCalleesAtBCOf CM fs h cert k hc) (osCalleesMaxOfC CM fs h cert k hc) hq
    (osPureSizesC CM fs)

/-- **`open_stacked` over every completeness model at `main`'s frame sizes and certificates**:
`CalleesOpenC`'s field. -/
theorem open_stacked_completeAtBC_b2c (CM : CompModel) :
    CompleteOpenAtBC CM B2C.fs B2C.cert 16 (CapAgreesC CM) B2C.calleesHyps_b2c.Bop :=
  open_stacked_completeAtBC_of CM B2C.fs B2C.fsAgree_fs B2C.cert 16 B2C.g1Certs B2C.osOqFits

/-- **At the deployed model**: the deployed `open_stacked_completeAtB_of` (`CompleteOpenAtB … CapAgrees`). -/
theorem open_stacked_completeAtB_of_comp (fs : String → ℕ) (h : FsAgree fs) (cert : String → V → ℕ)
    (k : ℕ) (hc : G1Certs fs cert) (hq : OsOqFits fs cert) :
    CompleteOpenAtB fs cert k CapAgrees (osBop fs (osCalleesMaxOf fs h cert k hc) (osPureSizes fs)) := by
  intro μ r h1 h2 h3 h4 root cv xs os w cv' roots' target c Lin hrun hcap hm
  exact completeAtBS_deployed.mp (open_stacked_completeAtBC_of CompModel.deployed fs h cert k hc hq μ r h1 h2 h3 h4
    root cv xs os w cv' roots' target c Lin (runsWithM_deployed.mpr hrun)
    ((capAgreesC_deployed μ r root cv xs os target).mpr hcap) hm)

end
end LeanVM.Guest.B1
