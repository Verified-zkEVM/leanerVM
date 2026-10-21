/-
  LeanVM.Guest.B1.Comp.Whir.LocT.OsInstAllT

  `open_stacked` at every candidate, bounded, over a completeness model, its tree loading the stream
  words it reads and decoding to the run's openings (`Loc/OsInstAllB.lean` in tree form).
-/

module

public import LeanVM.Guest.B1.Comp.Whir.LocT.OsInstBT0
public import LeanVM.Guest.B1.Comp.Whir.LocT.OsInstBT1
public import LeanVM.Guest.B1.Comp.Whir.LocT.OsInstBT2
public import LeanVM.Guest.B1.Comp.Whir.LocT.OsInstBT3
public import LeanVM.Guest.B1.Comp.Whir.Loc.OsInstAllB
public import LeanVM.Guest.B1.Comp.Whir.LoadsT.OsStreamL
public import LeanVM.Guest.B1.Comp.Whir.LoadsT.CapL

/-!
# `open_stacked` in tree form at every candidate

`OsQ μ r os fp t`: the tree decodes to the openings `os` (`OsDec`). `os_caseT`: a configuration's
tree form (`os_completeOpenAtBCT`) gives `CompleteOpenAtBCL`'s, the stream words loaded by every
valid tree (`os_streamLoads`) at the run's stream length (`os_kit_of_runCT`).
`open_stacked_completeAtBCL`: `open_stacked_completeAtBC` in tree form.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub
open LeanVM.Guest.Located (osCfgOf openNames_idxOf)
open LeanVM.E2E.Complete
open LeanVM.Protocol.Compile (Bytes)
open LeanVM.Protocol (Digest)

@[expose] public section

/-- **The opening's predicate**: its tree decodes to the openings `os`. -/
def OsQ (μ r : ℕ) (os : List Opening) (_fp : ℕ) (t : Tree) : Prop := OsDec μ r os t

/-- `verify_merkle_cap`'s valid trees load its flagged nodes' children (the Tables agent's
`vmc_capLoads`). -/
theorem vmcCapLoads : VmcCapLoads := fun _ _ h4 h8 _ _ _ _ _ hn hv hc hf => vmc_capLoads h4 h8 hn hv hc hf

theorem osCfgOf_0 : osCfgOf (openName 22 1) = osCfg0 := by
  unfold osCfgOf openName; rw [openNames_idxOf _ (by decide)]; rfl

theorem osCfgOf_1 : osCfgOf (openName 23 1) = osCfg1 := by
  unfold osCfgOf openName; rw [openNames_idxOf _ (by decide)]; rfl

theorem osCfgOf_2 : osCfgOf (openName 24 1) = osCfg2 := by
  unfold osCfgOf openName; rw [openNames_idxOf _ (by decide)]; rfl

theorem osCfgOf_3 : osCfgOf (openName 25 1) = osCfg3 := by
  unfold osCfgOf openName; rw [openNames_idxOf _ (by decide)]; rfl

theorem osCfgOf_4 : osCfgOf (openName 26 1) = osCfg4 := by
  unfold osCfgOf openName; rw [openNames_idxOf _ (by decide)]; rfl

theorem osCfgOf_5 : osCfgOf (openName 27 1) = osCfg5 := by
  unfold osCfgOf openName; rw [openNames_idxOf _ (by decide)]; rfl

theorem osCfgOf_6 : osCfgOf (openName 28 1) = osCfg6 := by
  unfold osCfgOf openName; rw [openNames_idxOf _ (by decide)]; rfl

theorem osCfgOf_7 : osCfgOf (openName 22 2) = osCfg7 := by
  unfold osCfgOf openName; rw [openNames_idxOf _ (by decide)]; rfl

theorem osCfgOf_8 : osCfgOf (openName 23 2) = osCfg8 := by
  unfold osCfgOf openName; rw [openNames_idxOf _ (by decide)]; rfl

theorem osCfgOf_9 : osCfgOf (openName 24 2) = osCfg9 := by
  unfold osCfgOf openName; rw [openNames_idxOf _ (by decide)]; rfl

theorem osCfgOf_10 : osCfgOf (openName 25 2) = osCfg10 := by
  unfold osCfgOf openName; rw [openNames_idxOf _ (by decide)]; rfl

theorem osCfgOf_11 : osCfgOf (openName 26 2) = osCfg11 := by
  unfold osCfgOf openName; rw [openNames_idxOf _ (by decide)]; rfl

theorem osCfgOf_12 : osCfgOf (openName 27 2) = osCfg12 := by
  unfold osCfgOf openName; rw [openNames_idxOf _ (by decide)]; rfl

theorem osCfgOf_13 : osCfgOf (openName 28 2) = osCfg13 := by
  unfold osCfgOf openName; rw [openNames_idxOf _ (by decide)]; rfl

theorem osCfgOf_14 : osCfgOf (openName 22 3) = osCfg14 := by
  unfold osCfgOf openName; rw [openNames_idxOf _ (by decide)]; rfl

theorem osCfgOf_15 : osCfgOf (openName 23 3) = osCfg15 := by
  unfold osCfgOf openName; rw [openNames_idxOf _ (by decide)]; rfl

theorem osCfgOf_16 : osCfgOf (openName 24 3) = osCfg16 := by
  unfold osCfgOf openName; rw [openNames_idxOf _ (by decide)]; rfl

theorem osCfgOf_17 : osCfgOf (openName 25 3) = osCfg17 := by
  unfold osCfgOf openName; rw [openNames_idxOf _ (by decide)]; rfl

theorem osCfgOf_18 : osCfgOf (openName 26 3) = osCfg18 := by
  unfold osCfgOf openName; rw [openNames_idxOf _ (by decide)]; rfl

theorem osCfgOf_19 : osCfgOf (openName 27 3) = osCfg19 := by
  unfold osCfgOf openName; rw [openNames_idxOf _ (by decide)]; rfl

theorem osCfgOf_20 : osCfgOf (openName 28 3) = osCfg20 := by
  unfold osCfgOf openName; rw [openNames_idxOf _ (by decide)]; rfl

theorem osCfgOf_21 : osCfgOf (openName 22 4) = osCfg21 := by
  unfold osCfgOf openName; rw [openNames_idxOf _ (by decide)]; rfl

theorem osCfgOf_22 : osCfgOf (openName 23 4) = osCfg22 := by
  unfold osCfgOf openName; rw [openNames_idxOf _ (by decide)]; rfl

theorem osCfgOf_23 : osCfgOf (openName 24 4) = osCfg23 := by
  unfold osCfgOf openName; rw [openNames_idxOf _ (by decide)]; rfl

theorem osCfgOf_24 : osCfgOf (openName 25 4) = osCfg24 := by
  unfold osCfgOf openName; rw [openNames_idxOf _ (by decide)]; rfl

theorem osCfgOf_25 : osCfgOf (openName 26 4) = osCfg25 := by
  unfold osCfgOf openName; rw [openNames_idxOf _ (by decide)]; rfl

theorem osCfgOf_26 : osCfgOf (openName 27 4) = osCfg26 := by
  unfold osCfgOf openName; rw [openNames_idxOf _ (by decide)]; rfl

theorem osCfgOf_27 : osCfgOf (openName 28 4) = osCfg27 := by
  unfold osCfgOf openName; rw [openNames_idxOf _ (by decide)]; rfl

variable {Ht : Bytes → Digest} {CM : CompModel}

variable {fs : String → ℕ} {cert : String → V → ℕ} {k : ℕ}

/-- **A configuration's tree form gives `CompleteOpenAtBCL`'s**: the stream words loaded, the
openings decoded. -/
theorem os_caseT {cfg : OsCfg} {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall) (h22 : 22 ≤ μ)
    (h28 : μ ≤ 28) (h1 : 1 ≤ r) (h4 : r ≤ 4) (hcfg : osCfgOf (openName μ r) = cfg)
    (hHt : ∀ x d, CM.H x = some d → d = Ht x) {root cv : Digest} {xs : List E} {os : List Opening} {w : WhirEnd}
    {cv' : Digest} {roots' : List (Digest × ℕ × ℕ)} {target : E} {c : ℕ} {Lin : Main.Layout}
    (hrun : RunsWithM CM.hm (whirOpen μ r target) cv xs os [(root, stackShape μ r)] w cv' roots')
    (hcap : CapAgreesW Ht μ r root cv xs os target)
    (hLin : ∀ rd, LowDef k rd → Main.MemL rd Lin → ReadsAt rd (ofK (Parameters.gpow c)) xs) {B B' : ℕ}
    (h : CompleteAtBST CM.sem fs cert k (openName μ r) Lin [(digestScalars cv).1, (digestScalars cv).2,
      target, (digestScalars root).1, (digestScalars root).2, ofK (Parameters.gpow c)]
      (fun rets Lout => ∃ b, rets = [w.target, ofK (Parameters.gpow b), w.inner, w.residual] ∧
        Lout = [(b, w.point ++ List.replicate (pointCap - w.point.length) 0)]) B (fun _ _ t => OsDecCfg cfg os t))
    (hB : B ≤ B') :
    CompleteAtBST CM.sem fs cert k (openName μ r) Lin [(digestScalars cv).1, (digestScalars cv).2,
      target, (digestScalars root).1, (digestScalars root).2, ofK (Parameters.gpow c)]
      (fun rets Lout => ∃ b, rets = [w.target, ofK (Parameters.gpow b), w.inner, w.residual] ∧
        Lout = [(b, w.point ++ List.replicate (pointCap - w.point.length) 0)]) B'
      (fun fp _ t => LoadsWords t c xs ∧ OsQ μ r os fp t) := by
  obtain ⟨d, hx, -, -, -, -, -, hlen, -⟩ := os_kit_of_runCT (Ht := Ht) (CM := CM) hok hHt hrun hcap
  refine CompleteAtBST.monoT (h.and_of_valid (Q' := fun _ _ t => LoadsWords t c xs)
    fun _ rd hl hm t _ hn hv => os_streamLoads h22 h28 h1 h4 (hLin rd hl hm) (by rw [hcfg, ← hx]; exact hlen) hn hv)
    le_rfl hB fun _ _ t ht => ⟨ht.1, ?_⟩
  show OsDec μ r os t
  unfold OsDec
  rw [hcfg]
  exact ht.2

set_option maxRecDepth 100000 in
/-- **`open_stacked` is complete, placed, at every candidate, by trees of at most `osBopC CM` words,
loading the stream words they read and decoding to the run's openings.** -/
theorem open_stacked_completeAtBCL (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (h1 : OsCalleesAtBC CM fs cert k)
    (hm : OsCalleesMaxC CM h1) (hq : OsOqFits fs cert) (hp : OsPureSizesC CM fs) :
    CompleteOpenAtBCL CM fs cert k (CapAgreesC CM) (osBopC CM fs hm hp) OsQ := by
  intro μ r hμ1 hμ2 hr1 hr2
  interval_cases μ <;> interval_cases r
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => match hcap with
    | ⟨Ht, hHt, hag⟩ => os_caseT (CM := CM) osCfgOk_0 (by decide) (by decide) (by decide) (by decide) (osCfgOf_0) hHt hrun
      ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin
      (os_completeOpenAtBCT (Ht := Ht) (CM := CM) osCfgOk_0 osAllBodyFacts.b0
        (osKidsAtB_0C (Ht := Ht) (CM := CM) h1 hm hq hp) (osKidsAtBT_0C (Ht := Ht) (CM := CM) h1 hm hq hp) osCapNames_0
        vmcCapLoads hHt osCallees_0 os_find_0 rfl os_body_0
        (by rw [Program.loop_of_find? os_find_0]; decide +kernel) osRootCells_0 hrun
        ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin)
      (le_max_left _ _)
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => match hcap with
    | ⟨Ht, hHt, hag⟩ => os_caseT (CM := CM) osCfgOk_7 (by decide) (by decide) (by decide) (by decide) (osCfgOf_7) hHt hrun
      ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin
      (os_completeOpenAtBCT (Ht := Ht) (CM := CM) osCfgOk_7 osAllBodyFacts.b7
        (osKidsAtB_7C (Ht := Ht) (CM := CM) h1 hm hq hp) (osKidsAtBT_7C (Ht := Ht) (CM := CM) h1 hm hq hp) osCapNames_7
        vmcCapLoads hHt osCallees_7 os_find_7 rfl os_body_7
        (by rw [Program.loop_of_find? os_find_7]; decide +kernel) osRootCells_7 hrun
        ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin)
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => match hcap with
    | ⟨Ht, hHt, hag⟩ => os_caseT (CM := CM) osCfgOk_14 (by decide) (by decide) (by decide) (by decide) (osCfgOf_14) hHt hrun
      ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin
      (os_completeOpenAtBCT (Ht := Ht) (CM := CM) osCfgOk_14 osAllBodyFacts.b14
        (osKidsAtB_14C (Ht := Ht) (CM := CM) h1 hm hq hp) (osKidsAtBT_14C (Ht := Ht) (CM := CM) h1 hm hq hp) osCapNames_14
        vmcCapLoads hHt osCallees_14 os_find_14 rfl os_body_14
        (by rw [Program.loop_of_find? os_find_14]; decide +kernel) osRootCells_14 hrun
        ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin)
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => match hcap with
    | ⟨Ht, hHt, hag⟩ => os_caseT (CM := CM) osCfgOk_21 (by decide) (by decide) (by decide) (by decide) (osCfgOf_21) hHt hrun
      ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin
      (os_completeOpenAtBCT (Ht := Ht) (CM := CM) osCfgOk_21 osAllBodyFacts.b21
        (osKidsAtB_21C (Ht := Ht) (CM := CM) h1 hm hq hp) (osKidsAtBT_21C (Ht := Ht) (CM := CM) h1 hm hq hp) osCapNames_21
        vmcCapLoads hHt osCallees_21 os_find_21 rfl os_body_21
        (by rw [Program.loop_of_find? os_find_21]; decide +kernel) osRootCells_21 hrun
        ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin)
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))))))))))))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => match hcap with
    | ⟨Ht, hHt, hag⟩ => os_caseT (CM := CM) osCfgOk_1 (by decide) (by decide) (by decide) (by decide) (osCfgOf_1) hHt hrun
      ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin
      (os_completeOpenAtBCT (Ht := Ht) (CM := CM) osCfgOk_1 osAllBodyFacts.b1
        (osKidsAtB_1C (Ht := Ht) (CM := CM) h1 hm hq hp) (osKidsAtBT_1C (Ht := Ht) (CM := CM) h1 hm hq hp) osCapNames_1
        vmcCapLoads hHt osCallees_1 os_find_1 rfl os_body_1
        (by rw [Program.loop_of_find? os_find_1]; decide +kernel) osRootCells_1 hrun
        ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin)
      (le_max_of_le_right (le_max_left _ _))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => match hcap with
    | ⟨Ht, hHt, hag⟩ => os_caseT (CM := CM) osCfgOk_8 (by decide) (by decide) (by decide) (by decide) (osCfgOf_8) hHt hrun
      ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin
      (os_completeOpenAtBCT (Ht := Ht) (CM := CM) osCfgOk_8 osAllBodyFacts.b8
        (osKidsAtB_8C (Ht := Ht) (CM := CM) h1 hm hq hp) (osKidsAtBT_8C (Ht := Ht) (CM := CM) h1 hm hq hp) osCapNames_8
        vmcCapLoads hHt osCallees_8 os_find_8 rfl os_body_8
        (by rw [Program.loop_of_find? os_find_8]; decide +kernel) osRootCells_8 hrun
        ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin)
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => match hcap with
    | ⟨Ht, hHt, hag⟩ => os_caseT (CM := CM) osCfgOk_15 (by decide) (by decide) (by decide) (by decide) (osCfgOf_15) hHt hrun
      ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin
      (os_completeOpenAtBCT (Ht := Ht) (CM := CM) osCfgOk_15 osAllBodyFacts.b15
        (osKidsAtB_15C (Ht := Ht) (CM := CM) h1 hm hq hp) (osKidsAtBT_15C (Ht := Ht) (CM := CM) h1 hm hq hp) osCapNames_15
        vmcCapLoads hHt osCallees_15 os_find_15 rfl os_body_15
        (by rw [Program.loop_of_find? os_find_15]; decide +kernel) osRootCells_15 hrun
        ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin)
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))))))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => match hcap with
    | ⟨Ht, hHt, hag⟩ => os_caseT (CM := CM) osCfgOk_22 (by decide) (by decide) (by decide) (by decide) (osCfgOf_22) hHt hrun
      ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin
      (os_completeOpenAtBCT (Ht := Ht) (CM := CM) osCfgOk_22 osAllBodyFacts.b22
        (osKidsAtB_22C (Ht := Ht) (CM := CM) h1 hm hq hp) (osKidsAtBT_22C (Ht := Ht) (CM := CM) h1 hm hq hp) osCapNames_22
        vmcCapLoads hHt osCallees_22 os_find_22 rfl os_body_22
        (by rw [Program.loop_of_find? os_find_22]; decide +kernel) osRootCells_22 hrun
        ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin)
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))))))))))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => match hcap with
    | ⟨Ht, hHt, hag⟩ => os_caseT (CM := CM) osCfgOk_2 (by decide) (by decide) (by decide) (by decide) (osCfgOf_2) hHt hrun
      ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin
      (os_completeOpenAtBCT (Ht := Ht) (CM := CM) osCfgOk_2 osAllBodyFacts.b2
        (osKidsAtB_2C (Ht := Ht) (CM := CM) h1 hm hq hp) (osKidsAtBT_2C (Ht := Ht) (CM := CM) h1 hm hq hp) osCapNames_2
        vmcCapLoads hHt osCallees_2 os_find_2 rfl os_body_2
        (by rw [Program.loop_of_find? os_find_2]; decide +kernel) osRootCells_2 hrun
        ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin)
      (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => match hcap with
    | ⟨Ht, hHt, hag⟩ => os_caseT (CM := CM) osCfgOk_9 (by decide) (by decide) (by decide) (by decide) (osCfgOf_9) hHt hrun
      ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin
      (os_completeOpenAtBCT (Ht := Ht) (CM := CM) osCfgOk_9 osAllBodyFacts.b9
        (osKidsAtB_9C (Ht := Ht) (CM := CM) h1 hm hq hp) (osKidsAtBT_9C (Ht := Ht) (CM := CM) h1 hm hq hp) osCapNames_9
        vmcCapLoads hHt osCallees_9 os_find_9 rfl os_body_9
        (by rw [Program.loop_of_find? os_find_9]; decide +kernel) osRootCells_9 hrun
        ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin)
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => match hcap with
    | ⟨Ht, hHt, hag⟩ => os_caseT (CM := CM) osCfgOk_16 (by decide) (by decide) (by decide) (by decide) (osCfgOf_16) hHt hrun
      ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin
      (os_completeOpenAtBCT (Ht := Ht) (CM := CM) osCfgOk_16 osAllBodyFacts.b16
        (osKidsAtB_16C (Ht := Ht) (CM := CM) h1 hm hq hp) (osKidsAtBT_16C (Ht := Ht) (CM := CM) h1 hm hq hp) osCapNames_16
        vmcCapLoads hHt osCallees_16 os_find_16 rfl os_body_16
        (by rw [Program.loop_of_find? os_find_16]; decide +kernel) osRootCells_16 hrun
        ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin)
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => match hcap with
    | ⟨Ht, hHt, hag⟩ => os_caseT (CM := CM) osCfgOk_23 (by decide) (by decide) (by decide) (by decide) (osCfgOf_23) hHt hrun
      ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin
      (os_completeOpenAtBCT (Ht := Ht) (CM := CM) osCfgOk_23 osAllBodyFacts.b23
        (osKidsAtB_23C (Ht := Ht) (CM := CM) h1 hm hq hp) (osKidsAtBT_23C (Ht := Ht) (CM := CM) h1 hm hq hp) osCapNames_23
        vmcCapLoads hHt osCallees_23 os_find_23 rfl os_body_23
        (by rw [Program.loop_of_find? os_find_23]; decide +kernel) osRootCells_23 hrun
        ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin)
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))))))))))))))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => match hcap with
    | ⟨Ht, hHt, hag⟩ => os_caseT (CM := CM) osCfgOk_3 (by decide) (by decide) (by decide) (by decide) (osCfgOf_3) hHt hrun
      ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin
      (os_completeOpenAtBCT (Ht := Ht) (CM := CM) osCfgOk_3 osAllBodyFacts.b3
        (osKidsAtB_3C (Ht := Ht) (CM := CM) h1 hm hq hp) (osKidsAtBT_3C (Ht := Ht) (CM := CM) h1 hm hq hp) osCapNames_3
        vmcCapLoads hHt osCallees_3 os_find_3 rfl os_body_3
        (by rw [Program.loop_of_find? os_find_3]; decide +kernel) osRootCells_3 hrun
        ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin)
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => match hcap with
    | ⟨Ht, hHt, hag⟩ => os_caseT (CM := CM) osCfgOk_10 (by decide) (by decide) (by decide) (by decide) (osCfgOf_10) hHt hrun
      ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin
      (os_completeOpenAtBCT (Ht := Ht) (CM := CM) osCfgOk_10 osAllBodyFacts.b10
        (osKidsAtB_10C (Ht := Ht) (CM := CM) h1 hm hq hp) (osKidsAtBT_10C (Ht := Ht) (CM := CM) h1 hm hq hp) osCapNames_10
        vmcCapLoads hHt osCallees_10 os_find_10 rfl os_body_10
        (by rw [Program.loop_of_find? os_find_10]; decide +kernel) osRootCells_10 hrun
        ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin)
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => match hcap with
    | ⟨Ht, hHt, hag⟩ => os_caseT (CM := CM) osCfgOk_17 (by decide) (by decide) (by decide) (by decide) (osCfgOf_17) hHt hrun
      ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin
      (os_completeOpenAtBCT (Ht := Ht) (CM := CM) osCfgOk_17 osAllBodyFacts.b17
        (osKidsAtB_17C (Ht := Ht) (CM := CM) h1 hm hq hp) (osKidsAtBT_17C (Ht := Ht) (CM := CM) h1 hm hq hp) osCapNames_17
        vmcCapLoads hHt osCallees_17 os_find_17 rfl os_body_17
        (by rw [Program.loop_of_find? os_find_17]; decide +kernel) osRootCells_17 hrun
        ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin)
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))))))))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => match hcap with
    | ⟨Ht, hHt, hag⟩ => os_caseT (CM := CM) osCfgOk_24 (by decide) (by decide) (by decide) (by decide) (osCfgOf_24) hHt hrun
      ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin
      (os_completeOpenAtBCT (Ht := Ht) (CM := CM) osCfgOk_24 osAllBodyFacts.b24
        (osKidsAtB_24C (Ht := Ht) (CM := CM) h1 hm hq hp) (osKidsAtBT_24C (Ht := Ht) (CM := CM) h1 hm hq hp) osCapNames_24
        vmcCapLoads hHt osCallees_24 os_find_24 rfl os_body_24
        (by rw [Program.loop_of_find? os_find_24]; decide +kernel) osRootCells_24 hrun
        ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin)
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))))))))))))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => match hcap with
    | ⟨Ht, hHt, hag⟩ => os_caseT (CM := CM) osCfgOk_4 (by decide) (by decide) (by decide) (by decide) (osCfgOf_4) hHt hrun
      ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin
      (os_completeOpenAtBCT (Ht := Ht) (CM := CM) osCfgOk_4 osAllBodyFacts.b4
        (osKidsAtB_4C (Ht := Ht) (CM := CM) h1 hm hq hp) (osKidsAtBT_4C (Ht := Ht) (CM := CM) h1 hm hq hp) osCapNames_4
        vmcCapLoads hHt osCallees_4 os_find_4 rfl os_body_4
        (by rw [Program.loop_of_find? os_find_4]; decide +kernel) osRootCells_4 hrun
        ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin)
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => match hcap with
    | ⟨Ht, hHt, hag⟩ => os_caseT (CM := CM) osCfgOk_11 (by decide) (by decide) (by decide) (by decide) (osCfgOf_11) hHt hrun
      ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin
      (os_completeOpenAtBCT (Ht := Ht) (CM := CM) osCfgOk_11 osAllBodyFacts.b11
        (osKidsAtB_11C (Ht := Ht) (CM := CM) h1 hm hq hp) (osKidsAtBT_11C (Ht := Ht) (CM := CM) h1 hm hq hp) osCapNames_11
        vmcCapLoads hHt osCallees_11 os_find_11 rfl os_body_11
        (by rw [Program.loop_of_find? os_find_11]; decide +kernel) osRootCells_11 hrun
        ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin)
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => match hcap with
    | ⟨Ht, hHt, hag⟩ => os_caseT (CM := CM) osCfgOk_18 (by decide) (by decide) (by decide) (by decide) (osCfgOf_18) hHt hrun
      ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin
      (os_completeOpenAtBCT (Ht := Ht) (CM := CM) osCfgOk_18 osAllBodyFacts.b18
        (osKidsAtB_18C (Ht := Ht) (CM := CM) h1 hm hq hp) (osKidsAtBT_18C (Ht := Ht) (CM := CM) h1 hm hq hp) osCapNames_18
        vmcCapLoads hHt osCallees_18 os_find_18 rfl os_body_18
        (by rw [Program.loop_of_find? os_find_18]; decide +kernel) osRootCells_18 hrun
        ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin)
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))))))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => match hcap with
    | ⟨Ht, hHt, hag⟩ => os_caseT (CM := CM) osCfgOk_25 (by decide) (by decide) (by decide) (by decide) (osCfgOf_25) hHt hrun
      ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin
      (os_completeOpenAtBCT (Ht := Ht) (CM := CM) osCfgOk_25 osAllBodyFacts.b25
        (osKidsAtB_25C (Ht := Ht) (CM := CM) h1 hm hq hp) (osKidsAtBT_25C (Ht := Ht) (CM := CM) h1 hm hq hp) osCapNames_25
        vmcCapLoads hHt osCallees_25 os_find_25 rfl os_body_25
        (by rw [Program.loop_of_find? os_find_25]; decide +kernel) osRootCells_25 hrun
        ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin)
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))))))))))))))))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => match hcap with
    | ⟨Ht, hHt, hag⟩ => os_caseT (CM := CM) osCfgOk_5 (by decide) (by decide) (by decide) (by decide) (osCfgOf_5) hHt hrun
      ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin
      (os_completeOpenAtBCT (Ht := Ht) (CM := CM) osCfgOk_5 osAllBodyFacts.b5
        (osKidsAtB_5C (Ht := Ht) (CM := CM) h1 hm hq hp) (osKidsAtBT_5C (Ht := Ht) (CM := CM) h1 hm hq hp) osCapNames_5
        vmcCapLoads hHt osCallees_5 os_find_5 rfl os_body_5
        (by rw [Program.loop_of_find? os_find_5]; decide +kernel) osRootCells_5 hrun
        ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin)
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => match hcap with
    | ⟨Ht, hHt, hag⟩ => os_caseT (CM := CM) osCfgOk_12 (by decide) (by decide) (by decide) (by decide) (osCfgOf_12) hHt hrun
      ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin
      (os_completeOpenAtBCT (Ht := Ht) (CM := CM) osCfgOk_12 osAllBodyFacts.b12
        (osKidsAtB_12C (Ht := Ht) (CM := CM) h1 hm hq hp) (osKidsAtBT_12C (Ht := Ht) (CM := CM) h1 hm hq hp) osCapNames_12
        vmcCapLoads hHt osCallees_12 os_find_12 rfl os_body_12
        (by rw [Program.loop_of_find? os_find_12]; decide +kernel) osRootCells_12 hrun
        ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin)
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => match hcap with
    | ⟨Ht, hHt, hag⟩ => os_caseT (CM := CM) osCfgOk_19 (by decide) (by decide) (by decide) (by decide) (osCfgOf_19) hHt hrun
      ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin
      (os_completeOpenAtBCT (Ht := Ht) (CM := CM) osCfgOk_19 osAllBodyFacts.b19
        (osKidsAtB_19C (Ht := Ht) (CM := CM) h1 hm hq hp) (osKidsAtBT_19C (Ht := Ht) (CM := CM) h1 hm hq hp) osCapNames_19
        vmcCapLoads hHt osCallees_19 os_find_19 rfl os_body_19
        (by rw [Program.loop_of_find? os_find_19]; decide +kernel) osRootCells_19 hrun
        ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin)
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))))))))))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => match hcap with
    | ⟨Ht, hHt, hag⟩ => os_caseT (CM := CM) osCfgOk_26 (by decide) (by decide) (by decide) (by decide) (osCfgOf_26) hHt hrun
      ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin
      (os_completeOpenAtBCT (Ht := Ht) (CM := CM) osCfgOk_26 osAllBodyFacts.b26
        (osKidsAtB_26C (Ht := Ht) (CM := CM) h1 hm hq hp) (osKidsAtBT_26C (Ht := Ht) (CM := CM) h1 hm hq hp) osCapNames_26
        vmcCapLoads hHt osCallees_26 os_find_26 rfl os_body_26
        (by rw [Program.loop_of_find? os_find_26]; decide +kernel) osRootCells_26 hrun
        ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin)
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))))))))))))))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => match hcap with
    | ⟨Ht, hHt, hag⟩ => os_caseT (CM := CM) osCfgOk_6 (by decide) (by decide) (by decide) (by decide) (osCfgOf_6) hHt hrun
      ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin
      (os_completeOpenAtBCT (Ht := Ht) (CM := CM) osCfgOk_6 osAllBodyFacts.b6
        (osKidsAtB_6C (Ht := Ht) (CM := CM) h1 hm hq hp) (osKidsAtBT_6C (Ht := Ht) (CM := CM) h1 hm hq hp) osCapNames_6
        vmcCapLoads hHt osCallees_6 os_find_6 rfl os_body_6
        (by rw [Program.loop_of_find? os_find_6]; decide +kernel) osRootCells_6 hrun
        ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin)
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => match hcap with
    | ⟨Ht, hHt, hag⟩ => os_caseT (CM := CM) osCfgOk_13 (by decide) (by decide) (by decide) (by decide) (osCfgOf_13) hHt hrun
      ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin
      (os_completeOpenAtBCT (Ht := Ht) (CM := CM) osCfgOk_13 osAllBodyFacts.b13
        (osKidsAtB_13C (Ht := Ht) (CM := CM) h1 hm hq hp) (osKidsAtBT_13C (Ht := Ht) (CM := CM) h1 hm hq hp) osCapNames_13
        vmcCapLoads hHt osCallees_13 os_find_13 rfl os_body_13
        (by rw [Program.loop_of_find? os_find_13]; decide +kernel) osRootCells_13 hrun
        ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin)
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => match hcap with
    | ⟨Ht, hHt, hag⟩ => os_caseT (CM := CM) osCfgOk_20 (by decide) (by decide) (by decide) (by decide) (osCfgOf_20) hHt hrun
      ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin
      (os_completeOpenAtBCT (Ht := Ht) (CM := CM) osCfgOk_20 osAllBodyFacts.b20
        (osKidsAtB_20C (Ht := Ht) (CM := CM) h1 hm hq hp) (osKidsAtBT_20C (Ht := Ht) (CM := CM) h1 hm hq hp) osCapNames_20
        vmcCapLoads hHt osCallees_20 os_find_20 rfl os_body_20
        (by rw [Program.loop_of_find? os_find_20]; decide +kernel) osRootCells_20 hrun
        ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin)
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))))))))))))))))
  · exact fun _ _ _ _ _ _ _ _ _ _ hrun hcap hLin => match hcap with
    | ⟨Ht, hHt, hag⟩ => os_caseT (CM := CM) osCfgOk_27 (by decide) (by decide) (by decide) (by decide) (osCfgOf_27) hHt hrun
      ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin
      (os_completeOpenAtBCT (Ht := Ht) (CM := CM) osCfgOk_27 osAllBodyFacts.b27
        (osKidsAtB_27C (Ht := Ht) (CM := CM) h1 hm hq hp) (osKidsAtBT_27C (Ht := Ht) (CM := CM) h1 hm hq hp) osCapNames_27
        vmcCapLoads hHt osCallees_27 os_find_27 rfl os_body_27
        (by rw [Program.loop_of_find? os_find_27]; decide +kernel) osRootCells_27 hrun
        ((capAgreesW_iff_with _ _ _ _ _ _ _ _).mpr hag) hLin)
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))))))))))))))))))))))))))

end
end LeanVM.Guest.B1
