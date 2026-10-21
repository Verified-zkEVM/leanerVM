/-
  LeanVM.Guest.B1.Comp.Whir.Loc.OsInstBaseB

  The instances' callees of `open_stacked`, bounded, over a completeness model (`Whir/OsInstBaseB.lean`)
-/

module

public import LeanVM.Guest.B1.Whir.OsInstBaseB
public import LeanVM.Guest.B1.Comp.Whir.Loc.OsFinal3B

/-!
# The instances' callees of `open_stacked`, bounded, over a completeness model (`Whir/OsInstBaseB.lean`)
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub
open LeanVM.E2E.Complete
open LeanVM.Protocol.Compile (Bytes)
open LeanVM.Protocol (Digest)

@[expose] public section

variable {Ht : Bytes → Digest} {CM : CompModel}

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

/-- **Group 1's callees' bounds, at most constants**, at the argument shapes `open_stacked` calls them
with (`opening_ood_point` at `g^m`, `m ≤ 22`; `grind_check` at `g^17`). -/
structure OsCalleesMaxC (CM : CompModel) {fs : String → ℕ} {cert : String → V → ℕ} {k : ℕ} (h1 : OsCalleesAtBC CM fs cert k) : Type where
  foldMax : ℕ
  fold : ∀ a, h1.foldB a ≤ foldMax
  canonicalMax : ℕ
  canonical : ∀ a, h1.canonicalB a ≤ canonicalMax
  oodMax : ℕ
  ood : ∀ a m, a.getD 3 0 = gen ^ m → m ≤ 22 → h1.oodB a ≤ oodMax
  grindMax : ℕ
  grind : ∀ a, a.getD 3 0 = gen ^ Whir.queryGrindingBits → h1.grindB a ≤ grindMax
  finalMsg4Max : ℕ
  finalMsg4 : ∀ a, h1.finalMsg4B a ≤ finalMsg4Max
  finalMsg8Max : ℕ
  finalMsg8 : ∀ a, h1.finalMsg8B a ≤ finalMsg8Max
  finalMsg16Max : ℕ
  finalMsg16 : ∀ a, h1.finalMsg16B a ≤ finalMsg16Max
  finalMsg32Max : ℕ
  finalMsg32 : ∀ a, h1.finalMsg32B a ≤ finalMsg32Max
  rowWeights4Max : ℕ
  rowWeights4 : ∀ a, h1.rowWeights4B a ≤ rowWeights4Max
  rowWeights6Max : ℕ
  rowWeights6 : ∀ a, h1.rowWeights6B a ≤ rowWeights6Max
  foldFinal2Max : ℕ
  foldFinal2 : ∀ a, h1.foldFinal2B a ≤ foldFinal2Max
  foldFinal3Max : ℕ
  foldFinal3 : ∀ a, h1.foldFinal3B a ≤ foldFinal3Max
  foldFinal4Max : ℕ
  foldFinal4 : ∀ a, h1.foldFinal4B a ≤ foldFinal4Max
  foldFinal5Max : ℕ
  foldFinal5 : ∀ a, h1.foldFinal5B a ≤ foldFinal5Max

/-- **The trees' sizes of `open_stacked`'s pure callees**: its caps' and its residual loops' at
their trip counts. -/
structure OsPureSizesC (CM : CompModel) (fs : String → ℕ) : Type where
  capB : String → ℕ
  cap : ∀ name ∈ osCapNames, TotalLeB CM.sem coreProgram fs name fun _ => capB name
  resB : String → ℕ
  res : ∀ p ∈ osResLoops, ∀ rd (t : Tree) (args rets : List E), t.name = p.1 → args.take 2 = [1, gen ^ p.2] →
    t.ValidB CM.sem coreProgram rd args rets → t.BufsOk coreProgram → t.total fs ≤ resB p.1

/-- Group 1's maxima by name. -/
def osG1PairsC (CM : CompModel) {k : ℕ} {h1 : OsCalleesAtBC CM fs cert k} (hm : OsCalleesMaxC CM h1) : List (String × ℕ) :=
  [("opening_fold", hm.foldMax),
    ("assert_canonical", hm.canonicalMax),
    ("opening_ood_point", hm.oodMax),
    ("grind_check", hm.grindMax),
    ("opening_final_message__L4", hm.finalMsg4Max),
    ("opening_final_message__L8", hm.finalMsg8Max),
    ("opening_final_message__L16", hm.finalMsg16Max),
    ("opening_final_message__L32", hm.finalMsg32Max),
    ("opening_row_weights__L4_L0", hm.rowWeights4Max),
    ("opening_row_weights__L6_L1", hm.rowWeights6Max),
    ("fold_final_msg__L2", hm.foldFinal2Max),
    ("fold_final_msg__L3", hm.foldFinal3Max),
    ("fold_final_msg__L4", hm.foldFinal4Max),
    ("fold_final_msg__L5", hm.foldFinal5Max)]

/-- A level's bound by name: its queries', cap's, query-position loop's and residual loop's. -/
def osLvBdC (CM : CompModel) (fs : String → ℕ) (hp : OsPureSizesC CM fs) (lv : OsLvl) (f : String) : ℕ :=
  max (if f = lv.queriesFn then fs f + (lv.queries + 1) + (lv.queries + 1) * fs (osOqLoop f) else 0)
    (max (if f = lv.verifyCap then hp.capB f else 0)
      (max (if f = lv.sqLoop then sqTot fs lv lv.squeezes 0 else 0) (if f = lv.resLoop then hp.resB f else 0)))

/-- **The callees' bound by name** at a configuration. -/
def osBdC (CM : CompModel) (fs : String → ℕ) {cert : String → V → ℕ} {k : ℕ} {h1 : OsCalleesAtBC CM fs cert k} (hm : OsCalleesMaxC CM h1)
    (hp : OsPureSizesC CM fs) (cfg : OsCfg) (f : String) : ℕ :=
  max (osPairsMax (osG1PairsC CM hm) f) (((List.range cfg.levels.length).map fun l => osLvBdC CM fs hp (cfg.lv l) f).foldr max 0)

section Bd

variable {k : ℕ} {h1 : OsCalleesAtBC CM fs cert k} (hm : OsCalleesMaxC CM h1) (hp : OsPureSizesC CM fs) (cfg : OsCfg)

theorem osBd_g1C {f : String} {v : ℕ} (h : (f, v) ∈ osG1PairsC CM hm) : v ≤ osBdC CM fs hm hp cfg f :=
  le_max_of_le_left (osPairsMax_ge h)

theorem osBd_lvC {l : ℕ} (hl : l < cfg.levels.length) (f : String) : osLvBdC CM fs hp (cfg.lv l) f ≤ osBdC CM fs hm hp cfg f :=
  le_max_of_le_right (os_foldr_max_ge (List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩))

theorem osKB_foldC : CompleteRelBS CM.sem fs cert k "opening_fold" (MeaningOpeningFoldComp CM) (osBdC CM fs hm hp cfg "opening_fold") :=
  fun a r L h => (h1.fold a r L h).mono le_rfl ((hm.fold a).trans (osBd_g1C (CM := CM) hm hp cfg (by simp [osG1PairsC])))

theorem osKB_canonicalC : CompleteRelBS CM.sem fs cert k "assert_canonical" (fun _ args rets => MeaningAssertCanonical args rets)
    (osBdC CM fs hm hp cfg "assert_canonical") :=
  fun a r L h => (h1.canonical a r L h).mono le_rfl ((hm.canonical a).trans (osBd_g1C (CM := CM) hm hp cfg (by simp [osG1PairsC])))

theorem osKB_oodC : OsOodAtBC CM fs cert k (osBdC CM fs hm hp cfg "opening_ood_point") :=
  fun m h22 a r L ha h => (h1.ood a r L h).mono le_rfl
    ((hm.ood a m ha h22).trans (osBd_g1C (CM := CM) hm hp cfg (by simp [osG1PairsC])))

theorem osKB_grindC : OsGrindAtBC CM fs cert k (osBdC CM fs hm hp cfg "grind_check") :=
  fun a r L ha h => (h1.grind a r L h).mono le_rfl ((hm.grind a ha).trans (osBd_g1C (CM := CM) hm hp cfg (by simp [osG1PairsC])))

theorem osKB_finalMsg4C : OsFinalMsgAtBC CM fs cert k "opening_final_message__L4" 4 fun _ => osBdC CM fs hm hp cfg "opening_final_message__L4" :=
  fun a r L h => (h1.finalMsg4 a r L h).mono le_rfl ((hm.finalMsg4 a).trans (osBd_g1C (CM := CM) hm hp cfg (by simp [osG1PairsC])))

theorem osKB_finalMsg8C : OsFinalMsgAtBC CM fs cert k "opening_final_message__L8" 8 fun _ => osBdC CM fs hm hp cfg "opening_final_message__L8" :=
  fun a r L h => (h1.finalMsg8 a r L h).mono le_rfl ((hm.finalMsg8 a).trans (osBd_g1C (CM := CM) hm hp cfg (by simp [osG1PairsC])))

theorem osKB_finalMsg16C : OsFinalMsgAtBC CM fs cert k "opening_final_message__L16" 16 fun _ => osBdC CM fs hm hp cfg "opening_final_message__L16" :=
  fun a r L h => (h1.finalMsg16 a r L h).mono le_rfl ((hm.finalMsg16 a).trans (osBd_g1C (CM := CM) hm hp cfg (by simp [osG1PairsC])))

theorem osKB_finalMsg32C : OsFinalMsgAtBC CM fs cert k "opening_final_message__L32" 32 fun _ => osBdC CM fs hm hp cfg "opening_final_message__L32" :=
  fun a r L h => (h1.finalMsg32 a r L h).mono le_rfl ((hm.finalMsg32 a).trans (osBd_g1C (CM := CM) hm hp cfg (by simp [osG1PairsC])))

theorem osKB_rowWeights4C : OsRowWeightsAtBC CM fs cert k "opening_row_weights__L4_L0" 4 0 fun _ => osBdC CM fs hm hp cfg "opening_row_weights__L4_L0" :=
  fun a r L h => (h1.rowWeights4 a r L h).mono le_rfl ((hm.rowWeights4 a).trans (osBd_g1C (CM := CM) hm hp cfg (by simp [osG1PairsC])))

theorem osKB_rowWeights6C : OsRowWeightsAtBC CM fs cert k "opening_row_weights__L6_L1" 6 1 fun _ => osBdC CM fs hm hp cfg "opening_row_weights__L6_L1" :=
  fun a r L h => (h1.rowWeights6 a r L h).mono le_rfl ((hm.rowWeights6 a).trans (osBd_g1C (CM := CM) hm hp cfg (by simp [osG1PairsC])))

theorem osKB_foldFinal2C : OsFoldFinalAtBC CM fs cert k "fold_final_msg__L2" 2 fun _ => osBdC CM fs hm hp cfg "fold_final_msg__L2" :=
  fun a r L h => (h1.foldFinal2 a r L h).mono le_rfl ((hm.foldFinal2 a).trans (osBd_g1C (CM := CM) hm hp cfg (by simp [osG1PairsC])))

theorem osKB_foldFinal3C : OsFoldFinalAtBC CM fs cert k "fold_final_msg__L3" 3 fun _ => osBdC CM fs hm hp cfg "fold_final_msg__L3" :=
  fun a r L h => (h1.foldFinal3 a r L h).mono le_rfl ((hm.foldFinal3 a).trans (osBd_g1C (CM := CM) hm hp cfg (by simp [osG1PairsC])))

theorem osKB_foldFinal4C : OsFoldFinalAtBC CM fs cert k "fold_final_msg__L4" 4 fun _ => osBdC CM fs hm hp cfg "fold_final_msg__L4" :=
  fun a r L h => (h1.foldFinal4 a r L h).mono le_rfl ((hm.foldFinal4 a).trans (osBd_g1C (CM := CM) hm hp cfg (by simp [osG1PairsC])))

theorem osKB_foldFinal5C : OsFoldFinalAtBC CM fs cert k "fold_final_msg__L5" 5 fun _ => osBdC CM fs hm hp cfg "fold_final_msg__L5" :=
  fun a r L h => (h1.foldFinal5 a r L h).mono le_rfl ((hm.foldFinal5 a).trans (osBd_g1C (CM := CM) hm hp cfg (by simp [osG1PairsC])))

end Bd

theorem VmcCompleteAtBC.mono {k D : ℕ} {name : String} {B B' : ℕ} (h : VmcCompleteAtBC CM fs cert k D name B) (hB : B ≤ B') :
    VmcCompleteAtBC CM fs cert k D name B' := fun L c f r hm => (h L c f r hm).mono le_rfl hB

/-- **A level's callees by bounded trees, from their parts.** -/
theorem osLvKidsAtB_mkC {k : ℕ} {h1 : OsCalleesAtBC CM fs cert k} {hm : OsCalleesMaxC CM h1} {hp : OsPureSizesC CM fs} {cfg : OsCfg}
    {l : ℕ} (hl : l < cfg.levels.length)
    (hrw : OsRowWeightsAtBC CM fs cert κ (cfg.lv l).rowWeights (cfg.lv l).folds (if l = 0 then 1 else 0)
      fun _ => osBdC CM fs hm hp cfg (cfg.lv l).rowWeights)
    (hcn : (cfg.lv l).verifyCap ∈ osCapNames)
    (hcap : ∀ {B : ℕ}, TotalLeB CM.sem coreProgram fs (cfg.lv l).verifyCap (fun _ => B) →
      VmcCompleteAtBC CM fs cert κ (cfg.lv l).capDepth (cfg.lv l).verifyCap B) {loop : String}
    (hq : OqCompleteAtBC CM Ht fs cert κ (if l = 0 then 1 else 0) (2 ^ (cfg.lv l).folds) (cfg.lv l).depth
      (cfg.lv l).capDepth (cfg.lv l).queriesFn fun n => fs (cfg.lv l).queriesFn + (n + 1) + (n + 1) * fs loop)
    (hloop : osOqLoop (cfg.lv l).queriesFn = loop)
    (hdec : OsDecodeAtDC CM fs cert κ (cfg.lv l).depth (cfg.lv l).decode) (hpl : sqPlaceB (cfg.lv l) = true)
    {fn : Fn} (hsf : coreProgram.find? (cfg.lv l).sqLoop = some fn) (hsp : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4])
    (hsb : fn.body = sqLoopOf (cfg.lv l)) (hsl : coreProgram.loop (cfg.lv l).sqLoop = true) {fr : Fn}
    (hrf : coreProgram.find? (cfg.lv l).resLoop = some fr)
    (hrp : fr.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6]) (hrb : fr.body = resLoopOf cfg l (cfg.lv l))
    (hpure : Stmt.pureList [(cfg.lv l).resLoop] (resLoopOf cfg l (cfg.lv l)) = true)
    (hres : ((cfg.lv l).resLoop, (cfg.lv l).queries) ∈ osResLoops) :
    OsLvKidsAtBC CM Ht fs cert κ cfg (osBdC CM fs hm hp cfg) l where
  rw := hrw
  cap := (hcap (hp.cap _ hcn)).mono <| le_trans (le_max_of_le_right (le_max_of_le_left (by simp)))
    (osBd_lvC (CM := CM) hm hp cfg hl _)
  queries := ⟨_, hq, le_trans (by rw [← hloop]; exact le_max_of_le_left (by simp)) (osBd_lvC (CM := CM) hm hp cfg hl _)⟩
  decode := hdec
  sqPlace := sqPlace_of hpl
  sqFn := ⟨fn, hsf, hsp, hsb⟩
  sqLoop := hsl
  sqLe := le_trans (le_max_of_le_right (le_max_of_le_right (le_max_of_le_left (by simp))))
    (osBd_lvC (CM := CM) hm hp cfg hl _)
  resPure := fun g hg f hf => by
    simp only [List.mem_singleton] at hg
    subst hg
    rw [hrf] at hf
    cases hf
    rw [hrb]
    exact hpure
  resFn := ⟨fr, hrf, hrp, hrb⟩
  resTot := fun rd t args rets hn ha hv hb => le_trans (hp.res _ hres rd t args rets hn ha hv hb)
    (le_trans (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (by simp)))) (osBd_lvC (CM := CM) hm hp cfg hl _))

end
end LeanVM.Guest.B1
