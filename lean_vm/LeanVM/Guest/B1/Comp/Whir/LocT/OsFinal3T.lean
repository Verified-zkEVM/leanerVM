/-
  LeanVM.Guest.B1.Comp.Whir.LocT.OsFinal3T

  `open_stacked` at a configuration, placed, bounded, over a completeness model, by a tree decoding to
  the run's openings (`Loc/OsFinal3B.lean` with the decoding).
-/

module

public import LeanVM.Guest.B1.Comp.Whir.LocT.OsDecRoot
public import LeanVM.Guest.B1.Comp.Whir.LocT.OsPlaceT
public import LeanVM.Guest.B1.Comp.Whir.LocT.OsRunT
public import LeanVM.Guest.B1.Comp.Whir.Loc.OsFinal3B

/-!
# `open_stacked` by a tree decoding to its openings

`OsDecCfg cfg os t`: on every reader satisfying `t`'s load equations, frame valuation linked to `t`
and valuation agreeing with `t`'s node on its named cells, `osOsOf cfg` decodes `os`.
`os_completeOpenAtBCT`: `os_completeOpenAtBC` by such trees.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub
open LeanVM.Guest.B1.Main (MemL RegionL)
open LeanVM.E2E.Complete
open LeanVM.Protocol.Compile (Bytes)
open LeanVM.Protocol (Digest)

@[expose] public section

/-- **The tree decodes to the openings `os` at the configuration `cfg`.** -/
def OsDecCfg (cfg : OsCfg) (os : List Opening) (t : Tree) : Prop :=
  ∀ (rd : Reader) (V : FrameVals) (σ' : Val), Sat rd (t.loadEqns coreProgram) → KidsLink V t →
    B2C.NodeAgree t σ' → osOsOf cfg σ' (wqV rd V cfg) = os

variable {Ht : Bytes → Digest} {CM : CompModel}

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {bd : String → ℕ}

set_option maxHeartbeats 1000000 in
/-- **`open_stacked` at a configuration is complete, placed, by a bounded tree.** -/
theorem os_completeOpenAtBCT {cfg : OsCfg} {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall)
    (hbf : OsBodyFacts cfg) (hk : OsKidsAtBC CM Ht fs cert κ cfg bd)
    (hkT : OsKidsAtBCT CM Ht fs cert κ cfg bd) (hcn : OsCapNames cfg) (hVL : VmcCapLoads) (hHt : ∀ x dg, CM.H x = some dg → dg = Ht x)
    (hcal : ∀ rd, OsCallees rd cfg) {name : String} {fn : Fn}
    (hfind : coreProgram.find? name = some fn) (hp : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5])
    (hb : fn.body = osBody cfg) (hloop : coreProgram.loop name = false)
    (hcells : CellsOk name (osLvsReads cfg 0 cfg.levels (osHead cfg).2)) {root cv : Digest} {xs : List E}
    {os : List Opening} {w : WhirEnd} {cv' : Digest} {roots' : List (Digest × ℕ × ℕ)} {target : E} {c : ℕ}
    {Lin : Main.Layout} (hrun : RunsWithM CM.hm (whirOpen μ r target) cv xs os [(root, stackShape μ r)] w cv' roots')
    (hcap : CapAgreesW Ht μ r root cv xs os target)
    (hLin : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd (ofK (Parameters.gpow c)) xs) :
    CompleteAtBST CM.sem fs cert κ name Lin [(digestScalars cv).1, (digestScalars cv).2, target, (digestScalars root).1,
      (digestScalars root).2, ofK (Parameters.gpow c)] (fun rets Lout =>
      ∃ b, rets = [w.target, ofK (Parameters.gpow b), w.inner, w.residual] ∧
        Lout = [(b, w.point ++ List.replicate (pointCap - w.point.length) 0)])
      (fs name + (osSizes cfg).sum + osCallsMax fs bd cfg) (fun _ _ t => OsDecCfg cfg os t) := by
  obtain ⟨d, hx, hcv, htg, hrt, hos, hkit, -, hlastq⟩ := os_kit_of_runCT (Ht := Ht) (CM := CM) hok hHt hrun hcap
  subst hx hcv htg hrt hos
  have hn := hok.len2
  obtain ⟨sp', Q', hQ, hch⟩ := hkit.chain
  have hrunOk := d.runOk_ofC (Ht := Ht) (CM := CM) hok hkit.len hch hkit.chst
  have hbody : fn.body = (osHead cfg).1 ++ (osLevels cfg 0 cfg.levels (osHead cfg).2).1 ++
      (osTail cfg.yrLog (OsRun.sL cfg)).1 ++ osFinPre cfg ++ [.ret (osRetVs cfg)] := by
    rw [hb, hbf.last, os_pre_eq]
  have hst := hbf.straight
  rw [os_pre_eq] at hst
  have had := hbf.addrs
  rw [os_pre_eq] at had
  have hal := hbf.allocs
  rw [os_pre_eq] at hal
  have htf : (d.tfW Ht).length = cfg.yrLog := by
    simp only [OsData.tfW, List.length_append, List.length_cons, List.length_nil, hkit.chst]; have := hok.yr2; omega
  have hjo : 11 + 2 * cfg.levels.length + 1 < (osSizes cfg).length := by rw [os_length_osSizes]; omega
  have hpreS := hst
  refine os_completeAt_placeBCT (CM := CM) hfind hloop κ Lin _ _ hbody hst had (osSizes cfg) (11 + 2 * cfg.levels.length + 1) hjo
    (C := osTC) (osCallsMax fs bd cfg) fun fp => ?_
  set b0 := fp + fs name
  set R := d.runOfW Ht cfg (ofK (Parameters.gpow c)) b0
  set σ := Val.ofArgs (osBodyValsW Ht cfg R)
  set rets : List E := [w.target, ofK (Parameters.gpow (b0 + ((osSizes cfg).take (11 + 2 * cfg.levels.length + 1)).sum)),
    w.inner, w.residual]
  have hpt : osPtrAt cfg b0 (11 + 2 * cfg.levels.length + 1) =
      ofK (Parameters.gpow (b0 + ((osSizes cfg).take (11 + 2 * cfg.levels.length + 1)).sum)) := by
    unfold osPtrAt; rw [os_bases_getD _ _ _ hjo]
  have hout : ∀ Q : List E, (fun rets Lout => ∃ b, rets = [w.target, ofK (Parameters.gpow b), w.inner, w.residual] ∧
      Lout = [(b, w.point ++ List.replicate (pointCap - w.point.length) 0)]) rets
      [(b0 + ((osSizes cfg).take (11 + 2 * cfg.levels.length + 1)).sum,
        (d.ownQW Ht cfg Q).getD (11 + 2 * cfg.levels.length + 1) [])] := fun Q => by
    refine ⟨_, rfl, ?_⟩
    have hhd : (cfg.levels.headD default).folds = (cfg.lv 0).folds := by
      cases h' : cfg.levels with
      | nil => simp [h'] at hn
      | cons a b' => simp [OsCfg.lv, h']
    have hlane : (cfg.levels.headD default).folds ≤ cfg.nFolds := by rw [hhd]; exact hok.laneLe
    rw [OsData.ownQ_getD_ptC (Ht := Ht), OsData.ptC_eqC (Ht := Ht) hrunOk.fchLen htf hlane hok.pt42 hbf.tch, hkit.w, hhd]
    have hfl' : ((d.endLW Ht cfg).2.2.folds ++ d.tfW Ht).length = cfg.nFolds + cfg.yrLog := by
      rw [List.length_append, htf]; exact congrArg (· + _) hrunOk.fchLen
    have hpl : (((d.endLW Ht cfg).2.2.folds ++ d.tfW Ht).drop (cfg.lv 0).folds ++
        ((d.endLW Ht cfg).2.2.folds ++ d.tfW Ht).take (cfg.lv 0).folds).length = cfg.nFolds + cfg.yrLog := by
      simp only [List.length_append, List.length_drop, List.length_take, hfl']
      have := hok.laneLe; omega
    rw [hpl]
    rfl
  have hparams : fn.params.map σ = [(digestScalars d.cv).1, (digestScalars d.cv).2, d.target,
      (digestScalars d.root).1, (digestScalars d.root).2, ofK (Parameters.gpow c)] := by
    rw [hp]; rfl
  have hfit : ∀ Q : List E, Q.length ≤ cfg.posLen →
      List.Forall₂ (fun c s => c.length ≤ s) (d.ownQW Ht cfg Q) (osSizes cfg) := fun Q hQ =>
    os_own_fitsC (Ht := Ht) hbf.layout hok.yr5 (by rw [hkit.chst]; have := hok.yr2; omega) hQ (le_of_eq hrunOk.fchLen)
  by_cases hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 (osLkW Ht cfg d Lin b0)
  · obtain ⟨N, L, ps, hW, hD, hN, hK⟩ := d.kids_atBCT (Ht := Ht) (CM := CM) hok hbf hk hkT hcn hVL hHt hkit hLin hex
      (b0 + (osSizes cfg).sum)
    have hw := Main.walk_straight σ (osRetVs cfg) _ hpreS
    rw [← hbody] at hw
    obtain ⟨-, -, -, i4⟩ := Main.straight_parts σ _ hpreS
    have hcalls := i4.trans (os_calls_eq cfg σ)
    refine ⟨σ, d.ownQW Ht cfg (OsData.qbpC cfg fs cert fun l => ps.getD l 0), rets, N, L, fun _ => False, _,
      fun rd => osLvsQs (fun l f a b t => osQB Ht cfg d b0 l f a b rd t) σ 0
        (osLvsKOf cfg σ 0 (osHead cfg).2 cfg.levels.length) ++
        ((((osTail cfg.yrLog (OsRun.sL cfg)).1.filterMap Main.Stmt.callS).map (Main.mkCall σ)).map (fun _ _ _ => True) ++
          (((osFinPre cfg).filterMap Main.Stmt.callS).map (Main.mkCall σ)).map (fun _ _ _ => True)),
      os_calls_eq cfg σ, hN, hfit _ (by rw [OsData.qbpC, os_length_segC]), hout _, hW, hD, hparams,
      fun rd hl hmB hmLin => ?_, fun rd hl hmB hmL hmLin => by
        rw [List.map_append, List.map_append]; exact hK rd hl hmB hmL hmLin,
      fun rd hl hmB hmL hmLin ks hkv hks => ?_⟩
    rotate_left
    · have hmk : MemL rd (osLkW Ht cfg d Lin b0) :=
        Main.memL_append.mpr ⟨hmLin, OsData.memL_ownQ_nilC (Ht := Ht) hmB⟩
      show OsDecCfg cfg d.os (Memory.Tree.node name σ (osSizes cfg) ks)
      exact OsData.os_decQC (Ht := Ht) (CM := CM) (Lin := Lin) (b0 := b0) (σ := σ) (rd := rd) (ks := ks)
        (bufs := osSizes cfg) hok hbf hkT hkit hlastq hcells hfind hw hcalls hmk hkv hks
        (by rw [Memory.length_bases, List.length_map])
    obtain ⟨hH, hA⟩ := d.body_atC (Ht := Ht) (CM := CM) hok hbf hkit (hcal rd) (os_bufReadsC (Ht := Ht) hmB) (hLin rd hl hmLin)
    rw [hpt] at hH
    rw [hal]
    refine ⟨os_holdsList_of_eqC (CM := CM) hb hH, ?_, ?_⟩
    · have := congrArg (List.map Prod.snd) hA
      simp only [osAllocs, List.map_map] at this
      rw [osAllocVals_snd] at this
      exact this
    · have := congrArg (List.map Prod.fst) hA
      simp only [osAllocs, List.map_map] at this
      rw [osAllocVals_fst (d.runOf_ptrsC (Ht := Ht) cfg _ b0)] at this
      rw [List.map_map]; exact this
  · refine ⟨σ, d.ownQW Ht cfg (OsData.qbpC cfg fs cert fun _ => 0), rets, 0, [], fun _ => False, _, fun _ => [],
      os_calls_eq cfg σ,
      Nat.zero_le _, hfit _ (by rw [OsData.qbpC, os_length_segC]), hout _, fun _ h => by simp at h, disj_nil, hparams,
      fun rd hl hmB hmLin => absurd ⟨rd, hl, Main.memL_append.mpr ⟨hmLin, OsData.memL_ownQ_nilC (Ht := Ht) hmB⟩⟩ hex,
      fun rd hl hmB _ hmLin => absurd ⟨rd, hl, Main.memL_append.mpr ⟨hmLin, OsData.memL_ownQ_nilC (Ht := Ht) hmB⟩⟩ hex,
      fun rd hl hmB _ hmLin => absurd ⟨rd, hl, Main.memL_append.mpr ⟨hmLin, OsData.memL_ownQ_nilC (Ht := Ht) hmB⟩⟩ hex⟩

end
end LeanVM.Guest.B1
