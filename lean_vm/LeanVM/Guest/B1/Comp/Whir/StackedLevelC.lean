/-
  LeanVM.Guest.B1.Comp.Whir.StackedLevelC

  `open_stacked`'s levels over a completeness model.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.StackedEndC

/-!
# The levels over a completeness model (TRIAGE #36)

`Whir/StackedC6.lean`, `StackedC7.lean` and `StackedC9.lean` over a `CompModel` and a total hash
`Ht`: a level's two parts (`osLevelA_completeC`, `osLevelB_completeC`), one level
(`osLevel_completeC`) and every level (`osLevels_completeC`) at their honest values over `Ht`, under
`CM.sem`, from the levels' data `OsChainC` (each level's `OsLvAns`: what the model answers at it).
The calls are taken at their call relations as in the deployed lemmas, `opening_fold`'s at a run
under the model (`OsLvCallHC`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub LeanVM.E2E.Complete

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## Calls under any semantics -/

theorem os_holdsListB_toTC {S : BlakeSem} {C : CallRel} {ss : List Stmt} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsListB S C rd σ ss next kret) : Stmt.HoldsListB S osTC rd σ ss next kret :=
  holdsListB_mono (fun _ _ _ _ => trivial) ss id (fun _ h => h) h

/-- **A straight block's calls** satisfy the call relation it holds at, under any semantics
(`os_callsOk_of_holdsList`). -/
theorem os_callsOk_of_holdsListB {S : BlakeSem} {C : CallRel} : ∀ (ss : List Stmt), ss.all Main.Stmt.straight = true →
    ∀ {next : Prop} {kret : List E → Prop}, Stmt.HoldsListB S C rd σ ss next kret → OsCallsOk C σ ss
  | [], _, _, _, _ => fun c hc => by simp at hc
  | s :: ss, hs, next, kret, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hs
    match s, hs.1 with
    | .atom a, _ =>
      simp only [Stmt.HoldsListB, Stmt.HoldsB] at h
      intro c hc
      rw [List.filterMap_cons_none (show Main.Stmt.callS (.atom a) = none from rfl)] at hc
      exact os_callsOk_of_holdsListB ss hs.2 h.2 c hc
    | .call f args rets, _ =>
      simp only [Stmt.HoldsListB, Stmt.HoldsB] at h
      intro c hc ht
      rw [List.filterMap_cons_some (show Main.Stmt.callS (.call f args rets) = some (none, f, args, rets) from rfl),
        List.map_cons] at hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · simpa [Main.mkCall] using h.1
      · exact os_callsOk_of_holdsListB ss hs.2 h.2 c hc' ht
    | .callIf cc f args, _ =>
      simp only [Stmt.HoldsListB, Stmt.HoldsB] at h
      intro c hc ht
      rw [List.filterMap_cons_some (show Main.Stmt.callS (.callIf cc f args) = some (some cc, f, args, []) from rfl),
        List.map_cons] at hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · simp only [Main.mkCall, decide_eq_true_eq] at ht
        simpa [Main.mkCall] using h.2.1 ht
      · exact os_callsOk_of_holdsListB ss hs.2 h.2.2 c hc' ht

variable {CM : CompModel} {Ht : Bytes → Digest}

/-- The values of the level's first part from its first: the folds' (the cursor's base at `cur`),
the residual's or the next commitment's, the nonce's. -/
def osLvValsAW (Ht : Bytes → Digest) (cfg : OsCfg) (lvl : ℕ) (xs : List E) (cv : Digest) (p : ℕ) (w : WhirState) (H : OsLvH)
    (co : ℕ) (cur oodzv : E) : List E :=
  osFoldsValsW Ht xs (cfg.lv lvl).folds cv p w.quad (cur * gen ^ (p - co)) co ++
    (if lvl = cfg.yrLevel then osFinalValsW Ht H.cv1 (osHMs cfg lvl xs p) (cur * gen ^ osHP1 cfg lvl p) 0 cfg.yrLen
    else osCommitValsW Ht lvl (cfg.lv lvl).logCols oodzv H.cv1 (osHW cfg lvl xs p 0) (osHW cfg lvl xs p 1)
      (osHW cfg lvl xs p 2) (osHW cfg lvl xs p 3) (osHW cfg lvl xs p 4)) ++
    osGrindValsW Ht (cfg.lv lvl).grindBits (osHNonce cfg lvl xs p) (osHCv2W Ht cfg lvl xs p H.cv1)


/-- **A level's first part** at its honest values (G:1096-1142). -/
theorem osLevelA_completeC {cfg : OsCfg} {μ lvl : ℕ} {L : Whir.Level} {rest : List Whir.Level}
    (hspec : LvSpec cfg μ lvl L rest) {xs : List E} {cv : Digest} {p : ℕ} {w : WhirState}
    {osp : List Opening} {roots : List (Digest × ℕ × ℕ)} {H : OsLvH}
    (hok : OsLvOkW Ht cfg lvl xs p μ L cv w osp roots H) (hans : OsLvAns CM.hm Ht cfg lvl xs p L cv w osp roots H)
    {s : OsSt} {cur oodzv : E}
    (hat : OsAt σ s cv cur p) (hcop : s.co ≤ p) (hco8 : s.co ≤ 8)
    (hq : w.quad = [σ (.n s.c), σ (.n s.b), σ (.n s.a)]) (hoz : σ (.n osOodz) = oodzv)
    (hxs : ∀ j < xs.length, LoadHolds rd cur j (xs.getD j 0))
    (hfch : ∀ j < (cfg.lv lvl).folds, LoadHolds rd (σ (.n osFch)) ((cfg.lv lvl).foldsOff + j) (H.chs.getD j 0))
    (hrt2 : lvl ≠ cfg.yrLevel → LoadHolds rd (σ (.n osRoots)) (2 * lvl + 2) (osHW cfg lvl xs p 0) ∧
      LoadHolds rd (σ (.n osRoots)) (2 * lvl + 3) (osHW cfg lvl xs p 1))
    (hood : lvl ≠ cfg.yrLevel → LoadHolds rd (σ (.n osOod)) ((lvl + 1) * 4 + 0 * 4 + 1) (osHW cfg lvl xs p 2) ∧
      LoadHolds rd (σ (.n osOod)) ((lvl + 1) * 4 + 0 * 4 + 2) (osHW cfg lvl xs p 3) ∧
      LoadHolds rd (σ (.n osOod)) ((lvl + 1) * 4 + 0 * 4 + 3) (osHW cfg lvl xs p 4))
    {kret : List E → Prop}
    (hcf : ∀ (cv' : Digest) (p' : ℕ) (q' : List E), q'.length = 3 → p' + 2 ≤ xs.length →
      RunsToM CM.hm (foldStep q') cv' [xs.getD p' 0, xs.getD (p' + 1) 0]
        (challengeOf (sqCvW Ht cv'), polyEval q' (challengeOf (sqCvW Ht cv')),
          [xs.getD p' 0, polyEval q' (challengeOf (sqCvW Ht cv')) + xs.getD (p' + 1) 0, xs.getD (p' + 1) 0])
        (obsAllW Ht (sqCvW Ht cv') [xs.getD p' 0, xs.getD (p' + 1) 0]) →
      C "opening_fold" [(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ p', q'.getD 0 0, q'.getD 1 0,
        q'.getD 2 0] (osFoldRetsW Ht xs cv' p' q' (cur * gen ^ p')))
    (hcm : lvl = cfg.yrLevel → C cfg.finalMsg [(digestScalars H.cv1).1, (digestScalars H.cv1).2,
      cur * gen ^ osHP1 cfg lvl p, σ (.n osFmsg)]
      [(digestScalars (osHCv2W Ht cfg lvl xs p H.cv1)).1, (digestScalars (osHCv2W Ht cfg lvl xs p H.cv1)).2,
        cur * gen ^ osHP2 cfg lvl p])
    (hca : lvl ≠ cfg.yrLevel → C "assert_canonical" [osHW cfg lvl xs p 0] [0] ∧
      C "assert_canonical" [osHW cfg lvl xs p 1] [0] ∧
      C "opening_ood_point" [(digestScalars (osHCv12W Ht cfg lvl xs p H.cv1)).1,
        (digestScalars (osHCv12W Ht cfg lvl xs p H.cv1)).2, oodzv * osGw ((lvl + 1 + 0) * 22), osGw (cfg.lv lvl).logCols]
        [(digestScalars (sqAllW Ht (cfg.lv lvl).logCols (osHCv12W Ht cfg lvl xs p H.cv1)).2).1,
          (digestScalars (sqAllW Ht (cfg.lv lvl).logCols (osHCv12W Ht cfg lvl xs p H.cv1)).2).2])
    (hcg : C "grind_check" [(digestScalars (osHCv2W Ht cfg lvl xs p H.cv1)).1,
      (digestScalars (osHCv2W Ht cfg lvl xs p H.cv1)).2, osHNonce cfg lvl xs p, osGw (cfg.lv lvl).grindBits] [])
    (hv : ∀ j < (osLvValsAW Ht cfg lvl xs cv p w H s.co cur oodzv).length,
      σ (.n (s.k + j)) = (osLvValsAW Ht cfg lvl xs cv p w H s.co cur oodzv).getD j 0) :
    Stmt.HoldsListB CM.sem C rd σ ((osLvF cfg lvl s).1 ++ (osLvM cfg lvl s).1 ++ (osLvG cfg lvl s).1) True kret ∧
      OsAt σ (osLvG cfg lvl s).2 (osHCv3W Ht cfg lvl xs p H.cv1) cur (osHP2 cfg lvl p + 1) ∧
      (osLvG cfg lvl s).2.co = (if lvl = cfg.yrLevel then 1 else 6) ∧
      H.w1.quad = [σ (.n (osLvG cfg lvl s).2.c), σ (.n (osLvG cfg lvl s).2.b), σ (.n (osLvG cfg lvl s).2.a)] ∧
      H.w1.target = σ (.n (osLvG cfg lvl s).2.t) ∧
      (osLvG cfg lvl s).2.k = s.k + (osLvValsAW Ht cfg lvl xs cv p w H s.co cur oodzv).length := by
  obtain ⟨hf, hf0, hqq, hml0, hml1, hlc, hdep, hgr, hper, hs1, hs2, hs3, hs4, hdig, hcd1, hcd2, hb1,
    hb2, hb4, hb5, hnq, hb6, hlast, hyr, hnext⟩ := hspec
  have hcb := os_cb_of_at hat hcop
  set Vf := osFoldsValsW Ht xs (cfg.lv lvl).folds cv p w.quad (cur * gen ^ (p - s.co)) s.co with hVf
  set Vm := (if lvl = cfg.yrLevel then osFinalValsW Ht H.cv1 (osHMs cfg lvl xs p) (cur * gen ^ osHP1 cfg lvl p) 0
      cfg.yrLen
    else osCommitValsW Ht lvl (cfg.lv lvl).logCols oodzv H.cv1 (osHW cfg lvl xs p 0) (osHW cfg lvl xs p 1)
      (osHW cfg lvl xs p 2) (osHW cfg lvl xs p 3) (osHW cfg lvl xs p 4)) with hVm
  set Vg := osGrindValsW Ht (cfg.lv lvl).grindBits (osHNonce cfg lvl xs p) (osHCv2W Ht cfg lvl xs p H.cv1) with hVg
  have hVA : osLvValsAW Ht cfg lvl xs cv p w H s.co cur oodzv = Vf ++ Vm ++ Vg := rfl
  rw [hVA] at hv ⊢
  have hlg : Vg.length = 16 := by simp [hVg, osGrindValsW]
  -- the folds
  have hvf : ∀ j < (osFoldsValsW Ht xs (cfg.lv lvl).folds cv p w.quad (σ (.n s.cb)) s.co).length,
      σ (.n (s.k + j)) = (osFoldsValsW Ht xs (cfg.lv lvl).folds cv p w.quad (σ (.n s.cb)) s.co).getD j 0 := by
    rw [hcb]
    intro j hj
    have hj' : j < Vf.length := hj
    rw [hv j (by simp only [List.length_append]; omega), List.append_assoc, oq_getD_app_lt hj']
  have hrunF : RunsW Ht (foldRounds (cfg.lv lvl).folds w []) ⟨cv, xs.drop p, osp, roots⟩ (H.w1, H.chs)
      ⟨H.cv1, xs.drop (p + 2 * (cfg.lv lvl).folds), osp, roots⟩ := by
    rw [hf]; have := hok.folds; rw [osHP1, hf] at this; exact this
  obtain ⟨hF, hatF, hsp, hqF, htF, -, -, -, hcoF, hkF⟩ := osFolds_completeC (CM := CM) (σ := σ) (rd := rd) (fch := osFch)
    (kret := kret) hcf (cfg.lv lvl).folds (cfg.lv lvl).foldsOff s cv p w [] osp roots (H.w1, H.chs) _ hat
    (by omega) hq hrunF (by rw [hf]; exact hans.folds) hvf (fun j hj => by
      rw [hok.chs.1, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
        Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]
      exact hfch j hj)
  simp only at hatF hqF htF hcoF hkF
  rw [hcb, ← hVf] at hkF
  rw [ite_neg' (by omega)] at hcoF htF
  set sF := (osLvF cfg lvl s).2 with hsF
  have hsF' : (osFolds osFch (cfg.lv lvl).foldsOff (cfg.lv lvl).folds s).2 = sF := rfl
  rw [hsF'] at hatF hqF htF hcoF hkF
  have hcbF : σ (.n sF.cb) = cur * gen ^ osHP1 cfg lvl p := by
    rw [os_cb_of_at hatF (by omega), hcoF, Nat.sub_zero, osHP1]
  have hlen := hok.len
  have hP2 : osHP2 cfg lvl p + 3 ≤ xs.length := hlen
  have hvm : ∀ j < Vm.length, σ (.n (sF.k + j)) = Vm.getD j 0 := fun j hj => by
    rw [hkF, Nat.add_assoc, hv _ (by simp only [List.length_append]; omega), List.append_assoc, os_skip,
      oq_getD_app_lt hj]
  have hg0 : (cfg.lv lvl).grindBits ≠ 0 := by rw [hgr]; decide
  have hnonce : LoadHolds rd cur (osHP2 cfg lvl p) (osHNonce cfg lvl xs p) := hxs _ (by omega)
  have hsplit : (osLvF cfg lvl s).1 ++ (osLvM cfg lvl s).1 ++ (osLvG cfg lvl s).1 =
      (osLvF cfg lvl s).1 ++ ((osLvM cfg lvl s).1 ++ (osLvG cfg lvl s).1) := by rw [List.append_assoc]
  by_cases hl : lvl = cfg.yrLevel
  · have hVm' : Vm = osFinalValsW Ht H.cv1 (osHMs cfg lvl xs p) (σ (.n sF.cb)) sF.co cfg.yrLen := by
      rw [hVm, ite_pos' hl, hcbF, hcoF]
    rw [hVm'] at hvm
    have hM := osFinal_completeC (CM := CM) (rd := rd) (name := cfg.finalMsg) (n := cfg.yrLen) (fmsg := osFmsg) (kret := kret)
      (ms := osHMs cfg lvl xs p) hatF (by rw [hcoF]; omega)
      (by have := hcm hl; simp only [osHCv2W, osHP2, ite_pos' hl] at this; exact this) hvm
    have eM : osLvM cfg lvl s = osFinal cfg.finalMsg osFmsg sF := by rw [osLvM, ite_pos' hl]
    rw [← eM, ← hVm'] at hM
    obtain ⟨hMh, hatM, hcoM, -, hkM⟩ := hM
    have eP : H.cv1 = H.cv1 := rfl
    have hatM' : OsAt σ (osLvM cfg lvl s).2 (osHCv2W Ht cfg lvl xs p H.cv1) cur (osHP2 cfg lvl p) := by
      rw [osHCv2W, ite_pos' hl, osHP2, ite_pos' hl, osHP1]; exact hatM
    have hvg : ∀ j < 16, σ (.n ((osLvM cfg lvl s).2.k + j)) =
        (osGrindValsW Ht (cfg.lv lvl).grindBits (osHNonce cfg lvl xs p) (osHCv2W Ht cfg lvl xs p H.cv1)).getD j 0 :=
      fun j hj => by
        rw [hkM, hkF, show s.k + Vf.length + Vm.length + j = s.k + ((Vf ++ Vm).length + j) by simp; ring,
          hv _ (by simp only [List.length_append]; omega), os_skip]
    obtain ⟨hG, hatG, hcoG, -, hkG⟩ := osGrind_completeC (CM := CM) (kret := kret) hg0 hatM' hnonce hcg hans.nonce hvg
    refine ⟨?_, hatG, ?_, ?_, ?_, ?_⟩
    · rw [hsplit, holdsListB_append]
      refine (holdsListB_noRet _ (osFolds_noRet _ _ _ _) _ _).mpr ⟨hF, ?_⟩
      rw [holdsListB_append]
      refine (holdsListB_noRet _ (by rw [eM]; exact osFinal_noRet _ _ _) _ _).mpr ⟨hMh, hG⟩
    · show (osGrind (cfg.lv lvl).grindBits (osLvM cfg lvl s).2).2.co = _
      rw [hcoG, hcoM, ite_pos' hl]
    · have kG : (osLvG cfg lvl s).2.c = sF.c ∧ (osLvG cfg lvl s).2.b = sF.b ∧ (osLvG cfg lvl s).2.a = sF.a := by
        rw [osLvG, eM]; exact ⟨rfl, rfl, rfl⟩
      rw [hqF, kG.1, kG.2.1, kG.2.2]
    · have kG : (osLvG cfg lvl s).2.t = sF.t := by rw [osLvG, eM]; rfl
      rw [htF, kG]
    · show (osGrind (cfg.lv lvl).grindBits (osLvM cfg lvl s).2).2.k = _
      rw [hkG, hkM, hkF]; simp only [List.length_append, hlg]; ring
  · obtain ⟨next, rest', rfl⟩ : ∃ next rest', rest = next :: rest' := by
      cases rest with
      | nil => exact absurd (hlast.mp rfl) hl
      | cons a b => exact ⟨a, b, rfl⟩
    have hood1 := (hnext next rfl).1
    have hVm' : Vm = osCommitValsW Ht lvl (cfg.lv lvl).logCols (σ (.n osOodz)) H.cv1 (osHW cfg lvl xs p 0)
        (osHW cfg lvl xs p 1) (osHW cfg lvl xs p 2) (osHW cfg lvl xs p 3) (osHW cfg lvl xs p 4) := by
      rw [hVm, ite_neg' hl, hoz]
    have hlm : Vm.length = 84 := by
      rw [hVm']; simp [osCommitValsW, os_length_fsNextValsW, os_length_oodSampleValsW]
    rw [hlm] at hvm
    rw [hVm'] at hvm
    have hw : ∀ i < 5, LoadHolds rd cur (p + 2 * (cfg.lv lvl).folds + i) (osHW cfg lvl xs p i) := fun i hi => by
      have := hxs (osHP1 cfg lvl p + i) (by simp only [osHP2, ite_neg' hl] at hP2; omega)
      rwa [osHW, osHP1]
    obtain ⟨r0, r1⟩ := hrt2 hl
    obtain ⟨o1, o2, o3⟩ := hood hl
    have hM := osCommit_completeC (CM := CM) (rd := rd) (roots := osRoots) (oodz := osOodz) (ood := osOod) (lvl := lvl)
      (logCols := (cfg.lv lvl).logCols) (kret := kret) hatF (hw 0 (by omega)) (hw 1 (by omega))
      (by have := hw 2 (by omega); rwa [show p + 2 * (cfg.lv lvl).folds + 2 = p + 2 * (cfg.lv lvl).folds + 2 from rfl] at this)
      (hw 3 (by omega)) (hw 4 (by omega)) (hans.r0 hl) (hans.r1 hl) (hans.ry hl) (hans.rc0 hl) (hans.rc2 hl)
      r0 r1 o1 o2 o3 (hca hl).1 (hca hl).2.1
      (by rw [hoz]; exact (hca hl).2.2) hvm
    have eM : osLvM cfg lvl s = osCommit lvl (cfg.lv lvl).logCols 1 osRoots osOodz osOod sF := by
      rw [osLvM, ite_neg' hl, hood1]
    rw [← eM] at hM
    obtain ⟨hMh, hatM, hcoM, -, hkM⟩ := hM
    have hatM' : OsAt σ (osLvM cfg lvl s).2 (osHCv2W Ht cfg lvl xs p H.cv1) cur (osHP2 cfg lvl p) := by
      rw [osHCv2W, ite_neg' hl, osHP2, ite_neg' hl, osHP1, osHCv12W]; exact hatM
    have hvg : ∀ j < 16, σ (.n ((osLvM cfg lvl s).2.k + j)) =
        (osGrindValsW Ht (cfg.lv lvl).grindBits (osHNonce cfg lvl xs p) (osHCv2W Ht cfg lvl xs p H.cv1)).getD j 0 :=
      fun j hj => by
        rw [hkM, hkF, ← hlm, show s.k + Vf.length + Vm.length + j = s.k + ((Vf ++ Vm).length + j) by simp; ring,
          hv _ (by simp only [List.length_append]; omega), os_skip]
    obtain ⟨hG, hatG, hcoG, -, hkG⟩ := osGrind_completeC (CM := CM) (kret := kret) hg0 hatM' hnonce hcg hans.nonce hvg
    refine ⟨?_, hatG, ?_, ?_, ?_, ?_⟩
    · rw [hsplit, holdsListB_append]
      refine (holdsListB_noRet _ (osFolds_noRet _ _ _ _) _ _).mpr ⟨hF, ?_⟩
      rw [holdsListB_append]
      refine (holdsListB_noRet _ (by rw [eM]; exact osCommit_noRet _ _ _ _ _ _) _ _).mpr ⟨hMh, hG⟩
    · show (osGrind (cfg.lv lvl).grindBits (osLvM cfg lvl s).2).2.co = _
      rw [hcoG, hcoM, hcoF, ite_neg' hl]
    · have kG : (osLvG cfg lvl s).2.c = sF.c ∧ (osLvG cfg lvl s).2.b = sF.b ∧ (osLvG cfg lvl s).2.a = sF.a := by
        rw [osLvG, eM]; exact ⟨rfl, rfl, rfl⟩
      rw [hqF, kG.1, kG.2.1, kG.2.2]
    · have kG : (osLvG cfg lvl s).2.t = sF.t := by rw [osLvG, eM]; rfl
      rw [htF, kG]
    · show (osGrind (cfg.lv lvl).grindBits (osLvM cfg lvl s).2).2.k = _
      rw [hkG, hkM, hkF]; simp only [List.length_append, hlg, hlm]; ring


/-- The values of the level's second part from its first. -/
def osLvValsBW (Ht : Bytes → Digest) (cfg : OsCfg) (lvl : ℕ) (xs : List E) (p : ℕ) (H : OsLvH) (rt : Digest) (P : OsPtrs)
    (sqzv rewv : E) : List E :=
  let lv := cfg.lv lvl
  let lam := osHLamW Ht cfg lvl xs p H.cv1
  let enf := osHEnfW Ht cfg lvl xs p H
  let c0 := osHC cfg lvl xs p 0
  let c2 := osHC cfg lvl xs p 1
  let q0 := H.w1.quad.getD 0 0
  let q1 := H.w1.quad.getD 1 0
  let q2 := H.w1.quad.getD 2 0
  let t := H.w1.target
  let y := osHW cfg lvl xs p 2
  let c0o := osHW cfg lvl xs p 3
  let c2o := osHW cfg lvl xs p 4
  osSqueezesValsW Ht cfg.maxSq lv.squeezes sqzv (osHCv3W Ht cfg lvl xs p H.cv1) ++
    (osLamPowsVals lam lv.queries).take lv.queries ++
    (osQueriesSegsW Ht cfg lv lvl rewv P.fch P.caps P.flags P.qw P.qbp rt enf c0 c2
      (sqCvW Ht (osHCv4W Ht cfg lvl xs p H.cv1))).flatten ++
    (if lvl = cfg.yrLevel then osGlueVals lam enf c0 (enf + c2) c2 q0 q1 q2 t
    else osOodGlueVals y c0o c2o lam lam q0 q1 q2 t ++
      osGlueVals (lam * lam) enf c0 (enf + c2) c2 (q0 + lam * c0o) (q1 + lam * (y + c2o)) (q2 + lam * c2o)
        (t + lam * y))


/-- **A level's second part** at its honest values (G:1144-1213). -/
theorem osLevelB_completeC {cfg : OsCfg} {μ lvl : ℕ} {L : Whir.Level} {rest : List Whir.Level}
    (hspec : LvSpec cfg μ lvl L rest) {xs : List E} {p : ℕ} {H : OsLvH} {rt : Digest} {P : OsPtrs}
    {sqzv rewv cur : E} {sg : OsSt} (hP : OsPtrsAt σ P)
    (hat : OsAt σ sg (osHCv3W Ht cfg lvl xs p H.cv1) cur (osHP2 cfg lvl p + 1))
    (hqd : H.w1.quad = [σ (.n sg.c), σ (.n sg.b), σ (.n sg.a)]) (htg : H.w1.target = σ (.n sg.t))
    (hc0 : LoadHolds rd cur (osHP2 cfg lvl p + 1) (osHC cfg lvl xs p 0))
    (hc2 : LoadHolds rd cur (osHP2 cfg lvl p + 1 + 1) (osHC cfg lvl xs p 1))
    (alam : sqCvM CM.hm (osHCv4W Ht cfg lvl xs p H.cv1) = some (sqCvW Ht (osHCv4W Ht cfg lvl xs p H.cv1)))
    (ac0 : obsCvM CM.hm (sqCvW Ht (osHCv4W Ht cfg lvl xs p H.cv1)) (osHC cfg lvl xs p 0) =
      some (obsCvW Ht (sqCvW Ht (osHCv4W Ht cfg lvl xs p H.cv1)) (osHC cfg lvl xs p 0)))
    (ac2 : obsCvM CM.hm (obsCvW Ht (sqCvW Ht (osHCv4W Ht cfg lvl xs p H.cv1)) (osHC cfg lvl xs p 0))
      (osHC cfg lvl xs p 1) = some (osHCvEndW Ht cfg lvl xs p H.cv1))
    (l0 : LoadHolds rd sqzv 0 (digestScalars (osHCv3W Ht cfg lvl xs p H.cv1)).1)
    (l1 : LoadHolds rd sqzv 1 (digestScalars (osHCv3W Ht cfg lvl xs p H.cv1)).2)
    (l2 : LoadHolds rd sqzv (2 * (cfg.lv lvl).squeezes) (digestScalars (osHCv4W Ht cfg lvl xs p H.cv1)).1)
    (l3 : LoadHolds rd sqzv (2 * (cfg.lv lvl).squeezes + 1) (digestScalars (osHCv4W Ht cfg lvl xs p H.cv1)).2)
    (hqw : ∀ i < (cfg.lv lvl).queries,
      LoadHolds rd P.qw (lvl * cfg.maxQ + i) (osHLamW Ht cfg lvl xs p H.cv1 ^ i))
    (sr0 : LoadHolds rd P.roots (2 * lvl) (digestScalars rt).1)
    (sr1 : LoadHolds rd P.roots (2 * lvl + 1) (digestScalars rt).2)
    (hood : lvl ≠ cfg.yrLevel → LoadHolds rd P.ood ((lvl + 1) * 4) (osHLamW Ht cfg lvl xs p H.cv1) ∧
      LoadHolds rd P.ood ((lvl + 1) * 4 + 1) (osHW cfg lvl xs p 2) ∧
      LoadHolds rd P.ood ((lvl + 1) * 4 + 2) (osHW cfg lvl xs p 3) ∧
      LoadHolds rd P.ood ((lvl + 1) * 4 + 3) (osHW cfg lvl xs p 4))
    (hbeta : LoadHolds rd P.betas lvl (if lvl = cfg.yrLevel then osHLamW Ht cfg lvl xs p H.cv1
      else osHLamW Ht cfg lvl xs p H.cv1 * osHLamW Ht cfg lvl xs p H.cv1))
    {kret : List E → Prop} {Csq : CallRel}
    (hcsq : 1 + osGw (cfg.lv lvl).squeezes ≠ 0 →
      Csq (cfg.lv lvl).sqLoop [1, osGw (cfg.lv lvl).squeezes, sqzv, P.qpos, P.qbp] [])
    (hcrw : C (cfg.lv lvl).rowWeights [P.fch * gen ^ (cfg.lv lvl).foldsOff, rewv] [])
    (hccap : C (cfg.lv lvl).verifyCap [P.caps * gen ^ (4 * (cfg.lv lvl).capOff), P.flags * gen ^ (cfg.lv lvl).capOff]
      [(digestScalars rt).1, (digestScalars rt).2])
    (hcq : C (cfg.lv lvl).queriesFn [P.caps * gen ^ (4 * (cfg.lv lvl).capOff), P.flags * gen ^ (cfg.lv lvl).capOff,
      P.qw * gen ^ (lvl * cfg.maxQ), P.qbp * gen ^ (cfg.lv lvl).posOff, rewv, osGw (cfg.lv lvl).queries]
      [osHEnfW Ht cfg lvl xs p H])
    (hv : ∀ j < (osLvValsBW Ht cfg lvl xs p H rt P sqzv rewv).length,
      σ (.n (sg.k + j)) = (osLvValsBW Ht cfg lvl xs p H rt P sqzv rewv).getD j 0) :
    (Stmt.HoldsListB CM.sem Csq rd σ (osLvSq cfg lvl sg).1 True kret ∧ Stmt.HoldsListB CM.sem C rd σ (osLvRestB cfg lvl sg) True kret ∧
      OsLvSig σ cfg lvl sg sqzv rewv) ∧
      OsAt σ (osLvGl cfg lvl sg).2 (osHCvEndW Ht cfg lvl xs p H.cv1) cur (osHPEnd cfg lvl p) ∧
      (osLvGl cfg lvl sg).2.co = sg.co + 2 ∧
      (osHWEndW Ht cfg lvl xs p H).quad = [σ (.n (osLvGl cfg lvl sg).2.c), σ (.n (osLvGl cfg lvl sg).2.b),
        σ (.n (osLvGl cfg lvl sg).2.a)] ∧
      (osHWEndW Ht cfg lvl xs p H).target = σ (.n (osLvGl cfg lvl sg).2.t) ∧
      (osLvGl cfg lvl sg).2.k = sg.k + (osLvValsBW Ht cfg lvl xs p H rt P sqzv rewv).length := by
  obtain ⟨hf, hf0, hqq, hml0, hml1, hlc, hdep, hgr, hper, hs1, hs2, hs3, hs4, hdig, hcd1, hcd2, hb1,
    hb2, hb4, hb5, hnq, hb6, hlast, hyr, hnext⟩ := hspec
  set lv := cfg.lv lvl
  set lam := osHLamW Ht cfg lvl xs p H.cv1 with hlamd
  set enf := osHEnfW Ht cfg lvl xs p H
  set c0 := osHC cfg lvl xs p 0
  set c2 := osHC cfg lvl xs p 1
  set S1 := osSqueezesValsW Ht cfg.maxSq lv.squeezes sqzv (osHCv3W Ht cfg lvl xs p H.cv1) with hS1
  set S2 := (osLamPowsVals lam lv.queries).take lv.queries with hS2
  set S3 := (osQueriesSegsW Ht cfg lv lvl rewv P.fch P.caps P.flags P.qw P.qbp rt enf c0 c2
      (sqCvW Ht (osHCv4W Ht cfg lvl xs p H.cv1))).flatten with hS3
  set S4 := (if lvl = cfg.yrLevel then osGlueVals lam enf c0 (enf + c2) c2 (H.w1.quad.getD 0 0)
      (H.w1.quad.getD 1 0) (H.w1.quad.getD 2 0) H.w1.target
    else osOodGlueVals (osHW cfg lvl xs p 2) (osHW cfg lvl xs p 3) (osHW cfg lvl xs p 4) lam lam
      (H.w1.quad.getD 0 0) (H.w1.quad.getD 1 0) (H.w1.quad.getD 2 0) H.w1.target ++
      osGlueVals (lam * lam) enf c0 (enf + c2) c2 (H.w1.quad.getD 0 0 + lam * osHW cfg lvl xs p 3)
        (H.w1.quad.getD 1 0 + lam * (osHW cfg lvl xs p 2 + osHW cfg lvl xs p 4))
        (H.w1.quad.getD 2 0 + lam * osHW cfg lvl xs p 4) (H.w1.target + lam * osHW cfg lvl xs p 2)) with hS4
  have hVB : osLvValsBW Ht cfg lvl xs p H rt P sqzv rewv = S1 ++ S2 ++ S3 ++ S4 := rfl
  rw [hVB] at hv ⊢
  have hl1 : S1.length = 25 := by simp [hS1, osSqueezesValsW]
  have hl2 : S2.length = lv.queries := by
    simp only [hS2, List.length_take, osLamPowsVals, List.length_cons, List.length_map, List.length_range]; omega
  -- the squeezes
  obtain ⟨hS, hatS, hlamS, hcoS, hcbS, hkS⟩ := osSqueezes_completeC (CM := CM) (C := Csq) (rd := rd) (σ := σ) (kret := kret)
    (maxSq := cfg.maxSq) (qpos := osQpos) (qbp := osQbp) (loop := lv.sqLoop) (by omega) hat l0 l1 l2 l3
    (by rw [hP.qpos, hP.qbp]; exact hcsq) alam (fun j hj => by rw [hv j (by simp only [List.length_append]; omega), List.append_assoc, List.append_assoc,
      oq_getD_app_lt (by omega)])
  set sq := (osLvSq cfg lvl sg).2 with hsq
  have hsq' : (osSqueezes cfg.maxSq lv.squeezes osQpos osQbp lv.sqLoop sg).2 = sq := rfl
  rw [hsq'] at hatS hlamS hcoS hcbS hkS
  replace hlamS : σ (.n (sq.k - 1)) = lam := hlamS
  obtain ⟨hv123, g4⟩ := os_look_app hv
  obtain ⟨hv12, g3⟩ := os_look_app hv123
  obtain ⟨-, g2⟩ := os_look_app hv12
  rw [hl1] at g2
  simp only [List.length_append, hl1, hl2] at g3 g4
  -- the query weights
  have hL := osLamPows_completeB (S := CM.sem) (C := C) (rd := rd) (σ := σ) (lam := sq.k - 1) (qw := osQw) (base := lvl * cfg.maxQ)
    (k := sq.k) (kret := kret) lv.queries (fun i hi => by rw [hP.qw, hlamS]; exact hqw i hi)
    (fun j hj => by
      rw [hlamS, hkS, g2 j (by rw [hl2]; exact hj), hS2, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj,
        ← List.getD_eq_getElem?_getD])
  -- the queries
  set sq' : OsSt := { sq with k := sq.k + lv.queries }
  have hatq : OsAt σ sq' (sqCvW Ht (osHCv4W Ht cfg lvl xs p H.cv1)) cur (osHP2 cfg lvl p + 1) := ⟨hatS.fs, hatS.cursor⟩
  obtain ⟨hQ, hatQ, hcoQ, hcbQ, eq1, eq2, eq3, eq4, eq5, hkQ⟩ := osQueries_completeC (CM := CM) (rd := rd) (σ := σ)
    (cfg := cfg) (lv := lv) (lvl := lvl) (kret := kret) hb1 hb2 (by omega) hb4 hb5 hatq hc0 hc2 ac0 ac2
    (by rw [hP.roots]; exact sr0) (by rw [hP.roots]; exact sr1) (rewv := rewv) (qsum := enf)
    (by rw [hP.fch]; exact hcrw) (by rw [hP.caps, hP.flags]; exact hccap)
    (by rw [hP.caps, hP.flags, hP.qw, hP.qbp]; exact hcq) (fun j hj => by
      rw [hP.fch, hP.caps, hP.flags, hP.qw, hP.qbp] at hj ⊢
      rw [show sq'.k + j = sg.k + (25 + lv.queries) + j by simp only [sq', hkS]; ring]
      exact g3 j hj)
  set q := osQueries cfg lv lvl sq' with hqdef
  have eQ : osLvQ cfg lvl sg = q := rfl
  have kq : q.2.1.c = sg.c ∧ q.2.1.b = sg.b ∧ q.2.1.a = sg.a ∧ q.2.1.t = sg.t := ⟨rfl, rfl, rfl, rfl⟩
  rw [hP.fch, hP.caps, hP.flags, hP.qw, hP.qbp] at hkQ
  have hkq : q.2.1.k = sg.k + (25 + lv.queries + S3.length) := by
    rw [hkQ, ← hS3]; simp only [sq', hkS]; ring
  rw [← hkq] at g4
  have hq0 : H.w1.quad.getD 0 0 = σ (.n sg.c) := by rw [hqd]; rfl
  have hq1 : H.w1.quad.getD 1 0 = σ (.n sg.b) := by rw [hqd]; rfl
  have hq2 : H.w1.quad.getD 2 0 = σ (.n sg.a) := by rw [hqd]; rfl
  have hP3 : osHPEnd cfg lvl p = osHP2 cfg lvl p + 1 + 2 := by rw [osHPEnd]
  have hstB : osLvRestB cfg lvl sg = osLvL cfg lvl sg ++ q.1 ++ (osLvO cfg lvl sg).1 ++
      [.atom (.load (.n (osLvO cfg lvl sg).2.2) (.n osBetas) lvl)] ++ (osLvGl cfg lvl sg).1 := rfl
  have hsig : OsLvSig σ cfg lvl sg sqzv rewv := by
    have v0 := hv 0 (by simp [hl1])
    have v1 := hv 1 (by simp [hl1]; omega)
    have v4 := hv 4 (by simp [hl1]; omega)
    have v5 := hv 5 (by simp [hl1]; omega)
    have v6 := hv 6 (by simp [hl1]; omega)
    have hS3l : 2 ≤ S3.length := by simp [hS3, osQueriesSegsW]
    have w0 := g3 0 (by omega)
    have w1 := g3 1 (by omega)
    simp only [List.append_assoc] at v0 v1 v4 v5 v6
    rw [oq_getD_app_lt (by omega)] at v0 v1 v4 v5 v6
    refine ⟨by simpa [hS1, osSqueezesValsW] using v0, by simpa [hS1, osSqueezesValsW] using v1,
      by rw [v4]; simp [hS1, osSqueezesValsW]; rfl, by rw [v5]; simp [hS1, osSqueezesValsW],
      by rw [v6]; simp [hS1, osSqueezesValsW]; rfl, ?_, ?_⟩
    · rw [show (osLvSq cfg lvl sg).2.k + lv.queries = sg.k + (25 + lv.queries) + 0 by rw [← hsq, hkS]; ring, w0]
      simp [hS3, osQueriesSegsW]
    · rw [show (osLvSq cfg lvl sg).2.k + lv.queries + 1 = sg.k + (25 + lv.queries) + 1 by rw [← hsq, hkS]; ring, w1]
      simp [hS3, osQueriesSegsW]
  by_cases hl : lvl = cfg.yrLevel
  · have eO : osLvO cfg lvl sg = ([], q.2.1, sq.k - 1) := by rw [osLvO, ite_pos' hl]; rfl
    have hS4' : S4 = osGlueVals lam enf c0 (enf + c2) c2 (H.w1.quad.getD 0 0) (H.w1.quad.getD 1 0)
        (H.w1.quad.getD 2 0) H.w1.target := by rw [hS4, ite_pos' hl]
    have hl4 : S4.length = 8 := by rw [hS4']; rfl
    rw [hl4, hS4'] at g4
    have eGl : osLvGl cfg lvl sg = osGlue (sq.k - 1) q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2 q.2.1 := by
      rw [osLvGl, eO, eQ]
    obtain ⟨hG, gc, gb, ga, gt, gk, -, -, -, gco⟩ := osGlue_complete (C := C) (rd := rd) (σ := σ) (kret := kret)
      (sc := sq.k - 1) (v := q.2.2.1) (c0 := q.2.2.2.1) (c1 := q.2.2.2.2.1) (c2 := q.2.2.2.2.2) (s := q.2.1)
      (fun j hj => by
        rw [g4 j hj, hlamS, eq1, eq2, eq3, eq4, kq.1, kq.2.1, kq.2.2.1, kq.2.2.2, hq0, hq1, hq2, htg])
    rw [← eGl] at hG gc gb ga gt gk gco
    refine ⟨⟨hS, ?_, hsig⟩, ⟨by rw [eGl]; exact hatQ.fs, by rw [eGl, hP3]; exact hatQ.cursor⟩, ?_, ?_, ?_, ?_⟩
    · rw [hstB, eO]
      simp only [holdsListB_append]
      refine (holdsListB_noRet _ (osLamPows_noRet _ _ _ _ _) _ _).mpr ⟨hL,
        (holdsListB_noRet _ (osQueries_noRet _ _ _ _) _ _).mpr ⟨hQ, (holdsListB_noRet _ rfl _ _).mpr ⟨trivial,
        (holdsListB_noRet _ rfl _ _).mpr ⟨?_, hG⟩⟩⟩⟩
      simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, and_true]
      rw [hlamS, hP.betas]
      rw [ite_pos' hl] at hbeta
      exact hbeta
    · rw [gco, hcoQ]; show sq.co + 2 = _; rw [hcoS]
    · simp only [osHWEndW, osHPendingW, ite_pos' hl, List.nil_append, os_glue_one]
      rw [gc, gb, ga]
      show List.zipWith _ H.w1.quad _ = [σ (.n q.2.1.c) + σ (.n (sq.k - 1)) * σ (.n q.2.2.2.1),
        σ (.n q.2.1.b) + σ (.n (sq.k - 1)) * σ (.n q.2.2.2.2.1), σ (.n q.2.1.a) + σ (.n (sq.k - 1)) * σ (.n q.2.2.2.2.2)]
      rw [hqd, hlamS, eq2, eq3, eq4, kq.1, kq.2.1, kq.2.2.1]
      simp only [List.zipWith_cons_cons, List.zipWith_nil_right, one_mul]; rfl
    · simp only [osHWEndW, osHPendingW, ite_pos' hl, List.nil_append, os_glue_one]
      rw [gt]
      show H.w1.target + 1 * _ * _ = σ (.n q.2.1.t) + σ (.n (sq.k - 1)) * σ (.n q.2.2.1)
      rw [htg, hlamS, eq1, kq.2.2.2, one_mul]
    · rw [gk, hkq]; simp only [List.length_append, hl1, hl2, hl4]; ring
  · obtain ⟨next, rest', rfl⟩ : ∃ next rest', rest = next :: rest' := by
      cases rest with
      | nil => exact absurd (hlast.mp rfl) hl
      | cons a b => exact ⟨a, b, rfl⟩
    have hood1 := (hnext next rfl).1
    obtain ⟨o0, o1, o2, o3⟩ := hood hl
    set O := osOodGlue ((lvl + 1) * 4) (sq.k - 1) (sq.k - 1) q.2.1 with hO
    have eO : osLvO cfg lvl sg = (O.1, O.2, O.2.k - 1) := by
      rw [osLvO, ite_neg' hl, hood1, osOodGlues_one]; rfl
    have hS4' : S4 = osOodGlueVals (osHW cfg lvl xs p 2) (osHW cfg lvl xs p 3) (osHW cfg lvl xs p 4) lam lam
        (H.w1.quad.getD 0 0) (H.w1.quad.getD 1 0) (H.w1.quad.getD 2 0) H.w1.target ++
        osGlueVals (lam * lam) enf c0 (enf + c2) c2 (H.w1.quad.getD 0 0 + lam * osHW cfg lvl xs p 3)
          (H.w1.quad.getD 1 0 + lam * (osHW cfg lvl xs p 2 + osHW cfg lvl xs p 4))
          (H.w1.quad.getD 2 0 + lam * osHW cfg lvl xs p 4) (H.w1.target + lam * osHW cfg lvl xs p 2) := by
      rw [hS4, ite_neg' hl]
    rw [hS4'] at g4
    obtain ⟨g4a, g4b⟩ := os_look_app g4
    have hla : (osOodGlueVals (osHW cfg lvl xs p 2) (osHW cfg lvl xs p 3) (osHW cfg lvl xs p 4) lam lam
        (H.w1.quad.getD 0 0) (H.w1.quad.getD 1 0) (H.w1.quad.getD 2 0) H.w1.target).length = 13 := rfl
    rw [hla] at g4a g4b
    obtain ⟨hOh, oc, ob, oa, ot, ok1, ok, -, -, -, oco⟩ := osOodGlue_complete (C := C) (rd := rd) (σ := σ)
      (so := (lvl + 1) * 4) (sc := sq.k - 1) (lam := sq.k - 1) (s := q.2.1) (kret := kret)
      (by rw [hP.ood]; exact o1) (by rw [hP.ood]; exact o2) (by rw [hP.ood]; exact o3)
      (by rw [hP.ood, hlamS]; exact o0)
      (fun j hj => by rw [g4a j hj, hlamS, kq.1, kq.2.1, kq.2.2.1, kq.2.2.2, hq0, hq1, hq2, htg])
    rw [← hO] at hOh oc ob oa ot ok1 ok oco
    have eGl : osLvGl cfg lvl sg = osGlue (O.2.k - 1) q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2 O.2 := by
      rw [osLvGl, eO, eQ]
    rw [hlamS, kq.1] at oc
    rw [hlamS, kq.2.1] at ob
    rw [hlamS, kq.2.2.1] at oa
    rw [hlamS, kq.2.2.2] at ot
    rw [hlamS] at ok1
    obtain ⟨hG, gc, gb, ga, gt, gk, -, -, -, gco⟩ := osGlue_complete (C := C) (rd := rd) (σ := σ) (kret := kret)
      (sc := O.2.k - 1) (v := q.2.2.1) (c0 := q.2.2.2.1) (c1 := q.2.2.2.2.1) (c2 := q.2.2.2.2.2) (s := O.2)
      (fun j hj => by
        rw [show O.2.k + j = q.2.1.k + 13 + j by rw [ok]]
        rw [g4b j hj, ok1, eq1, eq2, eq3, eq4, oc, ob, oa, ot, hq0, hq1, hq2, htg])
    rw [← eGl] at hG gc gb ga gt gk gco
    refine ⟨⟨hS, ?_, hsig⟩, ⟨by rw [eGl]; exact hatQ.fs, by rw [eGl, hP3]; exact hatQ.cursor⟩, ?_, ?_, ?_, ?_⟩
    · rw [hstB, eO]
      simp only [holdsListB_append]
      refine (holdsListB_noRet _ (osLamPows_noRet _ _ _ _ _) _ _).mpr ⟨hL,
        (holdsListB_noRet _ (osQueries_noRet _ _ _ _) _ _).mpr ⟨hQ,
        (holdsListB_noRet _ (by simp [hO, osOodGlue, Stmt.noRetList, Stmt.noRet]) _ _).mpr ⟨hOh,
        (holdsListB_noRet _ rfl _ _).mpr ⟨?_, hG⟩⟩⟩⟩
      simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, and_true]
      rw [ok1, hP.betas]
      rw [ite_neg' hl] at hbeta
      exact hbeta
    · rw [gco, oco, hcoQ]; show sq.co + 2 = _; rw [hcoS]
    · simp only [osHWEndW, osHPendingW, ite_neg' hl, List.singleton_append, os_glue_two]
      rw [gc, gb, ga, ok1, eq2, eq3, eq4, oc, ob, oa, hqd]
      simp only [List.zipWith_cons_cons, List.zipWith_nil_right, one_mul]; rfl
    · simp only [osHWEndW, osHPendingW, ite_neg' hl, List.singleton_append, os_glue_two]
      rw [gt, ok1, eq1, ot, htg, one_mul]
    · have hl4' : S4.length = 21 := by rw [hS4']; rfl
      rw [gk, ok, hkq]; simp only [List.length_append, hl1, hl2, hl4']; ring




/-- What level `lvl` reads of the memory: the stream at `cur`, its challenges stored, its next root
and out-of-domain claim stored, its squeezes' states, its query weights, its root, its scalar. -/
structure OsLvMemW (Ht : Bytes → Digest) (rd : Reader) (cfg : OsCfg) (lvl : ℕ) (xs : List E) (p : ℕ) (H : OsLvH) (rt : Digest)
    (P : OsPtrs) (sqzv cur : E) : Prop where
  reads : ∀ j < xs.length, LoadHolds rd cur j (xs.getD j 0)
  fch : ∀ j < (cfg.lv lvl).folds, LoadHolds rd P.fch ((cfg.lv lvl).foldsOff + j) (H.chs.getD j 0)
  rt2 : lvl ≠ cfg.yrLevel → LoadHolds rd P.roots (2 * lvl + 2) (osHW cfg lvl xs p 0) ∧
    LoadHolds rd P.roots (2 * lvl + 3) (osHW cfg lvl xs p 1)
  ood : lvl ≠ cfg.yrLevel → LoadHolds rd P.ood ((lvl + 1) * 4) (osHLamW Ht cfg lvl xs p H.cv1) ∧
    LoadHolds rd P.ood ((lvl + 1) * 4 + 1) (osHW cfg lvl xs p 2) ∧
    LoadHolds rd P.ood ((lvl + 1) * 4 + 2) (osHW cfg lvl xs p 3) ∧
    LoadHolds rd P.ood ((lvl + 1) * 4 + 3) (osHW cfg lvl xs p 4)
  sq0 : LoadHolds rd sqzv 0 (digestScalars (osHCv3W Ht cfg lvl xs p H.cv1)).1
  sq1 : LoadHolds rd sqzv 1 (digestScalars (osHCv3W Ht cfg lvl xs p H.cv1)).2
  sq2 : LoadHolds rd sqzv (2 * (cfg.lv lvl).squeezes) (digestScalars (osHCv4W Ht cfg lvl xs p H.cv1)).1
  sq3 : LoadHolds rd sqzv (2 * (cfg.lv lvl).squeezes + 1) (digestScalars (osHCv4W Ht cfg lvl xs p H.cv1)).2
  qw : ∀ i < (cfg.lv lvl).queries, LoadHolds rd P.qw (lvl * cfg.maxQ + i) (osHLamW Ht cfg lvl xs p H.cv1 ^ i)
  rt0 : LoadHolds rd P.roots (2 * lvl) (digestScalars rt).1
  rt1 : LoadHolds rd P.roots (2 * lvl + 1) (digestScalars rt).2
  beta : LoadHolds rd P.betas lvl (if lvl = cfg.yrLevel then osHLamW Ht cfg lvl xs p H.cv1
    else osHLamW Ht cfg lvl xs p H.cv1 * osHLamW Ht cfg lvl xs p H.cv1)

/-- What level `lvl`'s calls are taken to satisfy, at their honest words: the first part's under
`CA`, the second's under `CB`. -/
structure OsLvCallHC (CM : CompModel) (Ht : Bytes → Digest) (CA CB Csq : CallRel) (cfg : OsCfg) (lvl : ℕ) (xs : List E) (p : ℕ) (H : OsLvH) (rt : Digest)
    (P : OsPtrs) (sqzv rewv cur : E) : Prop where
  fold : ∀ (cv' : Digest) (p' : ℕ) (q' : List E), q'.length = 3 → p' + 2 ≤ xs.length →
      RunsToM CM.hm (foldStep q') cv' [xs.getD p' 0, xs.getD (p' + 1) 0]
        (challengeOf (sqCvW Ht cv'), polyEval q' (challengeOf (sqCvW Ht cv')),
          [xs.getD p' 0, polyEval q' (challengeOf (sqCvW Ht cv')) + xs.getD (p' + 1) 0, xs.getD (p' + 1) 0])
        (obsAllW Ht (sqCvW Ht cv') [xs.getD p' 0, xs.getD (p' + 1) 0]) →
    CA "opening_fold" [(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ p', q'.getD 0 0, q'.getD 1 0,
      q'.getD 2 0] (osFoldRetsW Ht xs cv' p' q' (cur * gen ^ p'))
  final : lvl = cfg.yrLevel → CA cfg.finalMsg [(digestScalars H.cv1).1, (digestScalars H.cv1).2,
    cur * gen ^ osHP1 cfg lvl p, P.fmsg]
    [(digestScalars (osHCv2W Ht cfg lvl xs p H.cv1)).1, (digestScalars (osHCv2W Ht cfg lvl xs p H.cv1)).2,
      cur * gen ^ osHP2 cfg lvl p]
  commit : lvl ≠ cfg.yrLevel → CA "assert_canonical" [osHW cfg lvl xs p 0] [0] ∧
    CA "assert_canonical" [osHW cfg lvl xs p 1] [0] ∧
    CA "opening_ood_point" [(digestScalars (osHCv12W Ht cfg lvl xs p H.cv1)).1,
      (digestScalars (osHCv12W Ht cfg lvl xs p H.cv1)).2, P.oodz * osGw ((lvl + 1 + 0) * 22), osGw (cfg.lv lvl).logCols]
      [(digestScalars (sqAllW Ht (cfg.lv lvl).logCols (osHCv12W Ht cfg lvl xs p H.cv1)).2).1,
        (digestScalars (sqAllW Ht (cfg.lv lvl).logCols (osHCv12W Ht cfg lvl xs p H.cv1)).2).2]
  grind : CA "grind_check" [(digestScalars (osHCv2W Ht cfg lvl xs p H.cv1)).1,
    (digestScalars (osHCv2W Ht cfg lvl xs p H.cv1)).2, osHNonce cfg lvl xs p, osGw (cfg.lv lvl).grindBits] []
  sq : 1 + osGw (cfg.lv lvl).squeezes ≠ 0 →
    Csq (cfg.lv lvl).sqLoop [1, osGw (cfg.lv lvl).squeezes, sqzv, P.qpos, P.qbp] []
  rw : CB (cfg.lv lvl).rowWeights [P.fch * gen ^ (cfg.lv lvl).foldsOff, rewv] []
  cap : CB (cfg.lv lvl).verifyCap [P.caps * gen ^ (4 * (cfg.lv lvl).capOff), P.flags * gen ^ (cfg.lv lvl).capOff]
    [(digestScalars rt).1, (digestScalars rt).2]
  q : CB (cfg.lv lvl).queriesFn [P.caps * gen ^ (4 * (cfg.lv lvl).capOff), P.flags * gen ^ (cfg.lv lvl).capOff,
    P.qw * gen ^ (lvl * cfg.maxQ), P.qbp * gen ^ (cfg.lv lvl).posOff, rewv, osGw (cfg.lv lvl).queries]
    [osHEnfW Ht cfg lvl xs p H]

/-- The values of a level from its first. -/
def osLvValsW (Ht : Bytes → Digest) (cfg : OsCfg) (lvl : ℕ) (xs : List E) (cv : Digest) (p : ℕ) (w : WhirState) (H : OsLvH)
    (co : ℕ) (cur : E) (rt : Digest) (P : OsPtrs) (sqzv rewv : E) : List E :=
  osLvValsAW Ht cfg lvl xs cv p w H co cur P.oodz ++ osLvValsBW Ht cfg lvl xs p H rt P sqzv rewv

/-- **One level** at its honest values (G:1096-1213). -/
theorem osLevel_completeC {cfg : OsCfg} {μ lvl : ℕ} {L : Whir.Level} {rest : List Whir.Level}
    (hspec : LvSpec cfg μ lvl L rest) {xs : List E} {cv : Digest} {p : ℕ} {w : WhirState}
    {osp : List Opening} {roots : List (Digest × ℕ × ℕ)} {H : OsLvH}
    (hok : OsLvOkW Ht cfg lvl xs p μ L cv w osp roots H) (hans : OsLvAns CM.hm Ht cfg lvl xs p L cv w osp roots H)
    {s : OsSt} {cur : E} {rt : Digest} {P : OsPtrs}
    {sqzv rewv : E} (hP : OsPtrsAt σ P) (hat : OsAt σ s cv cur p) (hcop : s.co ≤ p) (hco8 : s.co ≤ 8)
    (hq : w.quad = [σ (.n s.c), σ (.n s.b), σ (.n s.a)]) (hm : OsLvMemW Ht rd cfg lvl xs p H rt P sqzv cur)
    {kret : List E → Prop} {CA CB Csq : CallRel} (hc : OsLvCallHC CM Ht CA CB Csq cfg lvl xs p H rt P sqzv rewv cur)
    (hv : ∀ j < (osLvValsW Ht cfg lvl xs cv p w H s.co cur rt P sqzv rewv).length,
      σ (.n (s.k + j)) = (osLvValsW Ht cfg lvl xs cv p w H s.co cur rt P sqzv rewv).getD j 0) :
    (OsCallsOk CA σ ((osLvF cfg lvl s).1 ++ (osLvM cfg lvl s).1 ++ (osLvG cfg lvl s).1) ∧
      OsCallsOk Csq σ (osLvSq cfg lvl (osLvG cfg lvl s).2).1 ∧
      OsCallsOk CB σ (osLvRestB cfg lvl (osLvG cfg lvl s).2) ∧
      OsLvSig σ cfg lvl (osLvG cfg lvl s).2 sqzv rewv) ∧
    Stmt.HoldsListB CM.sem osTC rd σ (osLevel cfg lvl (cfg.lv lvl) s).1 True kret ∧
      OsAt σ (osLevel cfg lvl (cfg.lv lvl) s).2 (osHCvEndW Ht cfg lvl xs p H.cv1) cur (osHPEnd cfg lvl p) ∧
      (osLevel cfg lvl (cfg.lv lvl) s).2.co = (if lvl = cfg.yrLevel then 3 else 8) ∧
      (osHWEndW Ht cfg lvl xs p H).quad = [σ (.n (osLevel cfg lvl (cfg.lv lvl) s).2.c),
        σ (.n (osLevel cfg lvl (cfg.lv lvl) s).2.b), σ (.n (osLevel cfg lvl (cfg.lv lvl) s).2.a)] ∧
      (osHWEndW Ht cfg lvl xs p H).target = σ (.n (osLevel cfg lvl (cfg.lv lvl) s).2.t) ∧
      (osLevel cfg lvl (cfg.lv lvl) s).2.k = s.k + (osLvValsW Ht cfg lvl xs cv p w H s.co cur rt P sqzv rewv).length := by
  obtain ⟨hA, hB⟩ := os_look_app hv
  obtain ⟨hHA, hatA, hcoA, hqA, htA, hkA⟩ := osLevelA_completeC (CM := CM) (C := CA) (rd := rd) (kret := kret) hspec hok hans hat hcop hco8 hq
    hP.oodz hm.reads (fun j hj => by rw [hP.fch]; exact hm.fch j hj)
    (fun h => by rw [hP.roots]; exact hm.rt2 h)
    (fun h => by
      rw [hP.ood]
      obtain ⟨-, o1, o2, o3⟩ := hm.ood h
      exact ⟨by simpa using o1, by simpa using o2, by simpa using o3⟩)
    hc.fold (fun h => by rw [hP.fmsg]; exact hc.final h) hc.commit hc.grind hA
  have hlen := hok.len
  obtain ⟨⟨hHsq, hHB, hsig⟩, hatB, hcoB, hqB, htB, hkB⟩ := osLevelB_completeC (CM := CM) (C := CB) (Csq := Csq) (rd := rd) (kret := kret) (rewv := rewv) hspec hP
    hatA hqA htA (hm.reads _ (by unfold osHPEnd at hlen; omega))
    (hm.reads (osHP2 cfg lvl p + 1 + 1) (by unfold osHPEnd at hlen; omega)) hans.lam hans.c0 hans.c2
    hm.sq0 hm.sq1 hm.sq2 hm.sq3 hm.qw hm.rt0 hm.rt1 (fun h => hm.ood h) hm.beta
    hc.sq hc.rw hc.cap hc.q (fun j hj => by rw [hkA]; exact hB j hj)
  have hstr := osLvStB_straight cfg lvl (osLvG cfg lvl s).2
  rw [osLvStB_eq, os_all_append, Bool.and_eq_true] at hstr
  rw [osLevel_parts]
  refine ⟨⟨os_callsOk_of_holdsListB _ (osLvStA_straight _ _ _) hHA,
    os_callsOk_of_holdsListB _ hstr.1 hHsq, os_callsOk_of_holdsListB _ hstr.2 hHB, hsig⟩, ?_, hatB, ?_, hqB, htB, ?_⟩
  · rw [holdsListB_append, osLvStB_eq, holdsListB_append (osLvSq cfg lvl (osLvG cfg lvl s).2).1]
    refine (holdsListB_noRet _ ?_ _ _).mpr ⟨os_holdsListB_toTC hHA,
      (holdsListB_noRet _ (osSqueezes_noRet _ _ _ _ _ _) _ _).mpr ⟨os_holdsListB_toTC hHsq, os_holdsListB_toTC hHB⟩⟩
    simp only [noRetList_append, osFolds_noRet, osLvF, osLvG, osGrind_noRet, Bool.and_true, Bool.true_and]
    unfold osLvM; split
    · exact osFinal_noRet _ _ _
    · rw [show (cfg.lv lvl).oodNext = 1 from ?_]
      · exact osCommit_noRet _ _ _ _ _ _
      · rename_i hl
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hlast, -, hnext⟩ := hspec
        cases rest with
        | nil => exact absurd (hlast.mp rfl) hl
        | cons a b => exact (hnext a rfl).1
  · show (osLvGl cfg lvl (osLvG cfg lvl s).2).2.co = _
    rw [hcoB, hcoA]; split <;> rfl
  · show (osLvGl cfg lvl (osLvG cfg lvl s).2).2.k = _
    rw [hkB, hkA, osLvValsW, List.length_append]; ring

/-- The values of the levels `lvl ..` from the first. -/
def osLvsValsW (Ht : Bytes → Digest) (cfg : OsCfg) (xs : List E) (cur : E) (P : OsPtrs) (sqz rew : ℕ → E) :
    ℕ → Digest → ℕ → WhirState → List (Digest × ℕ × ℕ) → OsSt → List OsLvH → List E
  | _, _, _, _, _, _, [] => []
  | lvl, cv, p, w, roots, s, H :: Hs =>
    osLvValsW Ht cfg lvl xs cv p w H s.co cur (roots.getD lvl default).1 P (sqz lvl) (rew lvl) ++
      osLvsValsW Ht cfg xs cur P sqz rew (lvl + 1) (osHCvEndW Ht cfg lvl xs p H.cv1) (osHPEnd cfg lvl p)
        (osHWEndW Ht cfg lvl xs p H) (osHRootsEnd cfg lvl roots H) (osLevel cfg lvl (cfg.lv lvl) s).2 Hs

/-- What the levels `lvl ..` read of the memory. -/
def OsLvsMemW (Ht : Bytes → Digest) (rd : Reader) (cfg : OsCfg) (xs : List E) (cur : E) (P : OsPtrs) (sqz : ℕ → E) :
    ℕ → Digest → ℕ → WhirState → List (Digest × ℕ × ℕ) → List OsLvH → Prop
  | _, _, _, _, _, [] => True
  | lvl, _cv, p, _w, roots, H :: Hs =>
    OsLvMemW Ht rd cfg lvl xs p H (roots.getD lvl default).1 P (sqz lvl) cur ∧
      OsLvsMemW Ht rd cfg xs cur P sqz (lvl + 1) (osHCvEndW Ht cfg lvl xs p H.cv1) (osHPEnd cfg lvl p)
        (osHWEndW Ht cfg lvl xs p H) (osHRootsEnd cfg lvl roots H) Hs

/-- The levels' call hypotheses, level `i`'s under `CA i` and `CB i`. -/
def OsLvsCallHC (CM : CompModel) (Ht : Bytes → Digest) (CA CB Csq : ℕ → CallRel) (cfg : OsCfg) (xs : List E) (cur : E) (P : OsPtrs) (sqz rew : ℕ → E) :
    ℕ → ℕ → WhirState → List (Digest × ℕ × ℕ) → List OsLvH → Prop
  | _, _, _, _, [] => True
  | lvl, p, _w, roots, H :: Hs =>
    OsLvCallHC CM Ht (CA lvl) (CB lvl) (Csq lvl) cfg lvl xs p H (roots.getD lvl default).1 P (sqz lvl) (rew lvl) cur ∧
      OsLvsCallHC CM Ht CA CB Csq cfg xs cur P sqz rew (lvl + 1) (osHPEnd cfg lvl p) (osHWEndW Ht cfg lvl xs p H)
        (osHRootsEnd cfg lvl roots H) Hs


/-- **Every level** at its honest values, from the levels' data. -/
theorem osLevels_completeC {cfg : OsCfg} {μ lane : ℕ} {Lall : List Whir.Level}
    (hlen : Lall.length = cfg.levels.length)
    (hspec : ∀ i < Lall.length, LvSpec cfg μ i (Lall.getD i default) (Lall.drop (i + 1)))
    (hyl : cfg.yrLevel = cfg.levels.length - 1) {xs : List E} {e : WhirEnd} {sp' : St} {Q : List (ℕ × List (ℕ × Opening))} {cur : E}
    {P : OsPtrs} {sqz rew : ℕ → E} (hP : OsPtrsAt σ P) {kret : List E → Prop} {CA CB Csq : ℕ → CallRel} :
    ∀ (Hs : List OsLvH) (lvl : ℕ) (cv : Digest) (p : ℕ) (w : WhirState) (osp : List Opening)
      (roots : List (Digest × ℕ × ℕ)) (s : OsSt), lvl + Hs.length = cfg.levels.length →
      OsChainC CM.hm Ht cfg μ lane xs Lall e sp' Q lvl cv p w osp roots Hs → OsAt σ s cv cur p → s.co ≤ p → s.co ≤ 8 →
      w.quad = [σ (.n s.c), σ (.n s.b), σ (.n s.a)] → OsLvsMemW Ht rd cfg xs cur P sqz lvl cv p w roots Hs →
      OsLvsCallHC CM Ht CA CB Csq cfg xs cur P sqz rew lvl p w roots Hs →
      (∀ j < (osLvsValsW Ht cfg xs cur P sqz rew lvl cv p w roots s Hs).length,
        σ (.n (s.k + j)) = (osLvsValsW Ht cfg xs cur P sqz rew lvl cv p w roots s Hs).getD j 0) →
      OsLvsCallsOk CA CB Csq cfg σ sqz rew lvl s Hs.length ∧
      Stmt.HoldsListB CM.sem osTC rd σ (osLevels cfg lvl (cfg.levels.drop lvl) s).1 True kret ∧
        OsAt σ (osLevels cfg lvl (cfg.levels.drop lvl) s).2 (osLvsEndW Ht cfg xs lvl cv p w roots Hs).1 cur
          (osLvsEndW Ht cfg xs lvl cv p w roots Hs).2.1 ∧
        (osLevels cfg lvl (cfg.levels.drop lvl) s).2.co = 3 ∧
        (osLvsEndW Ht cfg xs lvl cv p w roots Hs).2.2.quad = [σ (.n (osLevels cfg lvl (cfg.levels.drop lvl) s).2.c),
          σ (.n (osLevels cfg lvl (cfg.levels.drop lvl) s).2.b), σ (.n (osLevels cfg lvl (cfg.levels.drop lvl) s).2.a)] ∧
        (osLvsEndW Ht cfg xs lvl cv p w roots Hs).2.2.target = σ (.n (osLevels cfg lvl (cfg.levels.drop lvl) s).2.t) ∧
        (osLevels cfg lvl (cfg.levels.drop lvl) s).2.k = s.k + (osLvsValsW Ht cfg xs cur P sqz rew lvl cv p w roots s Hs).length
  | [], _, _, _, _, _, _, _, _, hch, _, _, _, _, _, _, _ => hch.elim
  | H :: Hs, lvl, cv, p, w, osp, roots, s, hl, hch, hat, hcop, hco8, hq, hm, hcH, hv => by
    obtain ⟨hok, hans, -, hlast, hnext⟩ := hch
    obtain ⟨hm1, hm2⟩ := hm
    obtain ⟨hc1, hc2⟩ := hcH
    simp only [List.length_cons] at hl
    have hlt : lvl < cfg.levels.length := by omega
    have hs := hspec lvl (by omega)
    have hdrop : cfg.levels.drop lvl = cfg.lv lvl :: cfg.levels.drop (lvl + 1) := by
      rw [List.drop_eq_getElem_cons hlt]
      simp [OsCfg.lv, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    rw [hdrop, osLevels_cons]
    have hvs : osLvsValsW Ht cfg xs cur P sqz rew lvl cv p w roots s (H :: Hs) =
        osLvValsW Ht cfg lvl xs cv p w H s.co cur (roots.getD lvl default).1 P (sqz lvl) (rew lvl) ++
        osLvsValsW Ht cfg xs cur P sqz rew (lvl + 1) (osHCvEndW Ht cfg lvl xs p H.cv1) (osHPEnd cfg lvl p)
          (osHWEndW Ht cfg lvl xs p H) (osHRootsEnd cfg lvl roots H) (osLevel cfg lvl (cfg.lv lvl) s).2 Hs := rfl
    rw [hvs] at hv ⊢
    obtain ⟨hv1, hv2⟩ := os_look_app hv
    obtain ⟨⟨hca1, hcq1, hcb1, hsq1⟩, hH1, hat1, hco1, hq1, ht1, hk1⟩ := osLevel_completeC (CM := CM) (rd := rd) (kret := kret)
      (rewv := rew lvl) hs hok hans hP hat hcop hco8 hq hm1 hc1 hv1
    have hend : osLvsEndW Ht cfg xs lvl cv p w roots (H :: Hs) = osLvsEndW Ht cfg xs (lvl + 1) (osHCvEndW Ht cfg lvl xs p H.cv1)
        (osHPEnd cfg lvl p) (osHWEndW Ht cfg lvl xs p H) (osHRootsEnd cfg lvl roots H) Hs := rfl
    rw [hend]
    by_cases hy : lvl = cfg.yrLevel
    · obtain ⟨rfl, -, -⟩ := hlast hy
      have hnil : cfg.levels.drop (lvl + 1) = [] := List.drop_eq_nil_of_le (by omega)
      rw [hnil]
      refine ⟨⟨hca1, hcq1, hcb1, hsq1, trivial⟩, ?_, hat1, by show (osLevel cfg lvl (cfg.lv lvl) s).2.co = 3; rw [hco1, ite_pos' hy],
        hq1, ht1, ?_⟩
      · simp only [osLevels, List.append_nil]; exact hH1
      · simp only [osLevels, osLvsValsW, List.append_nil]; exact hk1
    · have hch' := hnext hy
      rw [ite_neg' hy] at hco1
      have hk8 : 8 ≤ osHPEnd cfg lvl p := by
        simp only [osHPEnd, osHP2, ite_neg' hy]; omega
      obtain ⟨hcs2, hH2, hat2, hco2, hq2, ht2, hk2⟩ := osLevels_completeC hlen hspec hyl hP Hs (lvl + 1) _ _ _ _ _ _
        (by omega) hch' hat1 (by omega) (by omega) hq1 hm2 hc2 (fun j hj => by rw [hk1]; exact hv2 j hj)
      refine ⟨⟨hca1, hcq1, hcb1, hsq1, hcs2⟩, ?_, hat2, hco2, hq2, ht2, ?_⟩
      · rw [holdsListB_append]
        exact (holdsListB_noRet _ (osLevel_noRet _ _ _ _) _ _).mpr ⟨hH1, hH2⟩
      · rw [hk2, hk1, List.length_append]; ring


end
end LeanVM.Guest.B1
