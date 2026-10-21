/-
  LeanVM.Guest.B1.Comp.Whir.StackedDeployed

  `open_stacked`'s completeness over a completeness model, at the deployed model: the values over
  BLAKE2s are the deployed ones, and the deployed lemmas follow.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.OsDataC
public import LeanVM.Guest.B1.Comp.Whir.SqIter

/-!
# At the deployed model (TRIAGE #36)

At `blake2sBytes` the honest values over a total hash are the deployed ones (`…W_blake`), the
data `OsLvOkW`, `OsLvMemW`, `OsLvsMemW`, `OsBodyMemW` the deployed `OsLvOk`, …, and at
`CompModel.deployed` every hash is answered (`osLvAns_deployed`, `osChainC_of_deployed`). The
deployed completeness lemmas of `Whir/StackedC*.lean`, `OsBody.lean`, `OsData.lean` and
`SqIter.lean` follow from the generic ones (`…_of_comp`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub LeanVM.E2E.Complete

@[expose] public section

/-! ## The values at BLAKE2s -/

theorem sqAllW_blake' : sqAllW blake2sBytes = sqAll := funext fun n => funext fun cv => sqAllW_blake n cv

theorem osPosOfW_blake' : osPosOfW blake2sBytes = osPosOf :=
  funext fun d => funext fun cv => funext fun i => osPosOfW_blake d cv i

theorem osHCv2W_blake : osHCv2W blake2sBytes = osHCv2 := by
  funext cfg lvl xs p cv1; simp only [osHCv2W, osHCv2, sqAllW_blake']; rfl

theorem osHCv3W_blake : osHCv3W blake2sBytes = osHCv3 := by
  funext cfg lvl xs p cv1; simp only [osHCv3W, osHCv3, osHCv2W_blake]; rfl

theorem osHQsW_blake : osHQsW blake2sBytes = osHQs := by
  funext cfg lvl xs p cv1; simp only [osHQsW, osHQs, osHCv3W_blake, osPosOfW_blake']

theorem osHCv4W_blake : osHCv4W blake2sBytes = osHCv4 := by
  funext cfg lvl xs p cv1; simp only [osHCv4W, osHCv4, osHCv3W_blake, sqAllW_blake']

theorem osHLamW_blake : osHLamW blake2sBytes = osHLam := by
  funext cfg lvl xs p cv1; simp only [osHLamW, osHLam, osHCv4W_blake]; rfl

theorem osHCvEndW_blake : osHCvEndW blake2sBytes = osHCvEnd := by
  funext cfg lvl xs p cv1; simp only [osHCvEndW, osHCvEnd, osHCv4W_blake]; rfl

theorem osHEnfW_blake : osHEnfW blake2sBytes = osHEnf := by
  funext cfg lvl xs p H; simp only [osHEnfW, osHEnf, osHLamW_blake, osHQsW_blake]

theorem osHPendingW_blake : osHPendingW blake2sBytes = osHPending := by
  funext cfg lvl xs p cv1; simp only [osHPendingW, osHPending, sqAllW_blake']; rfl

theorem osHWEndW_blake : osHWEndW blake2sBytes = osHWEnd := by
  funext cfg lvl xs p H
  simp only [osHWEndW, osHWEnd, osHLamW_blake, osHPendingW_blake, osHEnfW_blake, osHQsW_blake]

theorem osFoldsValsW_blake (xs : List E) : ∀ (n : ℕ) (cv : Digest) (p : ℕ) (q : List E) (bv : E) (co : ℕ),
    osFoldsValsW blake2sBytes xs n cv p q bv co = osFoldsVals xs n cv p q bv co
  | 0, _, _, _, _, _ => rfl
  | n + 1, cv, p, q, bv, co => by
    simp only [osFoldsValsW, osFoldsVals]
    rw [osFoldsValsW_blake xs n]
    rfl

theorem osFoldsValsW_blake' : osFoldsValsW blake2sBytes = osFoldsVals :=
  funext fun xs => funext fun n => funext fun cv => funext fun p => funext fun q => funext fun bv =>
    funext fun co => osFoldsValsW_blake xs n cv p q bv co

theorem osOodSampleValsW_blake : osOodSampleValsW blake2sBytes = osOodSampleVals := by
  funext oz lc v cv y c0 c2; simp only [osOodSampleValsW, osOodSampleVals, sqAllW_blake']; rfl

theorem osCommitValsW_blake : osCommitValsW blake2sBytes = osCommitVals := by
  funext lvl lc v cv x0 x1 y c0 c2; simp only [osCommitValsW, osCommitVals, osOodSampleValsW_blake]; rfl

theorem osSqueezesValsW_blake : osSqueezesValsW blake2sBytes = osSqueezesVals := by
  funext m n v cv; simp only [osSqueezesValsW, osSqueezesVals, sqAllW_blake']; rfl

theorem osTailValsW_blake : osTailValsW blake2sBytes = osTailVals := by
  funext yr xs cv p q cbv co tchv w1 cv1; simp only [osTailValsW, osTailVals, osFoldsValsW_blake']; rfl

theorem osLvValsAW_blake : osLvValsAW blake2sBytes = osLvValsA := by
  funext cfg lvl xs cv p w H co cur v
  simp only [osLvValsAW, osLvValsA, osFoldsValsW_blake', osHCv2W_blake, osCommitValsW_blake]; rfl

theorem osLvValsBW_blake : osLvValsBW blake2sBytes = osLvValsB := by
  funext cfg lvl xs p H rt P sqzv rewv
  simp only [osLvValsBW, osLvValsB, osSqueezesValsW_blake, osHCv3W_blake, osHLamW_blake, osHEnfW_blake,
    osHCv4W_blake]; rfl

theorem osLvValsW_blake : osLvValsW blake2sBytes = osLvVals := by
  funext cfg lvl xs cv p w H co cur rt P sqzv rewv
  simp only [osLvValsW, osLvVals, osLvValsAW_blake, osLvValsBW_blake]

theorem osLvsValsW_blake (cfg : OsCfg) (xs : List E) (cur : E) (P : OsPtrs) (sqz rew : ℕ → E) :
    ∀ (Hs : List OsLvH) (lvl : ℕ) (cv : Digest) (p : ℕ) (w : WhirState) (roots : List (Digest × ℕ × ℕ))
      (s : OsSt), osLvsValsW blake2sBytes cfg xs cur P sqz rew lvl cv p w roots s Hs =
        osLvsVals cfg xs cur P sqz rew lvl cv p w roots s Hs
  | [], _, _, _, _, _, _ => rfl
  | H :: Hs, lvl, cv, p, w, roots, s => by
    simp only [osLvsValsW, osLvsVals, osLvValsW_blake, osHCvEndW_blake, osHWEndW_blake]
    rw [osLvsValsW_blake cfg xs cur P sqz rew Hs]

theorem osLvsEndW_blake (cfg : OsCfg) (xs : List E) :
    ∀ (Hs : List OsLvH) (lvl : ℕ) (cv : Digest) (p : ℕ) (w : WhirState) (roots : List (Digest × ℕ × ℕ)),
      osLvsEndW blake2sBytes cfg xs lvl cv p w roots Hs = osLvsEnd cfg xs lvl cv p w roots Hs
  | [], _, _, _, _, _ => rfl
  | H :: Hs, lvl, cv, p, w, roots => by
    simp only [osLvsEndW, osLvsEnd, osHCvEndW_blake, osHWEndW_blake]
    rw [osLvsEndW_blake cfg xs Hs]

theorem osLvsEndW_blake' : osLvsEndW blake2sBytes = osLvsEnd := by
  funext cfg xs lvl cv p w roots Hs; exact osLvsEndW_blake cfg xs Hs lvl cv p w roots

theorem osRunEndLW_blake : OsRun.endLW blake2sBytes = OsRun.endL := by
  funext cfg R; simp only [OsRun.endLW, OsRun.endL, osLvsEndW_blake']; rfl

theorem osRunWTW_blake : OsRun.wTW blake2sBytes = OsRun.wT := by
  funext cfg R; simp only [OsRun.wTW, OsRun.wT, osRunEndLW_blake]

theorem osBodyValsW_blake : osBodyValsW blake2sBytes = osBodyVals := by
  funext cfg R
  simp only [osBodyValsW, osBodyVals, osTailValsW_blake, osRunEndLW_blake]
  rw [osLvsValsW_blake]
  rfl

/-! ## The data at BLAKE2s -/

theorem osLvOkW_blake {cfg : OsCfg} {lvl : ℕ} {xs : List E} {p μ : ℕ} {L : Whir.Level} {cv : Digest}
    {w : WhirState} {osp : List Opening} {roots : List (Digest × ℕ × ℕ)} {H : OsLvH} :
    OsLvOkW blake2sBytes cfg lvl xs p μ L cv w osp roots H ↔ OsLvOk cfg lvl xs p μ L cv w osp roots H := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    rw [osHCv2W_blake] at h4
    rw [osHQsW_blake] at h5
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    refine ⟨h1, h2, h3, ?_, ?_, h6, h7⟩
    · rw [osHCv2W_blake]; exact h4
    · rw [osHQsW_blake]; exact h5

theorem osLvMemW_blake {rd : Reader} {cfg : OsCfg} {lvl : ℕ} {xs : List E} {p : ℕ} {H : OsLvH} {rt : Digest}
    {P : OsPtrs} {sqzv cur : E} :
    OsLvMemW blake2sBytes rd cfg lvl xs p H rt P sqzv cur ↔ OsLvMem rd cfg lvl xs p H rt P sqzv cur := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    rw [osHLamW_blake] at h4 h9 h12
    rw [osHCv3W_blake] at h5 h6
    rw [osHCv4W_blake] at h7 h8
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    refine ⟨h1, h2, h3, ?_, ?_, ?_, ?_, ?_, ?_, h10, h11, ?_⟩
    · rw [osHLamW_blake]; exact h4
    · rw [osHCv3W_blake]; exact h5
    · rw [osHCv3W_blake]; exact h6
    · rw [osHCv4W_blake]; exact h7
    · rw [osHCv4W_blake]; exact h8
    · rw [osHLamW_blake]; exact h9
    · rw [osHLamW_blake]; exact h12

theorem osLvsMemW_blake {rd : Reader} {cfg : OsCfg} {xs : List E} {cur : E} {P : OsPtrs} {sqz : ℕ → E} :
    ∀ (Hs : List OsLvH) (lvl : ℕ) (cv : Digest) (p : ℕ) (w : WhirState) (roots : List (Digest × ℕ × ℕ)),
      OsLvsMemW blake2sBytes rd cfg xs cur P sqz lvl cv p w roots Hs ↔ OsLvsMem rd cfg xs cur P sqz lvl cv p w roots Hs
  | [], _, _, _, _, _ => Iff.rfl
  | H :: Hs, lvl, cv, p, w, roots => by
    simp only [OsLvsMemW, OsLvsMem, osLvMemW_blake, osHCvEndW_blake, osHWEndW_blake, osLvsMemW_blake Hs]

theorem osBodyMemW_blake {rd : Reader} {σ : Val} {cfg : OsCfg} {R : OsRun} :
    OsBodyMemW blake2sBytes rd σ cfg R ↔ OsBodyMem rd σ cfg R := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
    exact ⟨h1, h2, h3, (osLvsMemW_blake _ _ _ _ _ _).mp h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
    exact ⟨h1, h2, h3, (osLvsMemW_blake _ _ _ _ _ _).mpr h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

/-- **At the deployed model, a level's hashes are answered.** -/
theorem osLvAns_deployed {cfg : OsCfg} {lvl : ℕ} {xs : List E} {p : ℕ} {L : Whir.Level} {cv : Digest}
    {w : WhirState} {osp : List Opening} {roots : List (Digest × ℕ × ℕ)} {H : OsLvH} :
    OsLvAns CompModel.deployed.hm blake2sBytes cfg lvl xs p L cv w osp roots H where
  folds := ansRun_blake _ _
  last := fun _ => by rw [obsAllM_hm_deployed]; rfl
  r0 := fun _ => rfl
  r1 := fun _ => rfl
  ood := fun _ => by rw [sqAllM_hm_deployed, sqAllW_blake]
  ry := fun _ => rfl
  rc0 := fun _ => rfl
  rc2 := fun _ => rfl
  base := rfl
  gc := rfl
  nonce := rfl
  sq := by rw [sqAllM_hm_deployed, sqAllW_blake]
  lam := rfl
  open_ := fun _ _ _ _ => openAll_some_blake _ _
  c0 := rfl
  c2 := rfl

theorem osChainC_deployed {cfg : OsCfg} {μ lane : ℕ} {xs : List E} {Lall : List Whir.Level} {e : WhirEnd}
    {sp' : St} {Q : List (ℕ × List (ℕ × Opening))} :
    ∀ (Hs : List OsLvH) (lvl : ℕ) (cv : Digest) (p : ℕ) (w : WhirState) (osp : List Opening)
      (roots : List (Digest × ℕ × ℕ)),
      OsChainC CompModel.deployed.hm blake2sBytes cfg μ lane xs Lall e sp' Q lvl cv p w osp roots Hs ↔
        OsChain cfg μ lane xs Lall e sp' Q lvl cv p w osp roots Hs
  | [], _, _, _, _, _, _ => Iff.rfl
  | H :: Hs, lvl, cv, p, w, osp, roots => by
    simp only [OsChainC, OsChain, osHQsW_blake, osHWEndW_blake, osHCvEndW_blake, osChainC_deployed Hs,
      osLvOkW_blake]
    constructor
    · rintro ⟨hok, -, hq, hl, hn⟩
      exact ⟨hok, hq, fun h => ⟨(hl h).1, (hl h).2.1⟩, hn⟩
    · rintro ⟨hok, hq, hl, hn⟩
      exact ⟨hok, osLvAns_deployed, hq, fun h => ⟨(hl h).1, (hl h).2, ansRun_blake _ _⟩, hn⟩

theorem osLvsCallHC_of_deployed {CA CB Csq : ℕ → CallRel} {cfg : OsCfg} {xs : List E} {cur : E} {P : OsPtrs}
    {sqz rew : ℕ → E} : ∀ (Hs : List OsLvH) (lvl p : ℕ) (w : WhirState) (roots : List (Digest × ℕ × ℕ)),
      OsLvsCallH CA CB Csq cfg xs cur P sqz rew lvl p w roots Hs →
        OsLvsCallHC CompModel.deployed blake2sBytes CA CB Csq cfg xs cur P sqz rew lvl p w roots Hs
  | [], _, _, _, _, _ => trivial
  | H :: Hs, lvl, p, w, roots, ⟨⟨f1, f2, f3, f4, f5, f6, f7, f8⟩, h2⟩ => by
    refine ⟨⟨fun cv' p' q' a b _ => f1 cv' p' q' a b, ?_, ?_, ?_, f5, f6, f7, ?_⟩, ?_⟩
    · rw [osHCv2W_blake]; exact f2
    · intro h; rw [sqAllW_blake']; exact f3 h
    · rw [osHCv2W_blake]; exact f4
    · rw [osHEnfW_blake]; exact f8
    · have := osLvsCallHC_of_deployed Hs (lvl + 1) _ _ _ h2
      rw [osHWEndW_blake]; exact this

section Recover

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## The deployed lemmas, from the generic ones -/

/-- The deployed `osFsNext_complete`, from the generic one. -/
theorem osFsNext_complete_of_comp {s : OsSt} {cv : Digest} {cur : E} {p : ℕ} (hat : OsAt σ s cv cur p)
    {x : E} (hx : LoadHolds rd cur p x) {kret : List E → Prop}
    (hv : ∀ j < 15, σ (.n (s.k + j)) = (osFsNextVals x cv).getD j 0) :
    Stmt.HoldsList C rd σ (osFsNext s).1 True kret ∧ OsAt σ (osFsNext s).2 (obsCv cv x) cur (p + 1) := by
  have h := osFsNext_completeC (CM := CompModel.deployed) (Ht := blake2sBytes) (C := C) (kret := kret) hat hx rfl hv
  rwa [show CompModel.deployed.sem = blakeDeployed from rfl, holdsListB_deployed] at h

/-- The deployed `osFolds_complete`, from the generic one. -/
theorem osFolds_complete_of_comp {xs : List E} {cur : E} {fch : ℕ} {kret : List E → Prop} {C : CallRel}
    (hcall : ∀ (cv' : Digest) (p' : ℕ) (q' : List E), q'.length = 3 → p' + 2 ≤ xs.length →
      C "opening_fold" [(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ p', q'.getD 0 0, q'.getD 1 0,
        q'.getD 2 0] (osFoldRets xs cv' p' q' (cur * gen ^ p'))) :
    ∀ (n fo : ℕ) (s : OsSt) (cv : Digest) (p : ℕ) (w : WhirState) (lf : List E) (osp : List Opening)
      (roots : List (Digest × ℕ × ℕ)) (res : WhirState × List E) (sp' : St),
      OsAt σ s cv cur p → s.co < 2 ^ 128 → w.quad = [σ (.n s.c), σ (.n s.b), σ (.n s.a)] →
      Runs (foldRounds n w lf) ⟨cv, xs.drop p, osp, roots⟩ res sp' →
      (∀ j < (osFoldsVals xs n cv p w.quad (σ (.n s.cb)) s.co).length,
        σ (.n (s.k + j)) = (osFoldsVals xs n cv p w.quad (σ (.n s.cb)) s.co).getD j 0) →
      (∀ j < n, LoadHolds rd (σ (.n fch)) (fo + j) (res.1.folds.getD (w.folds.length + j) 0)) →
      Stmt.HoldsList C rd σ (osFolds fch fo n s).1 True kret ∧
        OsAt σ (osFolds fch fo n s).2 sp'.cv cur (p + 2 * n) ∧ sp' = ⟨sp'.cv, xs.drop (p + 2 * n), osp, roots⟩ ∧
        res.1.quad = [σ (.n (osFolds fch fo n s).2.c), σ (.n (osFolds fch fo n s).2.b),
          σ (.n (osFolds fch fo n s).2.a)] ∧ res.1.target = (if n = 0 then w.target else σ (.n (osFolds fch fo n s).2.t)) ∧
        res.1.glued = w.glued ∧ res.1.folds.length = w.folds.length + n ∧
        (∃ chs, res.1.folds = w.folds ++ chs ∧ res.2 = lf ++ chs) ∧
        (osFolds fch fo n s).2.co = (if n = 0 then s.co else 0) ∧
        (osFolds fch fo n s).2.k = s.k + (osFoldsVals xs n cv p w.quad (σ (.n s.cb)) s.co).length := by
  intro n fo s cv p w lf osp roots res sp' hat hco hq hrun hv hst
  have h := osFolds_completeC (CM := CompModel.deployed) (Ht := blake2sBytes) (C := C) (kret := kret)
    (fun cv' p' q' a b _ => hcall cv' p' q' a b) n fo s cv p w lf osp roots res sp' hat hco hq hrun
    (ansRun_blake _ _) (by rw [osFoldsValsW_blake']; exact hv) hst
  rwa [osFoldsValsW_blake', show CompModel.deployed.sem = blakeDeployed from rfl, holdsListB_deployed] at h

/-- The deployed `osCommit_complete`, from the generic one. -/
theorem osCommit_complete_of_comp {lvl logCols roots oodz ood : ℕ} {s : OsSt} {cv : Digest} {cur : E} {p : ℕ}
    (hat : OsAt σ s cv cur p) {x0 x1 y c0 c2 : E} {kret : List E → Prop}
    (lx0 : LoadHolds rd cur p x0) (lx1 : LoadHolds rd cur (p + 1) x1)
    (ly : LoadHolds rd cur (p + 2) y) (lc0 : LoadHolds rd cur (p + 3) c0) (lc2 : LoadHolds rd cur (p + 4) c2)
    (sx0 : LoadHolds rd (σ (.n roots)) (2 * lvl + 2) x0) (sx1 : LoadHolds rd (σ (.n roots)) (2 * lvl + 3) x1)
    (sy : LoadHolds rd (σ (.n ood)) ((lvl + 1) * 4 + 0 * 4 + 1) y)
    (sc0 : LoadHolds rd (σ (.n ood)) ((lvl + 1) * 4 + 0 * 4 + 2) c0)
    (sc2 : LoadHolds rd (σ (.n ood)) ((lvl + 1) * 4 + 0 * 4 + 3) c2)
    (hca0 : C "assert_canonical" [x0] [0]) (hca1 : C "assert_canonical" [x1] [0])
    (hood : C "opening_ood_point" [(digestScalars (obsCv (obsCv cv x0) x1)).1,
      (digestScalars (obsCv (obsCv cv x0) x1)).2, σ (.n oodz) * osGw ((lvl + 1 + 0) * 22), osGw logCols]
      [(digestScalars (sqAll logCols (obsCv (obsCv cv x0) x1)).2).1,
        (digestScalars (sqAll logCols (obsCv (obsCv cv x0) x1)).2).2])
    (hv : ∀ j < 84, σ (.n (s.k + j)) = (osCommitVals lvl logCols (σ (.n oodz)) cv x0 x1 y c0 c2).getD j 0) :
    Stmt.HoldsList C rd σ (osCommit lvl logCols 1 roots oodz ood s).1 True kret ∧
      OsAt σ (osCommit lvl logCols 1 roots oodz ood s).2
        (obsCv (obsCv (obsCv (sqAll logCols (obsCv (obsCv cv x0) x1)).2 y) c0) c2) cur (p + 5) ∧
      (osCommit lvl logCols 1 roots oodz ood s).2.co = s.co + 5 ∧
      (osCommit lvl logCols 1 roots oodz ood s).2.cb = s.cb ∧ (osCommit lvl logCols 1 roots oodz ood s).2.k = s.k + 84 := by
  have h := osCommit_completeC (CM := CompModel.deployed) (Ht := blake2sBytes) (C := C) (kret := kret) hat lx0 lx1
    ly lc0 lc2 rfl rfl rfl rfl rfl sx0 sx1 sy sc0 sc2 hca0 hca1 (by rw [sqAllW_blake']; exact hood)
    (by rw [osCommitValsW_blake]; exact hv)
  rwa [sqAllW_blake', show CompModel.deployed.sem = blakeDeployed from rfl, holdsListB_deployed] at h

/-- The deployed `osGrind_complete`, from the generic one. -/
theorem osGrind_complete_of_comp {bits : ℕ} (hb0 : bits ≠ 0) {s : OsSt} {cv : Digest} {cur : E} {p : ℕ}
    (hat : OsAt σ s cv cur p) {n : E} (ln : LoadHolds rd cur p n) {kret : List E → Prop}
    (hcall : C "grind_check" [(digestScalars cv).1, (digestScalars cv).2, n, osGw bits] [])
    (hv : ∀ j < 16, σ (.n (s.k + j)) = (osGrindVals bits n cv).getD j 0) :
    Stmt.HoldsList C rd σ (osGrind bits s).1 True kret ∧
      OsAt σ (osGrind bits s).2 (absorbCv cv n 4) cur (p + 1) ∧ (osGrind bits s).2.co = s.co + 1 ∧
      (osGrind bits s).2.cb = s.cb ∧ (osGrind bits s).2.k = s.k + 16 := by
  have h := osGrind_completeC (CM := CompModel.deployed) (Ht := blake2sBytes) (C := C) (kret := kret) hb0 hat ln
    hcall rfl hv
  rwa [show CompModel.deployed.sem = blakeDeployed from rfl, holdsListB_deployed] at h

/-- The deployed `osSqueezes_complete`, from the generic one. -/
theorem osSqueezes_complete_of_comp {maxSq nsq qpos qbp : ℕ} {loop : String} (hnsq : 2 * nsq < 2 ^ 128) {s : OsSt}
    {cv : Digest} {cur : E} {p : ℕ} (hat : OsAt σ s cv cur p) {sqzv : E} {kret : List E → Prop}
    (l0 : LoadHolds rd sqzv 0 (digestScalars cv).1) (l1 : LoadHolds rd sqzv 1 (digestScalars cv).2)
    (l2 : LoadHolds rd sqzv (2 * nsq) (digestScalars (sqAll nsq cv).2).1)
    (l3 : LoadHolds rd sqzv (2 * nsq + 1) (digestScalars (sqAll nsq cv).2).2)
    (hcall : 1 + osGw nsq ≠ 0 → C loop [1, osGw nsq, sqzv, σ (.n qpos), σ (.n qbp)] [])
    (hv : ∀ j < 25, σ (.n (s.k + j)) = (osSqueezesVals maxSq nsq sqzv cv).getD j 0) :
    Stmt.HoldsList C rd σ (osSqueezes maxSq nsq qpos qbp loop s).1 True kret ∧
      OsAt σ (osSqueezes maxSq nsq qpos qbp loop s).2 (sqCv (sqAll nsq cv).2) cur p ∧
      σ (.n ((osSqueezes maxSq nsq qpos qbp loop s).2.k - 1)) = challengeOf (sqCv (sqAll nsq cv).2) ∧
      (osSqueezes maxSq nsq qpos qbp loop s).2.co = s.co ∧ (osSqueezes maxSq nsq qpos qbp loop s).2.cb = s.cb ∧
      (osSqueezes maxSq nsq qpos qbp loop s).2.k = s.k + 25 := by
  have h := osSqueezes_completeC (CM := CompModel.deployed) (Ht := blake2sBytes) (C := C) (kret := kret) (maxSq := maxSq)
    (loop := loop) hnsq hat l0 l1 (by rw [sqAllW_blake']; exact l2) (by rw [sqAllW_blake']; exact l3) hcall rfl
    (by rw [osSqueezesValsW_blake]; exact hv)
  rwa [sqAllW_blake', show CompModel.deployed.sem = blakeDeployed from rfl, holdsListB_deployed] at h

/-- The deployed `osQueries_complete`, from the generic one. -/
theorem osQueries_complete_of_comp {cfg : OsCfg} {lv : OsLvl} {lvl : ℕ} (hfo : lv.foldsOff < 2 ^ 128)
    (hco4 : 4 * lv.capOff < 2 ^ 128) (hco1 : lv.capOff < 2 ^ 128) (hqo : lvl * cfg.maxQ < 2 ^ 128)
    (hpo : lv.posOff < 2 ^ 128) {s : OsSt} {cv : Digest} {cur : E} {p : ℕ} (hat : OsAt σ s cv cur p)
    {rewv : E} {rt : Digest} {qsum c0 c2 : E} {kret : List E → Prop}
    (lc0 : LoadHolds rd cur p c0) (lc2 : LoadHolds rd cur (p + 1) c2)
    (sr0 : LoadHolds rd (σ (.n osRoots)) (2 * lvl) (digestScalars rt).1)
    (sr1 : LoadHolds rd (σ (.n osRoots)) (2 * lvl + 1) (digestScalars rt).2)
    (hrw : C lv.rowWeights [σ (.n osFch) * gen ^ lv.foldsOff, rewv] [])
    (hcap : C lv.verifyCap [σ (.n osCaps) * gen ^ (4 * lv.capOff), σ (.n osFlags) * gen ^ lv.capOff]
      [(digestScalars rt).1, (digestScalars rt).2])
    (hqf : C lv.queriesFn [σ (.n osCaps) * gen ^ (4 * lv.capOff), σ (.n osFlags) * gen ^ lv.capOff,
      σ (.n osQw) * gen ^ (lvl * cfg.maxQ), σ (.n osQbp) * gen ^ lv.posOff, rewv, osGw lv.queries] [qsum])
    (hv : ∀ j < (osQueriesSegs cfg lv lvl rewv (σ (.n osFch)) (σ (.n osCaps)) (σ (.n osFlags)) (σ (.n osQw))
        (σ (.n osQbp)) rt qsum c0 c2 cv).flatten.length,
      σ (.n (s.k + j)) = (osQueriesSegs cfg lv lvl rewv (σ (.n osFch)) (σ (.n osCaps)) (σ (.n osFlags)) (σ (.n osQw))
        (σ (.n osQbp)) rt qsum c0 c2 cv).flatten.getD j 0) :
    let q := osQueries cfg lv lvl s
    Stmt.HoldsList C rd σ q.1 True kret ∧ OsAt σ q.2.1 (obsCv (obsCv cv c0) c2) cur (p + 2) ∧
      q.2.1.co = s.co + 2 ∧ q.2.1.cb = s.cb ∧ σ (.n q.2.2.1) = qsum ∧ σ (.n q.2.2.2.1) = c0 ∧
      σ (.n q.2.2.2.2.1) = qsum + c2 ∧ σ (.n q.2.2.2.2.2) = c2 ∧ σ (.n (s.k + 1)) = rewv ∧
      q.2.1.k = s.k + (osQueriesSegs cfg lv lvl rewv (σ (.n osFch)) (σ (.n osCaps)) (σ (.n osFlags)) (σ (.n osQw))
        (σ (.n osQbp)) rt qsum c0 c2 cv).flatten.length := by
  intro q
  have h := osQueries_completeC (CM := CompModel.deployed) (Ht := blake2sBytes) (C := C) (kret := kret) (rewv := rewv)
    (rt := rt) (qsum := qsum) hfo hco4 hco1 hqo hpo hat lc0 lc2 rfl rfl sr0 sr1 hrw hcap hqf hv
  simp only [show CompModel.deployed.sem = blakeDeployed from rfl, holdsListB_deployed] at h
  exact h

/-- The deployed `osTail_complete`, from the generic one. -/
theorem osTail_complete_of_comp {yrLog : ℕ} {s : OsSt} {cv : Digest} {cur : E} {p : ℕ}
    (hat : OsAt σ s cv cur p) (hcop : s.co ≤ p) (hco : s.co ≤ 8) {xs : List E} {osp : List Opening}
    {roots : List (Digest × ℕ × ℕ)} {w : WhirState} (hw : w.folds = [])
    (hq : w.quad = [σ (.n s.c), σ (.n s.b), σ (.n s.a)]) {w1 : WhirState} {chs : List E} {cv1 : Digest}
    (hrun : Runs (foldRounds (yrLog - 1) w []) ⟨cv, xs.drop p, osp, roots⟩ (w1, chs)
      ⟨cv1, xs.drop (p + 2 * (yrLog - 1)), osp, roots⟩) {tchv : E}
    (htch : ∀ j < yrLog - 1, LoadHolds rd tchv j (chs.getD j 0))
    (hlast : LoadHolds rd tchv (yrLog - 1) (challengeOf (sqCv cv1)))
    (hz : ∀ j < 5 - yrLog, LoadHolds rd tchv (yrLog + j) 0) {kret : List E → Prop}
    (hcf : ∀ (cv' : Digest) (p' : ℕ) (q' : List E), q'.length = 3 → p' + 2 ≤ xs.length →
      C "opening_fold" [(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ p', q'.getD 0 0, q'.getD 1 0,
        q'.getD 2 0] (osFoldRets xs cv' p' q' (cur * gen ^ p')))
    (hv : ∀ j < (osTailVals yrLog xs cv p w.quad (cur * gen ^ (p - s.co)) s.co tchv w1 cv1).length,
      σ (.n (s.k + j)) = (osTailVals yrLog xs cv p w.quad (cur * gen ^ (p - s.co)) s.co tchv w1 cv1).getD j 0) :
    Stmt.HoldsList C rd σ (osTail yrLog s).1 True kret ∧
      σ (.n (osTail yrLog s).2.1.t) = polyEval w1.quad (challengeOf (sqCv cv1)) ∧
      σ (.n (osTail yrLog s).2.2.1) = tchv ∧
      (osTail yrLog s).2.1.k = s.k + (osTailVals yrLog xs cv p w.quad (cur * gen ^ (p - s.co)) s.co tchv w1 cv1).length := by
  have h := osTail_completeC (CM := CompModel.deployed) (Ht := blake2sBytes) (C := C) (kret := kret) hat hcop hco hw hq
    hrun (ansRun_blake _ _) rfl htch hlast hz (fun cv' p' q' a b _ => hcf cv' p' q' a b)
    (by rw [osTailValsW_blake]; exact hv)
  rwa [osTailValsW_blake, show CompModel.deployed.sem = blakeDeployed from rfl, holdsListB_deployed] at h

/-- The deployed `osHead_complete`, from the generic one. -/
theorem osHead_complete_of_comp {cfg : OsCfg} {fs0 fs1 target root0 root1 cur : E} {cv : Digest} {x0 x1 : E}
    {P : OsPtrs} (hcv : (fs0, fs1) = digestScalars cv) (lx0 : LoadHolds rd cur 0 x0)
    (lx1 : LoadHolds rd cur 1 x1) (lr0 : LoadHolds rd P.roots 0 root0) (lr1 : LoadHolds rd P.roots 1 root1)
    {kret : List E → Prop}
    (hv : ∀ j < 61, σ (.n j) = (osHeadVals cfg fs0 fs1 target root0 root1 cur cv x0 x1 P).getD j 0) :
    Stmt.HoldsList C rd σ (osHead cfg).1 True kret ∧
      OsAt σ (osHead cfg).2 (obsCv (obsCv cv x0) x1) cur 2 ∧ (osHead cfg).2.co = 2 ∧
      [σ (.n (osHead cfg).2.c), σ (.n (osHead cfg).2.b), σ (.n (osHead cfg).2.a)] = [x0, target + x1, x1] ∧
      σ (.n (osHead cfg).2.t) = target ∧ OsPtrsAt σ P ∧ (osHead cfg).2.k = 61 := by
  have h := osHead_completeC (CM := CompModel.deployed) (Ht := blake2sBytes) (C := C) (kret := kret) hcv lx0 lx1 lr0 lr1
    rfl rfl hv
  rwa [show CompModel.deployed.sem = blakeDeployed from rfl, holdsListB_deployed] at h

/-- The deployed `sqIter_holds`, from the generic one. -/
theorem sqIter_holds_of_comp {lv : OsLvl} (hpo : lv.posOff < 2 ^ 128)
    (hdig : osDigitsVal 1 (osPowDigits (192 / lv.depth)) = 192 / lv.depth) {x N sqz qpos qbp : E}
    {cv : Digest}
    (l0 : LoadHolds rd (sqz * (x * x)) 0 (digestScalars cv).1)
    (l1 : LoadHolds rd (sqz * (x * x)) 1 (digestScalars cv).2)
    (l2 : LoadHolds rd (sqz * (x * x)) 2 (digestScalars (sqCv cv)).1)
    (l3 : LoadHolds rd (sqz * (x * x)) 3 (digestScalars (sqCv cv)).2)
    (hdec : C lv.decode [challengeOf (sqCv cv), qpos * gen ^ lv.posOff * x ^ (192 / lv.depth),
      qbp * gen ^ lv.posOff * x ^ (192 / lv.depth)] [])
    (hK : IsInK (x * gen + N)) (hcall : x * gen + N ≠ 0 → C lv.sqLoop [x * gen, N, sqz, qpos, qbp] []) :
    Stmt.HoldsList C rd (sqIterVal lv x N sqz qpos qbp cv) (sqLoopOf lv) False (fun rs => rs = []) := by
  have h := sqIter_holdsC (CM := CompModel.deployed) (Ht := blake2sBytes) (C := C) hpo hdig l0 l1 l2 l3 rfl hdec hK hcall
  rwa [show CompModel.deployed.sem = blakeDeployed from rfl, holdsListB_deployed] at h

/-- The deployed `osBody_complete`, from the generic one. -/
theorem osBody_complete_of_comp {cfg : OsCfg} {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall)
    {R : OsRun} {e : WhirEnd} {sp' : St} {Q : List (ℕ × List (ℕ × Opening))}
    (hx2 : 2 ≤ R.xs.length) (hHs : R.Hs.length = cfg.levels.length)
    (hch : OsChain cfg μ (cfg.lv 0).folds R.xs Lall e sp' Q 0 R.cv0 2 (osW0 R.target R.xs) R.os (R.roots0 cfg) R.Hs)
    {ospT : List Opening} {rootsT : List (Digest × ℕ × ℕ)}
    (hrunT : Runs (foldRounds (cfg.yrLog - 1) (R.wT cfg) []) ⟨(R.endL cfg).1, R.xs.drop (R.endL cfg).2.1, ospT, rootsT⟩
      (R.w1t, R.chst) ⟨R.cv1t, R.xs.drop ((R.endL cfg).2.1 + 2 * (cfg.yrLog - 1)), ospT, rootsT⟩)
    (hDt : R.D.t = polyEval R.w1t.quad (challengeOf (sqCv R.cv1t)))
    (hzD : ∀ i < 42, osPtSrc cfg.nFolds (cfg.levels.headD default).folds cfg.yrLog (OsRun.tch cfg) i = none →
      R.D.ent i = 0) (hnq : ∀ lv ∈ cfg.levels, lv.queries < 2 ^ 128)
    (hσ : ∀ j < (osBodyVals cfg R).length, σ (.n j) = (osBodyVals cfg R).getD j 0)
    (hm : OsBodyMem rd σ cfg R)
    {CA CB Csq : ℕ → CallRel} (hcH : OsLvsCallH CA CB Csq cfg R.xs R.cur R.P R.sqz R.rew 0 2 (osW0 R.target R.xs)
      (R.roots0 cfg) R.Hs)
    {CT : CallRel} (hcT : ∀ (cv' : Digest) (p' : ℕ) (q' : List E), q'.length = 3 → p' + 2 ≤ R.xs.length →
      CT "opening_fold" [(digestScalars cv').1, (digestScalars cv').2, R.cur * gen ^ p', q'.getD 0 0, q'.getD 1 0,
        q'.getD 2 0] (osFoldRets R.xs cv' p' q' (R.cur * gen ^ p')))
    {CF : CallRel} (hcff : CF cfg.foldFinal [R.P.fmsg, R.tchv] [R.D.yat])
    (hcres : ∀ lvl < cfg.levels.length, 1 + osGw (cfg.levels.getD lvl default).queries ≠ 0 →
      CF (cfg.levels.getD lvl default).resLoop [1, osGw (cfg.levels.getD lvl default).queries, R.P.qpos,
        R.D.ba, R.D.bb, R.D.chv lvl, R.P.qw] []) :
    Stmt.HoldsList osTC rd σ (osBody cfg) False (fun rs => rs = [R.D.t, R.D.pt, osFinTot cfg R.D, R.D.yat]) ∧
      OsLvsCallsOk CA CB Csq cfg σ R.sqz R.rew 0 (osHead cfg).2 R.Hs.length ∧
      Stmt.HoldsList CT rd σ (osTail cfg.yrLog (OsRun.sL cfg)).1 True
        (fun rs => rs = [R.D.t, R.D.pt, osFinTot cfg R.D, R.D.yat]) ∧
      Stmt.HoldsList CF rd σ (osFinish cfg (OsRun.sT cfg) (OsRun.tch cfg)) False
        (fun rs => rs = [R.D.t, R.D.pt, osFinTot cfg R.D, R.D.yat]) ∧
      (σ (.n (OsRun.sL cfg).k) = osGw 5 ∧ σ (.n ((OsRun.sL cfg).k + 1)) = R.tchv) ∧
      OsFinSig σ cfg (OsRun.sT cfg) (OsRun.tch cfg) R.D := by
  have h := osBody_completeC (CM := CompModel.deployed) (Ht := blake2sBytes) (rd := rd) (σ := σ) (CA := CA) (CB := CB)
    (Csq := Csq) (CT := CT) (CF := CF) hok hx2 hHs rfl rfl ((osChainC_deployed _ _ _ _ _ _ _).mpr hch)
    (by rw [osRunWTW_blake, osRunEndLW_blake]; exact hrunT)
    (by rw [osRunWTW_blake, osRunEndLW_blake]; exact ansRun_blake _ _) rfl hDt hzD hnq
    (by rw [osBodyValsW_blake]; exact hσ) (osBodyMemW_blake.mpr hm) (osLvsCallHC_of_deployed _ _ _ _ _ hcH)
    (fun cv' p' q' a b _ => hcT cv' p' q' a b) hcff hcres
  simp only [show CompModel.deployed.sem = blakeDeployed from rfl, holdsListB_deployed] at h
  exact h

/-- The deployed `os_open_inv`, from the generic one. -/
theorem os_open_inv_of_comp {cfg : OsCfg} {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall)
    {target : E} {cv cv' : Digest} {xs : List E} {os : List Opening} {root : Digest}
    {roots' : List (Digest × ℕ × ℕ)} {w : WhirEnd}
    (h : RunsWith (whirOpen μ r target) cv xs os [(root, stackShape μ r)] w cv' roots') :
    2 ≤ xs.length ∧ ∃ Hs : List OsLvH, Hs.length = cfg.levels.length ∧
      OsChain cfg μ (cfg.lv 0).folds xs Lall w ⟨cv', [], [], roots'⟩
        (queriesOf (whirOpen μ r target) ⟨cv, xs, os, [(root, stackShape μ r)]⟩) 0
        (obsCv (obsCv cv (xs.getD 0 0)) (xs.getD 1 0)) 2 (osW0 target xs) os
        [(root, (cfg.lv 0).depth, 2 ^ (cfg.lv 0).folds)] Hs := by
  have h' : RunsWithM CompModel.deployed.hm (whirOpen μ r target) cv xs os [(root, stackShape μ r)] w cv' roots' :=
    runsWithM_deployed.mpr h
  obtain ⟨h2, -, -, Hs, hl, hch⟩ := os_open_invC (M := CompModel.deployed.hm) (Ht := blake2sBytes) hok
    (fun x d h => (Option.some.inj h).symm) h'
  rw [queriesOfW_blake] at hch
  exact ⟨h2, Hs, hl, (osChainC_deployed _ _ _ _ _ _ _).mp hch⟩

/-- The deployed `os_tailOpen_inv`, from the generic one. -/
theorem os_tailOpen_inv_of_comp {ml lane : ℕ} (hml : 1 ≤ ml) {s : WhirState} {res : List E} {st : St} {e : WhirEnd}
    {st' : St} (h : Runs (osTailOpen ml lane s res) st e st') :
    ∃ (w1 : WhirState) (chs : List E) (st1 : St),
      Runs (foldRounds (ml - 1) ⟨s.target, s.quad, [], []⟩ []) st (w1, chs) st1 ∧
      e = ⟨(s.folds ++ (chs ++ [challengeOf (sqCv st1.cv)])).drop lane ++
          (s.folds ++ (chs ++ [challengeOf (sqCv st1.cv)])).take lane,
        s.glued.foldl (fun w c ↦ w + c.scalar * c.weightAt (s.folds.drop c.foldStart ++
          (chs ++ [challengeOf (sqCv st1.cv)]))) 0,
        multilinearEval res (chs ++ [challengeOf (sqCv st1.cv)]),
        polyEval w1.quad (challengeOf (sqCv st1.cv))⟩ ∧
      st' = { st1 with cv := sqCv st1.cv } := by
  obtain ⟨w1, chs, st1, hr, -, -, he, hs⟩ := os_tailOpen_invC (M := CompModel.deployed.hm) (Ht := blake2sBytes) hml h
    (ansRun_blake _ _)
  exact ⟨w1, chs, st1, hr, he, hs⟩

end Recover

end
end LeanVM.Guest.B1
