/-
  LeanVM.Guest.B1.Comp.Whir.StackedChainC

  The stacked opening's levels' data over a completeness model: each level's data over a total
  hash `Ht`, and what the model answers at it.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.StackedAns

/-!
# The levels' data, answered (TRIAGE #36)

`OsLvAns M Ht …`: what the model answers at a level, in closed form over `Ht`: its fold rounds'
run (`AnsRun`), the residual's absorbs or the next commitment's two reads, the out-of-domain
sample's squeezes and three reads, the proof of work's three hashes, the positions' and `lam`'s
squeezes, the openings, the queries' intro. `os_level_invC`: `os_level_invW` with the level's run
answered gives its data `OsLvOkW` and `OsLvAns`, and the rest of the run answered from the level's
end. `OsChainC` (`OsChainW` with `OsLvAns` at each level and the tail's run answered),
`os_chain_of_runC`, `os_open_invC` (from a run the model answers, `RunsWithM`), `os_chain_tailC`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

section Ans

variable (M : HashModel) (Ht : Bytes → Digest) (cfg : OsCfg) (lvl : ℕ) (xs : List E) (p : ℕ)

/-- **What the model answers at level `lvl`** from `p` words, in closed form over `Ht`. -/
structure OsLvAns (L : Whir.Level) (cv : Digest) (w : WhirState) (osp : List Opening)
    (roots : List (Digest × ℕ × ℕ)) (H : OsLvH) : Prop where
  folds : AnsRun M.H Ht (foldRounds L.fold w []) ⟨cv, xs.drop p, osp, roots⟩
  last : lvl = cfg.yrLevel → obsAllM M H.cv1 (osHMs cfg lvl xs p) = some (obsAllW Ht H.cv1 (osHMs cfg lvl xs p))
  r0 : lvl ≠ cfg.yrLevel → obsCvM M H.cv1 (osHW cfg lvl xs p 0) = some (obsCvW Ht H.cv1 (osHW cfg lvl xs p 0))
  r1 : lvl ≠ cfg.yrLevel → obsCvM M (obsCvW Ht H.cv1 (osHW cfg lvl xs p 0)) (osHW cfg lvl xs p 1) =
    some (osHCv12W Ht cfg lvl xs p H.cv1)
  ood : lvl ≠ cfg.yrLevel → sqAllM M (cfg.lv lvl).logCols (osHCv12W Ht cfg lvl xs p H.cv1) =
    some (sqAllW Ht (cfg.lv lvl).logCols (osHCv12W Ht cfg lvl xs p H.cv1))
  ry : lvl ≠ cfg.yrLevel → obsCvM M (sqAllW Ht (cfg.lv lvl).logCols (osHCv12W Ht cfg lvl xs p H.cv1)).2
    (osHW cfg lvl xs p 2) = some (obsCvW Ht (sqAllW Ht (cfg.lv lvl).logCols (osHCv12W Ht cfg lvl xs p H.cv1)).2
      (osHW cfg lvl xs p 2))
  rc0 : lvl ≠ cfg.yrLevel → obsCvM M (obsCvW Ht (sqAllW Ht (cfg.lv lvl).logCols (osHCv12W Ht cfg lvl xs p H.cv1)).2
    (osHW cfg lvl xs p 2)) (osHW cfg lvl xs p 3) = some (obsCvW Ht (obsCvW Ht
      (sqAllW Ht (cfg.lv lvl).logCols (osHCv12W Ht cfg lvl xs p H.cv1)).2 (osHW cfg lvl xs p 2)) (osHW cfg lvl xs p 3))
  rc2 : lvl ≠ cfg.yrLevel → obsCvM M (obsCvW Ht (obsCvW Ht
    (sqAllW Ht (cfg.lv lvl).logCols (osHCv12W Ht cfg lvl xs p H.cv1)).2 (osHW cfg lvl xs p 2)) (osHW cfg lvl xs p 3))
    (osHW cfg lvl xs p 4) = some (obsCvW Ht (obsCvW Ht (obsCvW Ht
      (sqAllW Ht (cfg.lv lvl).logCols (osHCv12W Ht cfg lvl xs p H.cv1)).2 (osHW cfg lvl xs p 2)) (osHW cfg lvl xs p 3))
      (osHW cfg lvl xs p 4))
  base : M.H (digestBytes (osHCv2W Ht cfg lvl xs p H.cv1) ++ blockOf 0 3) =
    some (Ht (digestBytes (osHCv2W Ht cfg lvl xs p H.cv1) ++ blockOf 0 3))
  gc : M.H (digestBytes (Ht (digestBytes (osHCv2W Ht cfg lvl xs p H.cv1) ++ blockOf 0 3)) ++
    blockOf (osHNonce cfg lvl xs p) 4) = some (gcDigestW Ht (osHCv2W Ht cfg lvl xs p H.cv1) (osHNonce cfg lvl xs p))
  nonce : M.H (digestBytes (osHCv2W Ht cfg lvl xs p H.cv1) ++ blockOf (osHNonce cfg lvl xs p) 4) =
    some (osHCv3W Ht cfg lvl xs p H.cv1)
  sq : sqAllM M (cfg.lv lvl).squeezes (osHCv3W Ht cfg lvl xs p H.cv1) =
    some (sqAllW Ht (cfg.lv lvl).squeezes (osHCv3W Ht cfg lvl xs p H.cv1))
  lam : sqCvM M (osHCv4W Ht cfg lvl xs p H.cv1) = some (sqCvW Ht (osHCv4W Ht cfg lvl xs p H.cv1))
  open_ : ∀ rt hh ww, (osHRootsEnd cfg lvl roots H)[lvl]? = some (rt, hh, ww) →
    OpenAns M.H Ht rt hh ww (osHQsW Ht cfg lvl xs p H.cv1) osp
  c0 : obsCvM M (sqCvW Ht (osHCv4W Ht cfg lvl xs p H.cv1)) (osHC cfg lvl xs p 0) =
    some (obsCvW Ht (sqCvW Ht (osHCv4W Ht cfg lvl xs p H.cv1)) (osHC cfg lvl xs p 0))
  c2 : obsCvM M (obsCvW Ht (sqCvW Ht (osHCv4W Ht cfg lvl xs p H.cv1)) (osHC cfg lvl xs p 0)) (osHC cfg lvl xs p 1) =
    some (osHCvEndW Ht cfg lvl xs p H.cv1)

end Ans

variable {M : HashModel} {Ht : Bytes → Digest}

/-- **A level of the run, inverted, answered** (`os_level_invW`): the level's data, what the model
answers at it, and the rest of the run, answered, from the level's end. -/
theorem os_level_invC {cfg : OsCfg} {μ lane lvl : ℕ} {L : Whir.Level} {rest : List Whir.Level}
    (hspec : LvSpec cfg μ lvl L rest) {w : WhirState} (hfl : w.folds.length = (cfg.lv lvl).foldsOff)
    {cv : Digest} {xs : List E} {p : ℕ} {osp : List Opening} {roots : List (Digest × ℕ × ℕ)}
    (hrl : lvl < roots.length) {e : WhirEnd} {sp' : St}
    (h : RunsW Ht (whirLevelsOpen μ lane lvl (L :: rest) w) ⟨cv, xs.drop p, osp, roots⟩ e sp')
    (hA : AnsRun M.H Ht (whirLevelsOpen μ lane lvl (L :: rest) w) ⟨cv, xs.drop p, osp, roots⟩) :
    ∃ H : OsLvH, OsLvOkW Ht cfg lvl xs p μ L cv w osp roots H ∧ OsLvAns M Ht cfg lvl xs p L cv w osp roots H ∧
      (rest = [] → AnsRun M.H Ht (osTailOpen (μ - osLevelF cfg lvl) lane (osHWEndW Ht cfg lvl xs p H) (osHMs cfg lvl xs p))
        ⟨osHCvEndW Ht cfg lvl xs p H.cv1, xs.drop (osHPEnd cfg lvl p), H.osq, roots⟩) ∧
      (rest ≠ [] → AnsRun M.H Ht (whirLevelsOpen μ lane (lvl + 1) rest (osHWEndW Ht cfg lvl xs p H))
        ⟨osHCvEndW Ht cfg lvl xs p H.cv1, xs.drop (osHPEnd cfg lvl p), H.osq, osHRootsEnd cfg lvl roots H⟩) ∧
      (rest = [] → RunsW Ht (osTailOpen (μ - osLevelF cfg lvl) lane (osHWEndW Ht cfg lvl xs p H) (osHMs cfg lvl xs p))
        ⟨osHCvEndW Ht cfg lvl xs p H.cv1, xs.drop (osHPEnd cfg lvl p), H.osq, roots⟩ e sp') ∧
      (rest ≠ [] → RunsW Ht (whirLevelsOpen μ lane (lvl + 1) rest (osHWEndW Ht cfg lvl xs p H))
        ⟨osHCvEndW Ht cfg lvl xs p H.cv1, xs.drop (osHPEnd cfg lvl p), H.osq, osHRootsEnd cfg lvl roots H⟩ e sp') ∧
      ∃ rt hh ww, (osHRootsEnd cfg lvl roots H)[lvl]? = some (rt, hh, ww) ∧
        (rest = [] → queriesOfW Ht (whirLevelsOpen μ lane lvl (L :: rest) w) ⟨cv, xs.drop p, osp, roots⟩ =
          (hh, (osHQsW Ht cfg lvl xs p H.cv1).zip osp) ::
            queriesOfW Ht (osTailOpen (μ - osLevelF cfg lvl) lane (osHWEndW Ht cfg lvl xs p H) (osHMs cfg lvl xs p))
              ⟨osHCvEndW Ht cfg lvl xs p H.cv1, xs.drop (osHPEnd cfg lvl p), H.osq, roots⟩) ∧
        (rest ≠ [] → queriesOfW Ht (whirLevelsOpen μ lane lvl (L :: rest) w) ⟨cv, xs.drop p, osp, roots⟩ =
          (hh, (osHQsW Ht cfg lvl xs p H.cv1).zip osp) ::
            queriesOfW Ht (whirLevelsOpen μ lane (lvl + 1) rest (osHWEndW Ht cfg lvl xs p H))
              ⟨osHCvEndW Ht cfg lvl xs p H.cv1, xs.drop (osHPEnd cfg lvl p), H.osq, osHRootsEnd cfg lvl roots H⟩) := by
  obtain ⟨hf, hf0, hq, hml0, hml1, hlc, hdep, hgr, hper, hs1, hs2, hs3, hs4, hdig, hcd1, hcd2, hb1,
    hb2, hb4, hb5, hnq, hb6, hlast, hyr, hnext⟩ := hspec
  rw [os_whirLevelsOpen_cons] at h hA
  obtain ⟨⟨w1, chs⟩, s1, h1, h2⟩ := os_inv_bindW h
  obtain ⟨aF, hA2⟩ := AnsRun.bind_inv _ _ hA h1
  obtain ⟨e1, e2, e3, e4⟩ := os_foldRounds_stW h1
  obtain ⟨cv1, st1, op1, ro1⟩ := s1
  simp only at e1 e2 e3
  subst e1 e2 e3
  have hl1 := os_foldRounds_lenW _ _ _ _ _ _ h1
  obtain ⟨chs', hF1, hF2, hFl⟩ := os_foldRounds_foldsW h1
  simp only [List.nil_append] at hF1 hF2 hl1
  subst hF2
  have hw1l : w1.folds.length = osLevelF cfg lvl := by rw [hl1, hfl, osLevelF, hf]
  have hml : μ - w1.folds.length = (cfg.lv lvl).logCols := by rw [hw1l, hlc]
  dsimp only at h2 hA2
  rw [hml] at h2 hA2
  obtain ⟨⟨res, pend⟩, s2, h3, h4⟩ := os_inv_bindW h2
  obtain ⟨aM, hA3⟩ := AnsRun.bind_inv _ _ hA2 h3
  have h3o := h3
  have hd' : (cfg.lv lvl).logCols + L.logInvRate = (cfg.lv lvl).depth := by rw [hdep, hlc]
  have eP1 : osHP1 cfg lvl p = p + 2 * L.fold := by simp only [osHP1, hf]
  have hfolds : w1.folds = w.folds ++ chs ∧ chs.length = (cfg.lv lvl).folds := by
    refine ⟨hF1, ?_⟩
    have := congrArg List.length hF1
    simp only [List.length_append] at this
    omega
  cases rest with
  | nil =>
    have hyl : lvl = cfg.yrLevel := hlast.mp rfl
    have hyr' : cfg.yrLen = 2 ^ (cfg.lv lvl).logCols := by rw [hyr rfl, hlc]
    simp only [osLevelMid] at h3 aM
    obtain ⟨res', sM, hM, hM2⟩ := os_inv_bindW h3
    obtain ⟨aR, -⟩ := AnsRun.bind_inv _ _ aM hM
    have eR := ansRun_readN hM aR
    obtain ⟨hb, rfl⟩ := os_inv_pureW hM2
    simp only [Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    obtain ⟨hmsl, r, hsM, rfl⟩ := os_inv_readNW hM
    simp only at hsM
    obtain ⟨hms, hr, hlenM⟩ := os_drop_append hsM
    subst hr
    have eP2 : p + 2 * L.fold + res.length = osHP2 cfg lvl p := by
      rw [osHP2, eP1, ite_pos' hyl, hmsl, hyr']
    have eMs : res = osHMs cfg lvl xs p := by rw [osHMs, eP1, hyr', ← hmsl]; exact hms
    have eCv2 : obsAllW Ht cv1 res = osHCv2W Ht cfg lvl xs p cv1 := by rw [osHCv2W, ite_pos' hyl, eMs]
    rw [eP2, eCv2] at h4 h3o hA3
    simp only at h4 hA3
    obtain ⟨w', s3, h5, h6⟩ := os_inv_bindW h4
    obtain ⟨aQ, hA4⟩ := AnsRun.bind_inv _ _ hA3 h5
    obtain ⟨⟨g1, g2, g3⟩, eSq, eLam, eOpen, eC0, eC2⟩ :=
      os_lq_ansC (M := M) (nsq := (cfg.lv lvl).squeezes) hd' hq.symm hper hs1 hs2 hs3 h5 aQ
    obtain ⟨hlen, hpow, rows, osq, rt, hh, ww, hro, hoa, rfl, rfl, hqs⟩ := os_lq_invW (nsq := (cfg.lv lvl).squeezes)
      hd' hq.symm hper hs1 hs2 hs3 h5
    have hqo := os_qOf_levelW (lane := lane) h1 hml h3o h5
    refine ⟨⟨w1, chs, cv1, default, rows, osq⟩, ⟨by rw [eP1]; exact h1, hlen, fun h' => absurd hyl h', hpow,
      ⟨rt, hh, ww, by simp only [osHRootsEnd, ite_pos' hyl]; exact hro, hoa⟩, hw1l, hfolds⟩,
      ⟨aF, fun _ => by rw [← eMs]; exact eR, fun h' => absurd hyl h', fun h' => absurd hyl h',
        fun h' => absurd hyl h', fun h' => absurd hyl h', fun h' => absurd hyl h', fun h' => absurd hyl h',
        g1, g2, g3, eSq, eLam, fun rt' hh' ww' hr' => eOpen rt' hh' ww' (by
          simpa only [osHRootsEnd, ite_pos' hyl] using hr'), eC0, eC2⟩, fun _ => ?_,
      fun h' => absurd rfl h', fun _ => ?_,
      fun h' => absurd rfl h', rt, hh, ww, by simp only [osHRootsEnd, ite_pos' hyl]; exact hro, fun _ => ?_,
      fun h' => absurd rfl h'⟩
    · rw [← eMs, ← hlc]
      convert hA4 using 2
      all_goals try rfl
      simp only [osHWEndW, osHPendingW, ite_pos' hyl, List.nil_append, osHEnfW, osHRowsE, osHQsW, osHLamW, osHCv4W,
        osHCv3W, osHNonce, osHC]
    · rw [← eMs, ← hlc]
      convert h6 using 2
      all_goals try rfl
      simp only [osHWEndW, osHPendingW, ite_pos' hyl, List.nil_append, osHEnfW, osHRowsE, osHQsW, osHLamW, osHCv4W,
        osHCv3W, osHNonce, osHC]
    · rw [hqo, hqs, List.singleton_append, ← eMs, ← hlc]
      congr 2
      simp only [osHWEndW, osHPendingW, ite_pos' hyl, List.nil_append, osHEnfW, osHRowsE, osHQsW, osHLamW, osHCv4W,
        osHCv3W, osHNonce, osHC]
  | cons next rest' =>
    have hyl : lvl ≠ cfg.yrLevel := fun h' => absurd (hlast.mpr h') (by simp)
    obtain ⟨hood, hfo', hfl', hdep'⟩ := hnext next rfl
    simp only [osLevelMid, levelShape] at h3 aM
    obtain ⟨u, sA, hAc, h3⟩ := os_inv_bindW h3
    obtain ⟨aC1, aM⟩ := AnsRun.bind_inv _ _ aM hAc
    obtain ⟨x0, x1, rA, root, hsA, hroot, rfl⟩ := os_inv_commitPW hAc
    simp only at hsA
    rw [hsA] at aC1
    obtain ⟨eX0, eX1⟩ := ansRun_commitP aC1
    obtain ⟨hx0, hx1, rfl⟩ := os_drop_cons2 hsA
    obtain ⟨z, sB, hB, h3⟩ := os_inv_bindW h3
    obtain ⟨aB, aM⟩ := AnsRun.bind_inv _ _ aM hB
    have eB := ansRun_sampleN aB
    obtain ⟨rfl, rfl⟩ := os_inv_sampleNW hB
    obtain ⟨y, sC, hC, h3⟩ := os_inv_bindW h3
    obtain ⟨aCy, aM⟩ := AnsRun.bind_inv _ _ aM hC
    obtain ⟨rC, hsC, rfl⟩ := os_inv_readEW hC
    simp only at hsC
    rw [hsC] at aCy
    have eY := ansRun_readE aCy
    obtain ⟨hy, rfl⟩ := os_drop_cons hsC
    obtain ⟨intro, sD, hD, h3⟩ := os_inv_bindW h3
    obtain ⟨aD, -⟩ := AnsRun.bind_inv _ _ aM hD
    obtain ⟨c0o, c2o, rD, hsD, rfl, rfl⟩ := os_inv_roundPoly3W hD
    simp only at hsD
    rw [hsD] at aD
    obtain ⟨eC0o, eC2o⟩ := ansRun_roundPoly3 aD
    obtain ⟨hc0, hc2, rfl⟩ := os_drop_cons2 hsD
    obtain ⟨hb, rfl⟩ := os_inv_pureW h3
    simp only [Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    have eW : ∀ i, osHW cfg lvl xs p i = xs.getD (p + 2 * L.fold + i) 0 := fun i => by rw [osHW, eP1]
    have e0 : x0 = osHW cfg lvl xs p 0 := by rw [eW, Nat.add_zero, hx0]
    have e1 : x1 = osHW cfg lvl xs p 1 := by rw [eW, hx1]
    have e2 : y = osHW cfg lvl xs p 2 := by rw [eW, ← hy]
    have e3 : c0o = osHW cfg lvl xs p 3 := by rw [eW, ← hc0]
    have e4 : c2o = osHW cfg lvl xs p 4 := by rw [eW, ← hc2]
    have eP2 : p + 2 * L.fold + 2 + 1 + 2 = osHP2 cfg lvl p := by rw [osHP2, eP1, ite_neg' hyl]
    have eCv2 : obsCvW Ht (obsCvW Ht (obsCvW Ht (sqAllW Ht (cfg.lv lvl).logCols (obsCvW Ht (obsCvW Ht cv1 x0) x1)).2 y) c0o) c2o =
        osHCv2W Ht cfg lvl xs p cv1 := by rw [osHCv2W, ite_neg' hyl, osHCv12W, e0, e1, e2, e3, e4]
    have e12 : obsCvW Ht (obsCvW Ht cv1 x0) x1 = osHCv12W Ht cfg lvl xs p cv1 := by rw [osHCv12W, e0, e1]
    rw [eP2, eCv2] at h4 h3o hA3
    simp only at h4 hA3
    obtain ⟨w', s3, h5, h6⟩ := os_inv_bindW h4
    obtain ⟨aQ, hA4⟩ := AnsRun.bind_inv _ _ hA3 h5
    obtain ⟨⟨g1, g2, g3⟩, eSq, eLam, eOpen, eC0, eC2⟩ :=
      os_lq_ansC (M := M) (nsq := (cfg.lv lvl).squeezes) hd' hq.symm hper hs1 hs2 hs3 h5 aQ
    obtain ⟨hlen, hpow, rows, osq, rt, hh, ww, hro, hoa, rfl, rfl, hqs⟩ := os_lq_invW (nsq := (cfg.lv lvl).squeezes)
      hd' hq.symm hper hs1 hs2 hs3 h5
    have hqo := os_qOf_levelW (lane := lane) h1 hml h3o h5
    have eRoots : ro1 ++ [(root, (cfg.lv lvl).logCols - next.fold + next.logInvRate, 3 * 2 ^ next.fold)] =
        osHRootsEnd cfg lvl ro1 ⟨w1, chs, cv1, root, rows, osq⟩ := by
      rw [osHRootsEnd, ite_neg' hyl, hdep', hfl', hlc]
    refine ⟨⟨w1, chs, cv1, root, rows, osq⟩, ⟨by rw [eP1]; exact h1, hlen, fun _ => by rw [← e0, ← e1]; exact hroot,
      hpow, ⟨rt, hh, ww, by rw [← eRoots]; exact hro, hoa⟩, hw1l, hfolds⟩,
      ⟨aF, fun h' => absurd h' hyl, fun _ => by rw [← e0]; exact eX0, fun _ => by rw [← e12, ← e0, ← e1]; exact eX1,
        fun _ => by rw [← e12]; exact eB, fun _ => by rw [← e12, ← e2]; exact eY,
        fun _ => by rw [← e12, ← e2, ← e3]; exact eC0o, fun _ => by rw [← e12, ← e2, ← e3, ← e4]; exact eC2o,
        g1, g2, g3, eSq, eLam, fun rt' hh' ww' hr' => eOpen rt' hh' ww' (by rw [← eRoots] at hr'; exact hr'),
        eC0, eC2⟩, fun h' => absurd h' (by simp), fun _ => ?_, fun h' => absurd h' (by simp),
      fun _ => ?_, rt, hh, ww, by rw [← eRoots]; exact hro, fun h' => absurd h' (by simp), fun _ => ?_⟩
    · rw [← eRoots]
      convert hA4 using 2
      all_goals try rfl
      simp only [osHWEndW, osHPendingW, ite_neg' hyl, osHEnfW, osHRowsE, osHQsW, osHLamW, osHCv4W, osHCv3W,
        osHNonce, osHC, osHCv12W, ← e0, ← e1, ← e2, ← e3, ← e4, List.singleton_append]
    · rw [← eRoots]
      convert h6 using 2
      all_goals try rfl
      simp only [osHWEndW, osHPendingW, ite_neg' hyl, osHEnfW, osHRowsE, osHQsW, osHLamW, osHCv4W, osHCv3W,
        osHNonce, osHC, osHCv12W, ← e0, ← e1, ← e2, ← e3, ← e4, List.singleton_append]
    · rw [hqo, hqs, List.singleton_append, ← eRoots]
      congr 2
      simp only [osHWEndW, osHPendingW, ite_neg' hyl, osHEnfW, osHRowsE, osHQsW, osHLamW, osHCv4W, osHCv3W,
        osHNonce, osHC, osHCv12W, ← e0, ← e1, ← e2, ← e3, ← e4, List.singleton_append]

/-- The levels' data from level `lvl` on, each from where the previous one ends, the last one's
tail running to `e`, `sp'`. -/
def OsChainC (M : HashModel) (Ht : Bytes → Digest) (cfg : OsCfg) (μ lane : ℕ) (xs : List E) (Lall : List Whir.Level) (e : WhirEnd) (sp' : St)
    (Q : List (ℕ × List (ℕ × Opening))) :
    ℕ → Digest → ℕ → WhirState → List Opening → List (Digest × ℕ × ℕ) → List OsLvH → Prop
  | _, _, _, _, _, _, [] => False
  | lvl, cv, p, w, osp, roots, H :: Hs =>
    OsLvOkW Ht cfg lvl xs p μ (Lall.getD lvl default) cv w osp roots H ∧
      OsLvAns M Ht cfg lvl xs p (Lall.getD lvl default) cv w osp roots H ∧
      (∃ rt, roots[lvl]? = some (rt, (cfg.lv lvl).depth, oqR (if lvl = 0 then 1 else 0) (2 ^ (cfg.lv lvl).folds)) ∧
        ((cfg.lv lvl).depth, (osHQsW Ht cfg lvl xs p H.cv1).zip osp) ∈ Q) ∧
      (lvl = cfg.yrLevel → Hs = [] ∧
        RunsW Ht (osTailOpen (μ - osLevelF cfg lvl) lane (osHWEndW Ht cfg lvl xs p H) (osHMs cfg lvl xs p))
          ⟨osHCvEndW Ht cfg lvl xs p H.cv1, xs.drop (osHPEnd cfg lvl p), H.osq, roots⟩ e sp' ∧
        AnsRun M.H Ht (osTailOpen (μ - osLevelF cfg lvl) lane (osHWEndW Ht cfg lvl xs p H) (osHMs cfg lvl xs p))
          ⟨osHCvEndW Ht cfg lvl xs p H.cv1, xs.drop (osHPEnd cfg lvl p), H.osq, roots⟩) ∧
      (lvl ≠ cfg.yrLevel → OsChainC M Ht cfg μ lane xs Lall e sp' Q (lvl + 1) (osHCvEndW Ht cfg lvl xs p H.cv1)
        (osHPEnd cfg lvl p) (osHWEndW Ht cfg lvl xs p H) H.osq (osHRootsEnd cfg lvl roots H) Hs)


/-- **The levels' data**: a run of `whirLevelsOpen` from level `lvl`, at the state the guest's
invariant names, has the levels' data. -/
theorem os_chain_of_runC {cfg : OsCfg} {μ lane : ℕ} {Lall : List Whir.Level}
    (hlen : Lall.length = cfg.levels.length)
    (hspec : ∀ i < Lall.length, LvSpec cfg μ i (Lall.getD i default) (Lall.drop (i + 1)))
    (hyl : cfg.yrLevel = cfg.levels.length - 1) {xs : List E} {e : WhirEnd} {sp' : St}
    {Q : List (ℕ × List (ℕ × Opening))} :
    ∀ (j lvl : ℕ) (cv : Digest) (p : ℕ) (w : WhirState) (osp : List Opening) (roots : List (Digest × ℕ × ℕ)),
      lvl + j + 1 = Lall.length → w.folds.length = (cfg.lv lvl).foldsOff → roots.length = lvl + 1 →
      (∃ rt, roots[lvl]? = some (rt, (cfg.lv lvl).depth, oqR (if lvl = 0 then 1 else 0) (2 ^ (cfg.lv lvl).folds))) →
      (∀ b ∈ queriesOfW Ht (whirLevelsOpen μ lane lvl (Lall.drop lvl) w) ⟨cv, xs.drop p, osp, roots⟩, b ∈ Q) →
      RunsW Ht (whirLevelsOpen μ lane lvl (Lall.drop lvl) w) ⟨cv, xs.drop p, osp, roots⟩ e sp' →
      AnsRun M.H Ht (whirLevelsOpen μ lane lvl (Lall.drop lvl) w) ⟨cv, xs.drop p, osp, roots⟩ →
      ∃ Hs : List OsLvH, Hs.length = j + 1 ∧ OsChainC M Ht cfg μ lane xs Lall e sp' Q lvl cv p w osp roots Hs := by
  have hstep : ∀ {lvl : ℕ} {roots : List (Digest × ℕ × ℕ)} {H : OsLvH} {rt rt' : Digest} {hh ww : ℕ} {osq : List Opening},
      lvl < roots.length → roots[lvl]? = some (rt, (cfg.lv lvl).depth, oqR (if lvl = 0 then 1 else 0) (2 ^ (cfg.lv lvl).folds)) →
      (osHRootsEnd cfg lvl roots H)[lvl]? = some (rt', hh, ww) → hh = (cfg.lv lvl).depth := by
    intro lvl roots H rt rt' hh ww osq hl h1 h2
    have : (osHRootsEnd cfg lvl roots H)[lvl]? = roots[lvl]? := by
      unfold osHRootsEnd; split
      · rfl
      · exact List.getElem?_append_left hl
    rw [this, h1] at h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    exact h2.2.1.symm
  intro j
  induction j with
  | zero =>
    intro lvl cv p w osp roots hj hfl hrl hrt hQ h hA
    have hl : lvl < Lall.length := by omega
    have hs := hspec lvl hl
    have hLrest : Lall.drop (lvl + 1) = [] := List.drop_eq_nil_of_le (by omega)
    rw [hLrest] at hs
    rw [List.drop_eq_getElem_cons hl, show Lall[lvl] = Lall.getD lvl default by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl], hLrest] at h hA
    have hq0 := hQ
    rw [List.drop_eq_getElem_cons hl, show Lall[lvl] = Lall.getD lvl default by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl], hLrest] at hq0
    obtain ⟨H, hok, hans, htailA, -, htail, -, rt', hh, ww, hrt', hqe, -⟩ := os_level_invC hs hfl (by omega) h hA
    have hy : lvl = cfg.yrLevel := by rw [hyl]; omega
    obtain ⟨rt, hrt⟩ := hrt
    have hhd := hstep (H := H) (osq := []) (by omega) hrt hrt'
    subst hhd
    refine ⟨[H], rfl, hok, hans, ⟨rt, hrt, hq0 _ ?_⟩, fun _ => ⟨rfl, htail rfl, htailA rfl⟩, fun h' => absurd hy h'⟩
    rw [hqe rfl]; exact List.mem_cons_self
  | succ j ih =>
    intro lvl cv p w osp roots hj hfl hrl hrt hQ h hA
    have hl : lvl < Lall.length := by omega
    have hs := hspec lvl hl
    rw [List.drop_eq_getElem_cons hl, show Lall[lvl] = Lall.getD lvl default by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]] at h hA
    have hl1 : lvl + 1 < Lall.length := by omega
    have hcons : Lall.drop (lvl + 1) = Lall.getD (lvl + 1) default :: Lall.drop (lvl + 2) := by
      rw [List.drop_eq_getElem_cons hl1]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl1]
    have hq0 := hQ
    rw [List.drop_eq_getElem_cons hl, show Lall[lvl] = Lall.getD lvl default by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]] at hq0
    obtain ⟨H, hok, hans, -, hnextA, -, hnext, rt', hh, ww, hrt', -, hqe⟩ := os_level_invC hs hfl (by omega) h hA
    have hny : lvl ≠ cfg.yrLevel := by rw [hyl]; omega
    have hne : Lall.drop (lvl + 1) ≠ [] := by rw [hcons]; simp
    have hqe' := hqe hne
    obtain ⟨rt, hrt⟩ := hrt
    have hhd := hstep (H := H) (osq := []) (by omega) hrt hrt'
    subst hhd
    have hs' := hs
    rw [hcons] at hs'
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hnx⟩ := hs'
    obtain ⟨-, hfo', -, -⟩ := hnx _ rfl
    obtain ⟨Hs, hHl, hch⟩ := ih (lvl + 1) _ _ _ _ _ (by omega)
      (by rw [osHWEndW, os_glue_folds', hok.w1len, hfo'])
      (by rw [osHRootsEnd, ite_neg' hny, List.length_append, hrl]; rfl)
      ⟨H.root, by
        rw [osHRootsEnd, ite_neg' hny, List.getElem?_append_right (by omega), hrl, Nat.sub_self]
        simp [oqR]⟩
      (fun b hb => hq0 b (by rw [hqe']; exact List.mem_cons_of_mem _ hb))
      (hnext hne) (hnextA hne)
    refine ⟨H :: Hs, by simp [hHl], hok, hans, ⟨rt, hrt, hq0 _ ?_⟩, fun h' => absurd h' hny, fun _ => hch⟩
    rw [hqe']; exact List.mem_cons_self



/-- **The opening's run, inverted at the head**. -/
theorem os_open_invC {cfg : OsCfg} {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall)
    {target : E} {cv cv' : Digest} {xs : List E} {os : List Opening} {root : Digest}
    {roots' : List (Digest × ℕ × ℕ)} {w : WhirEnd}
    (hHt : ∀ x d, M.H x = some d → d = Ht x)
    (h : RunsWithM M (whirOpen μ r target) cv xs os [(root, stackShape μ r)] w cv' roots') :
    2 ≤ xs.length ∧ obsCvM M cv (xs.getD 0 0) = some (obsCvW Ht cv (xs.getD 0 0)) ∧
      obsCvM M (obsCvW Ht cv (xs.getD 0 0)) (xs.getD 1 0) =
        some (obsCvW Ht (obsCvW Ht cv (xs.getD 0 0)) (xs.getD 1 0)) ∧
      ∃ Hs : List OsLvH, Hs.length = cfg.levels.length ∧
      OsChainC M Ht cfg μ (cfg.lv 0).folds xs Lall w ⟨cv', [], [], roots'⟩
        (queriesOfW Ht (whirOpen μ r target) ⟨cv, xs, os, [(root, stackShape μ r)]⟩) 0
        (obsCvW Ht (obsCvW Ht cv (xs.getD 0 0)) (xs.getD 1 0)) 2 (osW0 target xs) os
        [(root, (cfg.lv 0).depth, 2 ^ (cfg.lv 0).folds)] Hs := by
  have hr := h [] []
  simp only [List.append_nil] at hr
  obtain ⟨hr', hA⟩ := runsM_runsW hHt _ (show RunsM M (whirOpen μ r target) ⟨cv, xs, os, [(root, stackShape μ r)]⟩ w
    ⟨cv', [], [], roots'⟩ from hr)
  unfold whirOpen at hr' hA
  obtain ⟨cfg', s1, h1, h2⟩ := os_inv_bindW hr'
  obtain ⟨-, hA1⟩ := AnsRun.bind_inv _ _ hA h1
  rw [hok.config] at h1
  simp only [Verifier.liftOption] at h1
  obtain ⟨hcfg, rfl⟩ := os_inv_retW h1
  subst cfg'
  obtain ⟨q, s2, h3, h4⟩ := os_inv_bindW h2
  obtain ⟨aH, hA2⟩ := AnsRun.bind_inv _ _ hA1 h3
  obtain ⟨c0, c2, rest, hs, rfl, rfl⟩ := os_inv_roundPoly3W h3
  simp only at hs
  rw [hs] at aH
  obtain ⟨eH0, eH1⟩ := ansRun_roundPoly3 aH
  have hlen := congrArg List.length hs
  simp only [List.length_cons] at hlen
  have hx : xs.drop 0 = c0 :: c2 :: rest := by simpa using hs
  obtain ⟨e0, e1, hrest⟩ := os_drop_cons2 hx
  subst hrest
  have hq := os_queriesOf_bindW (sumcheckRoundPoly 3 target none)
    (fun quad => whirLevelsOpen μ ((Lall.head?.map (·.fold)).getD 0) 0 Lall ⟨target, quad, [], []⟩) _ h3
  rw [os_queriesOf_noQW _ (os_noQ_roundPoly3 _), List.nil_append] at hq
  have eQ : queriesOfW Ht (whirOpen μ r target) ⟨cv, xs, os, [(root, stackShape μ r)]⟩ =
      queriesOfW Ht ((sumcheckRoundPoly 3 target none).bind (fun quad =>
        whirLevelsOpen μ ((Lall.head?.map (·.fold)).getD 0) 0 Lall ⟨target, quad, [], []⟩))
        ⟨cv, xs, os, [(root, stackShape μ r)]⟩ := by
    unfold whirOpen; rw [hok.config]; rfl
  rw [hok.lane, hok.shape] at h4 hA2
  refine ⟨by omega, by rw [e0]; exact eH0, by rw [e0, e1]; exact eH1, ?_⟩
  have hn := hok.len2
  subst e0 e1
  obtain ⟨Hs, hHl, hch⟩ := os_chain_of_runC (xs := xs) (e := w) (sp' := ⟨cv', [], [], roots'⟩)
    (Q := queriesOfW Ht (whirOpen μ r target) ⟨cv, xs, os, [(root, stackShape μ r)]⟩) hok.len hok.spec
    hok.yrLevel (cfg.levels.length - 1) 0 _ 2 (osW0 target xs) os [(root, (cfg.lv 0).depth, 2 ^ (cfg.lv 0).folds)]
    (by rw [hok.len]; omega)
    (by rw [hok.off0]; rfl) rfl ⟨root, by simp [oqR]⟩ (fun b hb => by
      rw [eQ, hq, hok.lane, hok.shape]
      rw [List.drop_zero] at hb
      exact hb) (by
      rw [List.drop_zero]
      exact h4) (by
      rw [List.drop_zero]
      exact hA2)
  exact ⟨Hs, by rw [hHl]; omega, hch⟩


/-- **The last level's tail**: from the levels' data, the tail runs from where the levels end. -/
theorem os_chain_tailC {cfg : OsCfg} {μ lane : ℕ} {xs : List E} {Lall : List Whir.Level} {e : WhirEnd}
    {sp' : St} {Q : List (ℕ × List (ℕ × Opening))} : ∀ (Hs : List OsLvH) (lvl : ℕ) (cv : Digest) (p : ℕ)
      (w : WhirState) (osp : List Opening)
      (roots : List (Digest × ℕ × ℕ)), OsChainC M Ht cfg μ lane xs Lall e sp' Q lvl cv p w osp roots Hs →
      RunsW Ht (osTailOpen (μ - osLevelF cfg (osLvsLast cfg xs lvl p roots Hs).1) lane
          (osLvsEndW Ht cfg xs lvl cv p w roots Hs).2.2
          (osHMs cfg (osLvsLast cfg xs lvl p roots Hs).1 xs (osLvsLast cfg xs lvl p roots Hs).2.1))
        ⟨(osLvsEndW Ht cfg xs lvl cv p w roots Hs).1, xs.drop (osLvsEndW Ht cfg xs lvl cv p w roots Hs).2.1,
          (osLvsLast cfg xs lvl p roots Hs).2.2.2.osq, (osLvsLast cfg xs lvl p roots Hs).2.2.1⟩ e sp' ∧
      AnsRun M.H Ht (osTailOpen (μ - osLevelF cfg (osLvsLast cfg xs lvl p roots Hs).1) lane
          (osLvsEndW Ht cfg xs lvl cv p w roots Hs).2.2
          (osHMs cfg (osLvsLast cfg xs lvl p roots Hs).1 xs (osLvsLast cfg xs lvl p roots Hs).2.1))
        ⟨(osLvsEndW Ht cfg xs lvl cv p w roots Hs).1, xs.drop (osLvsEndW Ht cfg xs lvl cv p w roots Hs).2.1,
          (osLvsLast cfg xs lvl p roots Hs).2.2.2.osq, (osLvsLast cfg xs lvl p roots Hs).2.2.1⟩
  | [], _, _, _, _, _, _, h => h.elim
  | [H], lvl, cv, p, w, osp, roots, h => by
    obtain ⟨-, -, -, hl, hn⟩ := h
    by_cases hy : lvl = cfg.yrLevel
    · exact ⟨(hl hy).2.1, (hl hy).2.2⟩
    · exact (hn hy).elim
  | H :: H' :: Hs, lvl, cv, p, w, osp, roots, h => by
    obtain ⟨-, -, -, hl, hn⟩ := h
    by_cases hy : lvl = cfg.yrLevel
    · exact absurd (hl hy).1 (by simp)
    · exact os_chain_tailC (H' :: Hs) (lvl + 1) _ _ _ _ _ (hn hy)


end
end LeanVM.Guest.B1
