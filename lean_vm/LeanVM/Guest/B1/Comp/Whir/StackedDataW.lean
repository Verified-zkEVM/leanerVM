/-
  LeanVM.Guest.B1.Comp.Whir.StackedDataW

  The stacked opening's levels' data over a total hash: `Whir/StackedC5.lean`'s level data and
  inversion, `StackedC8`'s chain of levels, `StackedC10`'s tail inversion and `StackedC15`'s
  opening inversion, over `Ht`.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.StackedInvW
public import LeanVM.Guest.B1.Whir.StackedC15
public import LeanVM.Guest.B1.Whir.StackedC9

/-!
# The levels' data over a total hash (TRIAGE #36)

The level's data from the specification's run (`OsLvH`, its positions `osHP*`, the words `osHW`,
`osHMs`, `osHNonce`, `osHC`, the roots `osHRootsEnd` read nothing of the hash and are the
deployed ones); its chain states, positions, challenges and the state after it over `Ht`
(`osHCv12W`, …, `osHWEndW`), the run's facts `OsLvOkW`, the chain of levels `OsChainW`, and the
deployed inversions over `Ht` (`os_level_invW`, `os_chain_of_runW`, `os_tail_invW`,
`os_open_invW`, `os_chain_tailW`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

section Data

variable (Ht : Bytes → Digest) (cfg : OsCfg) (lvl : ℕ) (xs : List E) (p : ℕ)

/-- The chain state after the next root. -/
def osHCv12W (cv1 : Digest) : Digest := obsCvW Ht (obsCvW Ht cv1 (osHW cfg lvl xs p 0)) (osHW cfg lvl xs p 1)

/-- The chain state after the residual or the next commitment and its out-of-domain claim. -/
def osHCv2W (cv1 : Digest) : Digest :=
  if lvl = cfg.yrLevel then obsAllW Ht cv1 (osHMs cfg lvl xs p)
  else obsCvW Ht (obsCvW Ht (obsCvW Ht (sqAllW Ht (cfg.lv lvl).logCols (osHCv12W Ht cfg lvl xs p cv1)).2 (osHW cfg lvl xs p 2))
    (osHW cfg lvl xs p 3)) (osHW cfg lvl xs p 4)

/-- The chain state after the nonce. -/
def osHCv3W (cv1 : Digest) : Digest := absorbCvW Ht (osHCv2W Ht cfg lvl xs p cv1) (osHNonce cfg lvl xs p) 4

/-- The query positions. -/
def osHQsW (cv1 : Digest) : List ℕ :=
  (List.range (cfg.lv lvl).queries).map (osPosOfW Ht (cfg.lv lvl).depth (osHCv3W Ht cfg lvl xs p cv1))

/-- The chain state after the positions' squeezes. -/
def osHCv4W (cv1 : Digest) : Digest := (sqAllW Ht (cfg.lv lvl).squeezes (osHCv3W Ht cfg lvl xs p cv1)).2

/-- The batching challenge. -/
def osHLamW (cv1 : Digest) : E := challengeOf (sqCvW Ht (osHCv4W Ht cfg lvl xs p cv1))

/-- The chain state after the level. -/
def osHCvEndW (cv1 : Digest) : Digest :=
  obsCvW Ht (obsCvW Ht (sqCvW Ht (osHCv4W Ht cfg lvl xs p cv1)) (osHC cfg lvl xs p 0)) (osHC cfg lvl xs p 1)

/-- The queries' enforced sum. -/
def osHEnfW (H : OsLvH) : E :=
  enforcedSum (osHRowsE lvl H.rows) H.chs
    (powers (osHLamW Ht cfg lvl xs p H.cv1) (osHQsW Ht cfg lvl xs p H.cv1).length)

/-- The out-of-domain claim the level glues (none at the last level). -/
def osHPendingW (cv1 : Digest) : List (E × List E × (List E → E)) :=
  if lvl = cfg.yrLevel then []
  else [(osHW cfg lvl xs p 2, [osHW cfg lvl xs p 3, osHW cfg lvl xs p 2 + osHW cfg lvl xs p 4, osHW cfg lvl xs p 4],
    fun x ↦ eqEval (sqAllW Ht (cfg.lv lvl).logCols (osHCv12W Ht cfg lvl xs p cv1)).1 x)]

/-- The state after the level. -/
def osHWEndW (H : OsLvH) : WhirState :=
  glue (osHLamW Ht cfg lvl xs p H.cv1) H.w1 (osHPendingW Ht cfg lvl xs p H.cv1 ++
    [(osHEnfW Ht cfg lvl xs p H, [osHC cfg lvl xs p 0, osHEnfW Ht cfg lvl xs p H + osHC cfg lvl xs p 1, osHC cfg lvl xs p 1],
      fun x ↦ inducedWeight (cfg.lv lvl).logCols (osHQsW Ht cfg lvl xs p H.cv1)
        (powers (osHLamW Ht cfg lvl xs p H.cv1) (osHQsW Ht cfg lvl xs p H.cv1).length) x)])

/-- What the run of level `lvl` from `p` words says of its data. -/
structure OsLvOkW (μ : ℕ) (L : Whir.Level) (cv : Digest) (w : WhirState) (osp : List Opening)
    (roots : List (Digest × ℕ × ℕ)) (H : OsLvH) : Prop where
  folds : RunsW Ht (foldRounds L.fold w []) ⟨cv, xs.drop p, osp, roots⟩ (H.w1, H.chs)
    ⟨H.cv1, xs.drop (osHP1 cfg lvl p), osp, roots⟩
  len : osHPEnd cfg lvl p ≤ xs.length
  root : lvl ≠ cfg.yrLevel → digestOfScalars (osHW cfg lvl xs p 0, osHW cfg lvl xs p 1) = some H.root
  pow : powOk Whir.queryGrindingBits (osHNonce cfg lvl xs p)
    (gcDigestW Ht (osHCv2W Ht cfg lvl xs p H.cv1) (osHNonce cfg lvl xs p)) = true
  open_ : ∃ rt hh ww, (osHRootsEnd cfg lvl roots H)[lvl]? = some (rt, hh, ww) ∧
    openAll (m := Id) Ht rt hh ww (osHQsW Ht cfg lvl xs p H.cv1) osp = some (H.rows, H.osq)
  w1len : H.w1.folds.length = osLevelF cfg lvl
  chs : H.w1.folds = w.folds ++ H.chs ∧ H.chs.length = (cfg.lv lvl).folds


end Data

variable {Ht : Bytes → Digest}

theorem os_foldRounds_stW : ∀ {n : ℕ} {w : WhirState} {lf xs : List E} {p : ℕ} {cv : Digest}
    {osp : List Opening} {roots : List (Digest × ℕ × ℕ)} {res : WhirState × List E} {s' : St},
    RunsW Ht (foldRounds n w lf) ⟨cv, xs.drop p, osp, roots⟩ res s' →
      s'.stream = xs.drop (p + 2 * n) ∧ s'.openings = osp ∧ s'.roots = roots ∧
        (n = 0 ∨ p + 2 * n ≤ xs.length)
  | 0, w, lf, xs, p, cv, osp, roots, res, s', h => by
    obtain ⟨rfl, rfl⟩ := os_inv_pureW h
    exact ⟨rfl, rfl, rfl, Or.inl rfl⟩
  | n + 1, w, lf, xs, p, cv, osp, roots, res, s', h => by
    rw [foldRounds_succ] at h
    obtain ⟨⟨ch, t, q'⟩, sp1, h1, h2⟩ := os_inv_bindW h
    obtain ⟨d0, d2, rest, hs, -, hsp1⟩ := os_runs_foldStepW h1
    simp only at hs
    have hlen := congrArg List.length hs
    simp only [List.length_drop, List.length_cons] at hlen
    obtain ⟨-, -, hrest⟩ := os_drop_cons2 hs
    subst hsp1 hrest
    obtain ⟨e1, e2, e3, e4⟩ := os_foldRounds_stW h2
    refine ⟨by rw [e1]; ring_nf, e2, e3, Or.inr ?_⟩
    omega


/-! ## The inversion -/

/-- **A level's queries, inverted** (V:1737-1749): the nonce, the positions, `lam`, the openings and
the intro, from `p2` words of `xs`. -/
theorem os_lq_invW {ml idx nsq depth nq : ℕ} {L : Whir.Level} {lf : List E} {w1 : WhirState}
    {pend : List (E × List E × (List E → E))} (hdq : ml + L.logInvRate = depth) (hnq : L.queries = nq)
    (hper : 0 < 192 / depth) (hs1 : nq ≤ nsq * (192 / depth))
    (hs2 : (nsq - 1) * (192 / depth) < nq ∨ nsq = 0) (hs3 : nsq ≤ nq)
    {cv2 : Digest} {xs : List E} {p2 : ℕ} {op : List Opening} {ro : List (Digest × ℕ × ℕ)} {w' : WhirState}
    {s3 : St} (h : RunsW Ht (osLevelQueries ml idx L lf w1 pend) ⟨cv2, xs.drop p2, op, ro⟩ w' s3) :
    let n := xs.getD p2 0
    let cv3 := absorbCvW Ht cv2 n 4
    let qs := (List.range nq).map (osPosOfW Ht depth cv3)
    let cv4 := (sqAllW Ht nsq cv3).2
    let lam := challengeOf (sqCvW Ht cv4)
    let c0 := xs.getD (p2 + 1) 0
    let c2 := xs.getD (p2 + 2) 0
    p2 + 3 ≤ xs.length ∧ powOk Whir.queryGrindingBits n (gcDigestW Ht cv2 n) = true ∧
      ∃ (rows : List (List K)) (osq : List Opening) (rt : Digest) (hh ww : ℕ), ro[idx]? = some (rt, hh, ww) ∧
        openAll (m := Id) Ht rt hh ww qs op = some (rows, osq) ∧
        w' = glue lam w1 (pend ++ [(enforcedSum (if idx = 0 then rows.map fun row ↦ row.reverse.map ofK
            else rows.map extRow) lf (powers lam qs.length),
          [c0, enforcedSum (if idx = 0 then rows.map fun row ↦ row.reverse.map ofK else rows.map extRow) lf
            (powers lam qs.length) + c2, c2], fun x ↦ inducedWeight ml qs (powers lam qs.length) x)]) ∧
        s3 = ⟨obsCvW Ht (obsCvW Ht (sqCvW Ht cv4) c0) c2, xs.drop (p2 + 3), osq, ro⟩ ∧
        queriesOfW Ht (osLevelQueries ml idx L lf w1 pend) ⟨cv2, xs.drop p2, op, ro⟩ = [(hh, qs.zip op)] := by
  subst hdq hnq
  intro n cv3 qs cv4 lam c0 c2
  simp only [osLevelQueries] at h
  obtain ⟨u, sA, hA, h1⟩ := os_inv_bindW h
  obtain ⟨n', rA, hsA, hpow, rfl⟩ := os_inv_grindPW hA
  simp only at hsA
  obtain ⟨hn, hrA⟩ := os_drop_cons hsA
  subst hrA hn
  have hlenA := congrArg List.length hsA
  simp only [List.length_drop, List.length_cons] at hlenA
  obtain ⟨qs', sB, hB, h2⟩ := os_inv_bindW h1
  obtain ⟨rfl, rfl⟩ := os_runs_detW (rest := xs.drop (p2 + 1)) hB
    (os_runsTo_sampleQueriesW hper hs1 hs2 hs3 _) rfl
  obtain ⟨lam', sC, hC, h3⟩ := os_inv_bindW h2
  obtain ⟨rfl, rfl⟩ := os_inv_sampleEW hC
  obtain ⟨words, sD, hD, h4⟩ := os_inv_bindW h3
  obtain ⟨rt, hh, ww, osq, hr, hoa, rfl⟩ := os_inv_queryPW hD
  obtain ⟨intro, sE, hE, h5⟩ := os_inv_bindW h4
  obtain ⟨d0, d2, rE, hsE, rfl, rfl⟩ := os_inv_roundPoly3W hE
  simp only at hsE
  have hlenE := congrArg List.length hsE
  simp only [List.length_drop, List.length_cons] at hlenE
  obtain ⟨hd0, hd2, hrE⟩ := os_drop_cons2 hsE
  obtain ⟨rfl, rfl⟩ := os_inv_retW h5
  subst hrE
  refine ⟨by omega, hpow, words, osq, rt, hh, ww, hr, hoa, ?_, ?_, ?_⟩
  · dsimp only; rw [← hd0, ← hd2, show p2 + 1 + 1 = p2 + 2 by ring]
  · dsimp only; rw [← hd0, ← hd2, show p2 + 1 + 1 = p2 + 2 by ring, show p2 + 1 + 2 = p2 + 3 by ring]
  · simp only [osLevelQueries, prog_bind_eq]
    rw [os_queriesOf_bindW _ _ _ hA, os_queriesOf_noQW (Prog.grindP _) trivial, List.nil_append,
      os_queriesOf_bindW _ _ _ hB, os_queriesOf_noQW (sampleQueries _ _) (os_noQ_sampleQueriesAux _ _ _),
      List.nil_append,
      os_queriesOf_bindW _ _ _ hC, os_queriesOf_noQW Prog.sampleE (fun _ => trivial), List.nil_append,
      os_queriesOf_bindW _ _ _ hD, os_queriesOf_queryPW hr hoa,
      os_queriesOf_bindW _ _ _ hE, os_queriesOf_noQW _ (os_noQ_roundPoly3 _), List.nil_append]
    rfl



/-- A level's query steps: its queries', then the rest's. -/
theorem os_qOf_levelW {μ lane lvl ml : ℕ} {L : Whir.Level} {rest : List Whir.Level} {w w1 w' : WhirState}
    {lf res : List E} {pend : List (E × List E × (List E → E))} {st st1 st2 st3 : St}
    (h1 : RunsW Ht (foldRounds L.fold w []) st (w1, lf) st1) (hml : μ - w1.folds.length = ml)
    (h3 : RunsW Ht (osLevelMid ml rest) st1 (res, pend) st2)
    (h5 : RunsW Ht (osLevelQueries ml lvl L lf w1 pend) st2 w' st3) :
    queriesOfW Ht (whirLevelsOpen μ lane lvl (L :: rest) w) st = queriesOfW Ht (osLevelQueries ml lvl L lf w1 pend) st2 ++
      queriesOfW Ht (match rest with
        | [] => osTailOpen ml lane w' res
        | _ :: _ => whirLevelsOpen μ lane (lvl + 1) rest w') st3 := by
  rw [os_whirLevelsOpen_cons, prog_bind_eq, os_queriesOf_bindW _ _ _ h1,
    os_queriesOf_noQW _ (os_noQ_foldRounds _ _ _), List.nil_append]
  dsimp only
  rw [hml, prog_bind_eq, os_queriesOf_bindW _ _ _ h3, os_queriesOf_noQW _ (os_noQ_levelMid _ _), List.nil_append]
  dsimp only
  rw [prog_bind_eq, os_queriesOf_bindW _ _ _ h5]
  cases rest <;> rfl

/-- **A level of the run, inverted**: one level of `whirLevelsOpen` from `p` words of `xs` has its
data `H` (`OsLvOkW Ht`), and the rest of the run continues from the level's end. -/
theorem os_level_invW {cfg : OsCfg} {μ lane lvl : ℕ} {L : Whir.Level} {rest : List Whir.Level}
    (hspec : LvSpec cfg μ lvl L rest) {w : WhirState} (hfl : w.folds.length = (cfg.lv lvl).foldsOff)
    {cv : Digest} {xs : List E} {p : ℕ} {osp : List Opening} {roots : List (Digest × ℕ × ℕ)}
    (hrl : lvl < roots.length) {e : WhirEnd} {sp' : St}
    (h : RunsW Ht (whirLevelsOpen μ lane lvl (L :: rest) w) ⟨cv, xs.drop p, osp, roots⟩ e sp') :
    ∃ H : OsLvH, OsLvOkW Ht cfg lvl xs p μ L cv w osp roots H ∧
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
  rw [os_whirLevelsOpen_cons] at h
  obtain ⟨⟨w1, chs⟩, s1, h1, h2⟩ := os_inv_bindW h
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
  dsimp only at h2
  rw [hml] at h2
  obtain ⟨⟨res, pend⟩, s2, h3, h4⟩ := os_inv_bindW h2
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
    simp only [osLevelMid] at h3
    obtain ⟨res', sM, hM, hM2⟩ := os_inv_bindW h3
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
    rw [eP2, eCv2] at h4 h3o
    simp only at h4
    obtain ⟨w', s3, h5, h6⟩ := os_inv_bindW h4
    obtain ⟨hlen, hpow, rows, osq, rt, hh, ww, hro, hoa, rfl, rfl, hqs⟩ := os_lq_invW (nsq := (cfg.lv lvl).squeezes)
      hd' hq.symm hper hs1 hs2 hs3 h5
    have hqo := os_qOf_levelW (lane := lane) h1 hml h3o h5
    refine ⟨⟨w1, chs, cv1, default, rows, osq⟩, ⟨by rw [eP1]; exact h1, hlen, fun h' => absurd hyl h', hpow,
      ⟨rt, hh, ww, by simp only [osHRootsEnd, ite_pos' hyl]; exact hro, hoa⟩, hw1l, hfolds⟩, fun _ => ?_,
      fun h' => absurd rfl h', rt, hh, ww, by simp only [osHRootsEnd, ite_pos' hyl]; exact hro, fun _ => ?_,
      fun h' => absurd rfl h'⟩
    swap
    · rw [hqo, hqs, List.singleton_append, ← eMs, ← hlc]
      congr 2
      simp only [osHWEndW, osHPendingW, ite_pos' hyl, List.nil_append, osHEnfW, osHRowsE, osHQsW, osHLamW, osHCv4W,
        osHCv3W, osHNonce, osHC]
    rw [← eMs, ← hlc]
    convert h6 using 2
    all_goals try rfl
    simp only [osHWEndW, osHPendingW, ite_pos' hyl, List.nil_append, osHEnfW, osHRowsE, osHQsW, osHLamW, osHCv4W, osHCv3W,
      osHNonce, osHC]
  | cons next rest' =>
    have hyl : lvl ≠ cfg.yrLevel := fun h' => absurd (hlast.mpr h') (by simp)
    obtain ⟨hood, hfo', hfl', hdep'⟩ := hnext next rfl
    simp only [osLevelMid, levelShape] at h3
    obtain ⟨u, sA, hA, h3⟩ := os_inv_bindW h3
    obtain ⟨x0, x1, rA, root, hsA, hroot, rfl⟩ := os_inv_commitPW hA
    simp only at hsA
    obtain ⟨hx0, hx1, rfl⟩ := os_drop_cons2 hsA
    obtain ⟨z, sB, hB, h3⟩ := os_inv_bindW h3
    obtain ⟨rfl, rfl⟩ := os_inv_sampleNW hB
    obtain ⟨y, sC, hC, h3⟩ := os_inv_bindW h3
    obtain ⟨rC, hsC, rfl⟩ := os_inv_readEW hC
    simp only at hsC
    obtain ⟨hy, rfl⟩ := os_drop_cons hsC
    obtain ⟨intro, sD, hD, h3⟩ := os_inv_bindW h3
    obtain ⟨c0o, c2o, rD, hsD, rfl, rfl⟩ := os_inv_roundPoly3W hD
    simp only at hsD
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
    rw [eP2, eCv2] at h4 h3o
    simp only at h4
    obtain ⟨w', s3, h5, h6⟩ := os_inv_bindW h4
    obtain ⟨hlen, hpow, rows, osq, rt, hh, ww, hro, hoa, rfl, rfl, hqs⟩ := os_lq_invW (nsq := (cfg.lv lvl).squeezes)
      hd' hq.symm hper hs1 hs2 hs3 h5
    have hqo := os_qOf_levelW (lane := lane) h1 hml h3o h5
    have eRoots : ro1 ++ [(root, (cfg.lv lvl).logCols - next.fold + next.logInvRate, 3 * 2 ^ next.fold)] =
        osHRootsEnd cfg lvl ro1 ⟨w1, chs, cv1, root, rows, osq⟩ := by
      rw [osHRootsEnd, ite_neg' hyl, hdep', hfl', hlc]
    refine ⟨⟨w1, chs, cv1, root, rows, osq⟩, ⟨by rw [eP1]; exact h1, hlen, fun _ => by rw [← e0, ← e1]; exact hroot,
      hpow, ⟨rt, hh, ww, by rw [← eRoots]; exact hro, hoa⟩, hw1l, hfolds⟩, fun h' => absurd h' (by simp),
      fun _ => ?_, rt, hh, ww, by rw [← eRoots]; exact hro, fun h' => absurd h' (by simp), fun _ => ?_⟩
    swap
    · rw [hqo, hqs, List.singleton_append, ← eRoots]
      congr 2
      simp only [osHWEndW, osHPendingW, ite_neg' hyl, osHEnfW, osHRowsE, osHQsW, osHLamW, osHCv4W, osHCv3W,
        osHNonce, osHC, osHCv12W, ← e0, ← e1, ← e2, ← e3, ← e4, List.singleton_append]
    rw [← eRoots]
    convert h6 using 2
    all_goals try rfl
    simp only [osHWEndW, osHPendingW, ite_neg' hyl, osHEnfW, osHRowsE, osHQsW, osHLamW, osHCv4W, osHCv3W,
      osHNonce, osHC, osHCv12W, ← e0, ← e1, ← e2, ← e3, ← e4, List.singleton_append]


/-- The levels' data from level `lvl` on, each from where the previous one ends, the last one's
tail running to `e`, `sp'`. -/
def OsChainW (Ht : Bytes → Digest) (cfg : OsCfg) (μ lane : ℕ) (xs : List E) (Lall : List Whir.Level) (e : WhirEnd) (sp' : St)
    (Q : List (ℕ × List (ℕ × Opening))) :
    ℕ → Digest → ℕ → WhirState → List Opening → List (Digest × ℕ × ℕ) → List OsLvH → Prop
  | _, _, _, _, _, _, [] => False
  | lvl, cv, p, w, osp, roots, H :: Hs =>
    OsLvOkW Ht cfg lvl xs p μ (Lall.getD lvl default) cv w osp roots H ∧
      (∃ rt, roots[lvl]? = some (rt, (cfg.lv lvl).depth, oqR (if lvl = 0 then 1 else 0) (2 ^ (cfg.lv lvl).folds)) ∧
        ((cfg.lv lvl).depth, (osHQsW Ht cfg lvl xs p H.cv1).zip osp) ∈ Q) ∧
      (lvl = cfg.yrLevel → Hs = [] ∧
        RunsW Ht (osTailOpen (μ - osLevelF cfg lvl) lane (osHWEndW Ht cfg lvl xs p H) (osHMs cfg lvl xs p))
          ⟨osHCvEndW Ht cfg lvl xs p H.cv1, xs.drop (osHPEnd cfg lvl p), H.osq, roots⟩ e sp') ∧
      (lvl ≠ cfg.yrLevel → OsChainW Ht cfg μ lane xs Lall e sp' Q (lvl + 1) (osHCvEndW Ht cfg lvl xs p H.cv1)
        (osHPEnd cfg lvl p) (osHWEndW Ht cfg lvl xs p H) H.osq (osHRootsEnd cfg lvl roots H) Hs)


/-- **The levels' data**: a run of `whirLevelsOpen` from level `lvl`, at the state the guest's
invariant names, has the levels' data. -/
theorem os_chain_of_runW {cfg : OsCfg} {μ lane : ℕ} {Lall : List Whir.Level}
    (hlen : Lall.length = cfg.levels.length)
    (hspec : ∀ i < Lall.length, LvSpec cfg μ i (Lall.getD i default) (Lall.drop (i + 1)))
    (hyl : cfg.yrLevel = cfg.levels.length - 1) {xs : List E} {e : WhirEnd} {sp' : St}
    {Q : List (ℕ × List (ℕ × Opening))} :
    ∀ (j lvl : ℕ) (cv : Digest) (p : ℕ) (w : WhirState) (osp : List Opening) (roots : List (Digest × ℕ × ℕ)),
      lvl + j + 1 = Lall.length → w.folds.length = (cfg.lv lvl).foldsOff → roots.length = lvl + 1 →
      (∃ rt, roots[lvl]? = some (rt, (cfg.lv lvl).depth, oqR (if lvl = 0 then 1 else 0) (2 ^ (cfg.lv lvl).folds))) →
      (∀ b ∈ queriesOfW Ht (whirLevelsOpen μ lane lvl (Lall.drop lvl) w) ⟨cv, xs.drop p, osp, roots⟩, b ∈ Q) →
      RunsW Ht (whirLevelsOpen μ lane lvl (Lall.drop lvl) w) ⟨cv, xs.drop p, osp, roots⟩ e sp' →
      ∃ Hs : List OsLvH, Hs.length = j + 1 ∧ OsChainW Ht cfg μ lane xs Lall e sp' Q lvl cv p w osp roots Hs := by
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
    intro lvl cv p w osp roots hj hfl hrl hrt hQ h
    have hl : lvl < Lall.length := by omega
    have hs := hspec lvl hl
    have hLrest : Lall.drop (lvl + 1) = [] := List.drop_eq_nil_of_le (by omega)
    rw [hLrest] at hs
    rw [List.drop_eq_getElem_cons hl, show Lall[lvl] = Lall.getD lvl default by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl], hLrest] at h
    have hq0 := hQ
    rw [List.drop_eq_getElem_cons hl, show Lall[lvl] = Lall.getD lvl default by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl], hLrest] at hq0
    obtain ⟨H, hok, htail, -, rt', hh, ww, hrt', hqe, -⟩ := os_level_invW hs hfl (by omega) h
    have hy : lvl = cfg.yrLevel := by rw [hyl]; omega
    obtain ⟨rt, hrt⟩ := hrt
    have hhd := hstep (H := H) (osq := []) (by omega) hrt hrt'
    subst hhd
    refine ⟨[H], rfl, hok, ⟨rt, hrt, hq0 _ ?_⟩, fun _ => ⟨rfl, htail rfl⟩, fun h' => absurd hy h'⟩
    rw [hqe rfl]; exact List.mem_cons_self
  | succ j ih =>
    intro lvl cv p w osp roots hj hfl hrl hrt hQ h
    have hl : lvl < Lall.length := by omega
    have hs := hspec lvl hl
    rw [List.drop_eq_getElem_cons hl, show Lall[lvl] = Lall.getD lvl default by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]] at h
    have hl1 : lvl + 1 < Lall.length := by omega
    have hcons : Lall.drop (lvl + 1) = Lall.getD (lvl + 1) default :: Lall.drop (lvl + 2) := by
      rw [List.drop_eq_getElem_cons hl1]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl1]
    have hq0 := hQ
    rw [List.drop_eq_getElem_cons hl, show Lall[lvl] = Lall.getD lvl default by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]] at hq0
    obtain ⟨H, hok, -, hnext, rt', hh, ww, hrt', -, hqe⟩ := os_level_invW hs hfl (by omega) h
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
      (hnext hne)
    refine ⟨H :: Hs, by simp [hHl], hok, ⟨rt, hrt, hq0 _ ?_⟩, fun h' => absurd h' hny, fun _ => hch⟩
    rw [hqe']; exact List.mem_cons_self


/-- The chain state, the stream position and the state after the levels. -/
def osLvsEndW (Ht : Bytes → Digest) (cfg : OsCfg) (xs : List E) :
    ℕ → Digest → ℕ → WhirState → List (Digest × ℕ × ℕ) → List OsLvH → Digest × ℕ × WhirState
  | _, cv, p, w, _, [] => (cv, p, w)
  | lvl, _cv, p, _w, roots, H :: Hs =>
    osLvsEndW Ht cfg xs (lvl + 1) (osHCvEndW Ht cfg lvl xs p H.cv1) (osHPEnd cfg lvl p) (osHWEndW Ht cfg lvl xs p H)
      (osHRootsEnd cfg lvl roots H) Hs


/-- **The tail rounds, inverted**: `n + 1` tail rounds are `n` fold rounds from any state of the
quadratic, then the closing challenge. -/
theorem os_tail_invW : ∀ (n : ℕ) (t : E) (q : List E) (st : St) (r : List E × E) (st' : St),
    RunsW Ht (tailRounds (n + 1) t q) st r st' → ∀ (w : WhirState) (lf : List E), w.quad = q →
      ∃ (w1 : WhirState) (chs : List E) (st1 : St), RunsW Ht (foldRounds n w lf) st (w1, lf ++ chs) st1 ∧
        r = (chs ++ [challengeOf (sqCvW Ht st1.cv)], polyEval w1.quad (challengeOf (sqCvW Ht st1.cv))) ∧
        st' = { st1 with cv := sqCvW Ht st1.cv } := by
  intro n
  induction n with
  | zero =>
    intro t q st r st' h w lf hq
    simp only [tailRounds] at h
    obtain ⟨ch, s1, h1, h2⟩ := os_inv_bindW h
    obtain ⟨rfl, rfl⟩ := os_inv_sampleEW h1
    simp only [↓reduceIte] at h2
    obtain ⟨rfl, rfl⟩ := os_inv_pureW h2
    refine ⟨w, [], st, ?_, by rw [List.nil_append, hq], rfl⟩
    rw [List.append_nil]
    exact RunsW.ret (w, lf) st
  | succ n ih =>
    intro t q st r st' h w lf hq
    rw [tailRounds] at h
    obtain ⟨ch, s1, h1, h2⟩ := os_inv_bindW h
    obtain ⟨rfl, rfl⟩ := os_inv_sampleEW h1
    rw [ite_neg' (by omega)] at h2
    obtain ⟨q', s2, h3, h4⟩ := os_inv_bindW h2
    obtain ⟨⟨rest, tg⟩, s3, h5, h6⟩ := os_inv_bindW h4
    obtain ⟨rfl, rfl⟩ := os_inv_pureW h6
    obtain ⟨c0, c2, rr, hs, rfl, rfl⟩ := os_inv_roundPoly3W h3
    obtain ⟨w1, chs, st1, hr1, he, hs'⟩ := ih _ _ _ _ _ h5
      ⟨polyEval w.quad (challengeOf (sqCvW Ht st.cv)), [c0, polyEval w.quad (challengeOf (sqCvW Ht st.cv)) + c2, c2],
        w.folds ++ [challengeOf (sqCvW Ht st.cv)], w.glued⟩ (lf ++ [challengeOf (sqCvW Ht st.cv)]) (by rw [hq])
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨w1, challengeOf (sqCvW Ht st.cv) :: chs, st1, ?_, by rw [List.cons_append], hs'⟩
    rw [foldRounds_succ]
    refine RunsW.bind (s1 := ⟨obsCvW Ht (obsCvW Ht (sqCvW Ht st.cv) c0) c2, rr, st.openings, st.roots⟩) (a := (challengeOf (sqCvW Ht st.cv), polyEval w.quad (challengeOf (sqCvW Ht st.cv)),
      [c0, polyEval w.quad (challengeOf (sqCvW Ht st.cv)) + c2, c2])) ?_ ?_
    · simp only [foldStep]
      refine RunsW.bind (os_runs_sampleEW _) ?_
      refine RunsW.bind (s1 := ⟨obsCvW Ht (obsCvW Ht (sqCvW Ht st.cv) c0) c2, rr, st.openings, st.roots⟩) ?_ (RunsW.ret _ _)
      have := os_runs_roundPoly3W (Ht := Ht) (sqCvW Ht st.cv) (polyEval w.quad (challengeOf (sqCvW Ht st.cv))) c0 c2 rr st.openings
        st.roots
      simp only at hs
      rw [← hs] at this
      exact this
    · rw [List.append_assoc, List.singleton_append] at hr1
      exact hr1


/-- **The opening's run, inverted at the head**. -/
theorem os_open_invW {cfg : OsCfg} {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall)
    {target : E} {cv cv' : Digest} {xs : List E} {os : List Opening} {root : Digest}
    {roots' : List (Digest × ℕ × ℕ)} {w : WhirEnd}
    (h : RunsWithW Ht (whirOpen μ r target) cv xs os [(root, stackShape μ r)] w cv' roots') :
    2 ≤ xs.length ∧ ∃ Hs : List OsLvH, Hs.length = cfg.levels.length ∧
      OsChainW Ht cfg μ (cfg.lv 0).folds xs Lall w ⟨cv', [], [], roots'⟩
        (queriesOfW Ht (whirOpen μ r target) ⟨cv, xs, os, [(root, stackShape μ r)]⟩) 0
        (obsCvW Ht (obsCvW Ht cv (xs.getD 0 0)) (xs.getD 1 0)) 2 (osW0 target xs) os
        [(root, (cfg.lv 0).depth, 2 ^ (cfg.lv 0).folds)] Hs := by
  have hr := h [] []
  simp only [List.append_nil] at hr
  have hr' : RunsW Ht (whirOpen μ r target) ⟨cv, xs, os, [(root, stackShape μ r)]⟩ w ⟨cv', [], [], roots'⟩ := hr
  unfold whirOpen at hr'
  obtain ⟨cfg', s1, h1, h2⟩ := os_inv_bindW hr'
  rw [hok.config] at h1
  simp only [Verifier.liftOption] at h1
  obtain ⟨hcfg, rfl⟩ := os_inv_retW h1
  subst cfg'
  obtain ⟨q, s2, h3, h4⟩ := os_inv_bindW h2
  obtain ⟨c0, c2, rest, hs, rfl, rfl⟩ := os_inv_roundPoly3W h3
  simp only at hs
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
  rw [hok.lane, hok.shape] at h4
  refine ⟨by omega, ?_⟩
  have hn := hok.len2
  subst e0 e1
  obtain ⟨Hs, hHl, hch⟩ := os_chain_of_runW (xs := xs) (e := w) (sp' := ⟨cv', [], [], roots'⟩)
    (Q := queriesOfW Ht (whirOpen μ r target) ⟨cv, xs, os, [(root, stackShape μ r)]⟩) hok.len hok.spec
    hok.yrLevel (cfg.levels.length - 1) 0 _ 2 (osW0 target xs) os [(root, (cfg.lv 0).depth, 2 ^ (cfg.lv 0).folds)]
    (by rw [hok.len]; omega)
    (by rw [hok.off0]; rfl) rfl ⟨root, by simp [oqR]⟩ (fun b hb => by
      rw [eQ, hq, hok.lane, hok.shape]
      rw [List.drop_zero] at hb
      exact hb) (by
      rw [List.drop_zero]
      exact h4)
  exact ⟨Hs, by rw [hHl]; omega, hch⟩


/-- **The last level's tail**: from the levels' data, the tail runs from where the levels end. -/
theorem os_chain_tailW {cfg : OsCfg} {μ lane : ℕ} {xs : List E} {Lall : List Whir.Level} {e : WhirEnd}
    {sp' : St} {Q : List (ℕ × List (ℕ × Opening))} : ∀ (Hs : List OsLvH) (lvl : ℕ) (cv : Digest) (p : ℕ)
      (w : WhirState) (osp : List Opening)
      (roots : List (Digest × ℕ × ℕ)), OsChainW Ht cfg μ lane xs Lall e sp' Q lvl cv p w osp roots Hs →
      RunsW Ht (osTailOpen (μ - osLevelF cfg (osLvsLast cfg xs lvl p roots Hs).1) lane
          (osLvsEndW Ht cfg xs lvl cv p w roots Hs).2.2
          (osHMs cfg (osLvsLast cfg xs lvl p roots Hs).1 xs (osLvsLast cfg xs lvl p roots Hs).2.1))
        ⟨(osLvsEndW Ht cfg xs lvl cv p w roots Hs).1, xs.drop (osLvsEndW Ht cfg xs lvl cv p w roots Hs).2.1,
          (osLvsLast cfg xs lvl p roots Hs).2.2.2.osq, (osLvsLast cfg xs lvl p roots Hs).2.2.1⟩ e sp'
  | [], _, _, _, _, _, _, h => h.elim
  | [H], lvl, cv, p, w, osp, roots, h => by
    obtain ⟨-, -, hl, hn⟩ := h
    by_cases hy : lvl = cfg.yrLevel
    · exact (hl hy).2
    · exact (hn hy).elim
  | H :: H' :: Hs, lvl, cv, p, w, osp, roots, h => by
    obtain ⟨-, -, hl, hn⟩ := h
    by_cases hy : lvl = cfg.yrLevel
    · exact absurd (hl hy).1 (by simp)
    · exact os_chain_tailW (H' :: Hs) (lvl + 1) _ _ _ _ _ (hn hy)


end
end LeanVM.Guest.B1
