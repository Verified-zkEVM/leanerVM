/-
  LeanVM.Guest.B1.Whir.StackedLevelM

  One level of `open_stacked` under a hash model against one level of `whirLevelsOpen` over the
  model's answered hash.
-/

module

public import LeanVM.Guest.B1.Whir.StackedQueriesM
public import LeanVM.Guest.B1.Whir.StackedLevel

/-!
# A level of the stacked opening under a hash model (TRIAGE #36)

`osLevel_soundM`: `Whir/StackedLevel.lean`'s `osLevel_sound_w` over a `HashModel`. The invariant
`OsLvInv` (the chain state, the words read, the running quadratic and claim, the fold challenges
stored, the roots read so far, the glued claims) names no hash and is the deployed one; the
level's three programs (`foldRounds`, `osLevelMid`, `osLevelQueries`) run over `M.H`
(`RunsToM`, `RunsM`), every hash answered, the query positions those of the answered challenges
(`osPosOfL`). The callees' meanings are `LvCalleesM`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- The callees of level `lvl` under a hash model, as their meanings. -/
structure LvCalleesM (M : HashModel) (rd : Reader) (cfg : OsCfg) (lvl : ℕ) : Prop where
  rw : ∀ a r, coreProgram.RelB M.sem rd (cfg.lv lvl).rowWeights a r →
    MeaningOpeningRowWeights (cfg.lv lvl).folds (if lvl = 0 then 1 else 0) rd a r
  cap : ∀ a r, coreProgram.RelB M.sem rd (cfg.lv lvl).verifyCap a r →
    MeaningVerifyMerkleCapWith M (cfg.lv lvl).capDepth rd a r
  queries : ∀ (n : ℕ) (pos : ℕ → ℕ) (cap flags qw qbp rew : E) (rets : List E), n < ordG →
    QueryBits rd qbp n (cfg.lv lvl).depth pos →
    coreProgram.RelB M.sem rd (cfg.lv lvl).queriesFn [cap, flags, qw, qbp, rew, gen ^ n] rets →
    ∃ qsc, MeaningOpeningQueriesWith M (if lvl = 0 then 1 else 0) (2 ^ (cfg.lv lvl).folds)
      (cfg.lv lvl).depth (cfg.lv lvl).capDepth n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets
  decode : ∀ a r, coreProgram.RelB M.sem rd (cfg.lv lvl).decode a r →
    MeaningDecodeQueryBits (cfg.lv lvl).depth rd a r
  sq : ∃ fn, coreProgram.find? (cfg.lv lvl).sqLoop = some fn ∧
    fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4] ∧ fn.body = sqLoopOf (cfg.lv lvl)

variable {M : HashModel} {rd : Reader} {σ : Val}

/-! ## The positions' bits -/

/-- **The query positions and their bit runs** from `decode_query_bits` at every answered
squeeze: query `i`'s position is `osPosOfL` (V:1598) of the challenges at `qpos[posOff + i]`, and
its bits at `qbp[posOff + i]`. -/
theorem queryBits_of_decodeM {depth nq nsq posOff : ℕ} {qpos qbp : E} {cs : List E}
    (hper : 0 < 192 / depth) (hs1 : nq ≤ nsq * (192 / depth))
    (hdec : ∀ j < nsq, MeaningDecodeQueryBits depth rd [cs.getD j 0,
      qpos * gen ^ (posOff + j * (192 / depth)), qbp * gen ^ (posOff + j * (192 / depth))] []) :
    QueryBits rd (qbp * gen ^ posOff) nq depth (osPosOfL depth cs) ∧
      ∀ i < nq, LoadHolds rd qpos (posOff + i) (eOfNat (osPosOfL depth cs i)) := by
  have hdiv : ∀ i < nq, i / (192 / depth) < nsq := fun i hi => by
    rw [Nat.div_lt_iff_lt_mul hper]; omega
  have hidx : ∀ i, posOff + i / (192 / depth) * (192 / depth) + i % (192 / depth) = posOff + i := by
    intro i; rw [Nat.add_assoc, Nat.div_add_mod']
  refine ⟨fun i hi => ⟨Nat.mod_lt _ (Nat.two_pow_pos _), fun dbp hdbp => ?_⟩, fun i hi => ?_⟩
  · obtain ⟨-, p, ⟨hpK, hfr⟩, hj⟩ := hdec _ (hdiv i hi)
    have hc := Nat.mod_lt i hper
    obtain ⟨-, lp⟩ := hj _ hc
    rw [loadHolds_mul_gen_pow, hidx] at lp
    rw [loadHolds_mul_gen_pow] at hdbp
    have hdq := loadHolds_unique lp hdbp
    subst hdq
    have hK : IsInK (p * gen ^ (i % (192 / depth) * depth)) := isInK_mul hpK (gen_pow_isInK _)
    refine ⟨hK, fun l hl w hw => ?_⟩
    rw [gen_pow_eq_ofK, limb0_mul_ofK hpK, mul_assoc, Parameters.gpow, Parameters.gpow, ← pow_add] at hw
    have hlt : i % (192 / depth) * depth + l < 192 := by
      have : i % (192 / depth) * depth + depth ≤ 192 / depth * depth := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hc
      have := Nat.div_mul_le_self 192 depth
      omega
    rw [hfr _ hlt w hw, osPosOfL, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
    simp [hl]
  · obtain ⟨-, p, -, hj⟩ := hdec _ (hdiv i hi)
    obtain ⟨lq, -⟩ := hj _ (Nat.mod_lt i hper)
    rw [loadHolds_mul_gen_pow, hidx] at lq
    exact lq

/-! ## A level's proof of work, positions and queries -/

theorem osLamPows_noBlake (lam qw base k : ℕ) : ∀ nq, Stmt.noBlakeList (osLamPows lam qw base k nq) = true
  | 0 => rfl
  | nq + 1 => by
    simp only [osLamPows, noBlakeList_append]
    split
    · rfl
    · rw [noBlakeList_append, noBlakeList_flatten_range _ _ (fun _ => rfl)]; rfl

/-- **A level after its claims under a hash model** (G:1136-1193): the nonce, the positions,
`lam`, the query weights and the queries; `osLevelQueries` (V:1737-1749) runs over the model's
answered hash, over the words and openings the guest reads. -/
theorem osLevelQ_soundM {C : CallRel} (hC : CallRel.Le C (coreProgram.RelB M.sem rd)) {cfg : OsCfg}
    {logN lvl : ℕ} {L : Whir.Level} {rest : List Whir.Level}
    (hspec : LvSpec cfg logN lvl L rest) (hcall : LvCalleesM M rd cfg lvl)
    {wq : List E → List E → List Opening}
    (hqW : SoundQueriesWCM M C rd (cfg.lv lvl).queriesFn (if lvl = 0 then 1 else 0) (2 ^ (cfg.lv lvl).folds)
      (cfg.lv lvl).depth (cfg.lv lvl).capDepth wq)
    {cur : E} {s sg ssq : OsSt} {cvm : Digest} {xsm : List E} (hat : OsCur rd σ cur s cvm xsm)
    {lf : List E} (hlfl : lf.length = (cfg.lv lvl).folds)
    (hlf : ∀ j < (cfg.lv lvl).folds,
      LoadHolds rd (σ (.n osFch)) ((cfg.lv lvl).foldsOff + j) (lf.getD j 0))
    {roots : List (Digest × ℕ × ℕ)} {rt : Digest}
    (hrt : roots[lvl]? = some (rt, (cfg.lv lvl).depth,
      oqR (if lvl = 0 then 1 else 0) (2 ^ (cfg.lv lvl).folds)))
    (lrt0 : LoadHolds rd (σ (.n osRoots)) (2 * lvl) (digestScalars rt).1)
    (lrt1 : LoadHolds rd (σ (.n osRoots)) (2 * lvl + 1) (digestScalars rt).2)
    (hsg : (osGrind (cfg.lv lvl).grindBits s).2 = sg)
    (hssq : (osSqueezes cfg.maxSq (cfg.lv lvl).squeezes osQpos osQbp (cfg.lv lvl).sqLoop sg).2 = ssq)
    {kret : List E → Prop}
    (hG : Stmt.HoldsListB M.sem C rd σ (osGrind (cfg.lv lvl).grindBits s).1 True kret)
    (hS : Stmt.HoldsListB M.sem C rd σ
      (osSqueezes cfg.maxSq (cfg.lv lvl).squeezes osQpos osQbp (cfg.lv lvl).sqLoop sg).1 True kret)
    (hL : Stmt.HoldsListB M.sem C rd σ
      (osLamPows (ssq.k - 1) osQw (lvl * cfg.maxQ) ssq.k (cfg.lv lvl).queries) True kret)
    (hQ : Stmt.HoldsListB M.sem C rd σ
      (osQueries cfg (cfg.lv lvl) lvl { ssq with k := ssq.k + (cfg.lv lvl).queries }).1 True kret) :
    ∃ (lam : E) (qs : List ℕ) (ysQ : List E) (os : List Opening) (cvq : Digest) (c0 c2 : E),
      os = osQueriesOs cfg (cfg.lv lvl) lvl { ssq with k := ssq.k + (cfg.lv lvl).queries } σ wq ∧
      σ (.n (ssq.k - 1)) = lam ∧
      OsCur rd σ cur (osQueries cfg (cfg.lv lvl) lvl { ssq with k := ssq.k + (cfg.lv lvl).queries }).2.1
        cvq (xsm ++ ysQ) ∧
      (osQueries cfg (cfg.lv lvl) lvl { ssq with k := ssq.k + (cfg.lv lvl).queries }).2.1.co = s.co + 3 ∧
      σ (.n (osQueries cfg (cfg.lv lvl) lvl { ssq with k := ssq.k + (cfg.lv lvl).queries }).2.2.2.1) = c0 ∧
      σ (.n (osQueries cfg (cfg.lv lvl) lvl { ssq with k := ssq.k + (cfg.lv lvl).queries }).2.2.2.2.2) = c2 ∧
      σ (.n (osQueries cfg (cfg.lv lvl) lvl { ssq with k := ssq.k + (cfg.lv lvl).queries }).2.2.2.2.1) =
        σ (.n (osQueries cfg (cfg.lv lvl) lvl { ssq with k := ssq.k + (cfg.lv lvl).queries }).2.2.1) + c2 ∧
      qs.length = (cfg.lv lvl).queries ∧
      (∀ j < (cfg.lv lvl).queries,
        LoadHolds rd (σ (.n osQpos)) ((cfg.lv lvl).posOff + j) (eOfNat (qs.getD j 0))) ∧
      (∀ j < (cfg.lv lvl).queries, LoadHolds rd (σ (.n osQw)) (lvl * cfg.maxQ + j) (lam ^ j)) ∧
      ∀ (w1 : WhirState) (pending : List (E × List E × (List E → E))) (r : List E) (o : List Opening),
        RunsM M (osLevelQueries (logN - osLevelF cfg lvl) lvl L lf w1 pending) ⟨cvm, ysQ ++ r, os ++ o, roots⟩
          (glue lam w1 (pending ++
            [(σ (.n (osQueries cfg (cfg.lv lvl) lvl { ssq with k := ssq.k + (cfg.lv lvl).queries }).2.2.1),
              [c0, σ (.n (osQueries cfg (cfg.lv lvl) lvl { ssq with k := ssq.k + (cfg.lv lvl).queries }).2.2.1)
                + c2, c2],
              fun x ↦ inducedWeight (logN - osLevelF cfg lvl) qs (powers lam qs.length) x)]))
          ⟨cvq, r, o, roots⟩ := by
  obtain ⟨hf, hf0, hq, hml0, hml1, hlc, hdep, hgr, hper, hs1, hs2, hs3, hs4, hdig, hcd1, hcd2, hb1,
    hb2, hb4, hb5, hnq, hb6, hlast, hyr, hnext⟩ := hspec
  obtain ⟨sqfn, hsqf, hsqp, hsqb⟩ := hcall.sq
  -- the nonce
  obtain ⟨n, cvg, hrunG, hatg, hcog⟩ := osGrind_soundM (by rw [hgr]; decide) (by rw [hgr]; decide) hat (holdsListB_rel hC hG)
  rw [hsg] at hatg hcog
  rw [hgr] at hrunG
  -- the positions and `lam`
  obtain ⟨cs, cvs, dl, hcs, hdl, hatq, hlam, hdec, hcoq⟩ := osSqueezes_soundM hsqf hsqp hsqb
    hcall.decode hdig (by omega) (by omega) hatg (holdsListB_rel hC hS)
  rw [hssq] at hatq hlam hcoq
  set lam := challengeOf dl
  obtain ⟨hbits, hqpos⟩ := queryBits_of_decodeM hper hs1 hdec
  have hqw := osLamPows_sound _ ((holdsListB_iff_of_noBlake (osLamPows_noBlake _ _ _ _ _) _ _).mp hL)
  rw [hlam] at hqw
  -- the queries
  obtain ⟨root, os, c0, c2, cvq, hosQ, lr0, lr1, hosl, hos, hsum, ⟨e1, he1, he2⟩, hatQ, hcoQ, e0, f1, f2⟩ :=
    osQueries_soundWM hC rfl hcall.rw hcall.cap hqW hcd1 hcd2 hb1 hb2 hb4 hb5 (by omega)
      hlfl hlf (fun i hi => by simpa using hqw i hi) hbits
      (s := { ssq with k := ssq.k + (cfg.lv lvl).queries }) (cv := dl)
      ⟨hatq.fs, hatq.reads, hatq.cursor⟩ hQ
  have hroot : root = rt := digestScalars_injective (Prod.ext (loadHolds_unique lr0 lrt0)
    (loadHolds_unique lr1 lrt1))
  subst hroot
  set qs := (List.range (cfg.lv lvl).queries).map (osPosOfL (cfg.lv lvl).depth cs)
  have hqsl : qs.length = (cfg.lv lvl).queries := by simp [qs]
  refine ⟨lam, qs, [n, c0, c2], os, cvq, c0, c2, hosQ, hlam, by simpa using hatQ,
    by rw [hcoQ, hcoq, hcog], e0, f2, f1, hqsl, fun j hj => ?_, fun j hj => by simpa using hqw j hj,
    fun w1 pending r o => ?_⟩
  · rw [os_getD_map_range _ hj]
    exact hqpos j hj
  simp only [osLevelQueries]
  conv at hsum => rhs; rw [← hqsl]
  rw [← hdep, ← hq, hsum]
  refine RunsM.bind (hrunG.runsM _ _ _) ?_
  refine RunsM.bind ((os_runsToM_sampleQueries hper hs1 hs2 hs3 hcs).runsM _ _ _) ?_
  refine RunsM.bind ((runsToM_sampleE hdl).runsM _ _ _) ?_
  refine RunsM.bind (os_runsM_queryP hrt (os_openAll_ofM qs os o (by rw [hosl, hqsl]) fun j hj => ?_)) ?_
  · obtain ⟨h1, h2, h3⟩ := hos j hj
    refine ⟨h1, h2, ?_⟩
    rw [os_getD_map_range _ (show j < (cfg.lv lvl).queries by omega)]
    exact h3
  refine RunsM.bind ((runsToM_roundPoly3 _ c0 c2 he1 he2).runsM _ _ _) ?_
  exact RunsM.ret _ _

/-! ## A level -/

private theorem digestOfScalars_pairM {x0 x1 : E} (h0 : IsCanonical128 x0) (h1 : IsCanonical128 x1) :
    digestOfScalars (x0, x1) = some (pairDigest x0 x1) := by
  simp [digestOfScalars, h0, h1, pairDigest]

private theorem recOk_appendM {cfg : OsCfg} {recs : List OsRec} {r : OsRec} {n : ℕ} (hl : recs.length = n)
    (hrecs : ∀ i < n, OsRecOk rd σ cfg i (recs.getD i default)) (hr : OsRecOk rd σ cfg n r) :
    ∀ i < n + 1, OsRecOk rd σ cfg i ((recs ++ [r]).getD i default) := by
  intro i hi
  rcases Nat.lt_or_ge i n with h | h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
    exact hrecs i h
  · obtain rfl : i = n := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hl, Nat.sub_self]
    exact hr

private theorem folds_appendM {fch : E} {ws chs : List E} {off : ℕ} (hoff : ws.length = off)
    (h1 : ∀ j < ws.length, LoadHolds rd fch j (ws.getD j 0))
    (h2 : ∀ j < chs.length, LoadHolds rd fch (off + j) (chs.getD j 0)) :
    ∀ j < (ws ++ chs).length, LoadHolds rd fch j ((ws ++ chs).getD j 0) := by
  intro j hj
  rw [List.length_append] at hj
  rcases Nat.lt_or_ge j ws.length with h | h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]
    exact h1 j h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right h, ← List.getD_eq_getElem?_getD]
    have := h2 (j - ws.length) (by omega)
    rw [hoff] at this ⊢
    rwa [show off + (j - off) = j by omega] at this

private theorem gluedOf_appendM (logN : ℕ) (cfg : OsCfg) (recs : List OsRec) (r : OsRec) :
    osGluedOf logN cfg (recs ++ [r]) = osGluedOf logN cfg recs ++ osRecGlued logN (osLevelF cfg recs.length) r := by
  simp [osGluedOf, List.zipIdx_append]

/-- **One level under a hash model** (G:1096-1213) against one level of `whirLevelsOpen`
(`os_whirLevelsOpen_cons`): `foldRounds`, `osLevelMid` and `osLevelQueries` run over the model's
answered hash, over the words and the openings the guest reads; the invariant holds at the next
level, or, after the last level, what the tail needs and the final message. -/
theorem osLevel_soundM {C : CallRel} (hC : CallRel.Le C (coreProgram.RelB M.sem rd)) {cfg : OsCfg}
    {logN lvl : ℕ} {L : Whir.Level} {rest : List Whir.Level}
    (hspec : LvSpec cfg logN lvl L rest) (hcall : LvCalleesM M rd cfg lvl)
    {wq : List E → List E → List Opening}
    (hqW : SoundQueriesWCM M C rd (cfg.lv lvl).queriesFn (if lvl = 0 then 1 else 0) (2 ^ (cfg.lv lvl).folds)
      (cfg.lv lvl).depth (cfg.lv lvl).capDepth wq)
    (hfin : ∀ a r, coreProgram.RelB M.sem rd cfg.finalMsg a r →
      MeaningOpeningFinalMessageWith M cfg.yrLen rd a r)
    {cur : E} {st : OsSt} {cv : Digest} {xs : List E} {w : WhirState} {roots : List (Digest × ℕ × ℕ)}
    (hinv : OsLvInv rd σ cfg logN cur lvl st cv xs w roots) {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem C rd σ (osLevel cfg lvl (cfg.lv lvl) st).1 True kret) :
    ∃ (ys1 : List E) (cv1 : Digest) (w1 : WhirState) (chs : List E),
      RunsToM M (foldRounds L.fold w []) cv ys1 (w1, chs) cv1 ∧ w1.folds.length = osLevelF cfg lvl ∧
    ∃ (ysM : List E) (cv2 : Digest) (residual : List E)
      (pending : List (E × List E × (List E → E))) (roots2 : List (Digest × ℕ × ℕ)),
      (∀ r o, RunsM M (osLevelMid (logN - osLevelF cfg lvl) rest) ⟨cv1, ysM ++ r, o, roots⟩
        (residual, pending) ⟨cv2, r, o, roots2⟩) ∧
    ∃ (ysQ : List E) (os : List Opening) (cv' : Digest) (w' : WhirState),
      os = osLevelOs cfg lvl (cfg.lv lvl) st σ wq ∧
      (∀ r o, RunsM M (osLevelQueries (logN - osLevelF cfg lvl) lvl L chs w1 pending)
        ⟨cv2, ysQ ++ r, os ++ o, roots2⟩ w' ⟨cv', r, o, roots2⟩) ∧
      (rest = [] → residual.length = cfg.yrLen ∧ ReadsAt rd (σ (.n osFmsg)) residual ∧
        OsEndInv rd σ cfg logN cur (lvl + 1) (osLevel cfg lvl (cfg.lv lvl) st).2 cv'
          (xs ++ ys1 ++ ysM ++ ysQ) w') ∧
      (rest ≠ [] → OsLvInv rd σ cfg logN cur (lvl + 1) (osLevel cfg lvl (cfg.lv lvl) st).2 cv'
        (xs ++ ys1 ++ ysM ++ ysQ) w' roots2) := by
  have hspec' := hspec
  obtain ⟨hf, hf0, hq, hml0, hml1, hlc, hdep, hgr, hper, hs1, hs2, hs3, hs4, hdig, hcd1, hcd2, hb1,
    hb2, hb4, hb5, hnq, hb6, hlast, hyr, hnext⟩ := hspec
  obtain ⟨hat, hco, hquad, htgt, hnf, hfch, hrl, ⟨rt, hrt, lrt0, lrt1⟩, ⟨recs, hrecl, hgl, hrecs⟩⟩ :=
    hinv
  unfold osLevel at h ⊢
  simp only at h ⊢
  simp only [holdsListB_append] at h
  obtain ⟨hF, h⟩ := holdsListB_true_of (osFolds_noRet _ _ _ _) h
  obtain ⟨ys1, cv1, chs, w1, hat1, hrun1, hchl, hq1, ht1, hfo1, hgl1, hlf1, hco1⟩ :=
    osFolds_soundM (fch := osFch) _ _ _ _ _ w [] hat (by omega) hquad htgt (holdsListB_rel hC hF)
  rw [ite_neg' (by rw [hf]; omega)] at hco1
  have hw1l : w1.folds.length = osLevelF cfg lvl := by
    rw [hfo1, List.length_append, hnf, hchl, osLevelF]
  refine ⟨ys1, cv1, w1, chs, by rw [← hf]; simpa using hrun1, hw1l, ?_⟩
  generalize hfr : osFolds osFch (cfg.lv lvl).foldsOff (cfg.lv lvl).folds st = fr at *
  by_cases hl : lvl = cfg.yrLevel
  · have hr0 : rest = [] := hlast.mpr hl
    subst hr0
    have he : (lvl = cfg.yrLevel) = True := eq_true hl
    simp only [he, ↓reduceIte] at h ⊢
    obtain ⟨hM, h⟩ := holdsListB_true_of (osFinal_noRet _ _ _) h
    obtain ⟨ms, cvF, hmsl, hrunF, hatM, hfm, hcoM⟩ := osFinal_soundM hfin hat1 (by omega) (holdsListB_rel hC hM)
    obtain ⟨hG, h⟩ := holdsListB_true_of (osGrind_noRet _ _) h
    obtain ⟨hS, h⟩ := holdsListB_true_of (osSqueezes_noRet _ _ _ _ _ _) h
    obtain ⟨hL, h⟩ := holdsListB_true_of (osLamPows_noRet _ _ _ _ _) h
    obtain ⟨hQ, h⟩ := holdsListB_true_of (osQueries_noRet _ _ _ _) h
    obtain ⟨-, h⟩ := holdsListB_true_of (by rfl) h
    obtain ⟨hB, h⟩ := holdsListB_split_free rfl rfl h
    rw [holdsListB_iff_of_noBlake rfl] at h
    obtain ⟨lam, qs, ysQ, os, cvq, c0, c2, hosQ, hlam, hatQ, hcoQ, e0, e2, e1, hqsl, hqpos, hqw, hrunQ⟩ :=
      osLevelQ_soundM hC hspec' hcall hqW hatM (lf := chs) (by rw [hchl]) hlf1 hrt lrt0 lrt1 rfl rfl hG hS hL hQ
    have hosE : os = osLevelOs cfg lvl (cfg.lv lvl) st σ wq := by
      rw [hosQ, osLevelOs, osLevelQState, hfr]
      simp only [he, ↓reduceIte]
    have hgl := osGlue_sound h
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hB
    have hk := osRest_keep cfg (cfg.lv lvl) lvl (osFinal cfg.finalMsg osFmsg fr.2).2
    simp only at hk
    obtain ⟨k1, k2, k3, k4⟩ := hk
    obtain ⟨f1, f2, f3, f4⟩ := osFinal_keep cfg.finalMsg osFmsg fr.2
    generalize (osSqueezes cfg.maxSq (cfg.lv lvl).squeezes osQpos osQbp (cfg.lv lvl).sqLoop
      (osGrind (cfg.lv lvl).grindBits (osFinal cfg.finalMsg osFmsg fr.2).2).2).2 = ssq at *
    generalize osQueries cfg (cfg.lv lvl) lvl { ssq with k := ssq.k + (cfg.lv lvl).queries } = qq at *
    obtain ⟨g1, g2, g3, g4⟩ := hgl
    rw [hlam] at g1 g2 g3 g4 hB
    rw [k1, f1] at g1
    rw [k2, f2, e1] at g2
    rw [k3, f3, e2] at g3
    rw [k4, f4] at g4
    rw [e0] at g1
    have hyr' := hyr rfl
    refine ⟨ms, cvF, ms, [], roots, fun r o => ?_, ysQ, os, cvq, _, hosE, fun r o => hrunQ w1 [] r o,
      fun _ => ⟨by rw [hmsl], hfm, ?_⟩, fun hne => absurd rfl hne⟩
    · simp only [osLevelMid]
      rw [← hyr']
      exact RunsM.bind (hrunF.runsM _ _ _) (RunsM.ret _ _)
    · simp only [List.nil_append, os_glue_one]
      refine ⟨⟨hatQ.fs, hatQ.reads, hatQ.cursor⟩, by
          show qq.2.1.co ≤ 8; rw [hcoQ, hcoM]; omega, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hq1]
        simp only [List.zipWith_cons_cons, List.zipWith_nil_right, one_mul]
        show [σ (.n fr.2.c) + lam * c0, σ (.n fr.2.b) + lam * (σ (.n qq.2.2.1) + c2),
          σ (.n fr.2.a) + lam * c2] = _
        rw [g1, g2, g3]
      · show w1.target + 1 * lam * σ (.n qq.2.2.1) = _
        rw [ht1, g4, one_mul]
      · show w1.folds.length = osLevelF cfg (lvl + 1 - 1)
        rw [hw1l, Nat.add_sub_cancel]
      · show ∀ j < w1.folds.length, LoadHolds rd (σ (.n osFch)) j (w1.folds.getD j 0)
        rw [hfo1]
        exact folds_appendM hnf hfch (fun j hj => hlf1 j (by rw [← hchl]; exact hj))
      · refine ⟨recs ++ [⟨lam, qs, none⟩], by simp [hrecl], ?_, recOk_appendM hrecl hrecs
          ⟨hqsl, hqpos, hqw, by simp [hl], fun _ => hB, fun z hz => absurd hz (by simp)⟩⟩
        show w1.glued ++ _ = _
        rw [gluedOf_appendM, hgl1, hgl, hrecl, hw1l]
        simp [osRecGlued]
  · obtain ⟨next, rest', rfl⟩ : ∃ next rest', rest = next :: rest' := by
      cases rest with
      | nil => exact absurd (hlast.mp rfl) hl
      | cons a b => exact ⟨a, b, rfl⟩
    obtain ⟨hood, hfo', hfl', hdep'⟩ := hnext next rfl
    have he : (lvl = cfg.yrLevel) = False := eq_false hl
    simp only [he, ↓reduceIte] at h ⊢
    rw [hood] at h ⊢
    simp only [osOodGlues, List.append_nil, Nat.zero_mul, Nat.add_zero] at h ⊢
    generalize hLC : (cfg.lv lvl).logCols = lc at h ⊢
    obtain rfl : lc = logN - osLevelF cfg lvl := hLC.symm.trans hlc
    obtain ⟨hM, h⟩ := holdsListB_true_of (osCommit_noRet _ _ _ _ _ _) h
    obtain ⟨x0, x1, y, c0o, c2o, d0, d1, zs, cvz, cvM, hk0, hk1, lx0, lx1, hd0, hd1, hrunZ,
      ⟨ey, ec0, hey, hec0, hec2⟩, hatM, hrs, ly, lc0, lc2, hcoM⟩ :=
      osCommit_soundM (by omega) (by omega) hb6 hat1 (holdsListB_rel hC hM)
    obtain ⟨hG, h⟩ := holdsListB_true_of (osGrind_noRet _ _) h
    obtain ⟨hS, h⟩ := holdsListB_true_of (osSqueezes_noRet _ _ _ _ _ _) h
    obtain ⟨hL, h⟩ := holdsListB_true_of (osLamPows_noRet _ _ _ _ _) h
    obtain ⟨hQ, h⟩ := holdsListB_true_of (osQueries_noRet _ _ _ _) h
    obtain ⟨hO, h⟩ := holdsListB_split_free rfl (by simp [osOodGlue, Stmt.noRetList, Stmt.noRet]) h
    obtain ⟨hB, h⟩ := holdsListB_split_free rfl rfl h
    rw [holdsListB_iff_of_noBlake rfl] at h
    have hrt' : (roots ++ [(pairDigest x0 x1, levelShape (logN - osLevelF cfg lvl) next
        (3 * 2 ^ next.fold))])[lvl]? = some (rt, (cfg.lv lvl).depth,
        oqR (if lvl = 0 then 1 else 0) (2 ^ (cfg.lv lvl).folds)) := by
      rw [List.getElem?_append_left (by omega)]; exact hrt
    obtain ⟨lam, qs, ysQ, os, cvq, c0, c2, hosQ, hlam, hatQ, hcoQ, e0, e2, e1, hqsl, hqpos, hqw, hrunQ⟩ :=
      osLevelQ_soundM hC hspec' hcall hqW hatM (lf := chs) (by rw [hchl]) hlf1 hrt' lrt0 lrt1 rfl rfl hG hS hL hQ
    have hosE : os = osLevelOs cfg lvl (cfg.lv lvl) st σ wq := by
      rw [hosQ, osLevelOs, osLevelQState, hfr]
      simp only [he, ↓reduceIte, hood, hLC]
    obtain ⟨lo, o1, o2, o3, o4, o5⟩ := osOodGlue_sound ly lc0 lc2 hO
    have hgl := osGlue_sound h
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hB
    have hk := osRest_keep cfg (cfg.lv lvl) lvl
      (osCommit lvl (logN - osLevelF cfg lvl) 1 osRoots osOodz osOod fr.2).2
    simp only at hk
    obtain ⟨k1, k2, k3, k4⟩ := hk
    obtain ⟨f1, f2, f3, f4⟩ := osCommit_keep lvl (logN - osLevelF cfg lvl) osRoots osOodz osOod fr.2
    generalize (osSqueezes cfg.maxSq (cfg.lv lvl).squeezes osQpos osQbp (cfg.lv lvl).sqLoop
      (osGrind (cfg.lv lvl).grindBits (osCommit lvl (logN - osLevelF cfg lvl) 1 osRoots osOodz osOod
        fr.2).2).2).2 = ssq at *
    generalize osQueries cfg (cfg.lv lvl) lvl { ssq with k := ssq.k + (cfg.lv lvl).queries } = qq at *
    obtain ⟨g1, g2, g3, g4⟩ := hgl
    rw [o5, hlam] at g1 g2 g3 g4 hB
    rw [hlam] at lo o1 o2 o3 o4
    rw [o1, k1, f1, e0] at g1
    rw [o2, k2, f2, e1] at g2
    rw [o3, k3, f3, e2] at g3
    rw [o4, k4, f4] at g4
    set ml := logN - osLevelF cfg lvl
    have hzs := sqAllM_of_runsToM hrunZ
    have hzl : zs.length = ml := length_sqAllM hzs
    refine ⟨[x0, x1, y, c0o, c2o], cvM, [],
      [(y, [c0o, y + c2o, c2o], fun x ↦ eqEval zs x)],
      roots ++ [(pairDigest x0 x1, levelShape ml next (3 * 2 ^ next.fold))], fun r o => ?_,
      ysQ, os, cvq, _, hosE, fun r o => hrunQ w1 _ r o, fun h0 => absurd h0 (by simp), fun _ => ?_⟩
    · simp only [osLevelMid, levelShape]
      refine RunsM.bind (os_runsM_commitP (digestOfScalars_pairM hk0 hk1) hd0 hd1 _ _ _ _ _) ?_
      refine RunsM.bind (hrunZ.runsM _ _ _) ?_
      refine RunsM.bind ((runsToM_readE hey).runsM _ _ _) ?_
      refine RunsM.bind ((runsToM_roundPoly3 _ _ _ hec0 hec2).runsM _ _ _) ?_
      exact RunsM.ret _ _
    · simp only [List.singleton_append, os_glue_two]
      refine ⟨⟨hatQ.fs, hatQ.reads, hatQ.cursor⟩, by
          show qq.2.1.co ≤ 8; rw [hcoQ, hcoM, hco1], ?_, ?_, ?_, ?_, by simp [hrl], ?_, ?_⟩
      · rw [hq1]
        simp only [List.zipWith_cons_cons, List.zipWith_nil_right, one_mul]
        show [σ (.n fr.2.c) + lam * c0o + lam * lam * c0,
          σ (.n fr.2.b) + lam * (y + c2o) + lam * lam * (σ (.n qq.2.2.1) + c2),
          σ (.n fr.2.a) + lam * c2o + lam * lam * c2] = _
        rw [g1, g2, g3]
      · show w1.target + 1 * lam * y + 1 * lam * lam * σ (.n qq.2.2.1) = _
        rw [ht1, g4]; simp only [one_mul]
      · show w1.folds.length = (cfg.lv (lvl + 1)).foldsOff
        rw [hw1l, hfo']
      · show ∀ j < w1.folds.length, LoadHolds rd (σ (.n osFch)) j (w1.folds.getD j 0)
        rw [hfo1]
        exact folds_appendM hnf hfch (fun j hj => hlf1 j (by rw [← hchl]; exact hj))
      · refine ⟨pairDigest x0 x1, ?_, ?_, ?_⟩
        · rw [List.getElem?_append_right (by omega), hrl, Nat.sub_self, List.getElem?_cons_zero,
            hdep', hfl']
          simp [levelShape, oqR]
        · rw [← (pairDigest_eq hk0 hk1)]; simpa [Nat.mul_add] using lx0
        · rw [← (pairDigest_eq hk0 hk1)]; simpa [Nat.mul_add] using lx1
      · refine ⟨recs ++ [⟨lam, qs, some zs⟩], by simp [hrecl], ?_, recOk_appendM hrecl hrecs
          ⟨hqsl, hqpos, hqw, by simp [hl], fun hz => absurd hz (by simp), fun z hz => ?_⟩⟩
        · show w1.glued ++ _ ++ _ = _
          rw [gluedOf_appendM, hgl1, hgl, hrecl, hw1l]
          simp [osRecGlued, ml]
        · simp only [Option.some.injEq] at hz
          subst hz
          exact ⟨hB, by rw [hzl, hlc], hrs, lo⟩

end
end LeanVM.Guest.B1
