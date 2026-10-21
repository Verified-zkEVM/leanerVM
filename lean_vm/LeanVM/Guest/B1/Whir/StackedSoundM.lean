/-
  LeanVM.Guest.B1.Whir.StackedSoundM

  `open_stacked` is sound under a hash model: its relation gives `OpenOutM`, the stacked opening
  run over the model's answered hash.
-/

module

public import LeanVM.Guest.B1.Whir.StackedEndM
public import LeanVM.Guest.B1.Whir.StackedSound

/-!
# `open_stacked` under a hash model (TRIAGE #36)

The outcome over a hash model is `VerifySub.InterfaceM`'s: `OpenOutWM M rd … os` (the stacked
opening's run at the openings `os`, `RunsWithM`, every hash answered by the model) and
`OpenOutM` (some openings).

`open_stacked_frame_wCM` (`open_stacked_frame_wC` over the model): a frame of `osBody cfg` under
`M.sem` over a call relation `C` below the program's, its levels' `opening_queries` sound with the
openings `wq` (`OsQueriesWCM`), gives `OpenOutWM` at the openings `osOsOf cfg σ wq`.
`open_stacked_model`: at a configuration whose facts match the specification's ladder
(`OsCfgOk`, decided per candidate, the deployed structure) and whose callees have their meanings
under the model (`OsCalleesM`), the relation under `M.sem` of a function whose body is
`osBody cfg` gives `OpenOutM`. The head and the levels and the tail read the chain over the
model (`osHead_soundM`, `osLevels_soundM`, `osTail_soundM`); what follows the tail has no
`BLAKE2S` row (`osFinish_noBlake`) and is `osFinish_sound`'s.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

variable {M : HashModel} {rd : Reader} {σ : Val}

/-! ## The head -/

/-- **The head under a hash model** (G:1062-1094): the first quadratic read from the chain state
of `fs0, fs1`, its two words absorbed by the model, the stack's root at the first root slot: the
invariant at level `0`. -/
theorem osHead_soundM {cfg : OsCfg} {logN : ℕ} (hoff : (cfg.lv 0).foldsOff = 0) {fs0 fs1 target root0 root1 cur : E}
    {root : Digest} (hroot : (root0, root1) = digestScalars root)
    (hσ : σ (.n 0) = fs0 ∧ σ (.n 1) = fs1 ∧ σ (.n 2) = target ∧ σ (.n 3) = root0 ∧ σ (.n 4) = root1 ∧
      σ (.n 5) = cur) {C : CallRel} {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem C rd σ (osHead cfg).1 True kret) :
    ∃ (cv d1 d2 : Digest) (x0 x1 : E), (fs0, fs1) = digestScalars cv ∧ obsCvM M cv x0 = some d1 ∧
      obsCvM M d1 x1 = some d2 ∧
      OsLvInv rd σ cfg logN cur 0 (osHead cfg).2 d2 [x0, x1]
        ⟨target, [x0, target + x1, x1], [], []⟩
        [(root, (cfg.lv 0).depth, oqR 1 (2 ^ (cfg.lv 0).folds))] := by
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := hσ
  unfold osHead at h ⊢
  simp only at h ⊢
  simp only [holdsListB_append] at h
  obtain ⟨hc, h⟩ := holdsListB_split_free rfl rfl h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hc
  obtain ⟨hx, h⟩ := holdsListB_true_of (by rfl) h
  have hx' := hx
  unfold osFsNext at hx'
  obtain ⟨⟨-, cv, -, hcv, -, -⟩, -⟩ := holdsB_fsNextT (M := M) _ _ _ _ _ hx'
  have hat0 : OsCur rd σ cur ⟨8, 6, 7, 5, 0, 0, 0, 0, 2⟩ cv [] :=
    ⟨hcv, readsAt_nil _ _, by show σ (.n 5) * gen ^ 0 = cur * gen ^ 0; rw [e5]⟩
  obtain ⟨d1, hd1, hat1⟩ := osFsNext_soundM hat0 hx
  obtain ⟨hy, h⟩ := holdsListB_true_of (by rfl) h
  obtain ⟨d2, hd2, hat2⟩ := osFsNext_soundM hat1 hy
  obtain ⟨hadd, h⟩ := holdsListB_split_free rfl rfl h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hadd
  simp only [osHeap, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, true_and] at h
  obtain ⟨-, -, -, -, l3, l4, -⟩ := h
  refine ⟨cv, d1, d2, σ (.n 8), σ (.n 23), by rw [← e0, ← e1, ← hc.1, ← hc.2]; exact hcv, hd1, hd2,
    ⟨hat2.fs, hat2.reads, hat2.cursor⟩, by decide, ?_, e2.symm, by rw [hoff]; rfl,
    fun j hj => absurd hj (by simp), rfl, ⟨root, by simp, ?_, ?_⟩, ⟨[], rfl, rfl, fun i hi => absurd hi (by simp)⟩⟩
  · show [σ (.n 8), target + σ (.n 23), σ (.n 23)] = [σ (.n 8), σ (.n 38), σ (.n 23)]
    rw [hadd, e2]
  · rw [← (congrArg Prod.fst hroot : root0 = _), ← e3]; exact l3
  · rw [← (congrArg Prod.snd hroot : root1 = _), ← e4]; exact l4

/-! ## After the tail -/

private theorem zipIdx_map_rangeM {α β : Type} [Inhabited α] (f : α × ℕ → β) (l : List α) :
    l.zipIdx.map f = (List.range l.length).map fun i => f (l.getD i default, i) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getElem_zipIdx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1)]

private theorem readsAt_getDM {p : E} {l : List E} (h : ReadsAt rd p l) :
    ∀ j < l.length, LoadHolds rd p j (l.getD j 0) := fun j hj => by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]; exact h j hj

theorem osPoint_noBlake (nFolds lane yrLog tch k : ℕ) :
    Stmt.noBlakeList (osPoint nFolds lane yrLog tch k) = true := by
  simp only [osPoint, Stmt.noBlakeList, Stmt.noBlake, Bool.true_and]
  rw [noBlakeList_flatten_range _ _ (fun i => by unfold osPtBlk; split <;> rfl)]

theorem osBases_noBlake (yrLog tch ba bb : ℕ) : ∀ (lvl : ℕ) (lvs : List OsLvl) (k : ℕ),
    Stmt.noBlakeList (osBases yrLog tch ba bb lvl lvs k).1 = true
  | _, [], _ => rfl
  | lvl, lv :: rest, k => by
    have hnr : ∀ items k', Stmt.noBlakeList (osBasisRow ba bb items k').1 = true := by
      intro items
      induction items with
      | nil => intro; rfl
      | cons it rest ih =>
        intro k'
        obtain ⟨slot, src, inv⟩ := it
        simp only [osBasisRow, noBlakeList_append, ih, Bool.and_true]
        unfold osBasisBlk; split <;> rfl
    simp only [osBases, noBlakeList_append, hnr, osBases_noBlake yrLog tch ba bb (lvl + 1) rest,
      Bool.and_self]

theorem osResiduals_noBlake (maxQ ich ba bb k : ℕ) (lvs : List OsLvl) :
    Stmt.noBlakeList (osResiduals maxQ ich ba bb k lvs) = true := by
  unfold osResiduals
  rw [zipIdx_map_rangeM, noBlakeList_flatten_range _ _ (fun _ => rfl)]

theorem osOodWeights_noBlake (yrLog tch : ℕ) : ∀ (prev ol : ℕ) (lvs : List OsLvl) (acc : Option ℕ) (k : ℕ),
    (∀ lv ∈ lvs, lv.oodHere = 1) → Stmt.noBlakeList (osOodWeights yrLog tch prev ol lvs acc k).1 = true
  | _, _, [], _, _, _ => rfl
  | prev, ol, lv :: rest, acc, k, hood => by
    have h1 : lv.oodHere = 1 := hood lv (by simp)
    have hnr : ∀ k', Stmt.noBlakeList (osOodWeight yrLog tch (prev - yrLog) lv.foldsOff ol 0 k') = true := by
      intro k'
      unfold osOodWeight osOodFacs
      rw [os_zipIdx_map_range, List.map_map]
      show Stmt.noBlakeList (List.flatten _) = true
      rw [noBlakeList_flatten_range _ _ (fun _ => rfl)]
    simp only [osOodWeights, h1, List.range_one, List.foldl_cons, List.foldl_nil]
    rw [noBlakeList_append, osOodWeights_noBlake yrLog tch _ _ rest _ _ (fun lv' h' => hood lv' (by simp [h']))]
    cases acc <;> simp [hnr, noBlakeList_append, Stmt.noBlakeList, Stmt.noBlake]

/-- What follows the tail has no `BLAKE2S` row. -/
theorem osFinish_noBlake (cfg : OsCfg) (st : OsSt) (tch : ℕ) (hood : ∀ lv ∈ cfg.levels.tail, lv.oodHere = 1) :
    Stmt.noBlakeList (osFinish cfg st tch) = true := by
  unfold osFinish
  simp only [noBlakeList_append, osPoint_noBlake, osBases_noBlake, osResiduals_noBlake,
    osOodWeights_noBlake _ _ _ _ _ _ _ hood]
  split <;> rfl

/-- **After the tail** (G:1229-1317), its residual loops given by `hres0` (`osFinish_sound`
with the callees it reads named): the guest returns the final claim, the rotated point's
buffer, the glued claims' weight at the terminal point and the residual's value there. -/
theorem osFinish_soundR {cfg : OsCfg} {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall)
    (hres0 : ∀ i < cfg.levels.length, ∃ fn, coreProgram.find? (cfg.lv i).resLoop = some fn ∧
      fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧ fn.body = resLoopOf cfg i (cfg.lv i))
    {st : OsSt} {tch : ℕ} {wL : WhirState} {residual tf : List E}
    (hfl : wL.folds.length = cfg.nFolds)
    (hfch : ∀ j < wL.folds.length, LoadHolds rd (σ (.n osFch)) j (wL.folds.getD j 0))
    (hgl : ∃ recs : List OsRec, recs.length = cfg.levels.length ∧ wL.glued = osGluedOf μ cfg recs ∧
      ∀ i < cfg.levels.length, OsRecOk rd σ cfg i (recs.getD i default))
    (hresl : residual.length = cfg.yrLen) (hres : ReadsAt rd (σ (.n osFmsg)) residual)
    (htfl : tf.length = cfg.yrLog) (htch : ReadsAt rd (σ (.n tch)) (tf ++ List.replicate (5 - cfg.yrLog) 0))
    {rets : List E} {C : CallRel}
    (hC7 : ∀ i < cfg.levels.length, ∀ a, a.length = 7 → C (cfg.lv i).resLoop a [] →
      coreProgram.Rel rd (cfg.lv i).resLoop a [])
    (hC2 : ∀ a r, a.length = 2 → C cfg.foldFinal a r → MeaningFoldFinalMsg cfg.yrLog rd a r)
    (h : Stmt.HoldsList C rd σ (osFinish cfg st tch) False (fun rs => rs = rets)) :
    ∃ pt, rets = [σ (.n st.t), pt,
        wL.glued.foldl (fun w c ↦ w + c.scalar * c.weightAt (wL.folds.drop c.foldStart ++ tf)) 0,
        multilinearEval residual tf] ∧
      ReadsAt rd pt (((wL.folds ++ tf).drop (cfg.lv 0).folds ++ (wL.folds ++ tf).take (cfg.lv 0).folds) ++
        List.replicate (42 - (cfg.nFolds + cfg.yrLog)) 0) := by
  obtain ⟨recs, hrecl, hglr, hrecs⟩ := hgl
  have hn := hok.len2
  have hhd : cfg.levels.headD default = cfg.lv 0 := by
    cases h' : cfg.levels with
    | nil => simp [h'] at hn
    | cons a b => simp [OsCfg.lv, h']
  unfold osFinish at h
  simp only [hhd] at h
  generalize hbs : osBases cfg.yrLog tch (st.k + 1 + 44) (st.k + 1 + 46) 0 cfg.levels (st.k + 1 + 47) = bs at h
  generalize hod : osOodWeights cfg.yrLog tch (cfg.lv 0).logCols 1 cfg.levels.tail none
    (bs.2 + 3 + 13 * cfg.levels.length) = od at h
  simp only [holdsList_append] at h
  obtain ⟨hF, h⟩ := holdsList_true_of (by rfl) h
  obtain ⟨hP, h⟩ := holdsList_true_of (by
    simp only [osPoint, Stmt.noRetList, Stmt.noRet, Bool.true_and]
    rw [noRetList_flatten_range _ _ (fun i => by unfold osPtBlk; split <;> rfl)]) h
  obtain ⟨-, h⟩ := holdsList_true_of (by rfl) h
  obtain ⟨-, h⟩ := holdsList_true_of (by rfl) h
  obtain ⟨hB, h⟩ := holdsList_true_of (by rw [← hbs]; exact osBases_noRet _ _ _ _ _ _ _) h
  obtain ⟨-, h⟩ := holdsList_true_of (by rfl) h
  obtain ⟨hI0, h⟩ := holdsList_true_of (by rfl) h
  obtain ⟨hR, h⟩ := holdsList_true_of (by
    unfold osResiduals; rw [zipIdx_map_rangeM, noRetList_flatten_range _ _ (fun _ => rfl)]) h
  obtain ⟨hO, h⟩ := holdsList_true_of (by rw [← hod]; exact osOodWeights_noRet _ _ _ _ _ _ _ hok.ood) h
  obtain ⟨hC, h⟩ := holdsList_true_of (by rfl) h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, and_true] at hF hI0 hC
  have hlast := hok.spec (cfg.levels.length - 1) (by rw [hok.len]; omega)
  rw [show cfg.levels.length - 1 + 1 = Lall.length by rw [hok.len]; omega, List.drop_length] at hlast
  have hyr : cfg.yrLen = 2 ^ cfg.yrLog := by
    rw [hlast.yrLen, hok.nFolds, ← hok.total, Nat.add_sub_cancel_left]
  -- the residual's value
  obtain ⟨mm, ps, hmml, hpsl, hmm, hps, hyat⟩ := hC2 _ _ rfl hF
  have hps' : ps = tf := os_readsAt_unique hps (os_readsAt_prefix htch) (by rw [hpsl, htfl])
  have hmm' : mm = residual := os_readsAt_unique hmm hres (by rw [hmml, hresl, hyr])
  simp only [List.cons.injEq, and_true] at hyat
  rw [hps', hmm'] at hyat
  -- the point
  have htch' : ∀ j < cfg.yrLog, LoadHolds rd (σ (.n tch)) j (tf.getD j 0) := fun j hj => by
    have := readsAt_getDM htch j (by simp; omega)
    rwa [os_getD_append_lt (by omega)] at this
  have hpt := osPoint_sound hok.laneLe hok.pt42 hfl htfl (fun j hj => hfch j (by rw [hfl]; exact hj))
    htch' hP
  set n := cfg.levels.length with hnn
  set P := wL.folds
  -- the levels' facts
  have hspec : ∀ i < n, LvSpec cfg μ i (Lall.getD i default) (Lall.drop (i + 1)) := fun i hi =>
    hok.spec i (by rw [hok.len]; exact hi)
  -- the basis rows
  rw [← hbs] at hB
  have hbasis : ∀ i < n, ∀ it ∈ osBasisCoords cfg.yrLog tch i (cfg.lv i),
      OsBasisOk rd σ (st.k + 1 + 44) (st.k + 1 + 46) it := fun i hi it hit =>
    osBases_sound 0 cfg.levels _ hB i hi it (by simpa using hit)
  -- the residual chains
  have hres' := osResiduals_sound (ich := bs.2 + 1) (ba := st.k + 1 + 44) (bb := st.k + 1 + 46)
    (k := bs.2 + 3) hres0 (fun i hi => ⟨((hspec i hi).logCols).2.1, ((hspec i hi).logCols).2.2⟩) hC7 hR
  choose! rc hrcB hrc0 i0 bv rr hi0 hbv hrr hi1 using hres'
  have hich : ∀ i ≤ n, LoadHolds rd (σ (.n (bs.2 + 1))) i (∑ i' ∈ Finset.range i, bv i' * rr i') := by
    intro i hi
    induction i with
    | zero => rw [Finset.sum_range_zero, ← word_zero, ← hI0.1]; exact hI0.2
    | succ i ih =>
      have := hi1 i (by omega)
      rw [loadHolds_unique (hi0 i (by omega)) (ih (by omega))] at this
      rwa [Finset.sum_range_succ]
  -- the levels' terminal points
  set pt : ℕ → List E := fun i => P.drop (osLevelF cfg i) ++ tf
  have hIW : ∀ i < n, rr i = inducedWeight (μ - osLevelF cfg i) (recs.getD i default).queries
      (powers (recs.getD i default).lam (recs.getD i default).queries.length) (pt i) := by
    intro i hi
    obtain ⟨hpre, hrfo, hml, hFP, htab⟩ := hok.lvs i hi
    rw [← ((hspec i hi).logCols).1]
    exact os_rc_eq_inducedWeight htfl (by rw [hfl]; exact hFP) (by rw [hfl]; exact hpre) hrfo hml htab.ok
      hfch htch' (hbasis i hi) (hrecs i hi) (hrcB i hi) (hrc0 i hi) (hrr i hi)
  -- the out-of-domain weights
  set W : ℕ → E := fun j => match (recs.getD j default).ood with
    | some z => (recs.getD j default).lam * eqEval z (pt j)
    | none => 0
  have htail : ∀ i, cfg.levels.tail.getD i default = cfg.lv (i + 1) := by
    intro i; simp [OsCfg.lv, List.getD_eq_getElem?_getD]
  have hsome : ∀ i < n - 1, ∃ z, (recs.getD i default).ood = some z := by
    intro i hi
    have := (hrecs i (by omega)).2.2.2.1
    rw [hok.yrLevel] at this
    cases h' : (recs.getD i default).ood with
    | none => exact absurd (this.mp h') (by omega)
    | some z => exact ⟨z, rfl⟩
  rw [← hod] at hO
  have hOOD := osOodWeights_sound cfg.levels.tail 1 (cfg.lv 0).logCols none _ W hok.ood (fun i hi k' hk => by
    have hi' : i + 1 < n := by simp at hi; omega
    have hpc : osPrevColsAt cfg.levels.tail (cfg.lv 0).logCols i = (cfg.lv i).logCols := by
      cases i with
      | zero => rfl
      | succ i => simp only [osPrevColsAt, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, htail]
    have hfo : (cfg.levels.tail.getD i default).foldsOff = osLevelF cfg i := by
      rw [htail]
      have hs := hspec i (by omega)
      rw [List.drop_eq_getElem_cons (by rw [hok.len]; omega)] at hs
      exact hs.nextFolds
    rw [hpc, hfo] at hk
    rw [hpc]
    obtain ⟨hpre, hrfo, hml, hFP, -⟩ := hok.lvs i (by omega)
    obtain ⟨z, hz⟩ := hsome i (by omega)
    obtain ⟨-, -, -, -, -, hzs⟩ := hrecs i (by omega)
    obtain ⟨-, hzl, hzr, hsc⟩ := hzs z hz
    have hzl' : z.length = (cfg.lv i).logCols := hzl
    have hlv : (cfg.lv i).logCols = (cfg.levels[i]?.getD default).logCols := by
      simp [OsCfg.lv, List.getD_eq_getElem?_getD]
    have hzf : (cfg.lv i).logCols - cfg.yrLog + cfg.yrLog = (cfg.lv i).logCols := by omega
    have hptl : (pt i).length = (cfg.lv i).logCols := by simp [pt, P, hfl, htfl]; omega
    rw [osOodWeight_sound (by have := (hspec i (by omega)).logCols.2.1; omega) hk
      (sc := (recs.getD i default).lam) (z := fun t => z.getD t 0) (c := fun t => (pt i).getD t 0)
      (by convert hsc using 2; ring)
      (fun t ht => by
        have := readsAt_getDM hzr t (by omega)
        rw [loadHolds_mul_gen_pow] at this
        convert this using 2; ring)
      (fun t ht => by
        unfold osOodSrc
        split
        · rw [os_getD_append_lt (by simp [P, hfl]; omega), os_getD_drop']
          exact hfch _ (by rw [hfl]; omega)
        · rw [os_getD_append_ge (by simp [P, hfl]; omega)]
          simp only [List.length_drop, P, hfl]
          rw [show t - (cfg.nFolds - osLevelF cfg i) = t - ((cfg.lv i).logCols - cfg.yrLog) by omega]
          exact htch' _ (by omega))]
    simp only [W, hz]
    rw [os_eqEval_eq z (pt i) (by rw [hzl, hptl]), hzl, hzf]) hO
  simp only [osAccVal, zero_add] at hOOD
  rw [hod] at hOOD
  -- the glued weight, level by level
  have hlvl : ∀ i < n, osRecInner μ (osLevelF cfg i) (recs.getD i default) (pt i) = bv i * rr i + W i := by
    intro i hi
    obtain ⟨-, -, -, hnone, hb1, hb2⟩ := hrecs i hi
    rw [hIW i hi]
    unfold osRecInner
    simp only [W]
    cases h' : (recs.getD i default).ood with
    | none =>
      rw [loadHolds_unique (hbv i hi) (hb1 h')]
      simp
    | some z =>
      rw [loadHolds_unique (hbv i hi) (hb2 z h').1]
      simp only [one_mul]
      ring
  have hW0 : W (n - 1) = 0 := by
    have := (hrecs (n - 1) (by omega)).2.2.2.1
    rw [hok.yrLevel] at this
    simp only [W, this.mpr rfl]
  have hinner : wL.glued.foldl (fun w c ↦ w + c.scalar * c.weightAt (wL.folds.drop c.foldStart ++ tf)) 0 =
      (∑ i ∈ Finset.range n, bv i * rr i) + ∑ i ∈ Finset.range (n - 1), W i := by
    rw [hglr, os_gluedOf_inner, hrecl, Finset.sum_congr rfl fun i hi => hlvl i (Finset.mem_range.mp hi),
      Finset.sum_add_distrib]
    congr 1
    rw [show n = n - 1 + 1 by omega, Finset.sum_range_succ, Nat.add_sub_cancel, hW0, add_zero]
  have hichN := loadHolds_unique hC.2.2 (hich n le_rfl)
  rw [show cfg.levels.tail.length = n - 1 by simp [n]] at hOOD
  -- the returns
  rcases hacc : od.2.1 with _ | a
  · rw [hacc] at h hOOD
    simp only at hOOD
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at h
    obtain ⟨-, -, -, e3, hret⟩ := h
    refine ⟨σ (.n (st.k + 1)), ?_, hpt⟩
    rw [← hret, hC.1, hC.2.1, e3, hichN, hinner, ← hOOD, add_zero, hyat]
  · rw [hacc] at h hOOD
    simp only at hOOD
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at h
    obtain ⟨-, -, -, e3, e4, hret⟩ := h
    refine ⟨σ (.n (st.k + 1)), ?_, hpt⟩
    rw [← hret, hC.1, hC.2.1, e4, e3, hichN, hinner, ← hOOD, hyat]

/-! ## The theorem -/

/-- The callees of a configuration under a hash model, as their meanings, and its residual
loops. -/
structure OsCalleesM (M : HashModel) (rd : Reader) (cfg : OsCfg) : Prop where
  lv : ∀ i < cfg.levels.length, LvCalleesM M rd cfg i
  fin : ∀ a r, coreProgram.RelB M.sem rd cfg.finalMsg a r → MeaningOpeningFinalMessageWith M cfg.yrLen rd a r
  ff : ∀ a r, coreProgram.RelB M.sem rd cfg.foldFinal a r → MeaningFoldFinalMsg cfg.yrLog rd a r
  res : ∀ i < cfg.levels.length, ∃ fn, coreProgram.find? (cfg.lv i).resLoop = some fn ∧
    fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧ fn.body = resLoopOf cfg i (cfg.lv i)

/-- The levels' `opening_queries` are sound under a hash model with the openings `wq`, over the
call relation `C` (`OsQueriesWC`). -/
def OsQueriesWCM (M : HashModel) (C : CallRel) (rd : Reader) (cfg : OsCfg)
    (wq : ℕ → List E → List E → List Opening) : Prop :=
  ∀ i < cfg.levels.length, SoundQueriesWCM M C rd (cfg.lv i).queriesFn (if i = 0 then 1 else 0)
    (2 ^ (cfg.lv i).folds) (cfg.lv i).depth (cfg.lv i).capDepth (wq i)

/-- The levels' callees under a hash model give witness functions for their `opening_queries`. -/
theorem exists_osQueriesWM {cfg : OsCfg} (hcal : OsCalleesM M rd cfg) :
    ∃ wq, OsQueriesWCM M (coreProgram.RelB M.sem rd) rd cfg wq := by
  have h : ∀ i, ∃ w, i < cfg.levels.length → SoundQueriesWCM M (coreProgram.RelB M.sem rd) rd
      (cfg.lv i).queriesFn (if i = 0 then 1 else 0) (2 ^ (cfg.lv i).folds) (cfg.lv i).depth
      (cfg.lv i).capDepth w := by
    intro i
    by_cases hi : i < cfg.levels.length
    · obtain ⟨w, hw⟩ := exists_soundQueriesWM (hcal.lv i hi).queries
      exact ⟨w, fun _ => hw⟩
    · exact ⟨fun _ _ => [], fun h => absurd h hi⟩
  choose wq hwq using h
  exact ⟨wq, fun i hi => hwq i hi⟩

/-- **`open_stacked`'s frame at a configuration under a hash model, its openings named**
(G:1047-1317; TRIAGE #36; `open_stacked_frame_wC`): a valuation of the body `osBody cfg` at the
parameters `fs0, fs1, target, root0, root1, cur`, under the model's semantics over a call relation
`C` below the program's, at a configuration whose facts match the ladder of `(μ, r)`, whose
callees have their meanings under the model and whose levels' `opening_queries` are sound with the
openings `wq`, gives `OpenOutWM` at the openings `osOsOf cfg σ wq`. -/
theorem open_stacked_frame_wCM {C : CallRel} (hC : CallRel.Le C (coreProgram.RelB M.sem rd))
    {cfg : OsCfg} {μ r : ℕ} {Lall : List Whir.Level}
    (hok : OsCfgOk cfg μ r Lall) (hcal : OsCalleesM M rd cfg) {wq : ℕ → List E → List E → List Opening}
    (hqW : OsQueriesWCM M C rd cfg wq) {root : Digest}
    {fs0 fs1 target root0 root1 cur : E} {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (hpar : [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5)] =
      [fs0, fs1, target, root0, root1, cur])
    {body : List Stmt} (hb : body = osBody cfg)
    (h : Stmt.HoldsListB M.sem C rd σ body False fun rs => rs = rets) :
    OpenOutWM M rd μ r root fs0 fs1 target cur rets (osOsOf cfg σ wq) := by
  subst hb
  simp only [List.cons.injEq] at hpar
  obtain ⟨e0, e1, e2, e3, e4, e5, -⟩ := hpar
  have hn := hok.len2
  unfold osBody at h
  simp only [holdsListB_append] at h
  -- the head
  obtain ⟨hH, h⟩ := holdsListB_true_of (osHead_noRet _) h
  obtain ⟨cv, d1, d2, x0, x1, hcv, hd1, hd2, hinv0⟩ :=
    osHead_soundM (logN := μ) hok.off0 hroot ⟨e0, e1, e2, e3, e4, e5⟩ hH
  -- the levels
  obtain ⟨hL, h⟩ := holdsListB_true_of (osLevels_noRet _ _ _ _) h
  have hcl : ∀ i < Lall.length, LvCalleesM M rd cfg i := fun i hi => hcal.lv i (by rw [← hok.len]; exact hi)
  obtain ⟨ys, os, cvL, wL, rootsL, residual, hosE, hend, hresl, hres, hcont⟩ :=
    osLevels_soundM (lane := (cfg.lv 0).folds) hC hok.len hok.spec hcl
      (fun i hi => hqW i (by rw [← hok.len]; exact hi)) hcal.fin (cfg.levels.length - 1) 0 _ _
      _ _ _ (by rw [hok.len]; omega) hinv0 (by simpa using hL)
  rw [hok.len] at hend hcont
  simp only [List.drop_zero] at hend hcont hosE
  rw [← osOsOf] at hosE
  rw [← hosE]
  generalize (osLevels cfg 0 cfg.levels (osHead cfg).2).2 = sL at *
  -- the tail
  obtain ⟨hT, h⟩ := holdsListB_true_of (osTail_noRet _ _) h
  obtain ⟨ysT, tf, cvT, htfl, hreads, hrunT, htch⟩ :=
    osTail_soundM hok.yr2 hok.yr5 hend.cur hend.co (holdsListB_rel hC hT)
  generalize osTail cfg.yrLog sL = tl at *
  -- after the tail
  rw [holdsListB_iff_of_noBlake (osFinish_noBlake _ _ _ hok.ood)] at h
  have hnf : wL.folds.length = cfg.nFolds := by rw [hend.nfolds, hok.nFolds]
  obtain ⟨pt, hrets, hpt⟩ := osFinish_soundR hok hcal.res hnf hend.folds hend.glued hresl hres htfl htch
    (fun i hi a _ h => (resLoop_relB (hcal.res i hi).choose_spec.1 (hcal.res i hi).choose_spec.2.2 _ _).mp
      (hC _ _ _ h))
    (fun a r _ h => hcal.ff a r (hC _ _ _ h)) h
  have hptl : ((wL.folds ++ tf).drop (cfg.lv 0).folds ++ (wL.folds ++ tf).take (cfg.lv 0).folds).length =
      cfg.nFolds + cfg.yrLog := by
    simp [hnf, htfl]; have := hok.laneLe; omega
  refine ⟨cv, [x0, x1] ++ ys ++ ysT,
    ⟨(wL.folds ++ tf).drop (cfg.lv 0).folds ++ (wL.folds ++ tf).take (cfg.lv 0).folds,
      wL.glued.foldl (fun w c ↦ w + c.scalar * c.weightAt (wL.folds.drop c.foldStart ++ tf)) 0,
      multilinearEval residual tf, σ (.n tl.2.1.t)⟩, cvT, rootsL, hcv, hreads, fun rest orest => ?_,
    pt, by rw [hrets], by rw [hptl]; exact hpt, by rw [hptl, hok.total]⟩
  have htail : RunsM M (osTailOpen (μ - osLevelF cfg (cfg.levels.length - 1)) (cfg.lv 0).folds wL residual)
      ⟨cvL, ysT ++ rest, orest, rootsL⟩
      ⟨(wL.folds ++ tf).drop (cfg.lv 0).folds ++ (wL.folds ++ tf).take (cfg.lv 0).folds,
        wL.glued.foldl (fun w c ↦ w + c.scalar * c.weightAt (wL.folds.drop c.foldStart ++ tf)) 0,
        multilinearEval residual tf, σ (.n tl.2.1.t)⟩ ⟨cvT, rest, orest, rootsL⟩ := by
    rw [hok.nFolds, ← hok.total, Nat.add_sub_cancel_left]
    unfold osTailOpen
    rw [hend.quad]
    exact RunsM.bind ((hrunT wL.target).runsM _ _ _) (RunsM.ret _ _)
  have hrun := hcont (ysT ++ rest) orest _ _ htail
  show RunsM M (whirOpen μ r target) _ _ _
  unfold whirOpen
  rw [show oqR 1 (2 ^ (cfg.lv 0).folds) = 2 ^ (cfg.lv 0).folds by simp [oqR]] at hrun
  rw [hok.config, hok.shape]
  refine RunsM.bind (RunsM.ret _ _) ?_
  rw [hok.lane]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine RunsM.bind ((runsToM_roundPoly3 target x0 x1 hd1 hd2).runsM _ _ _) ?_
  exact hrun

/-- **`open_stacked` at a configuration is sound under a hash model** (G:1047-1317; TRIAGE #36):
the relation under `M.sem` of a function whose body is `osBody cfg`, at a configuration whose
facts match the ladder of `(μ, r)` and whose callees have their meanings under the model, gives
`OpenOutM` (`whirOpen μ r`, V:1763, over `M.H`, up to its terminal). -/
theorem open_stacked_model {cfg : OsCfg} {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall)
    {name : String} {fn : Fn} (hfind : coreProgram.find? name = some fn)
    (hp : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5]) (hb : fn.body = osBody cfg)
    (hcal : OsCalleesM M rd cfg) {root : Digest} {fs0 fs1 target root0 root1 cur : E} {rets : List E}
    (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.RelB M.sem rd name [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOutM M rd μ r root fs0 fs1 target cur rets := by
  rw [relB_iff_sem hfind, hp] at h
  obtain ⟨σ, hpar, h⟩ := h
  simp only [List.map_cons, List.map_nil] at hpar
  obtain ⟨wq, hwq⟩ := exists_osQueriesWM hcal
  exact ⟨_, open_stacked_frame_wCM (fun _ _ _ h => h) hok hcal hwq hroot hpar hb h⟩

end
end LeanVM.Guest.B1
