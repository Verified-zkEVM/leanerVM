/-
  LeanVM.Guest.B1.Comp.Whir.StackedEndC

  `open_stacked`'s head and tail over a completeness model.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.StackedBlocksC

/-!
# The head and the tail over a completeness model (TRIAGE #36)

`Whir/StackedC10.lean` (`osTail_completeC`: the tail's fold rounds, run answered, and its closing
squeeze, answered) and `StackedC11.lean` (`osHead_completeC`: the first quadratic's two reads,
answered) over a `CompModel` and a total hash `Ht`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub LeanVM.E2E.Complete

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {CM : CompModel} {Ht : Bytes → Digest}

/-- The values of `osTail` from its first: the buffer's size and pointer `tchv`, the fold rounds',
the closing squeeze's, the final claim's, the zeroed entries. -/
def osTailValsW (Ht : Bytes → Digest) (yrLog : ℕ) (xs : List E) (cv : Digest) (p : ℕ) (q : List E) (cbv : E) (co : ℕ) (tchv : E)
    (w1 : WhirState) (cv1 : Digest) : List E :=
  let last := challengeOf (sqCvW Ht cv1)
  let c := w1.quad.getD 0 0
  let b := w1.quad.getD 1 0
  let a := w1.quad.getD 2 0
  [osGw 5, tchv] ++ osFoldsValsW Ht xs (yrLog - 1) cv p q cbv co ++ (List.range 14).map (sqValsW Ht cv1) ++
    [last * b, c + last * b, last * last, last * last * a, c + last * b + last * last * a] ++
    List.replicate (5 - yrLog) 0

/-- **The tail** at its honest values (G:1216-1228). -/
theorem osTail_completeC {yrLog : ℕ} {s : OsSt} {cv : Digest} {cur : E} {p : ℕ}
    (hat : OsAt σ s cv cur p) (hcop : s.co ≤ p) (hco : s.co ≤ 8) {xs : List E} {osp : List Opening}
    {roots : List (Digest × ℕ × ℕ)} {w : WhirState} (hw : w.folds = [])
    (hq : w.quad = [σ (.n s.c), σ (.n s.b), σ (.n s.a)]) {w1 : WhirState} {chs : List E} {cv1 : Digest}
    (hrun : RunsW Ht (foldRounds (yrLog - 1) w []) ⟨cv, xs.drop p, osp, roots⟩ (w1, chs)
      ⟨cv1, xs.drop (p + 2 * (yrLog - 1)), osp, roots⟩)
    (hA : AnsRun CM.hm.H Ht (foldRounds (yrLog - 1) w []) ⟨cv, xs.drop p, osp, roots⟩)
    (asq : sqCvM CM.hm cv1 = some (sqCvW Ht cv1)) {tchv : E}
    (htch : ∀ j < yrLog - 1, LoadHolds rd tchv j (chs.getD j 0))
    (hlast : LoadHolds rd tchv (yrLog - 1) (challengeOf (sqCvW Ht cv1)))
    (hz : ∀ j < 5 - yrLog, LoadHolds rd tchv (yrLog + j) 0) {kret : List E → Prop}
    (hcf : ∀ (cv' : Digest) (p' : ℕ) (q' : List E), q'.length = 3 → p' + 2 ≤ xs.length →
      RunsToM CM.hm (foldStep q') cv' [xs.getD p' 0, xs.getD (p' + 1) 0]
        (challengeOf (sqCvW Ht cv'), polyEval q' (challengeOf (sqCvW Ht cv')),
          [xs.getD p' 0, polyEval q' (challengeOf (sqCvW Ht cv')) + xs.getD (p' + 1) 0, xs.getD (p' + 1) 0])
        (obsAllW Ht (sqCvW Ht cv') [xs.getD p' 0, xs.getD (p' + 1) 0]) →
      C "opening_fold" [(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ p', q'.getD 0 0, q'.getD 1 0,
        q'.getD 2 0] (osFoldRetsW Ht xs cv' p' q' (cur * gen ^ p')))
    (hv : ∀ j < (osTailValsW Ht yrLog xs cv p w.quad (cur * gen ^ (p - s.co)) s.co tchv w1 cv1).length,
      σ (.n (s.k + j)) = (osTailValsW Ht yrLog xs cv p w.quad (cur * gen ^ (p - s.co)) s.co tchv w1 cv1).getD j 0) :
    Stmt.HoldsListB CM.sem C rd σ (osTail yrLog s).1 True kret ∧
      σ (.n (osTail yrLog s).2.1.t) = polyEval w1.quad (challengeOf (sqCvW Ht cv1)) ∧
      σ (.n (osTail yrLog s).2.2.1) = tchv ∧
      (osTail yrLog s).2.1.k = s.k + (osTailValsW Ht yrLog xs cv p w.quad (cur * gen ^ (p - s.co)) s.co tchv w1 cv1).length := by
  have hcb := os_cb_of_at hat hcop
  set F := osFoldsValsW Ht xs (yrLog - 1) cv p w.quad (cur * gen ^ (p - s.co)) s.co with hF
  set Q := (List.range 14).map (sqValsW Ht cv1) with hQ
  set last := challengeOf (sqCvW Ht cv1)
  set T : List E := [last * w1.quad.getD 1 0, w1.quad.getD 0 0 + last * w1.quad.getD 1 0, last * last,
    last * last * w1.quad.getD 2 0, w1.quad.getD 0 0 + last * w1.quad.getD 1 0 + last * last * w1.quad.getD 2 0]
    with hT
  have hV : osTailValsW Ht yrLog xs cv p w.quad (cur * gen ^ (p - s.co)) s.co tchv w1 cv1 =
      [osGw 5, tchv] ++ F ++ Q ++ T ++ List.replicate (5 - yrLog) 0 := rfl
  rw [hV] at hv ⊢
  obtain ⟨hv4, gZ⟩ := os_look_app hv
  obtain ⟨hv3, gT⟩ := os_look_app hv4
  obtain ⟨hv2, gQ⟩ := os_look_app hv3
  obtain ⟨gH, gF⟩ := os_look_app hv2
  have h0 : σ (.n s.k) = osGw 5 := by simpa using gH 0 (by simp)
  have h1 : σ (.n (s.k + 1)) = tchv := by simpa using gH 1 (by simp)
  simp only [List.length_cons, List.length_nil, List.length_append] at gF gQ gT gZ
  have hQl : Q.length = 14 := by simp [hQ]
  have hTl : T.length = 5 := rfl
  set s2 : OsSt := { s with k := s.k + 2 }
  have hat2 : OsAt σ s2 cv cur p := ⟨hat.fs, hat.cursor⟩
  obtain ⟨hFh, hatF, hsp, hqF, -, -, -, -, -, hkF⟩ := osFolds_completeC (CM := CM) (rd := rd) (σ := σ) (fch := s.k + 1)
    (kret := kret) hcf (yrLog - 1) 0 s2 cv p w [] osp roots (w1, chs) _ hat2 (by show s.co < _; omega) hq hrun hA
    (fun j hj => by
      show σ (.n (s.k + 2 + j)) = _
      rw [show (σ (.n s2.cb)) = cur * gen ^ (p - s.co) from hcb] at hj ⊢
      exact gF j hj)
    (fun j hj => by
      obtain ⟨chs', hf1, hf2, -⟩ := (os_foldRounds_foldsW hrun)
      have hf1' : w1.folds = w.folds ++ chs' := hf1
      have hf2' : chs = chs' := by simpa using hf2
      subst hf2'
      show LoadHolds rd (σ (.n (s.k + 1))) (0 + j) (w1.folds.getD (w.folds.length + j) 0)
      simp only [h1, hf1', hw, List.nil_append, List.length_nil, Nat.zero_add]
      exact htch j hj)
  simp only at hatF hqF hkF
  rw [show (σ (.n s2.cb)) = cur * gen ^ (p - s.co) from hcb, ← hF] at hkF
  set f := osFolds (s.k + 1) 0 (yrLog - 1) s2 with hfd
  have hbb : f.2.k = s.k + (2 + F.length) := by rw [hkF]; simp only [s2]; ring
  have eQ : ∀ j < 14, σ (.n (f.2.k + j)) = sqValsW Ht cv1 j := fun j hj => by
    rw [hbb, gQ j (by rw [hQl]; exact hj), hQ]
    simp [List.getD_eq_getElem?_getD, hj]
  have eT : ∀ j < 5, σ (.n (f.2.k + 14 + j)) = T.getD j 0 := fun j hj => by
    rw [hbb, show s.k + (2 + F.length) + 14 = s.k + (2 + F.length + Q.length) by rw [hQl]; ring]
    exact gT j (by rw [hTl]; exact hj)
  have eZ : ∀ j < 5 - yrLog, σ (.n (f.2.k + 14 + 5 + j)) = 0 := fun j hj => by
    rw [hbb, show s.k + (2 + F.length) + 14 + 5 = s.k + (2 + F.length + Q.length + T.length) by
      rw [hQl, hTl]; ring]
    rw [gZ j (by simp; exact hj)]
    simp [List.getD_eq_getElem?_getD, hj]
  have e13 : σ (.n (f.2.k + 13)) = last := eQ 13 (by omega)
  have t0 := eT 0 (by omega); have t1 := eT 1 (by omega); have t2 := eT 2 (by omega)
  have t3 := eT 3 (by omega); have t4 := eT 4 (by omega)
  simp only [hT, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at t0 t1 t2 t3 t4
  have hq0 : w1.quad.getD 0 0 = σ (.n f.2.c) := by rw [hqF]; rfl
  have hq1 : w1.quad.getD 1 0 = σ (.n f.2.b) := by rw [hqF]; rfl
  have hq2 : w1.quad.getD 2 0 = σ (.n f.2.a) := by rw [hqF]; rfl
  unfold osTail
  dsimp only
  rw [← hfd]
  refine ⟨?_, ?_, h1, ?_⟩
  · simp only [holdsListB_append]
    refine (holdsListB_noRet _ rfl _ _).mpr ⟨?_, (holdsListB_noRet _ (osFolds_noRet _ _ _ _) _ _).mpr ⟨hFh,
      (holdsListB_noRet _ (by simp [squeezeT, squeezeStateT, challengeT, Stmt.noRetList, Stmt.noRet]) _ _).mpr
      ⟨?_, (holdsListB_noRet _ rfl _ _).mpr ⟨?_, ?_⟩⟩⟩⟩
    · simp only [osHeap, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, and_true]
      exact h0
    · exact holdsB_squeezeT_comp _ _ _ ⟨⟨cv1, sqCvW Ht cv1, hatF.fs, asq, fun j hj => by
        rw [eQ j hj, sqValsW_eq Ht cv1 hj]⟩, trivial⟩
    · simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, and_true]
      refine ⟨by rw [e13, h1]; exact hlast, by rw [t0, e13, hq1], by rw [t1, t0, hq0], by rw [t2, e13],
        by rw [t3, t2, hq2], by rw [t4, t1, t3]⟩
    · rw [holdsListB_flatten_range _ _ (fun _ => rfl)]
      refine ⟨fun j hj => ?_, trivial⟩
      simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, and_true]
      have := eZ j hj
      rw [show f.2.k + 14 + 5 + j = f.2.k + 14 + 5 + j from rfl] at this
      refine ⟨by rw [this, word_zero], by rw [this, h1]; exact hz j hj⟩
  · show σ (.n (f.2.k + 14 + 4)) = _
    rw [t4, hqF, os_polyEval_three]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
  · show f.2.k + 14 + 5 + (5 - yrLog) = _
    rw [hbb]; simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate, hQl, hTl]
    ring


/-- The head's values from `.n 0`: the parameters, the state's copies, the two reads, the first
quadratic's middle coefficient, each fixed buffer's size and pointer. -/
def osHeadValsW (Ht : Bytes → Digest) (cfg : OsCfg) (fs0 fs1 target root0 root1 cur : E) (cv : Digest) (x0 x1 : E) (P : OsPtrs) :
    List E :=
  [fs0, fs1, target, root0, root1, cur, fs0, fs1] ++ osFsNextValsW Ht x0 cv ++ osFsNextValsW Ht x1 (obsCvW Ht cv x0) ++
    [target + x1, osGw (4 * cfg.capLen), P.caps, osGw cfg.capLen, P.flags, osGw cfg.yrLen, P.fmsg,
      osGw (2 * cfg.levels.length), P.roots, osGw cfg.nFolds, P.fch, osGw cfg.levels.length, P.betas,
      osGw (cfg.levels.length * cfg.maxQ), P.qw, osGw cfg.posLen, P.qpos, osGw cfg.posLen, P.qbp,
      osGw (cfg.levels.length * 22), P.oodz, osGw (cfg.levels.length * 4), P.ood]

theorem os_length_headValsW (cfg : OsCfg) (fs0 fs1 target root0 root1 cur : E) (cv : Digest) (x0 x1 : E)
    (P : OsPtrs) : (osHeadValsW Ht cfg fs0 fs1 target root0 root1 cur cv x0 x1 P).length = 61 := by
  simp [osHeadValsW, os_length_fsNextValsW]

/-- **The head** at its honest values (G:1062-1094). -/
theorem osHead_completeC {cfg : OsCfg} {fs0 fs1 target root0 root1 cur : E} {cv : Digest} {x0 x1 : E}
    {P : OsPtrs} (hcv : (fs0, fs1) = digestScalars cv) (lx0 : LoadHolds rd cur 0 x0)
    (lx1 : LoadHolds rd cur 1 x1) (lr0 : LoadHolds rd P.roots 0 root0) (lr1 : LoadHolds rd P.roots 1 root1)
    (ax0 : obsCvM CM.hm cv x0 = some (obsCvW Ht cv x0))
    (ax1 : obsCvM CM.hm (obsCvW Ht cv x0) x1 = some (obsCvW Ht (obsCvW Ht cv x0) x1))
    {kret : List E → Prop}
    (hv : ∀ j < 61, σ (.n j) = (osHeadValsW Ht cfg fs0 fs1 target root0 root1 cur cv x0 x1 P).getD j 0) :
    Stmt.HoldsListB CM.sem C rd σ (osHead cfg).1 True kret ∧
      OsAt σ (osHead cfg).2 (obsCvW Ht (obsCvW Ht cv x0) x1) cur 2 ∧ (osHead cfg).2.co = 2 ∧
      [σ (.n (osHead cfg).2.c), σ (.n (osHead cfg).2.b), σ (.n (osHead cfg).2.a)] = [x0, target + x1, x1] ∧
      σ (.n (osHead cfg).2.t) = target ∧ OsPtrsAt σ P ∧ (osHead cfg).2.k = 61 := by
  set A : List E := [fs0, fs1, target, root0, root1, cur, fs0, fs1]
  set B := osFsNextValsW Ht x0 cv
  set Cn := osFsNextValsW Ht x1 (obsCvW Ht cv x0)
  set D : List E := [target + x1, osGw (4 * cfg.capLen), P.caps, osGw cfg.capLen, P.flags, osGw cfg.yrLen, P.fmsg,
      osGw (2 * cfg.levels.length), P.roots, osGw cfg.nFolds, P.fch, osGw cfg.levels.length, P.betas,
      osGw (cfg.levels.length * cfg.maxQ), P.qw, osGw cfg.posLen, P.qpos, osGw cfg.posLen, P.qbp,
      osGw (cfg.levels.length * 22), P.oodz, osGw (cfg.levels.length * 4), P.ood] with hD
  have hV : osHeadValsW Ht cfg fs0 fs1 target root0 root1 cur cv x0 x1 P = A ++ B ++ Cn ++ D := rfl
  have hl : (A ++ B ++ Cn ++ D).length = 61 := by rw [← hV]; exact os_length_headValsW _ _ _ _ _ _ _ _ _ _ _
  have hv' : ∀ j < (A ++ B ++ Cn ++ D).length, σ (.n (0 + j)) = (A ++ B ++ Cn ++ D).getD j 0 := fun j hj => by
    rw [Nat.zero_add, ← hV]; exact hv j (by rw [hl] at hj; exact hj)
  obtain ⟨hABC, gD⟩ := os_look_app hv'
  obtain ⟨hAB, gC⟩ := os_look_app hABC
  obtain ⟨gA, gB⟩ := os_look_app hAB
  have lA : A.length = 8 := rfl
  have lB : B.length = 15 := os_length_fsNextValsW _ _
  have lC : Cn.length = 15 := os_length_fsNextValsW _ _
  simp only [List.length_append, lA, lB, lC, Nat.zero_add] at gB gC gD
  have a0 : σ (.n 0) = fs0 := gA 0 (by simp [A])
  have a1 : σ (.n 1) = fs1 := gA 1 (by simp [A])
  have a2 : σ (.n 2) = target := gA 2 (by simp [A])
  have a3 : σ (.n 3) = root0 := gA 3 (by simp [A])
  have a4 : σ (.n 4) = root1 := gA 4 (by simp [A])
  have a5 : σ (.n 5) = cur := gA 5 (by simp [A])
  have a6 : σ (.n 6) = fs0 := gA 6 (by simp [A])
  have a7 : σ (.n 7) = fs1 := gA 7 (by simp [A])
  have d : ∀ j < 23, σ (.n (38 + j)) = D.getD j 0 := fun j hj => gD j (by simp [hD]; omega)
  have d0 := d 0 (by omega); have d1 := d 1 (by omega); have d2 := d 2 (by omega); have d3 := d 3 (by omega)
  have d4 := d 4 (by omega); have d5 := d 5 (by omega); have d6 := d 6 (by omega); have d7 := d 7 (by omega)
  have d8 := d 8 (by omega); have d9 := d 9 (by omega); have d10 := d 10 (by omega)
  have d11 := d 11 (by omega); have d12 := d 12 (by omega); have d13 := d 13 (by omega)
  have d14 := d 14 (by omega); have d15 := d 15 (by omega); have d16 := d 16 (by omega)
  have d17 := d 17 (by omega); have d18 := d 18 (by omega); have d19 := d 19 (by omega)
  have d20 := d 20 (by omega); have d21 := d 21 (by omega); have d22 := d 22 (by omega)
  simp only [hD, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero, Nat.reduceAdd]
    at d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d21 d22
  set s0 : OsSt := ⟨8, 6, 7, 5, 0, 0, 0, 0, 2⟩
  have hat0 : OsAt σ s0 cv cur 0 := ⟨by show (σ (.n 6), σ (.n 7)) = _; rw [a6, a7, hcv],
    by show σ (.n 5) * gen ^ 0 = cur * gen ^ 0; rw [a5]⟩
  obtain ⟨hF1, hat1⟩ := osFsNext_completeC (CM := CM) (C := C) (kret := kret) hat0 lx0 ax0 fun j hj => gB j hj
  obtain ⟨hF2, hat2⟩ := osFsNext_completeC (CM := CM) (C := C) (kret := kret) hat1 (by simpa using lx1) ax1 fun j hj =>
    gC j hj
  have b0 : σ (.n 8) = x0 := by simpa [B, osFsNextValsW] using gB 0 (by omega)
  have c0 : σ (.n 23) = x1 := by simpa [Cn, osFsNextValsW] using gC 0 (by omega)
  refine ⟨?_, ⟨hat2.fs, hat2.cursor⟩, rfl, ?_, a2, ⟨d2, d4, d6, d8, d10, d12, d14, d16, d18, d20, d22⟩, rfl⟩
  · unfold osHead
    dsimp only
    simp only [holdsListB_append]
    refine (holdsListB_noRet _ rfl _ _).mpr ⟨?_, (holdsListB_noRet _ rfl _ _).mpr ⟨hF1,
      (holdsListB_noRet _ rfl _ _).mpr ⟨hF2, ?_⟩⟩⟩
    · simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, and_true]
      exact ⟨by rw [a6, a0], by rw [a7, a1]⟩
    · simp only [osHeap, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, and_true, true_and]
      refine ⟨by rw [d0, a2, c0], d1, d3, d5, d7, by rw [a3, show osRoots = 46 from rfl, d8]; exact lr0, by rw [a4, show osRoots = 46 from rfl, d8]; exact lr1, d9, d11,
        d13, d15, d17, d19, d21⟩
  · show [σ (.n 8), σ (.n 38), σ (.n 23)] = _
    rw [b0, d0, c0]


end
end LeanVM.Guest.B1
