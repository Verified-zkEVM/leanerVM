/-
  LeanVM.Guest.B1.Comp.Whir.StackedBlocksC

  `open_stacked`'s blocks over a completeness model: the reads, the fold rounds, the final message,
  the out-of-domain sample, the next commitment, the proof of work, the squeezes and the queries.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.StackedChainC
public import LeanVM.Guest.B1.Whir.StackedLevelM

/-!
# `open_stacked`'s blocks over a completeness model (TRIAGE #36)

`Whir/StackedC1.lean`–`StackedC3.lean` over a `CompModel` and a total hash `Ht`: each block's
honest values over `Ht` (`…ValsW`), its relation under `CM.sem` (`…_completeC`). The blocks with a
`BLAKE2S` row take the model's answer for its string: `fs_next` (`osFsNext_completeC`, the absorb
of the word read), the proof of work's absorb (`osGrind_completeC`), the closing squeeze
(`osSqueezes_completeC`), and through them the out-of-domain sample, the next commitment and the
queries' intro; the fold rounds (`osFolds_completeC`) run answered, `opening_fold`'s call then
taken at a run under the model (`RunsToM CM.hm (foldStep q)`, what `MeaningOpeningFoldComp` asks).
The blocks without a row carry their deployed lemmas over (`osMat_completeB`,
`osLamPows_completeB`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub LeanVM.E2E.Complete

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## The blocks without a `BLAKE2S` row -/

theorem osMat_completeB {S : BlakeSem} {base off k : ℕ} (hoff : off < 2 ^ 128) {kret : List E → Prop}
    (hv : ∀ j < (osMatVals (σ (.n base)) off).length, σ (.n (k + j)) = (osMatVals (σ (.n base)) off).getD j 0) :
    Stmt.HoldsListB S C rd σ (osMat base off k).1 True kret ∧
      σ (.n (osMat base off k).2.1) = σ (.n base) * gen ^ off := by
  obtain ⟨h1, h2⟩ := osMat_complete (C := C) (rd := rd) (kret := kret) hoff hv
  exact ⟨(holdsListB_iff_of_noBlake (osMat_noBlake _ _ _) _ _).mpr h1, h2⟩

theorem osLamPows_completeB {S : BlakeSem} {lam qw base k : ℕ} {kret : List E → Prop} (nq : ℕ)
    (hst : ∀ i < nq, LoadHolds rd (σ (.n qw)) (base + i) (σ (.n lam) ^ i))
    (hv : ∀ j < nq, σ (.n (k + j)) = (osLamPowsVals (σ (.n lam)) nq).getD j 0) :
    Stmt.HoldsListB S C rd σ (osLamPows lam qw base k nq) True kret :=
  (holdsListB_iff_of_noBlake (osLamPows_noBlake _ _ _ _ _) _ _).mpr (osLamPows_complete nq hst hv)

variable {CM : CompModel} {Ht : Bytes → Digest}

/-- The values of `osFsNext` from its first: the word `x`, then `fs_compress`'s. -/
def osFsNextValsW (Ht : Bytes → Digest) (x : E) (cv : Digest) : List E := x :: (List.range 14).map (fsValsW Ht x cv 1)


/-- **`fs_next`** at its honest values: the word at the cursor read and absorbed. -/
theorem osFsNext_completeC {s : OsSt} {cv : Digest} {cur : E} {p : ℕ} (hat : OsAt σ s cv cur p)
    {x : E} (hx : LoadHolds rd cur p x) (hA : obsCvM CM.hm cv x = some (obsCvW Ht cv x)) {kret : List E → Prop}
    (hv : ∀ j < 15, σ (.n (s.k + j)) = (osFsNextValsW Ht x cv).getD j 0) :
    Stmt.HoldsListB CM.sem C rd σ (osFsNext s).1 True kret ∧ OsAt σ (osFsNext s).2 (obsCvW Ht cv x) cur (p + 1) := by
  have e0 : σ (.n s.k) = x := by simpa [osFsNextValsW] using hv 0 (by omega)
  have e : ∀ j < 14, σ (.n (s.k + 1 + j)) = fsValsW Ht x cv 1 j := fun j hj => by
    rw [show s.k + 1 + j = s.k + (j + 1) by ring, hv _ (by omega)]
    simp [osFsNextValsW, List.getD_eq_getElem?_getD, hj]
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · show Stmt.HoldsListB CM.sem C rd σ (fsNextT (.n s.f0) (.n s.f1) (.n s.cb) s.co s.k) True kret
    refine holdsB_fsNextT_comp _ _ _ _ _ ⟨⟨?_, cv, obsCvW Ht cv x, hat.fs, by rw [e0]; exact hA,
      fun j h1 h2 => ?_⟩, trivial⟩
    · have hl := os_cursor_load (j := 0) hat (by rw [Nat.add_zero]; exact hx)
      rw [Nat.add_zero] at hl
      rw [e0]; exact hl
    · rw [e j h2, e0, fsValsW_eq Ht x cv 1 h2]; rfl
  · show (σ (.n (s.k + 13)), σ (.n (s.k + 14))) = _
    rw [show s.k + 13 = s.k + 1 + 12 by ring, show s.k + 14 = s.k + 1 + 13 by ring, e 12 (by omega),
      e 13 (by omega)]
    rfl
  · show σ (.n s.cb) * gen ^ (s.co + 1) = cur * gen ^ (p + 1)
    rw [pow_succ, pow_succ, ← mul_assoc, ← mul_assoc, hat.cursor]


/-- The values of one fold round from its first, the cursor at `bv·g^co`, `p` words read: the
pointer, `opening_fold`'s returns, the copies, the next quadratic's middle coefficient. -/
def osFoldValsW (Ht : Bytes → Digest) (xs : List E) (cv : Digest) (p : ℕ) (q : List E) (bv : E) (co : ℕ) : List E :=
  let ch := challengeOf (sqCvW Ht cv)
  let t := polyEval q ch
  let d0 := xs.getD p 0
  let d2 := xs.getD (p + 1) 0
  let cv' := obsAllW Ht (sqCvW Ht cv) [d0, d2]
  osMatVals bv co ++ [(digestScalars cv').1, (digestScalars cv').2, bv * osGw co * gen ^ 2, t, d0, d2, ch,
    (digestScalars cv').1, (digestScalars cv').2, t + d2]

/-- `opening_fold`'s returns at a round. -/
def osFoldRetsW (Ht : Bytes → Digest) (xs : List E) (cv : Digest) (p : ℕ) (q : List E) (curv : E) : List E :=
  let ch := challengeOf (sqCvW Ht cv)
  let t := polyEval q ch
  let d0 := xs.getD p 0
  let d2 := xs.getD (p + 1) 0
  let cv' := obsAllW Ht (sqCvW Ht cv) [d0, d2]
  [(digestScalars cv').1, (digestScalars cv').2, curv * gen ^ 2, t, d0, d2, ch]


/-- **One fold round** at its honest values, its call holding. -/
theorem osFold_completeC {s : OsSt} {cv : Digest} {cur : E} {p : ℕ} {xs : List E} (hat : OsAt σ s cv cur p)
    (hco : s.co < 2 ^ 128) {fch fo : ℕ} {kret : List E → Prop}
    (hv : ∀ j < (osFoldValsW Ht xs cv p [σ (.n s.c), σ (.n s.b), σ (.n s.a)] (σ (.n s.cb)) s.co).length,
      σ (.n (s.k + j)) = (osFoldValsW Ht xs cv p [σ (.n s.c), σ (.n s.b), σ (.n s.a)] (σ (.n s.cb)) s.co).getD j 0)
    (hcall : C "opening_fold" [σ (.n s.f0), σ (.n s.f1), σ (.n s.cb) * gen ^ s.co, σ (.n s.c), σ (.n s.b),
      σ (.n s.a)] (osFoldRetsW Ht xs cv p [σ (.n s.c), σ (.n s.b), σ (.n s.a)] (σ (.n s.cb) * gen ^ s.co)))
    (hst : LoadHolds rd (σ (.n fch)) fo (challengeOf (sqCvW Ht cv))) :
    Stmt.HoldsListB CM.sem C rd σ (osFold s fch fo).1 True kret ∧
      OsAt σ (osFold s fch fo).2 (obsAllW Ht (sqCvW Ht cv) [xs.getD p 0, xs.getD (p + 1) 0]) cur (p + 2) ∧
      (osFold s fch fo).2.co = 0 ∧ σ (.n (osFold s fch fo).2.cb) = σ (.n s.cb) * osGw s.co * gen ^ 2 ∧
      σ (.n (osFold s fch fo).2.t) = polyEval [σ (.n s.c), σ (.n s.b), σ (.n s.a)] (challengeOf (sqCvW Ht cv)) ∧
      [σ (.n (osFold s fch fo).2.c), σ (.n (osFold s fch fo).2.b), σ (.n (osFold s fch fo).2.a)] =
        [xs.getD p 0, polyEval [σ (.n s.c), σ (.n s.b), σ (.n s.a)] (challengeOf (sqCvW Ht cv)) +
          xs.getD (p + 1) 0, xs.getD (p + 1) 0] ∧
      (osFold s fch fo).2.k = s.k + (osFoldValsW Ht xs cv p [σ (.n s.c), σ (.n s.b), σ (.n s.a)] (σ (.n s.cb)) s.co).length := by
  set q := [σ (.n s.c), σ (.n s.b), σ (.n s.a)]
  set M := osMatVals (σ (.n s.cb)) s.co with hM
  set ch := challengeOf (sqCvW Ht cv)
  set t := polyEval q ch
  set d0 := xs.getD p 0
  set d2 := xs.getD (p + 1) 0
  set cv' := obsAllW Ht (sqCvW Ht cv) [d0, d2]
  set T : List E := [(digestScalars cv').1, (digestScalars cv').2, σ (.n s.cb) * osGw s.co * gen ^ 2, t, d0, d2, ch,
    (digestScalars cv').1, (digestScalars cv').2, t + d2] with hT
  have hvals : osFoldValsW Ht xs cv p q (σ (.n s.cb)) s.co = M ++ T := rfl
  rw [hvals] at hv
  have hlen : (M ++ T).length = M.length + 10 := by simp [hT]
  have hr : (osMat s.cb s.co s.k).2.2 = s.k + M.length := by
    rw [osMat_next', hM, os_length_matVals' (σ (.n s.cb))]
  have hm := osMat_completeB (S := CM.sem) (C := C) (rd := rd) (σ := σ) (base := s.cb) (k := s.k) (kret := kret) hco fun j hj => by
    rw [hv j (by rw [hlen, hM]; omega), oq_getD_app_lt hj]
  have gT : ∀ j < 10, σ (.n ((osMat s.cb s.co s.k).2.2 + j)) = T.getD j 0 := fun j hj => by
    rw [hr, show s.k + M.length + j = s.k + (M.length + j) by ring, hv _ (by rw [hlen]; omega),
      oq_getD_app_ge (by omega), Nat.add_sub_cancel_left]
  have hgw : σ (.n s.cb) * osGw s.co = σ (.n s.cb) * gen ^ s.co := by rw [os_gw_eq hco]
  generalize hR : (osMat s.cb s.co s.k).2.2 = r at gT hr
  have g := fun j (hj : j < 10) => gT j hj
  have g0 := g 0 (by omega); have g1 := g 1 (by omega); have g2 := g 2 (by omega)
  have g3 := g 3 (by omega); have g4 := g 4 (by omega); have g5 := g 5 (by omega)
  have g6 := g 6 (by omega); have g7 := g 7 (by omega); have g8 := g 8 (by omega)
  have g9 := g 9 (by omega)
  simp only [hT, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  unfold osFold
  dsimp only
  rw [hR]
  refine ⟨?_, ⟨?_, ?_⟩, rfl, g2, g3, ?_, by rw [hvals, hlen, hr]; ring⟩
  · rw [holdsListB_append]
    refine (holdsListB_noRet _ (osMat_noRet _ _ _) _ _).mpr ⟨hm.1, ?_⟩
    simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, os_range7, List.map_cons, List.map_nil, and_true]
    refine ⟨?_, by rw [g7, g0], by rw [g8, g1], by rw [g6]; exact hst, by rw [g9, g3, g5]⟩
    rw [hm.2, g0, g1, g2, g3, g4, g5, g6, hgw]
    exact hcall
  · show (σ (.n (r + 7)), σ (.n (r + 8))) = _
    rw [g7, g8]
  · show σ (.n (r + 2)) * gen ^ 0 = cur * gen ^ (p + 2)
    rw [g2, pow_zero, mul_one, hgw, hat.cursor, mul_assoc, ← pow_add]
  · show [σ (.n (r + 4)), σ (.n (r + 9)), σ (.n (r + 5))] = _
    rw [g4, g9, g5]


/-- The values of `n` fold rounds from their first. -/
def osFoldsValsW (Ht : Bytes → Digest) (xs : List E) : ℕ → Digest → ℕ → List E → E → ℕ → List E
  | 0, _, _, _, _, _ => []
  | n + 1, cv, p, q, bv, co =>
    let ch := challengeOf (sqCvW Ht cv)
    let t := polyEval q ch
    let d0 := xs.getD p 0
    let d2 := xs.getD (p + 1) 0
    osFoldValsW Ht xs cv p q bv co ++
      osFoldsValsW Ht xs n (obsAllW Ht (sqCvW Ht cv) [d0, d2]) (p + 2) [d0, t + d2, d2] (bv * osGw co * gen ^ 2) 0


/-- **The fold rounds** at their honest values: `n` rounds of `foldRounds` (V:1678) from the
specification's state at `p` words of `xs` read, each challenge stored at `fch[fo + j]`. -/
theorem osFolds_completeC {xs : List E} {cur : E} {fch : ℕ} {kret : List E → Prop} {C : CallRel}
    (hcall : ∀ (cv' : Digest) (p' : ℕ) (q' : List E), q'.length = 3 → p' + 2 ≤ xs.length →
      RunsToM CM.hm (foldStep q') cv' [xs.getD p' 0, xs.getD (p' + 1) 0]
        (challengeOf (sqCvW Ht cv'), polyEval q' (challengeOf (sqCvW Ht cv')),
          [xs.getD p' 0, polyEval q' (challengeOf (sqCvW Ht cv')) + xs.getD (p' + 1) 0, xs.getD (p' + 1) 0])
        (obsAllW Ht (sqCvW Ht cv') [xs.getD p' 0, xs.getD (p' + 1) 0]) →
      C "opening_fold" [(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ p', q'.getD 0 0, q'.getD 1 0,
        q'.getD 2 0] (osFoldRetsW Ht xs cv' p' q' (cur * gen ^ p'))) :
    ∀ (n fo : ℕ) (s : OsSt) (cv : Digest) (p : ℕ) (w : WhirState) (lf : List E) (osp : List Opening)
      (roots : List (Digest × ℕ × ℕ)) (res : WhirState × List E) (sp' : St),
      OsAt σ s cv cur p → s.co < 2 ^ 128 → w.quad = [σ (.n s.c), σ (.n s.b), σ (.n s.a)] →
      RunsW Ht (foldRounds n w lf) ⟨cv, xs.drop p, osp, roots⟩ res sp' →
      AnsRun CM.hm.H Ht (foldRounds n w lf) ⟨cv, xs.drop p, osp, roots⟩ →
      (∀ j < (osFoldsValsW Ht xs n cv p w.quad (σ (.n s.cb)) s.co).length,
        σ (.n (s.k + j)) = (osFoldsValsW Ht xs n cv p w.quad (σ (.n s.cb)) s.co).getD j 0) →
      (∀ j < n, LoadHolds rd (σ (.n fch)) (fo + j) (res.1.folds.getD (w.folds.length + j) 0)) →
      Stmt.HoldsListB CM.sem C rd σ (osFolds fch fo n s).1 True kret ∧
        OsAt σ (osFolds fch fo n s).2 sp'.cv cur (p + 2 * n) ∧ sp' = ⟨sp'.cv, xs.drop (p + 2 * n), osp, roots⟩ ∧
        res.1.quad = [σ (.n (osFolds fch fo n s).2.c), σ (.n (osFolds fch fo n s).2.b),
          σ (.n (osFolds fch fo n s).2.a)] ∧ res.1.target = (if n = 0 then w.target else σ (.n (osFolds fch fo n s).2.t)) ∧
        res.1.glued = w.glued ∧ res.1.folds.length = w.folds.length + n ∧
        (∃ chs, res.1.folds = w.folds ++ chs ∧ res.2 = lf ++ chs) ∧
        (osFolds fch fo n s).2.co = (if n = 0 then s.co else 0) ∧
        (osFolds fch fo n s).2.k = s.k + (osFoldsValsW Ht xs n cv p w.quad (σ (.n s.cb)) s.co).length
  | 0, fo, s, cv, p, w, lf, osp, roots, res, sp', hat, _, _, hrun, _, _, _ => by
    obtain ⟨rfl, rfl⟩ := os_inv_pureW hrun
    exact ⟨trivial, by simpa [osFolds] using hat, by simp, by simpa [osFolds], by simp, rfl, by simp,
      ⟨[], by simp, by simp⟩, by simp [osFolds], by simp [osFolds, osFoldsValsW]⟩
  | n + 1, fo, s, cv, p, w, lf, osp, roots, res, sp', hat, hco, hq, hrun, hA, hv, hst => by
    rw [foldRounds_succ] at hrun hA
    obtain ⟨⟨ch, t, q'⟩, sp1, h1, h2⟩ := os_inv_bindW hrun
    obtain ⟨aS, hA2⟩ := AnsRun.bind_inv _ _ hA h1
    obtain ⟨d0, d2, rest, hs, he, hsp1⟩ := os_runs_foldStepW h1
    simp only at hs
    rw [hs] at aS
    have hRT := ansRun_foldStep aS
    have hlen2 : p + 2 ≤ xs.length := by
      have := congrArg List.length hs
      simp only [List.length_drop, List.length_cons] at this
      omega
    obtain ⟨hd0, hd2, hrest⟩ := os_drop_cons2 hs
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    subst hrest
    simp only at hsp1
    subst hsp1
    rw [hq] at hv
    set V1 := osFoldValsW Ht xs cv p [σ (.n s.c), σ (.n s.b), σ (.n s.a)] (σ (.n s.cb)) s.co with hV1
    have hvs : osFoldsValsW Ht xs (n + 1) cv p [σ (.n s.c), σ (.n s.b), σ (.n s.a)] (σ (.n s.cb)) s.co =
        V1 ++ osFoldsValsW Ht xs n (obsAllW Ht (sqCvW Ht cv) [d0, d2]) (p + 2)
          [d0, polyEval [σ (.n s.c), σ (.n s.b), σ (.n s.a)] (challengeOf (sqCvW Ht cv)) + d2, d2]
          (σ (.n s.cb) * osGw s.co * gen ^ 2) 0 := by rw [osFoldsValsW, ← hd0, ← hd2]
    rw [hvs] at hv
    obtain ⟨chs', hF1, hF2, hFl⟩ := os_foldRounds_foldsW h2
    simp only at hF1 hF2
    have hst0 : LoadHolds rd (σ (.n fch)) fo (challengeOf (sqCvW Ht cv)) := by
      have := hst 0 (by omega)
      rw [hF1, List.append_assoc, oq_getD_app_ge (by omega), Nat.add_sub_cancel_left] at this
      simpa using this
    have hc1 : C "opening_fold" [σ (.n s.f0), σ (.n s.f1), σ (.n s.cb) * gen ^ s.co, σ (.n s.c), σ (.n s.b),
        σ (.n s.a)] (osFoldRetsW Ht xs cv p [σ (.n s.c), σ (.n s.b), σ (.n s.a)] (σ (.n s.cb) * gen ^ s.co)) := by
      have := hcall cv p [σ (.n s.c), σ (.n s.b), σ (.n s.a)] rfl hlen2 (by rw [hd0, hd2, ← hq]; exact hRT)
      have e0 : (digestScalars cv).1 = σ (.n s.f0) := by rw [← hat.fs]
      have e1 : (digestScalars cv).2 = σ (.n s.f1) := by rw [← hat.fs]
      rw [e0, e1, ← hat.cursor] at this
      exact this
    obtain ⟨hH1, hat1, hco1, hcb1, ht1, hq1, hk1⟩ := osFold_completeC (CM := CM) (C := C) (rd := rd) (xs := xs)
      (fch := fch) (fo := fo) (kret := kret) hat hco (fun j hj => by
        have hj' : j < V1.length := hj
        rw [hv j (by simp only [List.length_append]; omega), oq_getD_app_lt hj]) hc1 hst0
    rw [hd0, hd2] at hat1 hq1
    rw [← hV1] at hk1
    set st1 := (osFold s fch fo).2
    set w1 : WhirState := ⟨polyEval [σ (.n s.c), σ (.n s.b), σ (.n s.a)] (challengeOf (sqCvW Ht cv)),
      [d0, polyEval [σ (.n s.c), σ (.n s.b), σ (.n s.a)] (challengeOf (sqCvW Ht cv)) + d2, d2],
      w.folds ++ [challengeOf (sqCvW Ht cv)], w.glued⟩ with hw1
    have ih := osFolds_completeC (xs := xs) (cur := cur) (fch := fch) (kret := kret) hcall n (fo + 1) st1
      (obsAllW Ht (sqCvW Ht cv) [d0, d2]) (p + 2) w1
      (lf ++ [challengeOf (sqCvW Ht cv)]) osp roots res sp' hat1 (by rw [hco1]; exact Nat.two_pow_pos 128) (by rw [hq1])
      (by simp only at h2; rw [hq] at h2; exact h2) (by simp only at hA2; rw [hq] at hA2; exact hA2)
      (fun j hj => by
        rw [show w1.quad = [d0, polyEval [σ (.n s.c), σ (.n s.b), σ (.n s.a)] (challengeOf (sqCvW Ht cv)) + d2, d2]
          from rfl, hcb1, hco1] at hj ⊢
        rw [hk1, Nat.add_assoc, hv _ (by simp only [List.length_append]; omega), oq_getD_app_ge (by omega),
          Nat.add_sub_cancel_left])
      (fun j hj => by
        have := hst (j + 1) (by omega)
        rwa [show fo + 1 + j = fo + (j + 1) by ring, show w1.folds.length + j = w.folds.length + (j + 1) by
          rw [show w1.folds = w.folds ++ [challengeOf (sqCvW Ht cv)] from rfl]; simp; omega])
    obtain ⟨hH, hat', hsp', hq', ht', hg', hfl', ⟨chs, hc1, hc2⟩, hco', hk'⟩ := ih
    refine ⟨?_, by rwa [show p + 2 * (n + 1) = p + 2 + 2 * n by ring], by rw [hsp']; congr 2; ring, hq', ?_,
      hg', by rw [hfl', show w1.folds = w.folds ++ [challengeOf (sqCvW Ht cv)] from rfl]; simp; omega,
      ⟨challengeOf (sqCvW Ht cv) :: chs, by rw [hc1, show w1.folds = w.folds ++ [challengeOf (sqCvW Ht cv)] from rfl]; simp,
        by rw [hc2]; simp⟩, ?_, ?_⟩
    · show Stmt.HoldsListB CM.sem C rd σ ((osFold s fch fo).1 ++ (osFolds fch (fo + 1) n st1).1) True kret
      rw [holdsListB_append]
      exact (holdsListB_noRet _ (osFold_noRet _ _ _) _ _).mpr ⟨hH1, hH⟩
    · rw [ht', ite_neg' (show ¬ (n + 1 = 0) by omega)]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [ite_pos' (show (0 : ℕ) = 0 from rfl)]; exact ht1.symm
      · rw [ite_neg' (show ¬ (n = 0) by omega)]; rfl
    · show (osFolds fch (fo + 1) n st1).2.co = _
      rw [hco', hco1]; split <;> simp
    · show (osFolds fch (fo + 1) n st1).2.k = _
      rw [hk', hk1, hq, hvs, List.length_append]
      rw [show w1.quad = [d0, polyEval [σ (.n s.c), σ (.n s.b), σ (.n s.a)] (challengeOf (sqCvW Ht cv)) + d2, d2]
        from rfl, hcb1, hco1]
      ring


/-! ## The final message -/

/-- The values of `osFinal` from its first: the pointer, the returns, the copies. -/
def osFinalValsW (Ht : Bytes → Digest) (cv : Digest) (ms : List E) (bv : E) (co n : ℕ) : List E :=
  osMatVals bv co ++ [(digestScalars (obsAllW Ht cv ms)).1, (digestScalars (obsAllW Ht cv ms)).2, bv * osGw co * gen ^ n,
    (digestScalars (obsAllW Ht cv ms)).1, (digestScalars (obsAllW Ht cv ms)).2]

/-- **The final message** at its honest values. -/
theorem osFinal_completeC {name : String} {n : ℕ} {s : OsSt} {cv : Digest} {cur : E} {p : ℕ}
    (hat : OsAt σ s cv cur p) (hco : s.co < 2 ^ 128) {fmsg : ℕ} {ms : List E}
    (hcall : C name [(digestScalars cv).1, (digestScalars cv).2, cur * gen ^ p, σ (.n fmsg)]
      [(digestScalars (obsAllW Ht cv ms)).1, (digestScalars (obsAllW Ht cv ms)).2, cur * gen ^ (p + n)])
    {kret : List E → Prop}
    (hv : ∀ j < (osFinalValsW Ht cv ms (σ (.n s.cb)) s.co n).length,
      σ (.n (s.k + j)) = (osFinalValsW Ht cv ms (σ (.n s.cb)) s.co n).getD j 0) :
    Stmt.HoldsListB CM.sem C rd σ (osFinal name fmsg s).1 True kret ∧
      OsAt σ (osFinal name fmsg s).2 (obsAllW Ht cv ms) cur (p + n) ∧ (osFinal name fmsg s).2.co = 0 ∧
      σ (.n (osFinal name fmsg s).2.cb) = σ (.n s.cb) * osGw s.co * gen ^ n ∧
      (osFinal name fmsg s).2.k = s.k + (osFinalValsW Ht cv ms (σ (.n s.cb)) s.co n).length := by
  set M := osMatVals (σ (.n s.cb)) s.co with hM
  set c := obsAllW Ht cv ms
  set T : List E := [(digestScalars c).1, (digestScalars c).2, σ (.n s.cb) * osGw s.co * gen ^ n,
    (digestScalars c).1, (digestScalars c).2] with hT
  have hvals : osFinalValsW Ht cv ms (σ (.n s.cb)) s.co n = M ++ T := rfl
  rw [hvals] at hv ⊢
  have hlen : (M ++ T).length = M.length + 5 := by simp [hT]
  have hr : (osMat s.cb s.co s.k).2.2 = s.k + M.length := by
    rw [osMat_next', hM, os_length_matVals' (σ (.n s.cb))]
  have hm := osMat_completeB (S := CM.sem) (C := C) (rd := rd) (σ := σ) (base := s.cb) (k := s.k) (kret := kret) hco
    fun j hj => by rw [hv j (by rw [hlen, hM]; omega), oq_getD_app_lt hj]
  have gT : ∀ j < 5, σ (.n ((osMat s.cb s.co s.k).2.2 + j)) = T.getD j 0 := fun j hj => by
    rw [hr, Nat.add_assoc, hv _ (by rw [hlen]; omega), os_skip]
  have hgw : σ (.n s.cb) * osGw s.co = σ (.n s.cb) * gen ^ s.co := by rw [os_gw_eq hco]
  generalize hR : (osMat s.cb s.co s.k).2.2 = r at gT hr
  have g0 := gT 0 (by omega); have g1 := gT 1 (by omega); have g2 := gT 2 (by omega)
  have g3 := gT 3 (by omega); have g4 := gT 4 (by omega)
  simp only [hT, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at g0 g1 g2 g3 g4
  unfold osFinal
  dsimp only
  rw [hR]
  refine ⟨?_, ⟨?_, ?_⟩, rfl, g2, by rw [hlen, hr]; ring⟩
  · rw [holdsListB_append]
    refine (holdsListB_noRet _ (osMat_noRet _ _ _) _ _).mpr ⟨hm.1, ?_⟩
    simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, and_true]
    refine ⟨?_, by rw [g3, g0], by rw [g4, g1]⟩
    have e0 : (digestScalars cv).1 = σ (.n s.f0) := by rw [← hat.fs]
    have e1 : (digestScalars cv).2 = σ (.n s.f1) := by rw [← hat.fs]
    rw [hm.2, g0, g1, g2, hgw, hat.cursor, mul_assoc, ← pow_add]
    rw [e0, e1] at hcall
    exact hcall
  · show (σ (.n (r + 3)), σ (.n (r + 4))) = _
    rw [g3, g4]
  · show σ (.n (r + 2)) * gen ^ 0 = cur * gen ^ (p + n)
    rw [g2, pow_zero, mul_one, hgw, hat.cursor, mul_assoc, ← pow_add]

/-! ## An out-of-domain sample -/

/-- The values of `osOodSample` from its first: the point's pointer and size, `opening_ood_point`'s
returns and their copies, the three reads. -/
def osOodSampleValsW (Ht : Bytes → Digest) (oz logCols : ℕ) (oodzv : E) (cv : Digest) (y c0 c2 : E) : List E :=
  let c' := (sqAllW Ht logCols cv).2
  [osGw oz, oodzv * osGw oz, osGw logCols, (digestScalars c').1, (digestScalars c').2, (digestScalars c').1,
    (digestScalars c').2] ++ osFsNextValsW Ht y c' ++ osFsNextValsW Ht c0 (obsCvW Ht c' y) ++
    osFsNextValsW Ht c2 (obsCvW Ht (obsCvW Ht c' y) c0)

theorem os_length_fsNextValsW (x : E) (cv : Digest) : (osFsNextValsW Ht x cv).length = 15 := by
  simp [osFsNextValsW]

theorem os_length_oodSampleValsW (oz logCols : ℕ) (oodzv : E) (cv : Digest) (y c0 c2 : E) :
    (osOodSampleValsW Ht oz logCols oodzv cv y c0 c2).length = 52 := by
  simp [osOodSampleValsW, os_length_fsNextValsW]

/-- **An out-of-domain sample** at its honest values: its point squeezed, its value and its
intro's `c0`, `c2` read and stored at `ood[so + 1 ..]`. -/
theorem osOodSample_completeC {s : OsSt} {cv : Digest} {cur : E} {p : ℕ} (hat : OsAt σ s cv cur p)
    {oz so logCols oodz ood : ℕ} {y c0 c2 : E} {kret : List E → Prop}
    (ly : LoadHolds rd cur p y) (lc0 : LoadHolds rd cur (p + 1) c0) (lc2 : LoadHolds rd cur (p + 2) c2)
    (ay : obsCvM CM.hm (sqAllW Ht logCols cv).2 y = some (obsCvW Ht (sqAllW Ht logCols cv).2 y))
    (ac0 : obsCvM CM.hm (obsCvW Ht (sqAllW Ht logCols cv).2 y) c0 =
      some (obsCvW Ht (obsCvW Ht (sqAllW Ht logCols cv).2 y) c0))
    (ac2 : obsCvM CM.hm (obsCvW Ht (obsCvW Ht (sqAllW Ht logCols cv).2 y) c0) c2 =
      some (obsCvW Ht (obsCvW Ht (obsCvW Ht (sqAllW Ht logCols cv).2 y) c0) c2))
    (sy : LoadHolds rd (σ (.n ood)) (so + 1) y) (sc0 : LoadHolds rd (σ (.n ood)) (so + 2) c0)
    (sc2 : LoadHolds rd (σ (.n ood)) (so + 3) c2)
    (hcall : C "opening_ood_point" [(digestScalars cv).1, (digestScalars cv).2, σ (.n oodz) * osGw oz, osGw logCols]
      [(digestScalars (sqAllW Ht logCols cv).2).1, (digestScalars (sqAllW Ht logCols cv).2).2])
    (hv : ∀ j < 52, σ (.n (s.k + j)) = (osOodSampleValsW Ht oz logCols (σ (.n oodz)) cv y c0 c2).getD j 0) :
    Stmt.HoldsListB CM.sem C rd σ (osOodSample oz so logCols oodz ood s).1 True kret ∧
      OsAt σ (osOodSample oz so logCols oodz ood s).2
        (obsCvW Ht (obsCvW Ht (obsCvW Ht (sqAllW Ht logCols cv).2 y) c0) c2) cur (p + 3) ∧
      (osOodSample oz so logCols oodz ood s).2.co = s.co + 3 ∧ (osOodSample oz so logCols oodz ood s).2.cb = s.cb ∧
      (osOodSample oz so logCols oodz ood s).2.k = s.k + 52 := by
  set c' := (sqAllW Ht logCols cv).2
  set A : List E := [osGw oz, σ (.n oodz) * osGw oz, osGw logCols, (digestScalars c').1, (digestScalars c').2,
    (digestScalars c').1, (digestScalars c').2] with hA
  set F1 := osFsNextValsW Ht y c'
  set F2 := osFsNextValsW Ht c0 (obsCvW Ht c' y)
  set F3 := osFsNextValsW Ht c2 (obsCvW Ht (obsCvW Ht c' y) c0)
  have hvals : osOodSampleValsW Ht oz logCols (σ (.n oodz)) cv y c0 c2 = A ++ (F1 ++ (F2 ++ F3)) := by
    simp only [osOodSampleValsW, List.append_assoc]; rfl
  rw [hvals] at hv
  have lA : A.length = 7 := rfl
  have l1 : F1.length = 15 := os_length_fsNextValsW _ _
  have l2 : F2.length = 15 := os_length_fsNextValsW _ _
  have gA : ∀ j < 7, σ (.n (s.k + j)) = A.getD j 0 := fun j hj => by
    rw [hv j (by omega), oq_getD_app_lt (by omega)]
  have e0 := gA 0 (by omega); have e1 := gA 1 (by omega); have e2 := gA 2 (by omega)
  have e3 := gA 3 (by omega); have e4 := gA 4 (by omega); have e5 := gA 5 (by omega)
  have e6 := gA 6 (by omega)
  simp only [hA, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at e0 e1 e2 e3 e4 e5 e6
  set s1 : OsSt := { s with k := s.k + 7, f0 := s.k + 5, f1 := s.k + 6 }
  have hat1 : OsAt σ s1 c' cur p := ⟨by show (σ (.n (s.k + 5)), σ (.n (s.k + 6))) = _; rw [e5, e6], hat.cursor⟩
  obtain ⟨h1, hat2⟩ := osFsNext_completeC (CM := CM) (C := C) (kret := kret) hat1 ly ay fun j hj => by
    rw [show s1.k + j = s.k + (A.length + j) by simp [s1, lA]; ring, hv _ (by omega), os_skip,
      oq_getD_app_lt (by omega)]
  obtain ⟨h2, hat3⟩ := osFsNext_completeC (CM := CM) (C := C) (kret := kret) hat2 lc0 ac0 fun j hj => by
    rw [show (osFsNext s1).2.k + j = s.k + (A.length + (F1.length + j)) by simp [osFsNext, s1, lA, l1]; ring,
      hv _ (by omega), os_skip, os_skip, oq_getD_app_lt (by omega)]
  obtain ⟨h3, hat4⟩ := osFsNext_completeC (CM := CM) (C := C) (kret := kret) hat3 lc2 ac2 fun j hj => by
    rw [show (osFsNext (osFsNext s1).2).2.k + j = s.k + (A.length + (F1.length + (F2.length + j))) by
      simp [osFsNext, s1, lA, l1, l2]; ring, hv _ (by omega), os_skip, os_skip, os_skip]
  have hk1 : s1.k = s.k + 7 := rfl
  unfold osOodSample
  dsimp only
  refine ⟨?_, hat4, rfl, rfl, by simp [osFsNext]⟩
  simp only [holdsListB_append]
  refine (holdsListB_noRet _ rfl _ _).mpr ⟨?_, ?_⟩
  · simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, and_true]
    refine ⟨e0, by rw [e1, e0], e2, ?_, by rw [e5, e3], by rw [e6, e4]⟩
    have f0 : (digestScalars cv).1 = σ (.n s.f0) := by rw [← hat.fs]
    have f1 : (digestScalars cv).2 = σ (.n s.f1) := by rw [← hat.fs]
    rw [e1, e2, e3, e4, ← f0, ← f1]
    exact hcall
  refine (holdsListB_noRet _ rfl _ _).mpr ⟨h1, ?_⟩
  refine (holdsListB_noRet _ rfl _ _).mpr ⟨h2, ?_⟩
  refine (holdsListB_noRet _ rfl _ _).mpr ⟨h3, ?_⟩
  have v1 : σ (.n s1.k) = y := by
    have := hv (A.length + 0) (by omega)
    rw [os_skip, oq_getD_app_lt (by omega)] at this
    exact this
  have v2 : σ (.n (osFsNext s1).2.k) = c0 := by
    have := hv (A.length + (F1.length + 0)) (by omega)
    rw [os_skip, os_skip, oq_getD_app_lt (by omega)] at this
    rw [show (osFsNext s1).2.k = s.k + (A.length + (F1.length + 0)) by simp [osFsNext, s1, lA, l1]]
    exact this
  have v3 : σ (.n (osFsNext (osFsNext s1).2).2.k) = c2 := by
    have := hv (A.length + (F1.length + (F2.length + 0))) (by omega)
    rw [os_skip, os_skip, os_skip] at this
    rw [show (osFsNext (osFsNext s1).2).2.k = s.k + (A.length + (F1.length + (F2.length + 0))) by
      simp [osFsNext, s1, lA, l1, l2]]
    exact this
  simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, and_true]
  exact ⟨by rw [v1]; exact sy, by rw [v2]; exact sc0, by rw [v3]; exact sc2⟩

/-! ## The next commitment -/

/-- The values of `osCommit` (one out-of-domain sample) from its first: the root's halves read,
`assert_canonical`'s returns, the sample. -/
def osCommitValsW (Ht : Bytes → Digest) (lvl logCols : ℕ) (oodzv : E) (cv : Digest) (x0 x1 y c0 c2 : E) : List E :=
  osFsNextValsW Ht x0 cv ++ osFsNextValsW Ht x1 (obsCvW Ht cv x0) ++ [0, 0] ++
    osOodSampleValsW Ht ((lvl + 1 + 0) * 22) logCols oodzv (obsCvW Ht (obsCvW Ht cv x0) x1) y c0 c2

/-- **The next commitment** at its honest values: the root's halves read and stored, then its
out-of-domain sample. -/
theorem osCommit_completeC {lvl logCols roots oodz ood : ℕ} {s : OsSt} {cv : Digest} {cur : E} {p : ℕ}
    (hat : OsAt σ s cv cur p) {x0 x1 y c0 c2 : E} {kret : List E → Prop}
    (lx0 : LoadHolds rd cur p x0) (lx1 : LoadHolds rd cur (p + 1) x1)
    (ly : LoadHolds rd cur (p + 2) y) (lc0 : LoadHolds rd cur (p + 3) c0) (lc2 : LoadHolds rd cur (p + 4) c2)
    (ax0 : obsCvM CM.hm cv x0 = some (obsCvW Ht cv x0))
    (ax1 : obsCvM CM.hm (obsCvW Ht cv x0) x1 = some (obsCvW Ht (obsCvW Ht cv x0) x1))
    (ay : obsCvM CM.hm (sqAllW Ht logCols (obsCvW Ht (obsCvW Ht cv x0) x1)).2 y =
      some (obsCvW Ht (sqAllW Ht logCols (obsCvW Ht (obsCvW Ht cv x0) x1)).2 y))
    (ac0 : obsCvM CM.hm (obsCvW Ht (sqAllW Ht logCols (obsCvW Ht (obsCvW Ht cv x0) x1)).2 y) c0 =
      some (obsCvW Ht (obsCvW Ht (sqAllW Ht logCols (obsCvW Ht (obsCvW Ht cv x0) x1)).2 y) c0))
    (ac2 : obsCvM CM.hm (obsCvW Ht (obsCvW Ht (sqAllW Ht logCols (obsCvW Ht (obsCvW Ht cv x0) x1)).2 y) c0) c2 =
      some (obsCvW Ht (obsCvW Ht (obsCvW Ht (sqAllW Ht logCols (obsCvW Ht (obsCvW Ht cv x0) x1)).2 y) c0) c2))
    (sx0 : LoadHolds rd (σ (.n roots)) (2 * lvl + 2) x0) (sx1 : LoadHolds rd (σ (.n roots)) (2 * lvl + 3) x1)
    (sy : LoadHolds rd (σ (.n ood)) ((lvl + 1) * 4 + 0 * 4 + 1) y)
    (sc0 : LoadHolds rd (σ (.n ood)) ((lvl + 1) * 4 + 0 * 4 + 2) c0)
    (sc2 : LoadHolds rd (σ (.n ood)) ((lvl + 1) * 4 + 0 * 4 + 3) c2)
    (hca0 : C "assert_canonical" [x0] [0]) (hca1 : C "assert_canonical" [x1] [0])
    (hood : C "opening_ood_point" [(digestScalars (obsCvW Ht (obsCvW Ht cv x0) x1)).1,
      (digestScalars (obsCvW Ht (obsCvW Ht cv x0) x1)).2, σ (.n oodz) * osGw ((lvl + 1 + 0) * 22), osGw logCols]
      [(digestScalars (sqAllW Ht logCols (obsCvW Ht (obsCvW Ht cv x0) x1)).2).1,
        (digestScalars (sqAllW Ht logCols (obsCvW Ht (obsCvW Ht cv x0) x1)).2).2])
    (hv : ∀ j < 84, σ (.n (s.k + j)) = (osCommitValsW Ht lvl logCols (σ (.n oodz)) cv x0 x1 y c0 c2).getD j 0) :
    Stmt.HoldsListB CM.sem C rd σ (osCommit lvl logCols 1 roots oodz ood s).1 True kret ∧
      OsAt σ (osCommit lvl logCols 1 roots oodz ood s).2
        (obsCvW Ht (obsCvW Ht (obsCvW Ht (sqAllW Ht logCols (obsCvW Ht (obsCvW Ht cv x0) x1)).2 y) c0) c2) cur (p + 5) ∧
      (osCommit lvl logCols 1 roots oodz ood s).2.co = s.co + 5 ∧
      (osCommit lvl logCols 1 roots oodz ood s).2.cb = s.cb ∧ (osCommit lvl logCols 1 roots oodz ood s).2.k = s.k + 84 := by
  set F1 := osFsNextValsW Ht x0 cv
  set F2 := osFsNextValsW Ht x1 (obsCvW Ht cv x0)
  set Z : List E := [0, 0] with hZ
  set O := osOodSampleValsW Ht ((lvl + 1 + 0) * 22) logCols (σ (.n oodz)) (obsCvW Ht (obsCvW Ht cv x0) x1) y c0 c2
  have hvals : osCommitValsW Ht lvl logCols (σ (.n oodz)) cv x0 x1 y c0 c2 = F1 ++ (F2 ++ (Z ++ O)) := by
    simp only [osCommitValsW, List.append_assoc]; rfl
  rw [hvals] at hv
  have l1 : F1.length = 15 := os_length_fsNextValsW _ _
  have l2 : F2.length = 15 := os_length_fsNextValsW _ _
  have lZ : Z.length = 2 := rfl
  obtain ⟨h1, hat1⟩ := osFsNext_completeC (CM := CM) (C := C) (kret := kret) hat lx0 ax0 fun j hj => by
    rw [hv j (by omega), oq_getD_app_lt (by omega)]
  obtain ⟨h2, hat2⟩ := osFsNext_completeC (CM := CM) (C := C) (kret := kret) hat1 lx1 ax1 fun j hj => by
    rw [show (osFsNext s).2.k + j = s.k + (F1.length + j) by simp [osFsNext, l1]; ring, hv _ (by omega), os_skip,
      oq_getD_app_lt (by omega)]
  set st2 : OsSt := { (osFsNext (osFsNext s).2).2 with k := (osFsNext (osFsNext s).2).2.k + 2 }
  have hk2 : st2.k = s.k + (F1.length + (F2.length + (Z.length + 0))) := by simp [st2, osFsNext, l1, l2, lZ]
  have hat2' : OsAt σ st2 (obsCvW Ht (obsCvW Ht cv x0) x1) cur (p + 1 + 1) := ⟨hat2.fs, hat2.cursor⟩
  obtain ⟨h3, hat3, hco3, hcb3, hk3⟩ := osOodSample_completeC (CM := CM) (oz := (lvl + 1 + 0) * 22)
    (so := (lvl + 1) * 4 + 0 * 4) (logCols := logCols) (oodz := oodz) (ood := ood) (kret := kret) hat2'
    (by simpa using ly) (by simpa [Nat.add_assoc] using lc0) (by simpa [Nat.add_assoc] using lc2) ay ac0 ac2 sy sc0 sc2 hood
    fun j hj => by rw [hk2, Nat.add_zero, show s.k + (F1.length + (F2.length + Z.length)) + j =
      s.k + (F1.length + (F2.length + (Z.length + j))) by ring, hv _ (by omega), os_skip, os_skip, os_skip]
  have v0 : σ (.n s.k) = x0 := by
    have := hv 0 (by omega); rw [oq_getD_app_lt (by omega)] at this; exact this
  have v1 : σ (.n (osFsNext s).2.k) = x1 := by
    have := hv (F1.length + 0) (by omega); rw [os_skip, oq_getD_app_lt (by omega)] at this
    rw [show (osFsNext s).2.k = s.k + (F1.length + 0) by simp [osFsNext, l1]]; exact this
  have w0 : σ (.n ((osFsNext (osFsNext s).2).2.k)) = 0 := by
    have := hv (F1.length + (F2.length + 0)) (by omega); rw [os_skip, os_skip, oq_getD_app_lt (by omega)] at this
    rw [show (osFsNext (osFsNext s).2).2.k = s.k + (F1.length + (F2.length + 0)) by simp [osFsNext, l1, l2]]
    exact this
  have w1 : σ (.n ((osFsNext (osFsNext s).2).2.k + 1)) = 0 := by
    have := hv (F1.length + (F2.length + 1)) (by omega); rw [os_skip, os_skip, oq_getD_app_lt (by omega)] at this
    rw [show (osFsNext (osFsNext s).2).2.k + 1 = s.k + (F1.length + (F2.length + 1)) by simp [osFsNext, l1, l2]]
    exact this
  unfold osCommit
  dsimp only
  simp only [osOods, List.append_nil]
  refine ⟨?_, by simpa [Nat.add_assoc] using hat3, by rw [hco3]; show s.co + 1 + 1 + 3 = s.co + 5; omega, by rw [hcb3]; rfl,
    by rw [hk3, hk2]; simp [lZ, l1, l2]⟩
  simp only [holdsListB_append]
  refine (holdsListB_noRet _ rfl _ _).mpr ⟨h1, ?_⟩
  refine (holdsListB_noRet _ rfl _ _).mpr ⟨h2, ?_⟩
  refine (holdsListB_noRet _ rfl _ _).mpr ⟨?_, h3⟩
  simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, and_true]
  exact ⟨by rw [v0, w0]; exact hca0, by rw [v1, w1]; exact hca1, by rw [v0]; exact sx0, by rw [v1]; exact sx1⟩

/-! ## The proof of work -/

/-- The values of `osGrind bits` (`bits ≠ 0`) from its first: the nonce, the bits' word, the
absorb's values. -/
def osGrindValsW (Ht : Bytes → Digest) (bits : ℕ) (n : E) (cv : Digest) : List E :=
  [n, osGw bits] ++ (List.range 14).map (fsValsW Ht n cv 4)

/-- **The query nonce** at its honest values (`bits ≠ 0`): the word at the cursor, `grind_check`'s
call, its absorb at tag 4. -/
theorem osGrind_completeC {bits : ℕ} (hb0 : bits ≠ 0) {s : OsSt} {cv : Digest} {cur : E} {p : ℕ}
    (hat : OsAt σ s cv cur p) {n : E} (ln : LoadHolds rd cur p n) {kret : List E → Prop}
    (hcall : C "grind_check" [(digestScalars cv).1, (digestScalars cv).2, n, osGw bits] [])
    (an : CM.H (digestBytes cv ++ blockOf n 4) = some (absorbCvW Ht cv n 4))
    (hv : ∀ j < 16, σ (.n (s.k + j)) = (osGrindValsW Ht bits n cv).getD j 0) :
    Stmt.HoldsListB CM.sem C rd σ (osGrind bits s).1 True kret ∧
      OsAt σ (osGrind bits s).2 (absorbCvW Ht cv n 4) cur (p + 1) ∧ (osGrind bits s).2.co = s.co + 1 ∧
      (osGrind bits s).2.cb = s.cb ∧ (osGrind bits s).2.k = s.k + 16 := by
  have e0 : σ (.n s.k) = n := by simpa [osGrindValsW] using hv 0 (by omega)
  have e1 : σ (.n (s.k + 1)) = osGw bits := by simpa [osGrindValsW] using hv 1 (by omega)
  have e : ∀ j < 14, σ (.n (s.k + 2 + j)) = fsValsW Ht n cv 4 j := fun j hj => by
    rw [Nat.add_assoc, hv _ (by omega), show 2 + j = j + 1 + 1 by ring]
    simp [osGrindValsW, List.getD_eq_getElem?_getD, hj]
  unfold osGrind
  dsimp only
  rw [ite_neg' hb0]
  refine ⟨?_, ⟨?_, ?_⟩, rfl, rfl, rfl⟩
  · simp only [holdsListB_append]
    refine (holdsListB_noRet _ rfl _ _).mpr ⟨?_, ?_⟩
    · simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, and_true]
      have hl := os_cursor_load (j := 0) hat (by rw [Nat.add_zero]; exact ln)
      rw [Nat.add_zero] at hl
      rw [e0]; exact hl
    refine (holdsListB_noRet _ rfl _ _).mpr ⟨?_, ?_⟩
    · simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, and_true]
      refine ⟨e1, ?_⟩
      have f0 : (digestScalars cv).1 = σ (.n s.f0) := by rw [← hat.fs]
      have f1 : (digestScalars cv).2 = σ (.n s.f1) := by rw [← hat.fs]
      rw [e0, e1, ← f0, ← f1]
      exact hcall
    · refine holdsB_fsCompressT_comp _ _ _ _ (tag := 4) (by decide) ⟨⟨cv, absorbCvW Ht cv n 4, hat.fs,
        by rw [e0]; exact an, fun j h1 h2 => ?_⟩, trivial⟩
      rw [e j h2, e0, fsValsW_eq Ht n cv 4 h2]
  · show (σ (.n (s.k + 14)), σ (.n (s.k + 15))) = _
    rw [show s.k + 14 = s.k + 2 + 12 by ring, show s.k + 15 = s.k + 2 + 13 by ring, e 12 (by omega),
      e 13 (by omega)]
    simp only [fsValsW]
  · show σ (.n s.cb) * gen ^ (s.co + 1) = cur * gen ^ (p + 1)
    rw [pow_succ, pow_succ, ← mul_assoc, ← mul_assoc, hat.cursor]


/-! ## The squeezes -/

/-- The values of `osSqueezes` from its first, the state buffer at `sqzv`: its size and pointer,
the loop's bound and arguments, the last state's pointer and cells, the closing squeeze's values. -/
def osSqueezesValsW (Ht : Bytes → Digest) (maxSq nsq : ℕ) (sqzv : E) (cv : Digest) : List E :=
  [osGw (2 * (maxSq + 1)), sqzv, 1, osGw nsq, 1 + osGw nsq, 1, osGw nsq, osGw (2 * nsq), sqzv * osGw (2 * nsq),
    (digestScalars (sqAllW Ht nsq cv).2).1, (digestScalars (sqAllW Ht nsq cv).2).2] ++
    (List.range 14).map (sqValsW Ht (sqAllW Ht nsq cv).2)

/-- **The query positions' squeezes** at their honest values: the state stored at `sqz[0 ..]`, the
loop's call, the last state read back at `sqz[2nsq ..]`, the batching challenge squeezed. -/
theorem osSqueezes_completeC {maxSq nsq qpos qbp : ℕ} {loop : String} (hnsq : 2 * nsq < 2 ^ 128) {s : OsSt}
    {cv : Digest} {cur : E} {p : ℕ} (hat : OsAt σ s cv cur p) {sqzv : E} {kret : List E → Prop}
    (l0 : LoadHolds rd sqzv 0 (digestScalars cv).1) (l1 : LoadHolds rd sqzv 1 (digestScalars cv).2)
    (l2 : LoadHolds rd sqzv (2 * nsq) (digestScalars (sqAllW Ht nsq cv).2).1)
    (l3 : LoadHolds rd sqzv (2 * nsq + 1) (digestScalars (sqAllW Ht nsq cv).2).2)
    (hcall : 1 + osGw nsq ≠ 0 → C loop [1, osGw nsq, sqzv, σ (.n qpos), σ (.n qbp)] [])
    (asq : sqCvM CM.hm (sqAllW Ht nsq cv).2 = some (sqCvW Ht (sqAllW Ht nsq cv).2))
    (hv : ∀ j < 25, σ (.n (s.k + j)) = (osSqueezesValsW Ht maxSq nsq sqzv cv).getD j 0) :
    Stmt.HoldsListB CM.sem C rd σ (osSqueezes maxSq nsq qpos qbp loop s).1 True kret ∧
      OsAt σ (osSqueezes maxSq nsq qpos qbp loop s).2 (sqCvW Ht (sqAllW Ht nsq cv).2) cur p ∧
      σ (.n ((osSqueezes maxSq nsq qpos qbp loop s).2.k - 1)) = challengeOf (sqCvW Ht (sqAllW Ht nsq cv).2) ∧
      (osSqueezes maxSq nsq qpos qbp loop s).2.co = s.co ∧ (osSqueezes maxSq nsq qpos qbp loop s).2.cb = s.cb ∧
      (osSqueezes maxSq nsq qpos qbp loop s).2.k = s.k + 25 := by
  set cS := (sqAllW Ht nsq cv).2
  set A : List E := [osGw (2 * (maxSq + 1)), sqzv, 1, osGw nsq, 1 + osGw nsq, 1, osGw nsq, osGw (2 * nsq),
    sqzv * osGw (2 * nsq), (digestScalars cS).1, (digestScalars cS).2] with hA
  have hvals : osSqueezesValsW Ht maxSq nsq sqzv cv = A ++ (List.range 14).map (sqValsW Ht cS) := rfl
  rw [hvals] at hv
  have lA : A.length = 11 := rfl
  have gA : ∀ j < 11, σ (.n (s.k + j)) = A.getD j 0 := fun j hj => by
    rw [hv j (by omega), oq_getD_app_lt (by omega)]
  have gS : ∀ j < 14, σ (.n (s.k + 11 + j)) = sqValsW Ht cS j := fun j hj => by
    rw [Nat.add_assoc, show 11 + j = A.length + j by rw [lA], hv _ (by omega), os_skip]
    simp [List.getD_eq_getElem?_getD, hj]
  have e := fun j (hj : j < 11) => gA j hj
  have e0 := e 0 (by omega); have e1 := e 1 (by omega); have e2 := e 2 (by omega)
  have e3 := e 3 (by omega); have e4 := e 4 (by omega); have e5 := e 5 (by omega)
  have e6 := e 6 (by omega); have e7 := e 7 (by omega); have e8 := e 8 (by omega)
  have e9 := e 9 (by omega); have e10 := e 10 (by omega)
  simp only [hA, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
  unfold osSqueezes
  dsimp only
  refine ⟨?_, ⟨?_, hat.cursor⟩, ?_, rfl, rfl, rfl⟩
  · rw [holdsListB_append]
    refine (holdsListB_noRet _ (by simp [osHeap, Stmt.noRetList, Stmt.noRet]) _ _).mpr ⟨?_, ?_⟩
    · simp only [osHeap, List.cons_append, List.nil_append, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB,
        List.map_cons, List.map_nil, and_true, true_and, word_one]
      refine ⟨e0, ?_, ?_, e2, e3, by rw [e4, e2, e3], e5, e6, ?_, fun h => by rw [e5, e6, e1]; exact hcall (by
        rwa [e4] at h), e7, by rw [e8, e1, e7], ?_, ?_⟩
      · have f0e : σ (.n s.f0) = (digestScalars cv).1 := congrArg Prod.fst hat.fs
        rw [e1, f0e]; exact l0
      · have f1e : σ (.n s.f1) = (digestScalars cv).2 := congrArg Prod.snd hat.fs
        rw [e1, f1e]; exact l1
      · rw [e4]; exact isInK_add (by simpa using gen_pow_isInK 0) (by rw [os_gw_eq (by omega)]; exact gen_pow_isInK _)
      · rw [e8, e9, os_gw_eq hnsq, loadHolds_gen_pow]; exact l2
      · rw [e8, e10, os_gw_eq hnsq, loadHolds_mul_gen_pow]; exact l3
    · exact holdsB_squeezeT_comp _ _ _ ⟨⟨cS, sqCvW Ht cS, by rw [e9, e10], asq,
        fun j hj => by rw [gS j hj, sqValsW_eq Ht cS hj]⟩, trivial⟩
  · show (σ (.n (s.k + 16)), σ (.n (s.k + 17))) = _
    rw [show s.k + 16 = s.k + 11 + 5 by ring, show s.k + 17 = s.k + 11 + 6 by ring, gS 5 (by omega),
      gS 6 (by omega)]
    rfl
  · show σ (.n (s.k + 25 - 1)) = _
    rw [show s.k + 25 - 1 = s.k + 11 + 13 by omega, gS 13 (by omega)]
    rfl


/-! ## The queries -/

/-- The value segments of `osQueries` from its first: the row weights' buffer, the pointers, the
cap's root, the query count and sum, the intro's reads, its middle coefficient. -/
def osQueriesSegsW (Ht : Bytes → Digest) (cfg : OsCfg) (lv : OsLvl) (lvl : ℕ) (rewv fchv capsv flagsv qwv qbpv : E) (rt : Digest)
    (qsum c0 c2 : E) (cv : Digest) : List (List E) :=
  [[osGw cfg.maxIl, rewv], osMatVals fchv lv.foldsOff, osMatVals capsv (4 * lv.capOff), osMatVals flagsv lv.capOff,
    [(digestScalars rt).1, (digestScalars rt).2], osMatVals capsv (4 * lv.capOff), osMatVals flagsv lv.capOff,
    osMatVals qwv (lvl * cfg.maxQ), osMatVals qbpv lv.posOff, [osGw lv.queries, qsum], osFsNextValsW Ht c0 cv,
    osFsNextValsW Ht c2 (obsCvW Ht cv c0), [qsum + c2]]

/-- **A level's queries** at their honest values: the row weights' buffer, the calls' pointers, the
cap's root checked against the level's root, the queries' sum, the intro's `c0`, `c2` read. -/
theorem osQueries_completeC {cfg : OsCfg} {lv : OsLvl} {lvl : ℕ} (hfo : lv.foldsOff < 2 ^ 128)
    (hco4 : 4 * lv.capOff < 2 ^ 128) (hco1 : lv.capOff < 2 ^ 128) (hqo : lvl * cfg.maxQ < 2 ^ 128)
    (hpo : lv.posOff < 2 ^ 128) {s : OsSt} {cv : Digest} {cur : E} {p : ℕ} (hat : OsAt σ s cv cur p)
    {rewv : E} {rt : Digest} {qsum c0 c2 : E} {kret : List E → Prop}
    (lc0 : LoadHolds rd cur p c0) (lc2 : LoadHolds rd cur (p + 1) c2)
    (ac0 : obsCvM CM.hm cv c0 = some (obsCvW Ht cv c0))
    (ac2 : obsCvM CM.hm (obsCvW Ht cv c0) c2 = some (obsCvW Ht (obsCvW Ht cv c0) c2))
    (sr0 : LoadHolds rd (σ (.n osRoots)) (2 * lvl) (digestScalars rt).1)
    (sr1 : LoadHolds rd (σ (.n osRoots)) (2 * lvl + 1) (digestScalars rt).2)
    (hrw : C lv.rowWeights [σ (.n osFch) * gen ^ lv.foldsOff, rewv] [])
    (hcap : C lv.verifyCap [σ (.n osCaps) * gen ^ (4 * lv.capOff), σ (.n osFlags) * gen ^ lv.capOff]
      [(digestScalars rt).1, (digestScalars rt).2])
    (hqf : C lv.queriesFn [σ (.n osCaps) * gen ^ (4 * lv.capOff), σ (.n osFlags) * gen ^ lv.capOff,
      σ (.n osQw) * gen ^ (lvl * cfg.maxQ), σ (.n osQbp) * gen ^ lv.posOff, rewv, osGw lv.queries] [qsum])
    (hv : ∀ j < (osQueriesSegsW Ht cfg lv lvl rewv (σ (.n osFch)) (σ (.n osCaps)) (σ (.n osFlags)) (σ (.n osQw))
        (σ (.n osQbp)) rt qsum c0 c2 cv).flatten.length,
      σ (.n (s.k + j)) = (osQueriesSegsW Ht cfg lv lvl rewv (σ (.n osFch)) (σ (.n osCaps)) (σ (.n osFlags)) (σ (.n osQw))
        (σ (.n osQbp)) rt qsum c0 c2 cv).flatten.getD j 0) :
    let q := osQueries cfg lv lvl s
    Stmt.HoldsListB CM.sem C rd σ q.1 True kret ∧ OsAt σ q.2.1 (obsCvW Ht (obsCvW Ht cv c0) c2) cur (p + 2) ∧
      q.2.1.co = s.co + 2 ∧ q.2.1.cb = s.cb ∧ σ (.n q.2.2.1) = qsum ∧ σ (.n q.2.2.2.1) = c0 ∧
      σ (.n q.2.2.2.2.1) = qsum + c2 ∧ σ (.n q.2.2.2.2.2) = c2 ∧ σ (.n (s.k + 1)) = rewv ∧
      q.2.1.k = s.k + (osQueriesSegsW Ht cfg lv lvl rewv (σ (.n osFch)) (σ (.n osCaps)) (σ (.n osFlags)) (σ (.n osQw))
        (σ (.n osQbp)) rt qsum c0 c2 cv).flatten.length := by
  intro q
  set segs := osQueriesSegsW Ht cfg lv lvl rewv (σ (.n osFch)) (σ (.n osCaps)) (σ (.n osFlags)) (σ (.n osQw))
    (σ (.n osQbp)) rt qsum c0 c2 cv with hsegs
  have look := os_seg_look hv
  have hl : segs.length = 13 := rfl
  have L := fun i (hi : i < 13) j (hj : j < (segs.getD i []).length) => look i (by omega) j hj
  have hlen : ∀ (b : E) off, (osMatVals b off).length = (osMatVals 0 off).length := os_length_matVals'
  set k := s.k
  -- positions
  set P := osMat osFch lv.foldsOff (k + 2)
  set CP := osMat osCaps (4 * lv.capOff) P.2.2
  set FP := osMat osFlags lv.capOff CP.2.2
  set r := FP.2.2
  set CP2 := osMat osCaps (4 * lv.capOff) (r + 2)
  set FP2 := osMat osFlags lv.capOff CP2.2.2
  set QP := osMat osQw (lvl * cfg.maxQ) FP2.2.2
  set BP := osMat osQbp lv.posOff QP.2.2
  set g := BP.2.2
  have hp : ∀ i, osPre segs (i + 1) = osPre segs i + (segs.getD i []).length := fun i => by
    simp only [osPre]
    rcases Nat.lt_or_ge i segs.length with h | h
    · rw [List.take_add_one, List.map_append, List.sum_append, List.getElem?_eq_getElem h]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr h]
  have g0 : (segs.getD 0 []).length = 2 := rfl
  have g1 : (segs.getD 1 []).length = (osMatVals 0 lv.foldsOff).length := hlen _ _
  have g2 : (segs.getD 2 []).length = (osMatVals 0 (4 * lv.capOff)).length := hlen _ _
  have g3 : (segs.getD 3 []).length = (osMatVals 0 lv.capOff).length := hlen _ _
  have g4 : (segs.getD 4 []).length = 2 := rfl
  have g5 : (segs.getD 5 []).length = (osMatVals 0 (4 * lv.capOff)).length := hlen _ _
  have g6 : (segs.getD 6 []).length = (osMatVals 0 lv.capOff).length := hlen _ _
  have g7 : (segs.getD 7 []).length = (osMatVals 0 (lvl * cfg.maxQ)).length := hlen _ _
  have g8 : (segs.getD 8 []).length = (osMatVals 0 lv.posOff).length := hlen _ _
  have g9 : (segs.getD 9 []).length = 2 := rfl
  have g10 : (segs.getD 10 []).length = 15 := os_length_fsNextValsW _ _
  have g11 : (segs.getD 11 []).length = 15 := os_length_fsNextValsW _ _
  have g12 : (segs.getD 12 []).length = 1 := rfl
  have o0 : osPre segs 0 = 0 := rfl
  have o1 : osPre segs 1 = 2 := by rw [hp, o0, g0]
  have o2 := hp 1; have o3 := hp 2; have o4 := hp 3; have o5 := hp 4; have o6 := hp 5; have o7 := hp 6
  have o8 := hp 7; have o9 := hp 8; have o10 := hp 9; have o11 := hp 10; have o12 := hp 11; have o13 := hp 12
  have q1 : k + 2 = k + osPre segs 1 := by rw [o1]
  have q2 : P.2.2 = k + osPre segs 2 := by rw [osMat_next', o2, o1, g1]; ring
  have q3 : CP.2.2 = k + osPre segs 3 := by rw [osMat_next', q2, o3, g2]; ring
  have q4 : r = k + osPre segs 4 := by rw [show r = FP.2.2 from rfl, osMat_next', q3, o4, g3]; ring
  have q5 : r + 2 = k + osPre segs 5 := by rw [q4, o5, g4]; ring
  have q6 : CP2.2.2 = k + osPre segs 6 := by rw [osMat_next', q5, o6, g5]; ring
  have q7 : FP2.2.2 = k + osPre segs 7 := by rw [osMat_next', q6, o7, g6]; ring
  have q8 : QP.2.2 = k + osPre segs 8 := by rw [osMat_next', q7, o8, g7]; ring
  have q9 : g = k + osPre segs 9 := by rw [show g = BP.2.2 from rfl, osMat_next', q8, o9, g8]; ring
  have q10 : g + 2 = k + osPre segs 10 := by rw [q9, o10, g9]; ring
  have q11 : g + 2 + 15 = k + osPre segs 11 := by rw [q10, o11, g10]; omega
  have q12 : g + 2 + 15 + 15 = k + osPre segs 12 := by rw [q11, o12, g11]; omega
  have qend : osPre segs 13 = segs.flatten.length := by
    simp only [osPre, show 13 = segs.length from rfl, List.take_length, List.length_flatten]
  -- the lookups
  have look0 := L 0 (by omega); have look1 := L 1 (by omega); have look2 := L 2 (by omega)
  have look3 := L 3 (by omega); have look4 := L 4 (by omega); have look5 := L 5 (by omega)
  have look6 := L 6 (by omega); have look7 := L 7 (by omega); have look8 := L 8 (by omega)
  have look9 := L 9 (by omega); have look10 := L 10 (by omega); have look11 := L 11 (by omega)
  have look12 := L 12 (by omega)
  rw [o0, Nat.add_zero] at look0
  have v0 : σ (.n k) = osGw cfg.maxIl := look0 0 (by omega)
  have v1 : σ (.n (k + 1)) = rewv := look0 1 (by omega)
  have mP := osMat_completeB (S := CM.sem) (C := C) (rd := rd) (σ := σ) (base := osFch) (k := k + 2) (kret := kret) hfo
    fun j hj => by rw [q1]; exact look1 j (by rwa [g1, ← hlen (σ (.n osFch))])
  have mCP := osMat_completeB (S := CM.sem) (C := C) (rd := rd) (σ := σ) (base := osCaps) (k := P.2.2) (kret := kret) hco4
    fun j hj => by rw [q2]; exact look2 j (by rwa [g2, ← hlen (σ (.n osCaps))])
  have mFP := osMat_completeB (S := CM.sem) (C := C) (rd := rd) (σ := σ) (base := osFlags) (k := CP.2.2) (kret := kret) hco1
    fun j hj => by rw [q3]; exact look3 j (by rwa [g3, ← hlen (σ (.n osFlags))])
  have vr0 : σ (.n r) = (digestScalars rt).1 := by rw [q4]; exact look4 0 (by omega)
  have vr1 : σ (.n (r + 1)) = (digestScalars rt).2 := by
    have := look4 1 (by omega); rw [← q4] at this; exact this
  have mCP2 := osMat_completeB (S := CM.sem) (C := C) (rd := rd) (σ := σ) (base := osCaps) (k := r + 2) (kret := kret) hco4
    fun j hj => by rw [q5]; exact look5 j (by rwa [g5, ← hlen (σ (.n osCaps))])
  have mFP2 := osMat_completeB (S := CM.sem) (C := C) (rd := rd) (σ := σ) (base := osFlags) (k := CP2.2.2) (kret := kret) hco1
    fun j hj => by rw [q6]; exact look6 j (by rwa [g6, ← hlen (σ (.n osFlags))])
  have mQP := osMat_completeB (S := CM.sem) (C := C) (rd := rd) (σ := σ) (base := osQw) (k := FP2.2.2) (kret := kret) hqo
    fun j hj => by rw [q7]; exact look7 j (by rwa [g7, ← hlen (σ (.n osQw))])
  have mBP := osMat_completeB (S := CM.sem) (C := C) (rd := rd) (σ := σ) (base := osQbp) (k := QP.2.2) (kret := kret) hpo
    fun j hj => by rw [q8]; exact look8 j (by rwa [g8, ← hlen (σ (.n osQbp))])
  have vg0 : σ (.n g) = osGw lv.queries := by rw [q9]; exact look9 0 (by omega)
  have vg1 : σ (.n (g + 1)) = qsum := by have := look9 1 (by omega); rw [← q9] at this; exact this
  set s1 : OsSt := { s with k := g + 2 }
  have hat1 : OsAt σ s1 cv cur p := ⟨hat.fs, hat.cursor⟩
  obtain ⟨hi0, hat2⟩ := osFsNext_completeC (CM := CM) (C := C) (kret := kret) hat1 lc0 ac0 fun j hj => by
    show σ (.n (g + 2 + j)) = _
    rw [q10]; exact look10 j (by omega)
  obtain ⟨hi2, hat3⟩ := osFsNext_completeC (CM := CM) (C := C) (kret := kret) hat2 lc2 ac2 fun j hj => by
    show σ (.n (g + 2 + 15 + j)) = _
    rw [q11]; exact look11 j (by omega)
  have vc0 : σ (.n s1.k) = c0 := by show σ (.n (g + 2)) = c0; rw [q10]; exact look10 0 (by omega)
  have vc2 : σ (.n (osFsNext s1).2.k) = c2 := by
    show σ (.n (g + 2 + 15)) = c2; have := look11 0 (by omega); rw [Nat.add_zero, ← q11] at this; exact this
  have vc1 : σ (.n (osFsNext (osFsNext s1).2).2.k) = qsum + c2 := by
    show σ (.n (g + 2 + 15 + 15)) = _; have := look12 0 (by omega); rw [Nat.add_zero, ← q12] at this; exact this
  refine ⟨?_, ⟨hat3.fs, hat3.cursor⟩, by simp [q, osQueries, osFsNext], rfl, vg1, vc0, vc1, vc2, v1, ?_⟩
  · show Stmt.HoldsListB CM.sem C rd σ (osHeap cfg.maxIl k ++ P.1 ++ [.call lv.rowWeights [.n P.2.1, .n (k + 1)] []] ++
      CP.1 ++ FP.1 ++ [.call lv.verifyCap [.n CP.2.1, .n FP.2.1] [.n r, .n (r + 1)],
        .atom (.load (.n r) (.n osRoots) (2 * lvl)), .atom (.load (.n (r + 1)) (.n osRoots) (2 * lvl + 1))] ++
      CP2.1 ++ FP2.1 ++ QP.1 ++ BP.1 ++ [.atom (.const (.n g) (osGw lv.queries)),
        .call lv.queriesFn [.n CP2.2.1, .n FP2.2.1, .n QP.2.1, .n BP.2.1, .n (k + 1), .n g] [.n (g + 1)]] ++
      (osFsNext s1).1 ++ (osFsNext (osFsNext s1).2).1 ++
      [.atom (.add (.n (osFsNext (osFsNext s1).2).2.k) (.n (g + 1)) (.n (osFsNext s1).2.k))]) True kret
    simp only [holdsListB_append]
    refine (holdsListB_noRet _ rfl _ _).mpr ⟨?_, (holdsListB_noRet _ (osMat_noRet _ _ _) _ _).mpr ⟨mP.1,
      (holdsListB_noRet _ rfl _ _).mpr ⟨⟨by simp only [List.map_cons, List.map_nil]; rw [mP.2, v1]; exact hrw, trivial⟩,
      (holdsListB_noRet _ (osMat_noRet _ _ _) _ _).mpr ⟨mCP.1,
      (holdsListB_noRet _ (osMat_noRet _ _ _) _ _).mpr ⟨mFP.1, (holdsListB_noRet _ rfl _ _).mpr ⟨?_,
      (holdsListB_noRet _ (osMat_noRet _ _ _) _ _).mpr ⟨mCP2.1, (holdsListB_noRet _ (osMat_noRet _ _ _) _ _).mpr
      ⟨mFP2.1, (holdsListB_noRet _ (osMat_noRet _ _ _) _ _).mpr ⟨mQP.1, (holdsListB_noRet _ (osMat_noRet _ _ _) _ _).mpr
      ⟨mBP.1, (holdsListB_noRet _ rfl _ _).mpr ⟨?_, (holdsListB_noRet _ rfl _ _).mpr ⟨hi0,
      (holdsListB_noRet _ rfl _ _).mpr ⟨hi2, ?_⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
    · simp only [osHeap, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, and_true]
      exact v0
    · simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, and_true]
      exact ⟨by rw [mCP.2, mFP.2, vr0, vr1]; exact hcap, by rw [vr0]; exact sr0, by rw [vr1]; exact sr1⟩
    · simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, and_true]
      refine ⟨vg0, ?_⟩
      rw [mCP2.2, mFP2.2, mQP.2, mBP.2, v1, vg0, vg1]
      exact hqf
    · simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, and_true]
      rw [vc1, vg1, vc2]
  · show (osFsNext (osFsNext s1).2).2.k + 1 = _
    rw [← qend, hp 12, show (osFsNext (osFsNext s1).2).2.k = g + 2 + 15 + 15 from rfl, q12, g12]; ring


end
end LeanVM.Guest.B1
