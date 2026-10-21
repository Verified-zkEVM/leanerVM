/-
  LeanVM.Guest.B1.Comp.Tables.GkrInvC

  The GKR walk's answered run read back over a hash model: the honest trace `verify_bus_gkr`
  follows, at the model's total hash, every hash answered.
-/

module

public import LeanVM.Guest.B1.Comp.Tables.RunFrameM
public import LeanVM.Guest.B1.Tables.GkrTrace

/-!
# The honest trace over a hash model

`GkrInv.lean`, `GkrPair.lean` and `GkrTrace.lean` over a hash model `M`, the run answered
(`RunsToM M`): `RunsToM.gkrStep_inv`, `RunsToM.sumcheck_inv`, `RunsToM.gkrPairs_inv`,
`pair_dataM`, `odd_dataM`, `RunsToM.gkrPhase_inv`, and `exists_traceM`: the whole walk as a
`GkrTrace` with its facts at the total hash (`GkrTrace.OkM`: `GkrTrace.Ok` with `obsCvT`,
`sqCvT`, `l10cvT`, the rounds' runs answered, and every other hash of the walk answered,
`L10Ans`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {M : HashModel}

/-! ## The children's chain at the total hash -/

variable (M) in
/-- The chain after the first `i` children at the total hash (`l10cv`). -/
def l10cvT (cvT : Digest) (es : ℕ → E) : ℕ → Digest
  | 0 => cvT
  | i + 1 => obsCvT M (l10cvT cvT es i) (es i)

variable (M) in
/-- **The first `n` children's absorbs are answered.** -/
def L10Ans (cvT : Digest) (es : ℕ → E) (n : ℕ) : Prop :=
  ∀ i < n, obsCvM M (l10cvT M cvT es i) (es i) = some (l10cvT M cvT es (i + 1))

theorem l10cvT_eq (cvT : Digest) (l : List E) :
    ∀ i ≤ l.length, l10cvT M cvT (fun j => l.getD j 0) i = obsAllT M cvT (l.take i)
  | 0, _ => rfl
  | i + 1, hi => by
    rw [l10cvT, l10cvT_eq cvT l i (by omega), obsAllT_take_succ _ _ (by omega)]

theorem l10Ans_of (cvT : Digest) {l : List E} (h : ObsAns M cvT l) :
    L10Ans M cvT (fun j => l.getD j 0) l.length := fun i hi => by
  rw [l10cvT_eq cvT l i (by omega), l10cvT_eq cvT l (i + 1) (by omega)]
  exact h i hi

/-! ## The steps, inverted -/

/-- **A step's answered run, inverted** (`RunsTo.gkrStep_inv`). -/
theorem RunsToM.gkrStep_inv {step : ℕ} {s s' : GkrState} {cv cv' : Digest} {ys : List E}
    (h : RunsToM M (gkrStep step s) cv ys s' cv') :
    ∃ (ws chs : List E) (cl : E) (cvS : Digest) (c0 c1 c2 pts : List E),
      sqCvM M cv = some (sqCvT M cv) ∧
      RunsToM M (sumcheck (polyEval s.values (challengeOf (sqCvT M cv))) (2 ^ step + 1)
        (s.point.map some)) (sqCvT M cv) ws (chs, cl) cvS ∧
      c0.length = 2 ^ step ∧ c1.length = 2 ^ step ∧ c2.length = 2 ^ step ∧
      cl = polyEval [prodE c0, prodE c1, prodE c2] (challengeOf (sqCvT M cv)) ∧
      ys = ws ++ (c0 ++ (c1 ++ c2)) ∧ ObsAns M cvS (c0 ++ (c1 ++ c2)) ∧
      sqAllM M step (obsAllT M cvS (c0 ++ (c1 ++ c2))) = some (pts, cv') ∧
      s' = ⟨[c0, c1, c2].map (multilinearEval · pts), pts ++ chs⟩ := by
  unfold gkrStep at h
  obtain ⟨x1, y1, comb, cv1, rfl, h1, k1⟩ := RunsToM.bind_inv' h
  obtain ⟨rfl, hc1, rfl⟩ := RunsToM.sampleEP_inv h1
  obtain rfl := (sqCvT_eq hc1).symm
  obtain ⟨ws, y2, ⟨chs, cl⟩, cvS, rfl, hsc, k2⟩ := RunsToM.bind_inv' k1
  obtain ⟨c0, y3, c0', cv3, rfl, h3, k3⟩ := RunsToM.bind_inv' k2
  obtain ⟨hl0, e0, ho0⟩ := RunsToM.readNP_inv h3
  obtain ⟨c1, y4, c1', cv4, rfl, h4, k4⟩ := RunsToM.bind_inv' k3
  obtain ⟨hl1, e1, ho1⟩ := RunsToM.readNP_inv h4
  obtain ⟨c2, y5, c2', cv5, rfl, h5, k5⟩ := RunsToM.bind_inv' k4
  obtain ⟨hl2, e2, ho2⟩ := RunsToM.readNP_inv h5
  obtain ⟨y6, y7, u, cv6, rfl, h6, k6⟩ := RunsToM.bind_inv' k5
  obtain ⟨hreq, rfl, rfl⟩ := RunsToM.requireP_inv h6
  obtain ⟨y8, y9, yy, cv8, rfl, h8, k8⟩ := RunsToM.bind_inv' k6
  obtain ⟨rfl, hsq⟩ := RunsToM.sampleNP_inv h8
  obtain ⟨rfl, rfl, rfl⟩ := RunsToM.pure_inv k8
  subst e0 e1 e2
  obtain ⟨rfl, a0⟩ := obsAllM_T ho0
  obtain ⟨rfl, a1⟩ := obsAllM_T ho1
  obtain ⟨rfl, a2⟩ := obsAllM_T ho2
  have hA : ObsAns M cvS (c0' ++ (c1' ++ c2')) := obsAns_append a0 (obsAns_append a1 a2)
  refine ⟨ws, chs, cl, cvS, c0', c1', c2', yy, hc1, hsc, hl0, hl1, hl2, ?_, by simp, hA, ?_, rfl⟩
  · simpa using hreq
  · rw [obsAllT_append, obsAllT_append]; exact hsq

/-- **An answered sumcheck's run, inverted**, round by round (`RunsTo.sumcheck_inv`). -/
theorem RunsToM.sumcheck_inv {count : ℕ} : ∀ (es : List (Option E)) (claim : E) (cv cv2 : Digest)
    (ws pt : List E) (fin : E), RunsToM M (sumcheck claim count es) cv ws (pt, fin) cv2 →
    ∃ (cl : ℕ → E) (cvr : ℕ → Digest) (wsr : ℕ → List E) (ch : ℕ → E), cl 0 = claim ∧ cvr 0 = cv ∧
      (∀ r (hr : r < es.length),
        RunsToM M (roundPoly count (cl r) es[r]) (cvr r) (wsr r) (cl (r + 1), ch r)
          (cvr (r + 1))) ∧
      ws = (List.range es.length).flatMap wsr ∧ pt = (List.range es.length).map ch ∧
      fin = cl es.length ∧ cv2 = cvr es.length
  | [], claim, cv, cv2, ws, pt, fin, h => by
    have h' : RunsToM M (pure ([], claim) : Prog (List E × E)) cv ws (pt, fin) cv2 := h
    obtain ⟨hx, he, hc⟩ := RunsToM.pure_inv h'
    simp only [Prod.mk.injEq] at he
    exact ⟨fun _ => claim, fun _ => cv, fun _ => [], fun _ => 0, rfl, rfl,
      fun r hr => absurd hr (by simp), by simp [hx], by simp [he.1], he.2, hc⟩
  | e :: es, claim, cv, cv2, ws, pt, fin, h => by
    rw [sumcheck_cons_eq] at h
    obtain ⟨w1, y1, ⟨claim', c⟩, cv1, rfl, h1, h⟩ := RunsToM.bind_inv' h
    obtain ⟨w2, y2, ⟨pt', fin'⟩, cv3, rfl, h2, h⟩ := RunsToM.bind_inv' h
    obtain ⟨rfl, he, rfl⟩ := RunsToM.pure_inv h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨cl, cvr, wsr, ch, h0, hc0, hr, hw, hp, hf, hcv⟩ :=
      RunsToM.sumcheck_inv es claim' cv1 cv2 w2 pt' fin h2
    refine ⟨fun k => if k = 0 then claim else cl (k - 1), fun k => if k = 0 then cv else cvr (k - 1),
      fun k => if k = 0 then w1 else wsr (k - 1), fun k => if k = 0 then c else ch (k - 1),
      rfl, rfl, fun r hr' => ?_, ?_, ?_, ?_, ?_⟩
    · match r with
      | 0 => simpa [h0, hc0] using h1
      | r + 1 =>
        have := hr r (by simpa using hr')
        simpa using this
    · rw [hw, List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
      simp
    · rw [hp, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
      simp [Function.comp_def]
    · simp [hf]
    · simp [hcv]

/-- **The pairs' answered run, inverted**, step by step (`RunsTo.gkrPairs_inv`). -/
theorem RunsToM.gkrPairs_inv : ∀ (m : ℕ) (s : GkrState) (cv : Digest) (xs : List E)
    (s' : GkrState) (cv' : Digest), RunsToM M (gkrPairs m s) cv xs s' cv' →
    ∃ (st : ℕ → GkrState) (cvs : ℕ → Digest) (ys : ℕ → List E), st 0 = s ∧ cvs 0 = cv ∧
      (∀ i < m, RunsToM M (gkrStep 2 (st i)) (cvs i) (ys i) (st (i + 1)) (cvs (i + 1))) ∧
      xs = (List.range m).flatMap ys ∧ s' = st m ∧ cv' = cvs m
  | 0, s, cv, xs, s', cv', h => by
    have h' : RunsToM M (pure s : Prog GkrState) cv xs s' cv' := h
    obtain ⟨hx, hs, hc⟩ := RunsToM.pure_inv h'
    exact ⟨fun _ => s, fun _ => cv, fun _ => [], rfl, rfl, fun i hi => absurd hi (by omega),
      by simp [hx], hs, hc⟩
  | m + 1, s, cv, xs, s', cv', h => by
    rw [gkrPairs_succ'] at h
    obtain ⟨y1, y2, s1, cv1, rfl, h1, h⟩ := RunsToM.bind_inv' h
    obtain ⟨st, cvs, ys, h0, hc0, hs, hx, hst, hcv⟩ := RunsToM.gkrPairs_inv m s1 cv1 y2 s' cv' h
    refine ⟨fun k => if k = 0 then s else st (k - 1), fun k => if k = 0 then cv else cvs (k - 1),
      fun k => if k = 0 then y1 else ys (k - 1), rfl, rfl, fun i hi => ?_, ?_, by simp [hst],
      by simp [hcv]⟩
    · match i with
      | 0 => simpa [h0, hc0] using h1
      | i + 1 => simpa using hs i (by omega)
    · rw [hx, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
      simp

theorem RunsToM.roundPoly_inv {count : ℕ} {claim e : E} {cv cv' : Digest} {ws : List E}
    {r : E × E} (h : RunsToM M (roundPoly count claim (some e)) cv ws r cv') :
    ws.length = count - 1 := by
  unfold roundPoly at h
  obtain ⟨x1, x2, msg, cv1, hx, h1, h⟩ := RunsToM.bind_inv' h
  unfold sumcheckRoundPoly at h1
  obtain ⟨y1, y2, tail, cv2, hy, h2, h1⟩ := RunsToM.bind_inv' h1
  obtain ⟨hl, -, -⟩ := RunsToM.readNP_inv h2
  obtain ⟨hy2, -, -⟩ := RunsToM.pure_inv h1
  obtain ⟨x3, x4, c, cv3, hz, h3, h⟩ := RunsToM.bind_inv' h
  obtain ⟨hx3, -, -⟩ := RunsToM.sampleEP_inv h3
  obtain ⟨hx4, -, -⟩ := RunsToM.pure_inv h
  rw [hx, hy, hz, hy2, hx3, hx4]
  simpa using hl

/-! ## A pair step and the odd step, read back -/

/-- What `pair_dataM` says of a pair step from `s` (of `L` coordinates) to `s'` reading `ys`, at
the total hash, every hash answered (`PairOk`). -/
def PairOkM (M : HashModel) (s s' : GkrState) (cv cv' : Digest) (ys : List E) (L : ℕ)
    (cl : ℕ → E) (cvr : ℕ → Digest) (wsr : ℕ → List E) (ch es : ℕ → E) : Prop :=
  sqCvM M cv = some (sqCvT M cv) ∧
  cl 0 = polyEval s.values (challengeOf (sqCvT M cv)) ∧ cvr 0 = sqCvT M cv ∧
    (∀ r < L, (wsr r).length = 4 ∧ RunsToM M (roundPoly 5 (cl r) (some (s.point.getD r 0)))
      (cvr r) (wsr r) (cl (r + 1), ch r) (cvr (r + 1))) ∧
    ys = (List.range L).flatMap wsr ++ (List.range 12).map es ∧
    L10Ans M (cvr L) es 12 ∧
    sqCvM M (l10cvT M (cvr L) es 12) = some (sqCvT M (l10cvT M (cvr L) es 12)) ∧
    sqCvM M (sqCvT M (l10cvT M (cvr L) es 12)) =
      some (sqCvT M (sqCvT M (l10cvT M (cvr L) es 12))) ∧
    cl L = es 0 * es 1 * es 2 * es 3 + challengeOf (sqCvT M cv) * (es 4 * es 5 * es 6 * es 7 +
      challengeOf (sqCvT M cv) * (es 8 * es 9 * es 10 * es 11)) ∧
    s'.point = [challengeOf (sqCvT M (l10cvT M (cvr L) es 12)),
      challengeOf (sqCvT M (sqCvT M (l10cvT M (cvr L) es 12)))] ++ (List.range L).map ch ∧
    s'.values = [l10Next es 0 (challengeOf (sqCvT M (l10cvT M (cvr L) es 12)))
        (challengeOf (sqCvT M (sqCvT M (l10cvT M (cvr L) es 12)))),
      l10Next es 4 (challengeOf (sqCvT M (l10cvT M (cvr L) es 12)))
        (challengeOf (sqCvT M (sqCvT M (l10cvT M (cvr L) es 12)))),
      l10Next es 8 (challengeOf (sqCvT M (l10cvT M (cvr L) es 12)))
        (challengeOf (sqCvT M (sqCvT M (l10cvT M (cvr L) es 12))))] ∧
    cv' = sqCvT M (sqCvT M (l10cvT M (cvr L) es 12))

theorem sqAllM_two_inv {pts : List E} {cv cv' : Digest} (h : sqAllM M 2 cv = some (pts, cv')) :
    sqCvM M cv = some (sqCvT M cv) ∧ sqCvM M (sqCvT M cv) = some (sqCvT M (sqCvT M cv)) ∧
      pts = [challengeOf (sqCvT M cv), challengeOf (sqCvT M (sqCvT M cv))] ∧
      cv' = sqCvT M (sqCvT M cv) := by
  obtain ⟨hs, rfl, rfl⟩ := sqAllM_T h
  exact ⟨hs 0 (by omega), hs 1 (by omega), rfl, rfl⟩

theorem sqAllM_one_inv {pts : List E} {cv cv' : Digest} (h : sqAllM M 1 cv = some (pts, cv')) :
    sqCvM M cv = some (sqCvT M cv) ∧ pts = [challengeOf (sqCvT M cv)] ∧ cv' = sqCvT M cv := by
  obtain ⟨hs, rfl, rfl⟩ := sqAllM_T h
  exact ⟨hs 0 (by omega), rfl, rfl⟩

/-- **A pair step's answered run, read back** (`pair_data`). -/
theorem pair_dataM {s s' : GkrState} {cv cv' : Digest} {ys : List E} {L : ℕ}
    (h : RunsToM M (gkrStep 2 s) cv ys s' cv') (hL : s.point.length = L) :
    ∃ (cl : ℕ → E) (cvr : ℕ → Digest) (wsr : ℕ → List E) (ch : ℕ → E) (es : ℕ → E),
      PairOkM M s s' cv cv' ys L cl cvr wsr ch es := by
  obtain ⟨ws, chs, cl, cvS, c0, c1, c2, pts, hq0, hsc, h0, h1, h2, hreq, rfl, hA, hsq, rfl⟩ :=
    RunsToM.gkrStep_inv h
  obtain ⟨a0, a1, a2, a3, rfl⟩ := list_four c0 h0
  obtain ⟨b0, b1, b2, b3, rfl⟩ := list_four c1 h1
  obtain ⟨d0, d1, d2, d3, rfl⟩ := list_four c2 h2
  obtain ⟨cl', cvr, wsr, ch, hc0, hcv0, hr, hws, hpt, hfin, hcvS⟩ :=
    RunsToM.sumcheck_inv _ _ _ _ _ _ _ hsc
  simp only [List.length_map, hL] at hr hws hpt hfin hcvS
  set l := [a0, a1, a2, a3] ++ ([b0, b1, b2, b3] ++ [d0, d1, d2, d3]) with hl
  have hes : l10cvT M cvS (fun i => l.getD i 0) 12 = obsAllT M cvS l := by
    rw [l10cvT_eq cvS l 12 (by simp [l])]; simp [l]
  have hans : L10Ans M cvS (fun i => l.getD i 0) 12 := l10Ans_of cvS hA
  obtain ⟨q1, q2, rfl, rfl⟩ := sqAllM_two_inv hsq
  refine ⟨cl', cvr, wsr, ch, fun i => l.getD i 0, hq0, hc0, hcv0, fun r hr' => ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · have := hr r (by simpa using hr')
    simp only [List.getElem_map] at this
    have hpe : s.point[r]'(by omega) = s.point.getD r 0 := by rw [List.getD_eq_getElem _ _ (by omega)]
    rw [hpe] at this
    exact ⟨by have := RunsToM.roundPoly_inv this; simpa using this, this⟩
  · rw [hws]
    congr 1
  · rw [← hcvS]; exact hans
  · rw [← hcvS, hes]; exact q1
  · rw [← hcvS, hes]; exact q2
  · rw [← hfin, hreq, polyEval_three]
    · simp only [prodE_four, l, List.cons_append, List.nil_append, List.getD_cons_zero,
        List.getD_cons_succ]
  · rw [← hcvS, hes, hpt]
  · rw [← hcvS, hes]
    simp only [List.map_cons, List.map_nil, multilinearEval_four, l10Next, List.cons.injEq,
      and_true, l, List.cons_append, List.nil_append, List.getD_cons_zero, List.getD_cons_succ]
    refine ⟨by ring, by ring, by ring⟩
  · rw [← hcvS, hes]

/-- What `odd_dataM` says of the odd step from `s` to `s'`, at the total hash, every hash
answered (`OddOk`). -/
def OddOkM (M : HashModel) (s s' : GkrState) (cv cv' : Digest) (oes : ℕ → E) : Prop :=
  sqCvM M cv = some (sqCvT M cv) ∧ L10Ans M (sqCvT M cv) oes 6 ∧
  sqCvM M (l10cvT M (sqCvT M cv) oes 6) = some (sqCvT M (l10cvT M (sqCvT M cv) oes 6)) ∧
  polyEval s.values (challengeOf (sqCvT M cv)) = oes 0 * oes 1 + challengeOf (sqCvT M cv) *
      (oes 2 * oes 3 + challengeOf (sqCvT M cv) * (oes 4 * oes 5)) ∧
    s'.point = [challengeOf (sqCvT M (l10cvT M (sqCvT M cv) oes 6))] ∧
    s'.values = [oes 0 + challengeOf (sqCvT M (l10cvT M (sqCvT M cv) oes 6)) * (oes 0 + oes 1),
      oes 2 + challengeOf (sqCvT M (l10cvT M (sqCvT M cv) oes 6)) * (oes 2 + oes 3),
      oes 4 + challengeOf (sqCvT M (l10cvT M (sqCvT M cv) oes 6)) * (oes 4 + oes 5)] ∧
    cv' = sqCvT M (l10cvT M (sqCvT M cv) oes 6)

/-- **The odd step's answered run, read back** (`odd_data`). -/
theorem odd_dataM {s s' : GkrState} {cv cv' : Digest} {ys : List E}
    (h : RunsToM M (gkrStep 1 s) cv ys s' cv') (hp : s.point = []) :
    ∃ oes : ℕ → E, ys = (List.range 6).map oes ∧ OddOkM M s s' cv cv' oes := by
  obtain ⟨ws, chs, cl, cvS, c0, c1, c2, pts, hq0, hsc, h0, h1, h2, hreq, rfl, hA, hsq, rfl⟩ :=
    RunsToM.gkrStep_inv h
  rw [hp] at hsc
  obtain ⟨cl', cvr, wsr, ch, hc0, hcv0, -, hws, hpt, hfin, hcvS⟩ :=
    RunsToM.sumcheck_inv _ _ _ _ _ _ _ hsc
  simp only [List.map_nil, List.length_nil, List.range_zero, List.flatMap_nil, List.map_nil]
    at hws hpt hfin hcvS
  subst hws hpt
  obtain rfl : cvS = sqCvT M cv := hcvS.trans hcv0
  obtain ⟨a0, a1, rfl⟩ := List.length_eq_two.mp h0
  obtain ⟨b0, b1, rfl⟩ := List.length_eq_two.mp h1
  obtain ⟨d0, d1, rfl⟩ := List.length_eq_two.mp h2
  set l := [a0, a1] ++ ([b0, b1] ++ [d0, d1]) with hl
  have hes : l10cvT M (sqCvT M cv) (fun i => l.getD i 0) 6 = obsAllT M (sqCvT M cv) l := by
    rw [l10cvT_eq (sqCvT M cv) l 6 (by simp [l])]; simp [l]
  have hans : L10Ans M (sqCvT M cv) (fun i => l.getD i 0) 6 := l10Ans_of (sqCvT M cv) hA
  obtain ⟨q1, rfl, rfl⟩ := sqAllM_one_inv hsq
  refine ⟨fun i => l.getD i 0, rfl, hq0, hans, by rw [hes]; exact q1, ?_, ?_, ?_, ?_⟩
  · rw [← hc0, ← hfin, hreq, polyEval_three]
    simp [prodE, l]
  · rw [hes]
    simp
  · rw [hes]
    simp [multilinearEval, foldPairs, l]
    refine ⟨by ring, by ring, by ring⟩
  · rw [hes]

/-! ## The trace -/

/-- **The GKR phase's answered run, inverted** (`RunsTo.gkrPhase_inv`). -/
theorem RunsToM.gkrPhase_inv {depth : ℕ} {cv cv' : Digest} {xs : List E} {r : E × List E × List E}
    (h : RunsToM M (gkrPhase depth) cv xs r cv') :
    ∃ (x0 cnt : E) (ys : List E) (s : GkrState), xs = x0 :: cnt :: ys ∧ cnt ≠ 0 ∧
      obsCvM M cv x0 = some (obsCvT M cv x0) ∧
      obsCvM M (obsCvT M cv x0) cnt = some (obsCvT M (obsCvT M cv x0) cnt) ∧
      RunsToM M (gkrLayers depth ⟨[x0, x0, cnt], []⟩) (obsCvT M (obsCvT M cv x0) cnt) ys s cv' ∧
      r = (cnt, s.point, s.values) := by
  unfold gkrPhase at h
  obtain ⟨x1, x2, r1, cv1, rfl, h1, h⟩ := RunsToM.bind_inv' h
  have h' : RunsToM M (Prog.require (r1.1 ≠ 0) >>= fun _ =>
      (pure r1 : Prog (E × List E × List E))) cv1 x2 r cv' := h
  obtain ⟨x3, x4, u, cv3, hx34, h3, hk⟩ := RunsToM.bind_inv' h'
  obtain ⟨hne, hx3, hc3⟩ := RunsToM.requireP_inv h3
  obtain ⟨hx4, hr, hc'⟩ := RunsToM.pure_inv hk
  subst hx3 hx4 hr hc3 hc'
  simp only [List.append_nil] at hx34
  subst hx34
  unfold verifyGkrGrandProducts at h1
  obtain ⟨y1, y2, x0, c1, rfl, g1, h1⟩ := RunsToM.bind_inv' h1
  obtain ⟨rfl, hc1⟩ := RunsToM.readEP_inv g1
  obtain rfl := (obsCvT_eq hc1).symm
  obtain ⟨y3, y4, cnt, c3, rfl, g3, h1⟩ := RunsToM.bind_inv' h1
  obtain ⟨rfl, hc3⟩ := RunsToM.readEP_inv g3
  obtain rfl := (obsCvT_eq hc3).symm
  obtain ⟨y5, y6, s, c5, rfl, g5, h1⟩ := RunsToM.bind_inv' h1
  obtain ⟨rfl, rfl, rfl⟩ := RunsToM.pure_inv h1
  exact ⟨x0, cnt, y5, s, by simp, hne, hc1, hc3, g5, rfl⟩

/-- **The pairs' facts** over the model, from the first state's point length (`pairs_facts`). -/
theorem pairs_factsM {m sh : ℕ} {P : ℕ → GkrState} {C : ℕ → Digest} {Y : ℕ → List E}
    (h0 : (P 0).point.length = sh)
    (hs : ∀ i < m, RunsToM M (gkrStep 2 (P i)) (C i) (Y i) (P (i + 1)) (C (i + 1))) :
    (∀ i ≤ m, (P i).point.length = gL sh i) ∧
      ∃ (CL : ℕ → ℕ → E) (CVR : ℕ → ℕ → Digest) (WSR : ℕ → ℕ → List E) (CH ES : ℕ → ℕ → E),
        ∀ i < m, PairOkM M (P i) (P (i + 1)) (C i) (C (i + 1)) (Y i) (gL sh i) (CL i) (CVR i)
          (WSR i) (CH i) (ES i) := by
  have hlen : ∀ i ≤ m, (P i).point.length = gL sh i := by
    intro i hi
    induction i with
    | zero => simpa [gL] using h0
    | succ i ih =>
      obtain ⟨_, _, _, _, _, -, -, -, -, -, -, -, -, -, hpt, -, -⟩ :=
        pair_dataM (hs i (by omega)) (ih (by omega))
      rw [hpt]; simp [gL]; omega
  refine ⟨hlen, ?_⟩
  have : ∀ i, ∃ (cl : ℕ → E) (cvr : ℕ → Digest) (wsr : ℕ → List E) (ch es : ℕ → E), i < m →
      PairOkM M (P i) (P (i + 1)) (C i) (C (i + 1)) (Y i) (gL sh i) cl cvr wsr ch es := by
    intro i
    by_cases hi : i < m
    · obtain ⟨cl, cvr, wsr, ch, es, h⟩ := pair_dataM (hs i hi) (hlen i (by omega))
      exact ⟨cl, cvr, wsr, ch, es, fun _ => h⟩
    · exact ⟨fun _ => 0, fun _ => default, fun _ => [], fun _ => 0, fun _ => 0,
        fun h => absurd h hi⟩
  choose CL CVR WSR CH ES hP using this
  exact ⟨CL, CVR, WSR, CH, ES, fun i hi => hP i hi⟩

/-- **The trace's facts over the model** for an answered run of `gkrPhase μ` from `cv` reading
`xs` to `r`, `cv'` (`GkrTrace.Ok`). -/
structure GkrTrace.OkM (M : HashModel) (T : GkrTrace) (μ : ℕ) (cv : Digest) (xs : List E)
    (r : E × List E × List E) (cv' : Digest) : Prop where
  hxs : xs = T.x0 :: T.cnt :: ((if μ % 2 = 1 then (List.range 6).map T.oes else []) ++
    (List.range (μ / 2)).flatMap T.Y)
  hcnt : T.cnt ≠ 0
  ax0 : obsCvM M cv T.x0 = some (obsCvT M cv T.x0)
  acnt : obsCvM M (obsCvT M cv T.x0) T.cnt = some (obsCvT M (obsCvT M cv T.x0) T.cnt)
  even : μ % 2 = 0 → T.P 0 = ⟨[T.x0, T.x0, T.cnt], []⟩ ∧
    T.C 0 = obsCvT M (obsCvT M cv T.x0) T.cnt
  odd : μ % 2 = 1 → OddOkM M ⟨[T.x0, T.x0, T.cnt], []⟩ (T.P 0)
    (obsCvT M (obsCvT M cv T.x0) T.cnt) (T.C 0) T.oes
  pair : ∀ i < μ / 2, PairOkM M (T.P i) (T.P (i + 1)) (T.C i) (T.C (i + 1)) (T.Y i)
    (gL (μ % 2) i) (T.CL i) (T.CVR i) (T.WSR i) (T.CH i) (T.ES i)
  hlen : ∀ i ≤ μ / 2, (T.P i).point.length = gL (μ % 2) i
  hr : r = (T.cnt, (T.P (μ / 2)).point, (T.P (μ / 2)).values)
  hcv : cv' = T.C (μ / 2)

/-- **An answered run of the GKR phase has an honest trace** (`exists_trace`). -/
theorem exists_traceM {μ : ℕ} {cv cv' : Digest} {xs : List E} {r : E × List E × List E}
    (h : RunsToM M (gkrPhase μ) cv xs r cv') : ∃ T : GkrTrace, T.OkM M μ cv xs r cv' := by
  obtain ⟨x0, cnt, ys, s, rfl, hne, ha0, hac, hL, rfl⟩ := RunsToM.gkrPhase_inv h
  rcases Nat.mod_two_eq_zero_or_one μ with hsh | hsh
  · have hμ : μ = 2 * (μ / 2) := by omega
    rw [hμ, gkrLayers_even] at hL
    obtain ⟨P, C, Y, h0, hc0, hs, hys, rfl, rfl⟩ := RunsToM.gkrPairs_inv _ _ _ _ _ _ hL
    obtain ⟨hlen, CL, CVR, WSR, CH, ES, hP⟩ := pairs_factsM (sh := 0) (by rw [h0]; rfl) hs
    refine ⟨⟨x0, cnt, fun _ => 0, P, C, Y, CL, CVR, WSR, CH, ES⟩, ⟨?_, hne, ha0, hac,
      fun _ => ⟨h0, hc0⟩, fun h => by omega, ?_, ?_, rfl, rfl⟩⟩
    · simp only [hsh, ite_neg' (by omega : ¬ (0 = 1)), List.nil_append, hys]
    · rw [hsh]; exact hP
    · rw [hsh]; exact hlen
  · have hμ : μ = 2 * (μ / 2) + 1 := by omega
    rw [hμ, gkrLayers_odd] at hL
    obtain ⟨y1, y2, s1, cv1, rfl, h1, hL2⟩ := RunsToM.bind_inv' hL
    obtain ⟨oes, rfl, hodd⟩ := odd_dataM h1 rfl
    obtain ⟨P, C, Y, h0, hc0, hs, hys, rfl, rfl⟩ := RunsToM.gkrPairs_inv _ _ _ _ _ _ hL2
    obtain ⟨hlen, CL, CVR, WSR, CH, ES, hP⟩ :=
      pairs_factsM (sh := 1) (by rw [h0, hodd.2.2.2.2.1]; rfl) hs
    refine ⟨⟨x0, cnt, oes, P, C, Y, CL, CVR, WSR, CH, ES⟩, ⟨?_, hne, ha0, hac, fun h => by omega,
      fun _ => ?_, ?_, ?_, rfl, rfl⟩⟩
    · simp only [hsh, hys, ↓reduceIte]
    · show OddOkM M _ (P 0) _ (C 0) oes
      rw [h0, hc0]; exact hodd
    · rw [hsh]; exact hP
    · rw [hsh]; exact hlen

end
end LeanVM.Guest.B1.VerifySub
