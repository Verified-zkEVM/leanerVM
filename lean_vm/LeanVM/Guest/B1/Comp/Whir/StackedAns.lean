/-
  LeanVM.Guest.B1.Comp.Whir.StackedAns

  What a completeness model answers along the stacked opening's run: each step's hash, in closed
  form, from an answered run.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.StackedDataW

/-!
# The stacked opening's answered hashes (TRIAGE #36)

An answered run (`AnsRun M.H Ht p s`, `Comp/Whir/RunW.lean`) names its hashes step by step. Read
along the run's pieces (`AnsRun.bind_inv` at the pieces' runs over `Ht`), they are the closed-form
facts the guest's `BLAKE2S` rows and its callees' meanings need: an absorb (`ansRun_readE`), a
squeeze (`ansRun_sampleE`), `n` absorbs and squeezes (`ansRun_readN`, `ansRun_sampleN`), a round's
two reads (`ansRun_roundPoly3`), a commitment's two reads (`ansRun_commitP`), the proof of work's
three hashes (`ansRun_grindP`), an opening (`ansRun_queryP`), the query positions' squeezes
(`ansRun_sampleQueries`), a fold round's run under the model (`ansRun_foldStep`), and a level's
queries (`os_lq_ansC`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

variable {M : HashModel} {Ht : Bytes → Digest}

/-! ## Steps -/

theorem ansRun_readE {cv : Digest} {x : E} {rest : List E} {os : List Opening}
    {roots : List (Digest × ℕ × ℕ)} (h : AnsRun M.H Ht Prog.readE ⟨cv, x :: rest, os, roots⟩) :
    obsCvM M cv x = some (obsCvW Ht cv x) := h.1

theorem ansRun_sampleE {s : St} (h : AnsRun M.H Ht Prog.sampleE s) : sqCvM M s.cv = some (sqCvW Ht s.cv) := h.1

theorem ansRun_commitP {hh ww : ℕ} {cv : Digest} {x0 x1 : E} {rest : List E} {os : List Opening}
    {roots : List (Digest × ℕ × ℕ)} (h : AnsRun M.H Ht (Prog.commitP hh ww) ⟨cv, x0 :: x1 :: rest, os, roots⟩) :
    obsCvM M cv x0 = some (obsCvW Ht cv x0) ∧
      obsCvM M (obsCvW Ht cv x0) x1 = some (obsCvW Ht (obsCvW Ht cv x0) x1) := ⟨h.1, h.2.1⟩

theorem ansRun_grindP {b : ℕ} {cv : Digest} {n : E} {rest : List E} {os : List Opening}
    {roots : List (Digest × ℕ × ℕ)} (h : AnsRun M.H Ht (Prog.grindP b) ⟨cv, n :: rest, os, roots⟩) :
    M.H (digestBytes cv ++ blockOf 0 3) = some (Ht (digestBytes cv ++ blockOf 0 3)) ∧
      M.H (digestBytes (Ht (digestBytes cv ++ blockOf 0 3)) ++ blockOf n 4) = some (gcDigestW Ht cv n) ∧
      M.H (digestBytes cv ++ blockOf n 4) = some (absorbCvW Ht cv n 4) := ⟨h.1, h.2.1, h.2.2.1⟩

theorem ansRun_queryP {i : ℕ} {ps : List ℕ} {s : St} {root : Digest} {hh ww : ℕ}
    (hr : s.roots[i]? = some (root, hh, ww)) (h : AnsRun M.H Ht (Prog.queryP i ps) s) :
    OpenAns M.H Ht root hh ww ps s.openings := by
  obtain ⟨cv, xs, os, roots⟩ := s
  simp only [Prog.queryP, AnsRun] at h hr
  rw [hr] at h
  exact h.1

theorem ansRun_readN : ∀ {n : ℕ} {s s' : St} {ys : List E}, RunsW Ht (Prog.readN n) s ys s' →
    AnsRun M.H Ht (Prog.readN n) s → obsAllM M s.cv ys = some (obsAllW Ht s.cv ys)
  | 0, s, s', ys, h, _ => by
    obtain ⟨rfl, rfl⟩ := os_inv_retW h
    rfl
  | n + 1, s, s', ys, h, hA => by
    unfold Prog.readN at h hA
    obtain ⟨x, s1, h1, h2⟩ := os_inv_bindW h
    obtain ⟨a1, hA2⟩ := AnsRun.bind_inv _ _ hA h1
    obtain ⟨zs, s2, h3, h4⟩ := os_inv_bindW h2
    obtain ⟨a3, -⟩ := AnsRun.bind_inv _ _ hA2 h3
    obtain ⟨rfl, rfl⟩ := os_inv_pureW h4
    obtain ⟨r1, hs1, rfl⟩ := os_inv_readEW h1
    obtain ⟨cv, xs, os, roots⟩ := s
    simp only at hs1
    subst hs1
    have e1 := ansRun_readE a1
    have e2 := ansRun_readN h3 a3
    simp only [obsAllM, e1, Option.bind_some]
    exact e2

theorem ansRun_sampleN : ∀ {n : ℕ} {s : St}, AnsRun M.H Ht (Prog.sampleN n) s →
    sqAllM M n s.cv = some (sqAllW Ht n s.cv)
  | 0, s, _ => rfl
  | n + 1, s, hA => by
    unfold Prog.sampleN at hA
    obtain ⟨a1, hA2⟩ := AnsRun.bind_inv _ _ hA (os_runs_sampleEW (Ht := Ht) s)
    obtain ⟨a3, -⟩ := AnsRun.bind_inv _ _ hA2
      ((runsToW_sampleN (Ht := Ht) n (sqCvW Ht s.cv)).runs s.stream s.openings s.roots)
    have e1 := ansRun_sampleE a1
    have e2 := ansRun_sampleN (s := { s with cv := sqCvW Ht s.cv }) a3
    simp only [sqAllM, e1, Option.bind_some, e2, Option.map_some]
    rfl

theorem ansRun_roundPoly3 {claim : E} {cv : Digest} {c0 c2 : E} {rest : List E} {os : List Opening}
    {roots : List (Digest × ℕ × ℕ)}
    (h : AnsRun M.H Ht (sumcheckRoundPoly 3 claim none) ⟨cv, c0 :: c2 :: rest, os, roots⟩) :
    obsCvM M cv c0 = some (obsCvW Ht cv c0) ∧
      obsCvM M (obsCvW Ht cv c0) c2 = some (obsCvW Ht (obsCvW Ht cv c0) c2) := by
  simp only [sumcheckRoundPoly] at h
  obtain ⟨a1, h2⟩ := AnsRun.bind_inv _ _ h (os_runs_readEW (Ht := Ht) cv c0 (c2 :: rest) os roots)
  obtain ⟨a2, -⟩ := AnsRun.bind_inv _ _ h2
    ((runsToW_readN (Ht := Ht) (obsCvW Ht cv c0) [c2]).runs rest os roots)
  have e2 := ansRun_readN ((runsToW_readN (Ht := Ht) (obsCvW Ht cv c0) [c2]).runs rest os roots) a2
  simp only [obsAllM, Option.bind_eq_some_iff] at e2
  obtain ⟨d, hd, hd2⟩ := e2
  refine ⟨ansRun_readE a1, ?_⟩
  rw [hd, hd2]
  rfl

/-- **A fold round the model answers runs under the model** (`foldStep`, V:1678), for
`opening_fold`'s meaning (`MeaningOpeningFoldComp`). -/
theorem ansRun_foldStep {q : List E} {cv : Digest} {d0 d2 : E} {rest : List E} {os : List Opening}
    {roots : List (Digest × ℕ × ℕ)} (h : AnsRun M.H Ht (foldStep q) ⟨cv, d0 :: d2 :: rest, os, roots⟩) :
    RunsToM M (foldStep q) cv [d0, d2]
      (challengeOf (sqCvW Ht cv), polyEval q (challengeOf (sqCvW Ht cv)),
        [d0, polyEval q (challengeOf (sqCvW Ht cv)) + d2, d2])
      (obsAllW Ht (sqCvW Ht cv) [d0, d2]) := by
  simp only [foldStep] at h
  obtain ⟨a1, h2⟩ := AnsRun.bind_inv _ _ h (os_runs_sampleEW (Ht := Ht) ⟨cv, d0 :: d2 :: rest, os, roots⟩)
  obtain ⟨a2, -⟩ := AnsRun.bind_inv _ _ h2
    (os_runs_roundPoly3W (Ht := Ht) (sqCvW Ht cv) (polyEval q (challengeOf (sqCvW Ht cv))) d0 d2 rest os roots)
  have e1 : sqCvM M cv = some (sqCvW Ht cv) := ansRun_sampleE a1
  obtain ⟨e2, e3⟩ := ansRun_roundPoly3 a2
  have hr := (runsToM_sampleE e1).bind (f := fun ch => do
      let quad ← sumcheckRoundPoly 3 (polyEval q ch) none
      pure (ch, polyEval q ch, quad))
    ((runsToM_roundPoly3 (polyEval q (challengeOf (sqCvW Ht cv))) d0 d2 e2 e3).bind
      (f := fun quad => (pure (challengeOf (sqCvW Ht cv), polyEval q (challengeOf (sqCvW Ht cv)), quad) :
        Prog _)) (runsToM_ret _ _))
  exact hr

/-! ## The query positions' squeezes -/

theorem ansRun_sampleQueriesAux (depth : ℕ) (hd : 0 < 192 / depth) :
    ∀ (k fuel rem : ℕ) (s : St), rem ≤ k * (192 / depth) → (k - 1) * (192 / depth) < rem ∨ k = 0 →
      k ≤ fuel → AnsRun M.H Ht (sampleQueriesAux depth fuel rem) s →
      sqAllM M k s.cv = some (sqAllW Ht k s.cv) := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _ _; rfl
  | succ k IH =>
    intro fuel rem s h1 h2 h3 hA
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hrem : rem ≠ 0 := by rcases h2 with h2 | h2 <;> omega
    have hn : min (192 / depth) rem = if k = 0 then rem else 192 / depth := by
      generalize 192 / depth = per at *
      split
      · subst_vars; simp at h1; omega
      · rcases h2 with h2 | h2
        · have : per ≤ k * per := Nat.le_mul_of_pos_left per (by omega)
          rw [show k + 1 - 1 = k by omega] at h2
          omega
        · omega
    have hr1 : rem - min (192 / depth) rem ≤ k * (192 / depth) := by
      rw [hn]
      generalize 192 / depth = per at *
      split
      · omega
      · rw [Nat.add_mul, Nat.one_mul] at h1; omega
    have hr2 : (k - 1) * (192 / depth) < rem - min (192 / depth) rem ∨ k = 0 := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · exact Or.inr hk
      · left
        rw [hn, ite_neg' (by omega)]
        generalize 192 / depth = per at *
        rcases h2 with h2 | h2
        · rw [show k + 1 - 1 = k by omega] at h2
          have : (k - 1) * per + per = k * per := by
            rw [← Nat.succ_mul, show (k - 1).succ = k by omega]
          omega
        · omega
    unfold sampleQueriesAux at hA
    simp only [hrem, ↓reduceIte] at hA
    obtain ⟨a1, hA2⟩ := AnsRun.bind_inv _ _ hA (os_runs_sampleEW (Ht := Ht) s)
    have hrun := (runsTo_sampleQueriesAuxW (Ht := Ht) depth hd k f (rem - min (192 / depth) rem) (sqCvW Ht s.cv)
      hr1 hr2 (by omega)).runs s.stream s.openings s.roots
    obtain ⟨a3, -⟩ := AnsRun.bind_inv _ _ hA2 hrun
    have e1 := ansRun_sampleE a1
    have e2 := IH f (rem - min (192 / depth) rem) { s with cv := sqCvW Ht s.cv } hr1 hr2 (by omega) a3
    simp only [sqAllM, e1, Option.bind_some, e2, Option.map_some]
    rfl

/-- **The query positions' squeezes are answered**: `sampleQueries` over `nq` positions in `k`
samples, answered, answers `k` squeezes. -/
theorem ansRun_sampleQueries {depth nq k : ℕ} (hd : 0 < 192 / depth) (h1 : nq ≤ k * (192 / depth))
    (h2 : (k - 1) * (192 / depth) < nq ∨ k = 0) (hk : k ≤ nq) {s : St}
    (hA : AnsRun M.H Ht (sampleQueries depth nq) s) : sqAllM M k s.cv = some (sqAllW Ht k s.cv) :=
  ansRun_sampleQueriesAux depth hd k nq nq s h1 h2 hk hA

/-! ## A level's queries -/

/-- **A level's queries, answered** (`os_lq_invW`): the nonce's three hashes, the positions' squeezes,
`lam`'s squeeze, the openings and the intro's two reads, each answered by the model. -/
theorem os_lq_ansC {ml idx nsq depth nq : ℕ} {L : Whir.Level} {lf : List E} {w1 : WhirState}
    {pend : List (E × List E × (List E → E))} (hdq : ml + L.logInvRate = depth) (hnq : L.queries = nq)
    (hper : 0 < 192 / depth) (hs1 : nq ≤ nsq * (192 / depth))
    (hs2 : (nsq - 1) * (192 / depth) < nq ∨ nsq = 0) (hs3 : nsq ≤ nq)
    {cv2 : Digest} {xs : List E} {p2 : ℕ} {op : List Opening} {ro : List (Digest × ℕ × ℕ)} {w' : WhirState}
    {s3 : St} (h : RunsW Ht (osLevelQueries ml idx L lf w1 pend) ⟨cv2, xs.drop p2, op, ro⟩ w' s3)
    (hA : AnsRun M.H Ht (osLevelQueries ml idx L lf w1 pend) ⟨cv2, xs.drop p2, op, ro⟩) :
    let n := xs.getD p2 0
    let cv3 := absorbCvW Ht cv2 n 4
    let qs := (List.range nq).map (osPosOfW Ht depth cv3)
    let cv4 := (sqAllW Ht nsq cv3).2
    let c0 := xs.getD (p2 + 1) 0
    let c2 := xs.getD (p2 + 2) 0
    (M.H (digestBytes cv2 ++ blockOf 0 3) = some (Ht (digestBytes cv2 ++ blockOf 0 3)) ∧
      M.H (digestBytes (Ht (digestBytes cv2 ++ blockOf 0 3)) ++ blockOf n 4) = some (gcDigestW Ht cv2 n) ∧
      M.H (digestBytes cv2 ++ blockOf n 4) = some cv3) ∧
    sqAllM M nsq cv3 = some (sqAllW Ht nsq cv3) ∧ sqCvM M cv4 = some (sqCvW Ht cv4) ∧
    (∀ rt hh ww, ro[idx]? = some (rt, hh, ww) → OpenAns M.H Ht rt hh ww qs op) ∧
    obsCvM M (sqCvW Ht cv4) c0 = some (obsCvW Ht (sqCvW Ht cv4) c0) ∧
    obsCvM M (obsCvW Ht (sqCvW Ht cv4) c0) c2 = some (obsCvW Ht (obsCvW Ht (sqCvW Ht cv4) c0) c2) := by
  subst hdq hnq
  intro n cv3 qs cv4 c0 c2
  simp only [osLevelQueries] at h hA
  obtain ⟨u, sA, hAr, h1⟩ := os_inv_bindW h
  obtain ⟨aA, hA1⟩ := AnsRun.bind_inv _ _ hA hAr
  obtain ⟨n', rA, hsA, hpow, rfl⟩ := os_inv_grindPW hAr
  simp only at hsA
  obtain ⟨hn, hrA⟩ := os_drop_cons hsA
  subst hrA hn
  rw [hsA] at aA
  obtain ⟨g1, g2, g3⟩ := ansRun_grindP aA
  obtain ⟨qs', sB, hB, h2⟩ := os_inv_bindW h1
  obtain ⟨aB, hA2⟩ := AnsRun.bind_inv _ _ hA1 hB
  have eB := ansRun_sampleQueries hper hs1 hs2 hs3 aB
  obtain ⟨rfl, rfl⟩ := os_runs_detW (rest := xs.drop (p2 + 1)) hB
    (os_runsTo_sampleQueriesW hper hs1 hs2 hs3 _) rfl
  obtain ⟨lam', sC, hC, h3⟩ := os_inv_bindW h2
  obtain ⟨aC, hA3⟩ := AnsRun.bind_inv _ _ hA2 hC
  have eC := ansRun_sampleE aC
  obtain ⟨rfl, rfl⟩ := os_inv_sampleEW hC
  obtain ⟨words, sD, hD, h4⟩ := os_inv_bindW h3
  obtain ⟨aD, hA4⟩ := AnsRun.bind_inv _ _ hA3 hD
  obtain ⟨rt, hh, ww, osq, hr, hoa, rfl⟩ := os_inv_queryPW hD
  obtain ⟨intro, sE, hE, h5⟩ := os_inv_bindW h4
  obtain ⟨aE, -⟩ := AnsRun.bind_inv _ _ hA4 hE
  obtain ⟨d0, d2, rE, hsE, rfl, rfl⟩ := os_inv_roundPoly3W hE
  simp only at hsE
  obtain ⟨hd0, hd2, hrE⟩ := os_drop_cons2 hsE
  rw [hsE] at aE
  obtain ⟨e1, e2⟩ := ansRun_roundPoly3 aE
  refine ⟨⟨g1, g2, g3⟩, eB, eC, fun rt' hh' ww' hr' => ?_, ?_, ?_⟩
  · have hq := ansRun_queryP hr' aD
    exact hq
  · show obsCvM M (sqCvW Ht cv4) (xs.getD (p2 + 1) 0) = some (obsCvW Ht (sqCvW Ht cv4) (xs.getD (p2 + 1) 0))
    rw [hd0]; exact e1
  · show obsCvM M (obsCvW Ht (sqCvW Ht cv4) (xs.getD (p2 + 1) 0)) (xs.getD (p2 + 2) 0) =
      some (obsCvW Ht (obsCvW Ht (sqCvW Ht cv4) (xs.getD (p2 + 1) 0)) (xs.getD (p2 + 2) 0))
    rw [show p2 + 1 + 1 = p2 + 2 by ring] at hd2
    rw [hd0, hd2]; exact e2

end
end LeanVM.Guest.B1
