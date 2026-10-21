/-
  LeanVM.Guest.B1.Comp.Whir.OsDataC

  The tail of the stacked opening's run over a completeness model: its fold rounds and its
  closing squeeze, answered.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.OsBody
public import LeanVM.Guest.B1.Whir.OsData

/-!
# The tail's data, answered (TRIAGE #36)

`os_tail_invC`, `os_tailOpen_invC`: `os_tail_inv`, `os_tailOpen_inv` over a total hash `Ht`, the
tail's run answered by the model: its fold rounds' run answered (`AnsRun`) and its closing squeeze
answered, what `osBody_completeC` takes of the tail (`hAT`, `asqT`). `AnsRun.bind_of` assembles an
answered bind from its pieces.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

variable {M : HashModel} {Ht : Bytes → Digest}

/-- **An answered bind from its pieces** (the converse of `AnsRun.bind_inv`). -/
theorem AnsRun.bind_of {H : Bytes → Option Digest} {α β : Type} :
    ∀ (p : Prog α) (f : α → Prog β) {s : St} {a : α} {s' : St},
      AnsRun H Ht p s → RunsW Ht p s a s' → AnsRun H Ht (f a) s' → AnsRun H Ht (p >>= f) s
  | .ret a0, f, s, a, s', _, hr, h2 => by
    unfold RunsW at hr
    simp only [runW, Compile.run, pure, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact h2
  | .fail, f, s, a, s', _, hr, _ => by cases hr
  | .read k, f, ⟨cv, stream, os, roots⟩, a, s', h1, hr, h2 => by
    rcases stream with _ | ⟨x, xs⟩
    · cases hr
    · exact ⟨h1.1, AnsRun.bind_of (k x) f h1.2 hr h2⟩
  | .sample k, f, s, a, s', h1, hr, h2 => ⟨h1.1, AnsRun.bind_of _ f h1.2 hr h2⟩
  | .grind bits k, f, ⟨cv, stream, os, roots⟩, a, s', h1, hr, h2 => by
    rcases stream with _ | ⟨n, xs⟩
    · cases hr
    · obtain ⟨g1, g2, g3, g4⟩ := h1
      unfold RunsW at hr
      simp only [runW, Compile.run, absorbBlock, bind, pure] at hr
      by_cases hp : powOk bits n (Ht (digestBytes (Ht (digestBytes cv ++ blockOf 0 3)) ++ blockOf n 4)) = true
      · simp only [hp, ↓reduceIte] at hr
        exact ⟨g1, g2, g3, AnsRun.bind_of k f g4 hr h2⟩
      · simp [hp] at hr
  | .commit hh ww k, f, ⟨cv, stream, os, roots⟩, a, s', h1, hr, h2 => by
    match stream, h1, hr with
    | [], _, hr => cases hr
    | [_], _, hr => cases hr
    | x0 :: x1 :: xs, h1, hr =>
      obtain ⟨g1, g2, g3⟩ := h1
      unfold RunsW at hr
      simp only [runW, Compile.run, absorbBlock, bind] at hr
      split at hr
      · rename_i root hroot
        refine ⟨g1, g2, fun root' hr' => ?_⟩
        rw [hroot] at hr'
        obtain rfl := Option.some.inj hr'
        exact AnsRun.bind_of k f (g3 root hroot) hr h2
      · cases hr
  | .query i ps k, f, ⟨cv, stream, os, roots⟩, a, s', h1, hr, h2 => by
    unfold RunsW at hr
    simp only [runW, Compile.run] at hr
    rw [prog_bind_eq]
    simp only [AnsRun, Prog.bind] at h1 ⊢
    split at hr
    · cases hr
    · rename_i root hh ww hroot
      rw [hroot] at h1 ⊢
      obtain ⟨g1, g2⟩ := h1
      dsimp only [bind] at hr
      split at hr
      · rename_i rows rest hrr
        refine ⟨g1, fun rows' rest' h' => ?_⟩
        rw [hrr] at h'
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h')
        exact AnsRun.bind_of _ f (g2 rows rest hrr) hr h2
      · cases hr

/-- **The tail rounds, inverted, answered** (`os_tail_invW`): `n + 1` tail rounds answered are `n`
fold rounds answered, then the closing squeeze answered. -/
theorem os_tail_invC : ∀ (n : ℕ) (t : E) (q : List E) (st : St) (r : List E × E) (st' : St),
    RunsW Ht (tailRounds (n + 1) t q) st r st' → AnsRun M.H Ht (tailRounds (n + 1) t q) st →
    ∀ (w : WhirState) (lf : List E), w.quad = q →
      ∃ (w1 : WhirState) (chs : List E) (st1 : St), RunsW Ht (foldRounds n w lf) st (w1, lf ++ chs) st1 ∧
        AnsRun M.H Ht (foldRounds n w lf) st ∧ sqCvM M st1.cv = some (sqCvW Ht st1.cv) ∧
        r = (chs ++ [challengeOf (sqCvW Ht st1.cv)], polyEval w1.quad (challengeOf (sqCvW Ht st1.cv))) ∧
        st' = { st1 with cv := sqCvW Ht st1.cv } := by
  intro n
  induction n with
  | zero =>
    intro t q st r st' h hA w lf hq
    simp only [tailRounds] at h hA
    obtain ⟨ch, s1, h1, h2⟩ := os_inv_bindW h
    obtain ⟨aS, -⟩ := AnsRun.bind_inv _ _ hA h1
    obtain ⟨rfl, rfl⟩ := os_inv_sampleEW h1
    simp only [↓reduceIte] at h2
    obtain ⟨rfl, rfl⟩ := os_inv_pureW h2
    refine ⟨w, [], st, ?_, trivial, ansRun_sampleE aS, by rw [List.nil_append, hq], rfl⟩
    rw [List.append_nil]
    exact RunsW.ret (w, lf) st
  | succ n ih =>
    intro t q st r st' h hA w lf hq
    rw [tailRounds] at h hA
    obtain ⟨ch, s1, h1, h2⟩ := os_inv_bindW h
    obtain ⟨aS, hA2⟩ := AnsRun.bind_inv _ _ hA h1
    obtain ⟨rfl, rfl⟩ := os_inv_sampleEW h1
    rw [ite_neg' (by omega)] at h2 hA2
    obtain ⟨q', s2, h3, h4⟩ := os_inv_bindW h2
    obtain ⟨aR, hA3⟩ := AnsRun.bind_inv _ _ hA2 h3
    obtain ⟨⟨rest, tg⟩, s3, h5, h6⟩ := os_inv_bindW h4
    obtain ⟨aT, -⟩ := AnsRun.bind_inv _ _ hA3 h5
    obtain ⟨rfl, rfl⟩ := os_inv_pureW h6
    obtain ⟨c0, c2, rr, hs, rfl, rfl⟩ := os_inv_roundPoly3W h3
    obtain ⟨w1, chs, st1, hr1, hA1, hsq1, he, hs'⟩ := ih _ _ _ _ _ h5 aT
      ⟨polyEval w.quad (challengeOf (sqCvW Ht st.cv)), [c0, polyEval w.quad (challengeOf (sqCvW Ht st.cv)) + c2, c2],
        w.folds ++ [challengeOf (sqCvW Ht st.cv)], w.glued⟩ (lf ++ [challengeOf (sqCvW Ht st.cv)]) (by rw [hq])
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hR3 : RunsW Ht (sumcheckRoundPoly 3 (polyEval w.quad (challengeOf (sqCvW Ht st.cv))) none)
        { st with cv := sqCvW Ht st.cv } [c0, polyEval w.quad (challengeOf (sqCvW Ht st.cv)) + c2, c2]
        ⟨obsCvW Ht (obsCvW Ht (sqCvW Ht st.cv) c0) c2, rr, st.openings, st.roots⟩ := by
      have := os_runs_roundPoly3W (Ht := Ht) (sqCvW Ht st.cv) (polyEval w.quad (challengeOf (sqCvW Ht st.cv))) c0 c2 rr
        st.openings st.roots
      simp only at hs
      rw [← hs] at this
      exact this
    have hStep : RunsW Ht (foldStep w.quad) st (challengeOf (sqCvW Ht st.cv), polyEval w.quad (challengeOf (sqCvW Ht st.cv)),
        [c0, polyEval w.quad (challengeOf (sqCvW Ht st.cv)) + c2, c2])
        ⟨obsCvW Ht (obsCvW Ht (sqCvW Ht st.cv) c0) c2, rr, st.openings, st.roots⟩ := by
      simp only [foldStep]
      exact RunsW.bind (os_runs_sampleEW _) (RunsW.bind hR3 (RunsW.ret _ _))
    have aStep : AnsRun M.H Ht (foldStep w.quad) st := by
      simp only [foldStep]
      exact AnsRun.bind_of _ _ aS (os_runs_sampleEW _) (AnsRun.bind_of _ _ (by rw [hq]; exact aR) hR3 trivial)
    refine ⟨w1, challengeOf (sqCvW Ht st.cv) :: chs, st1, ?_, ?_, hsq1, by rw [List.cons_append], hs'⟩
    · rw [foldRounds_succ]
      refine RunsW.bind hStep ?_
      rw [List.append_assoc, List.singleton_append] at hr1
      exact hr1
    · rw [foldRounds_succ]
      exact AnsRun.bind_of _ _ aStep hStep hA1

/-- **The tail, inverted, answered** (`os_tailOpen_inv`). -/
theorem os_tailOpen_invC {ml lane : ℕ} (hml : 1 ≤ ml) {s : WhirState} {res : List E} {st : St} {e : WhirEnd}
    {st' : St} (h : RunsW Ht (osTailOpen ml lane s res) st e st') (hA : AnsRun M.H Ht (osTailOpen ml lane s res) st) :
    ∃ (w1 : WhirState) (chs : List E) (st1 : St),
      RunsW Ht (foldRounds (ml - 1) ⟨s.target, s.quad, [], []⟩ []) st (w1, chs) st1 ∧
      AnsRun M.H Ht (foldRounds (ml - 1) ⟨s.target, s.quad, [], []⟩ []) st ∧
      sqCvM M st1.cv = some (sqCvW Ht st1.cv) ∧
      e = ⟨(s.folds ++ (chs ++ [challengeOf (sqCvW Ht st1.cv)])).drop lane ++
          (s.folds ++ (chs ++ [challengeOf (sqCvW Ht st1.cv)])).take lane,
        s.glued.foldl (fun w c ↦ w + c.scalar * c.weightAt (s.folds.drop c.foldStart ++
          (chs ++ [challengeOf (sqCvW Ht st1.cv)]))) 0,
        multilinearEval res (chs ++ [challengeOf (sqCvW Ht st1.cv)]),
        polyEval w1.quad (challengeOf (sqCvW Ht st1.cv))⟩ ∧
      st' = { st1 with cv := sqCvW Ht st1.cv } := by
  unfold osTailOpen at h hA
  obtain ⟨⟨tf, tg⟩, st2, h1, h2⟩ := os_inv_bindW h
  obtain ⟨aT, -⟩ := AnsRun.bind_inv _ _ hA h1
  obtain ⟨rfl, rfl⟩ := os_inv_retW h2
  rw [show ml = ml - 1 + 1 by omega] at h1 aT
  obtain ⟨w1, chs, st1, hr, hA1, hsq, he, hs⟩ := os_tail_invC (ml - 1) _ _ _ _ _ h1 aT ⟨s.target, s.quad, [], []⟩ [] rfl
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨w1, chs, st1, by simpa using hr, hA1, hsq, rfl, hs⟩

end
end LeanVM.Guest.B1
