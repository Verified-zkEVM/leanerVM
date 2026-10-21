/-
  LeanVM.Guest.B1.Comp.Whir.StackedInvW

  The stacked opening's runs inverted over a total hash: `Whir/StackedInv.lean`, the query steps
  (`OsSteps`), the lengths (`OpenLen`), the runs of the pieces and the query positions
  (`StackedRun`), the fold rounds (`StackedC1`), all over `Ht`.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.RunW
public import LeanVM.Guest.B1.Whir.OpenLen

/-!
# The stacked opening's runs over a total hash (TRIAGE #36)

The deployed inversions of the stacked opening's run (`os_inv_*`, `os_queriesOf_*`,
`os_*_len`, `os_runs_*`, `os_runsTo_sampleQueries`, `os_foldRounds_folds`, `os_runs_foldStep`)
read nothing of BLAKE2s but its chain states; over a total hash `Ht` they are the same proofs at
`RunsW Ht`, `obsCvW Ht`, `sqCvW Ht`, … (`…W`), and at `blake2sBytes` the deployed lemmas.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

variable {Ht : Bytes → Digest}

theorem RunsToW.of_eq {α : Type} {p : Prog α} {cv : Digest} {xs xs' : List E} {a a' : α}
    {c c' : Digest} (h : RunsToW Ht p cv xs a c) (hx : xs = xs') (ha : a = a') (hc : c = c') :
    RunsToW Ht p cv xs' a' c' := by
  subst hx ha hc; exact h

theorem inv_grind_consW {α : Type} (b : ℕ) (k : Prog α) (cv : Digest) (n : E) (xs : List E)
    (os : List Opening) (roots : List (Digest × ℕ × ℕ)) :
    runW Ht (.grind b k) ⟨cv, n :: xs, os, roots⟩ =
      if powOk b n (Ht (digestBytes (Ht (digestBytes cv ++ blockOf 0 3)) ++ blockOf n 4)) then
        runW Ht k ⟨Ht (digestBytes cv ++ blockOf n 4), xs, os, roots⟩
      else none := rfl

theorem os_inv_bindW {α β : Type} {p : Prog α} {f : α → Prog β} {s s'' : St} {b : β}
    (h : RunsW Ht (p >>= f) s b s'') : ∃ a s', RunsW Ht p s a s' ∧ RunsW Ht (f a) s' b s'' := RunsW.bind_inv h

theorem os_inv_retW {α : Type} {a b : α} {s s' : St} (h : RunsW Ht (Prog.ret a) s b s') : b = a ∧ s' = s := by
  unfold RunsW at h
  simp only [runW, Compile.run, pure, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem os_inv_pureW {α : Type} {a b : α} {s s' : St} (h : RunsW Ht (pure a : Prog α) s b s') : b = a ∧ s' = s :=
  os_inv_retW h

/-- A run is the forward run it is known to be. -/
theorem os_runs_detW {α : Type} {p : Prog α} {s s' : St} {a a0 : α} {cv0 : Digest} {ys rest : List E}
    (h : RunsW Ht p s a s') (hf : RunsToW Ht p s.cv ys a0 cv0) (hs : s.stream = ys ++ rest) :
    a = a0 ∧ s' = ⟨cv0, rest, s.openings, s.roots⟩ := by
  obtain ⟨cv, xs, os, roots⟩ := s
  simp only at hs
  subst hs
  have := hf rest os roots
  unfold RunsW at h
  rw [this] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem os_inv_sampleEW {s s' : St} {x : E} (h : RunsW Ht Prog.sampleE s x s') :
    x = challengeOf (sqCvW Ht s.cv) ∧ s' = ⟨sqCvW Ht s.cv, s.stream, s.openings, s.roots⟩ :=
  os_runs_detW (rest := s.stream) h (runsToW_sampleE s.cv) rfl

theorem os_inv_readEW {s s' : St} {x : E} (h : RunsW Ht Prog.readE s x s') :
    ∃ rest, s.stream = x :: rest ∧ s' = ⟨obsCvW Ht s.cv x, rest, s.openings, s.roots⟩ := by
  obtain ⟨cv, xs, os, roots⟩ := s
  match xs, h with
  | [], h => cases h
  | y :: ys, h =>
    obtain ⟨rfl, rfl⟩ := os_runs_detW (rest := ys) h (runsToW_readE cv y) rfl
    exact ⟨ys, rfl, rfl⟩

theorem os_inv_readNW : ∀ {n : ℕ} {s s' : St} {ys : List E}, RunsW Ht (Prog.readN n) s ys s' →
    ys.length = n ∧ ∃ rest, s.stream = ys ++ rest ∧ s' = ⟨obsAllW Ht s.cv ys, rest, s.openings, s.roots⟩
  | 0, s, s', ys, h => by
    obtain ⟨rfl, rfl⟩ := os_inv_retW h
    exact ⟨rfl, _, (List.nil_append _).symm, rfl⟩
  | n + 1, s, s', ys, h => by
    unfold Prog.readN at h
    obtain ⟨x, s1, h1, h2⟩ := os_inv_bindW h
    obtain ⟨zs, s2, h3, h4⟩ := os_inv_bindW h2
    obtain ⟨rfl, rfl⟩ := os_inv_pureW h4
    obtain ⟨r1, hs1, rfl⟩ := os_inv_readEW h1
    obtain ⟨hl, r2, hs2, rfl⟩ := os_inv_readNW h3
    refine ⟨by simp [hl], r2, by rw [hs1]; simp only at hs2; rw [hs2]; rfl, rfl⟩

theorem os_inv_sampleNW {n : ℕ} {s s' : St} {ys : List E} (h : RunsW Ht (Prog.sampleN n) s ys s') :
    ys = (sqAllW Ht n s.cv).1 ∧ s' = ⟨(sqAllW Ht n s.cv).2, s.stream, s.openings, s.roots⟩ :=
  os_runs_detW (rest := s.stream) h (runsToW_sampleN n s.cv) rfl

theorem os_inv_roundPoly3W {claim : E} {s s' : St} {q : List E} (h : RunsW Ht (sumcheckRoundPoly 3 claim none) s q s') :
    ∃ c0 c2 rest, s.stream = c0 :: c2 :: rest ∧ q = [c0, claim + c2, c2] ∧
      s' = ⟨obsCvW Ht (obsCvW Ht s.cv c0) c2, rest, s.openings, s.roots⟩ := by
  simp only [sumcheckRoundPoly] at h
  obtain ⟨c0, s1, h1, h2⟩ := os_inv_bindW h
  obtain ⟨tl, s2, h3, h4⟩ := os_inv_bindW h2
  obtain ⟨rfl, rfl⟩ := os_inv_pureW h4
  obtain ⟨r1, hs1, rfl⟩ := os_inv_readEW h1
  obtain ⟨hl, r2, hs2, rfl⟩ := os_inv_readNW h3
  match tl, hl with
  | [c2], _ =>
    refine ⟨c0, c2, r2, by rw [hs1]; simp only at hs2; rw [hs2]; rfl, by simp [sumE], rfl⟩

theorem os_inv_grindPW {b : ℕ} {s s' : St} {u : Unit} (h : RunsW Ht (Prog.grindP b) s u s') :
    ∃ n rest, s.stream = n :: rest ∧ powOk b n (gcDigestW Ht s.cv n) = true ∧
      s' = ⟨absorbCvW Ht s.cv n 4, rest, s.openings, s.roots⟩ := by
  obtain ⟨cv, xs, os, roots⟩ := s
  match xs, h with
  | [], h => cases h
  | n :: rest, h =>
    unfold RunsW Prog.grindP at h
    rw [inv_grind_consW] at h
    split at h
    · rename_i hpow
      have := os_inv_retW (Ht := Ht) h
      exact ⟨n, rest, rfl, hpow, this.2⟩
    · cases h

theorem os_inv_commitPW {hh ww : ℕ} {s s' : St} {u : Unit} (h : RunsW Ht (Prog.commitP hh ww) s u s') :
    ∃ x0 x1 rest root, s.stream = x0 :: x1 :: rest ∧ digestOfScalars (x0, x1) = some root ∧
      s' = ⟨obsCvW Ht (obsCvW Ht s.cv x0) x1, rest, s.openings, s.roots ++ [(root, hh, ww)]⟩ := by
  obtain ⟨cv, xs, os, roots⟩ := s
  match xs, h with
  | [], h => cases h
  | [_], h => cases h
  | x0 :: x1 :: rest, h =>
    unfold RunsW Prog.commitP at h
    simp only [runW, Compile.run] at h
    split at h
    · rename_i root hroot
      have := os_inv_retW (Ht := Ht) h
      exact ⟨x0, x1, rest, root, rfl, hroot, this.2⟩
    · cases h

theorem os_inv_queryPW {i : ℕ} {ps : List ℕ} {s s' : St} {rows : List (List K)}
    (h : RunsW Ht (Prog.queryP i ps) s rows s') :
    ∃ root hh ww rest, s.roots[i]? = some (root, hh, ww) ∧
      openAll (m := Id) Ht root hh ww ps s.openings = some (rows, rest) ∧
      s' = ⟨s.cv, s.stream, rest, s.roots⟩ := by
  obtain ⟨cv, xs, os, roots⟩ := s
  unfold RunsW Prog.queryP at h
  simp only [runW, Compile.run] at h
  split at h
  · cases h
  · rename_i root hh ww hr
    simp only [bind] at h
    split at h
    · rename_i rows' rest hoa
      have := os_inv_retW (Ht := Ht) h
      obtain ⟨rfl, rfl⟩ := this
      exact ⟨root, hh, ww, rest, hr, hoa, rfl⟩
    · cases h


/-- **A bind's query steps**: the first program's, then the continuation's. -/
theorem os_queriesOf_bindW {α β : Type} (p : Prog α) (f : α → Prog β) :
    ∀ (s : St) {a : α} {s' : St}, RunsW Ht p s a s' → queriesOfW Ht (p.bind f) s = queriesOfW Ht p s ++ queriesOfW Ht (f a) s' := by
  induction p with
  | ret a0 =>
    intro s a s' h
    obtain ⟨rfl, rfl⟩ := os_inv_retW h
    rfl
  | fail => intro s a s' h; cases h
  | read k ih =>
    intro s a s' h
    obtain ⟨cv, xs, os, roots⟩ := s
    cases xs with
    | nil => cases h
    | cons x xs =>
      have h' : RunsW Ht (k x) ⟨absorbBlock (m := Id) Ht cv (blockOf x 1), xs, os, roots⟩ a s' := h
      exact ih x _ h'
  | sample k ih =>
    intro s a s' h
    exact ih _ _ h
  | grind b k ih =>
    intro s a s' h
    obtain ⟨cv, xs, os, roots⟩ := s
    cases xs with
    | nil => cases h
    | cons n xs =>
      unfold RunsW at h
      simp only [runW, Compile.run, bind, pure] at h
      simp only [queriesOfW, Prog.bind]
      split at h
      · rename_i hp
        simp only [hp, ↓reduceIte]
        exact ih _ h
      · cases h
  | commit hh ww k ih =>
    intro s a s' h
    obtain ⟨cv, xs, os, roots⟩ := s
    match xs, h with
    | [], h => cases h
    | [_], h => cases h
    | x0 :: x1 :: xs, h =>
      unfold RunsW at h
      simp only [runW, Compile.run, bind] at h
      simp only [queriesOfW, Prog.bind]
      split at h
      · rename_i root hr
        rw [hr]
        exact ih _ h
      · cases h
  | query i ps k ih =>
    intro s a s' h
    unfold RunsW at h
    simp only [runW, Compile.run] at h
    simp only [queriesOfW, Prog.bind]
    split at h
    · cases h
    · rename_i root hh ww hr
      rw [hr]
      simp only [bind] at h
      split at h
      · rename_i rows rest hoa
        simp only [hoa, List.cons_append]
        exact congrArg _ (ih rows _ h)
      · cases h


theorem os_queriesOf_noQW {α : Type} : ∀ (p : Prog α), osNoQ p → ∀ s, queriesOfW Ht p s = []
  | .ret _, _, _ => rfl
  | .fail, _, _ => rfl
  | .read k, h, s => by
    simp only [queriesOfW]; split
    · rfl
    · exact os_queriesOf_noQW _ (h _) _
  | .sample k, h, s => os_queriesOf_noQW _ (h _) _
  | .grind _ k, h, s => by
    simp only [queriesOfW]; split
    · rfl
    · split
      · exact os_queriesOf_noQW k h _
      · rfl
  | .commit _ _ k, h, s => by
    simp only [queriesOfW]; split
    · split
      · exact os_queriesOf_noQW k h _
      · rfl
    · rfl
  | .query .., h, _ => h.elim


/-- A query step's own steps. -/
theorem os_queriesOf_queryPW {i : ℕ} {ps : List ℕ} {s : St} {root : Digest} {hh ww : ℕ}
    {rows : List (List K)} {rest : List Opening} (hr : s.roots[i]? = some (root, hh, ww))
    (ho : openAll (m := Id) Ht root hh ww ps s.openings = some (rows, rest)) :
    queriesOfW Ht (Prog.queryP i ps) s = [(hh, ps.zip s.openings)] := by
  simp only [Prog.queryP, queriesOfW, hr, ho]


theorem os_foldRounds_lenW : ∀ (n : ℕ) (w : WhirState) (lf : List E) (s : St) (res : WhirState × List E) (s' : St),
    RunsW Ht (foldRounds n w lf) s res s' → res.1.folds.length = w.folds.length + n
  | 0, w, lf, s, res, s', h => by
    obtain ⟨rfl, -⟩ := os_inv_pureW h
    rfl
  | n + 1, w, lf, s, res, s', h => by
    simp only [foldRounds] at h
    obtain ⟨ch, s1, -, h2⟩ := os_inv_bindW h
    obtain ⟨q, s2, -, h4⟩ := os_inv_bindW h2
    have := os_foldRounds_lenW n _ _ _ _ _ h4
    simp only [List.length_append, List.length_singleton] at this
    omega

theorem os_tailRounds_lenW : ∀ (n : ℕ) (t : E) (q : List E) (s : St) (res : List E × E) (s' : St),
    RunsW Ht (tailRounds n t q) s res s' → res.1.length = n
  | 0, t, q, s, res, s', h => by
    obtain ⟨rfl, -⟩ := os_inv_pureW h
    rfl
  | n + 1, t, q, s, res, s', h => by
    simp only [tailRounds] at h
    obtain ⟨ch, s1, -, h2⟩ := os_inv_bindW h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [↓reduceIte] at h2
      obtain ⟨rfl, -⟩ := os_inv_pureW h2
      rfl
    · rw [ite_neg' (by omega)] at h2
      obtain ⟨q', s2, -, h4⟩ := os_inv_bindW h2
      obtain ⟨⟨rest, t'⟩, s3, h5, h6⟩ := os_inv_bindW h4
      obtain ⟨rfl, -⟩ := os_inv_pureW h6
      have := os_tailRounds_lenW n _ _ _ _ _ h5
      simp [this]


theorem os_levelQueries_foldsW {ml idx : ℕ} {L : Whir.Level} {lf : List E} {w : WhirState}
    {pending : List (E × List E × (List E → E))} {s s' : St} {w' : WhirState}
    (h : RunsW Ht (osLevelQueries ml idx L lf w pending) s w' s') : w'.folds = w.folds := by
  simp only [osLevelQueries] at h
  obtain ⟨_, _, -, h1⟩ := os_inv_bindW h
  obtain ⟨_, _, -, h2⟩ := os_inv_bindW h1
  obtain ⟨_, _, -, h3⟩ := os_inv_bindW h2
  obtain ⟨_, _, -, h4⟩ := os_inv_bindW h3
  obtain ⟨_, _, -, h5⟩ := os_inv_bindW h4
  obtain ⟨rfl, -⟩ := os_inv_pureW h5
  exact os_glue_folds _ _ _


theorem os_whirLevelsOpen_lenW (logN lane : ℕ) : ∀ (levels : List Whir.Level) (idx : ℕ) (w : WhirState) (s : St)
    (e : WhirEnd) (s' : St), RunsW Ht (whirLevelsOpen logN lane idx levels w) s e s' →
    (levels.map (·.fold)).sum + w.folds.length ≤ logN → e.point.length = logN
  | [], _, _, _, _, _, h, _ => by cases h
  | L :: rest, idx, w, s, e, s', h, hle => by
    rw [os_whirLevelsOpen_cons] at h
    obtain ⟨⟨w1, lf⟩, s1, h1, h2⟩ := os_inv_bindW h
    have hl1 := os_foldRounds_lenW _ _ _ _ _ _ h1
    simp only at hl1
    obtain ⟨⟨res, pending⟩, s2, -, h3⟩ := os_inv_bindW h2
    obtain ⟨w2, s3, h4, h5⟩ := os_inv_bindW h3
    have hf2 := os_levelQueries_foldsW h4
    simp only [List.map_cons, List.sum_cons] at hle
    match rest, h5 with
    | [], h5 =>
      simp only [osTailOpen] at h5
      obtain ⟨⟨tf, tgt⟩, s4, h6, h7⟩ := os_inv_bindW h5
      obtain ⟨rfl, -⟩ := os_inv_pureW h7
      have := os_tailRounds_lenW _ _ _ _ _ _ h6
      simp only at this
      rw [os_rotate_length, List.length_append, this, hf2, hl1]
      simp only [List.map_nil, List.sum_nil] at hle
      omega
    | _ :: _, h5 =>
      refine os_whirLevelsOpen_lenW logN lane _ _ _ _ _ _ h5 ?_
      rw [hf2, hl1]; omega


theorem os_runs_readEW (cv : Digest) (x : E) (rest : List E) (os : List Opening)
    (roots : List (Digest × ℕ × ℕ)) :
    RunsW Ht Prog.readE ⟨cv, x :: rest, os, roots⟩ x ⟨obsCvW Ht cv x, rest, os, roots⟩ := rfl

theorem os_runs_sampleEW (st : St) :
    RunsW Ht Prog.sampleE st (challengeOf (sqCvW Ht st.cv)) { st with cv := sqCvW Ht st.cv } := rfl

theorem os_runs_roundPoly3W (cv : Digest) (claim c0 c2 : E) (rest : List E) (os : List Opening)
    (roots : List (Digest × ℕ × ℕ)) :
    RunsW Ht (sumcheckRoundPoly 3 claim none) ⟨cv, c0 :: c2 :: rest, os, roots⟩ [c0, claim + c2, c2]
      ⟨obsCvW Ht (obsCvW Ht cv c0) c2, rest, os, roots⟩ := by
  simp only [sumcheckRoundPoly, Prog.readN, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc,
    Prog.ret_bind, sumE, List.foldl, zero_add, Nat.reduceSub]
  rfl

theorem os_runs_commitPW {cv : Digest} {x0 x1 : E} {root : Digest}
    (h : digestOfScalars (x0, x1) = some root) (height width : ℕ) (rest : List E)
    (os : List Opening) (roots : List (Digest × ℕ × ℕ)) :
    RunsW Ht (Prog.commitP height width) ⟨cv, x0 :: x1 :: rest, os, roots⟩ ()
      ⟨obsCvW Ht (obsCvW Ht cv x0) x1, rest, os, roots ++ [(root, height, width)]⟩ := by
  simp only [RunsW, Prog.commitP, runW, Compile.run, h]
  rfl

theorem os_runs_grindPW {cv : Digest} {bits : ℕ} {n : E} (h : powOk bits n (gcDigestW Ht cv n) = true)
    (rest : List E) (os : List Opening) (roots : List (Digest × ℕ × ℕ)) :
    RunsW Ht (Prog.grindP bits) ⟨cv, n :: rest, os, roots⟩ () ⟨absorbCvW Ht cv n 4, rest, os, roots⟩ := by
  have h' : powOk bits n (Ht (digestBytes (Ht (digestBytes cv ++ blockOf 0 3)) ++
      blockOf n 4)) = true := h
  simp only [RunsW, Prog.grindP, runW, Compile.run, absorbBlock]
  simp only [bind, pure, h', ↓reduceIte]
  rfl

theorem os_runs_queryPW {cv : Digest} {i : ℕ} {ps : List ℕ} {xs : List E} {os orest : List Opening}
    {roots : List (Digest × ℕ × ℕ)} {root : Digest} {height width : ℕ} {rows : List (List K)}
    (hr : roots[i]? = some (root, height, width))
    (ho : openAll (m := Id) Ht root height width ps os = some (rows, orest)) :
    RunsW Ht (Prog.queryP i ps) ⟨cv, xs, os, roots⟩ rows ⟨cv, xs, orest, roots⟩ := by
  simp only [RunsW, Prog.queryP, runW, Compile.run, hr]
  simp only [bind] at ho ⊢
  rw [ho]
  rfl


theorem sqAll_succ'W (j : ℕ) (cv : Digest) : (sqAllW Ht (j + 1) cv).2 = (sqAllW Ht j (sqCvW Ht cv)).2 := rfl

/-- **`sampleQueriesAux`** (V:1598): `k` samples cover `rem` positions, `per = 192/depth` at a
time, ending at the chain state after `k` squeezes. -/
theorem runsTo_sampleQueriesAuxW (depth : ℕ) (hd : 0 < 192 / depth) :
    ∀ (k fuel rem : ℕ) (cv : Digest), rem ≤ k * (192 / depth) → (k - 1) * (192 / depth) < rem ∨ k = 0 →
      k ≤ fuel →
      RunsToW Ht (sampleQueriesAux depth fuel rem) cv [] ((List.range rem).map (osPosOfW Ht depth cv))
        (sqAllW Ht k cv).2 := by
  intro k
  induction k with
  | zero =>
    intro fuel rem cv h1 _ _
    obtain rfl : rem = 0 := by omega
    show RunsToW Ht (sampleQueriesAux depth fuel 0) cv [] [] cv
    cases fuel with
    | zero => exact runsToW_ret _ _
    | succ f =>
      simp only [sampleQueriesAux, ↓reduceIte]
      exact runsToW_ret _ _
  | succ k IH =>
    intro fuel rem cv h1 h2 h3
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
    have ih := IH f (rem - min (192 / depth) rem) (sqCvW Ht cv) hr1 hr2 (by omega)
    unfold sampleQueriesAux
    simp only [hrem, ↓reduceIte]
    refine RunsToW.of_eq (RunsToW.bind (runsToW_sampleE cv) (RunsToW.bind ih (runsToW_ret _ _))) (by simp) ?_ rfl
    have hr : List.range rem = List.range (min (192 / depth) rem) ++
        (List.range (rem - min (192 / depth) rem)).map (min (192 / depth) rem + ·) := by
      rw [← List.range_add]; congr 1; omega
    rw [hr, List.map_append, List.map_map]
    refine congrArg₂ (· ++ ·) ?_ ?_
    · refine List.map_congr_left fun i hi => ?_
      have hi' : i < min (192 / depth) rem := List.mem_range.mp hi
      have e1 : i / (192 / depth) = 0 := Nat.div_eq_of_lt (by omega)
      have e2 : i % (192 / depth) = i := Nat.mod_eq_of_lt (by omega)
      simp only [osPosOfW]
      rw [e1, e2]
      rfl
    · refine List.map_congr_left fun i hi => ?_
      simp only [Function.comp, osPosOfW]
      rcases Nat.eq_zero_or_pos k with hk | hk
      · have : rem - min (192 / depth) rem = 0 := by rw [hn, ite_pos' hk]; omega
        rw [this] at hi; simp at hi
      · rw [show min (192 / depth) rem = 192 / depth by rw [hn, ite_neg' (by omega)],
          show (192 / depth + i) / (192 / depth) = i / (192 / depth) + 1 by
            rw [Nat.add_comm, Nat.add_div_right _ hd],
          Nat.add_mod_left, sqAll_succ'W]

/-- `sampleQueries` (V:1610) over `nq` positions in `k = ⌈nq / per⌉` samples. -/
theorem os_runsTo_sampleQueriesW {depth nq k : ℕ} (hd : 0 < 192 / depth) (h1 : nq ≤ k * (192 / depth))
    (h2 : (k - 1) * (192 / depth) < nq ∨ k = 0) (hk : k ≤ nq) (cv : Digest) :
    RunsToW Ht (sampleQueries depth nq) cv [] ((List.range nq).map (osPosOfW Ht depth cv)) (sqAllW Ht k cv).2 :=
  runsTo_sampleQueriesAuxW depth hd k nq nq cv h1 h2 hk


theorem os_foldRounds_foldsW : ∀ {n : ℕ} {w : WhirState} {lf : List E} {s : St} {res : WhirState × List E} {s' : St},
    RunsW Ht (foldRounds n w lf) s res s' →
      ∃ chs, res.1.folds = w.folds ++ chs ∧ res.2 = lf ++ chs ∧ chs.length = n
  | 0, w, lf, s, res, s', h => by
    obtain ⟨rfl, -⟩ := os_inv_pureW h
    exact ⟨[], by simp, by simp, rfl⟩
  | n + 1, w, lf, s, res, s', h => by
    simp only [foldRounds] at h
    obtain ⟨ch, s1, -, h2⟩ := os_inv_bindW h
    obtain ⟨q, s2, -, h4⟩ := os_inv_bindW h2
    obtain ⟨chs, h5, h6, h7⟩ := os_foldRounds_foldsW h4
    exact ⟨ch :: chs, by rw [h5]; simp, by rw [h6]; simp, by simp [h7]⟩

theorem os_runs_foldStepW {q : List E} {sp sp' : St} {r : E × E × List E}
    (h : RunsW Ht (foldStep q) sp r sp') :
    ∃ d0 d2 rest, sp.stream = d0 :: d2 :: rest ∧
      r = (challengeOf (sqCvW Ht sp.cv), polyEval q (challengeOf (sqCvW Ht sp.cv)),
        [d0, polyEval q (challengeOf (sqCvW Ht sp.cv)) + d2, d2]) ∧
      sp' = ⟨obsAllW Ht (sqCvW Ht sp.cv) [d0, d2], rest, sp.openings, sp.roots⟩ := by
  simp only [foldStep] at h
  obtain ⟨ch, s1, h1, h2⟩ := os_inv_bindW h
  obtain ⟨qq, s2, h3, h4⟩ := os_inv_bindW h2
  obtain ⟨rfl, rfl⟩ := os_inv_pureW h4
  obtain ⟨rfl, rfl⟩ := os_inv_sampleEW h1
  obtain ⟨c0, c2, rest, hs, rfl, rfl⟩ := os_inv_roundPoly3W h3
  exact ⟨c0, c2, rest, hs, rfl, rfl⟩


end
end LeanVM.Guest.B1
