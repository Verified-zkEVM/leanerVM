/-
  LeanVM.Guest.B1.Whir.StackedBlocksM

  The soundness of `open_stacked`'s blocks under a hash model: each block's relation gives its
  facts in the specification's terms, every hash the block makes answered by the model.
-/

module

public import LeanVM.Guest.B1.Whir.StackedBlocks
public import LeanVM.Guest.B1.Whir.StackedRunM
public import LeanVM.Guest.B1.Grind

/-!
# The blocks of `open_stacked` under a hash model (TRIAGE #36)

`Whir/StackedBlocks.lean` over a `HashModel`, against the same running state `OsCur` (which names
no hash). Each block that reads or squeezes the chain gives the new chain state as the model's
answered digest and the piece of the specification's run over `M.H` (`RunsToM`); the blocks
without a `BLAKE2S` row (the pointers, the query weights, the glue) carry their deployed lemmas
over (`holdsListB_iff_of_noBlake`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {M : HashModel} {C : CallRel} {rd : Reader} {σ : Val}

private theorem readsAt_appendM {cur : E} {xs ys : List E} (hx : ReadsAt rd cur xs)
    (hy : ∀ j (hj : j < ys.length), LoadHolds rd cur (xs.length + j) ys[j]) :
    ReadsAt rd cur (xs ++ ys) := by
  intro k hk
  rw [List.length_append] at hk
  rcases Nat.lt_or_ge k xs.length with h | h
  · rw [List.getElem_append_left h]; exact hx k h
  · rw [List.getElem_append_right h]
    have := hy (k - xs.length) (by omega)
    rwa [show xs.length + (k - xs.length) = k by omega] at this

theorem osMat_noBlake (base off k : ℕ) : Stmt.noBlakeList (osMat base off k).1 = true := by
  unfold osMat; split <;> rfl

/-- The cursor's pointer under any semantics (`osMat_sound`). -/
theorem osMat_soundM {S : BlakeSem} {base off k : ℕ} (hoff : off < 2 ^ 128) {kret : List E → Prop}
    (h : Stmt.HoldsListB S C rd σ (osMat base off k).1 True kret) :
    σ (.n (osMat base off k).2.1) = σ (.n base) * gen ^ off :=
  osMat_sound hoff ((holdsListB_iff_of_noBlake (osMat_noBlake _ _ _) _ _).mp h)

/-! ## `fs_next` -/

/-- **`fs_next` under a hash model**: the word at the cursor is read and absorbed, the new state
the model's answered digest. -/
theorem osFsNext_soundM {cur : E} {s : OsSt} {cv : Digest} {xs : List E} (hat : OsCur rd σ cur s cv xs)
    {kret : List E → Prop} (h : Stmt.HoldsListB M.sem C rd σ (osFsNext s).1 True kret) :
    ∃ d, obsCvM M cv (σ (.n s.k)) = some d ∧
      OsCur rd σ cur (osFsNext s).2 d (xs ++ [σ (.n s.k)]) := by
  obtain ⟨⟨hl, cv', d, hcv', hd, e⟩, -⟩ := holdsB_fsNextT _ _ _ _ _ h
  have hcv : cv' = cv := digestScalars_injective (hcv'.symm.trans hat.fs)
  subst hcv
  refine ⟨d, hd, ?_, readsAt_appendM hat.reads fun j hj => ?_, ?_⟩
  · show (σ (.n (s.k + 13)), σ (.n (s.k + 14))) = _
    rw [show s.k + 13 = s.k + 1 + 12 by ring, show s.k + 14 = s.k + 1 + 13 by ring,
      e 12 (by omega) (by omega), e 13 (by omega) (by omega)]
    rfl
  · simp only [List.length_cons, List.length_nil] at hj
    obtain rfl : j = 0 := by omega
    exact hat.load (j := 0) (by simpa using hl)
  · show σ (.n s.cb) * gen ^ (s.co + 1) = cur * gen ^ (xs ++ [σ (.n s.k)]).length
    rw [List.length_append, List.length_singleton, pow_succ, pow_succ, ← mul_assoc, ← mul_assoc,
      hat.cursor]

/-- `fs_next` under a hash model, as a run: the read of the word (`readE`). -/
theorem osFsNext_runM {cur : E} {s : OsSt} {cv : Digest} {xs : List E} (hat : OsCur rd σ cur s cv xs)
    {kret : List E → Prop} (h : Stmt.HoldsListB M.sem C rd σ (osFsNext s).1 True kret) :
    ∃ d, RunsToM M Prog.readE cv [σ (.n s.k)] (σ (.n s.k)) d ∧ obsCvM M cv (σ (.n s.k)) = some d ∧
      OsCur rd σ cur (osFsNext s).2 d (xs ++ [σ (.n s.k)]) := by
  obtain ⟨d, hd, hat'⟩ := osFsNext_soundM hat h
  exact ⟨d, runsToM_readE hd, hd, hat'⟩

/-! ## The fold rounds -/

theorem osFold_noBlake (s : OsSt) (fch fo : ℕ) : Stmt.noBlakeList (osFold s fch fo).1 = true := by
  unfold osFold
  simp only [noBlakeList_append, osMat_noBlake, Bool.true_and]
  rfl

private theorem range7_mapM (r : ℕ) : ((List.range 7).map fun j => V.n (r + j)) =
    [.n r, .n (r + 1), .n (r + 2), .n (r + 3), .n (r + 4), .n (r + 5), .n (r + 6)] := by
  simp [List.range_succ]

/-- **One fold round under a hash model** (`opening_fold`, G:945): from the chain state `cv`,
the challenge `r` is stored at `fch[fo]`, the next quadratic's `d0, d2` are read, and the running
quadratic and claim are `foldStep`'s (V:1678), its run answered by the model. -/
theorem osFold_soundM {cur : E} {s : OsSt} {cv : Digest} {xs : List E} (hat : OsCur rd σ cur s cv xs)
    (hco : s.co < 2 ^ 128) {fch fo : ℕ} {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem (coreProgram.RelB M.sem rd) rd σ (osFold s fch fo).1 True kret) :
    ∃ d0 d2 r cv', OsCur rd σ cur (osFold s fch fo).2 cv' (xs ++ [d0, d2]) ∧
      (osFold s fch fo).2.co = 0 ∧
      RunsToM M (foldStep [σ (.n s.c), σ (.n s.b), σ (.n s.a)]) cv [d0, d2]
        (r, σ (.n (osFold s fch fo).2.t),
          [σ (.n (osFold s fch fo).2.c), σ (.n (osFold s fch fo).2.b), σ (.n (osFold s fch fo).2.a)])
        cv' ∧
      LoadHolds rd (σ (.n fch)) fo r := by
  rw [holdsListB_iff_of_noBlake (osFold_noBlake _ _ _)] at h
  unfold osFold at h ⊢
  simp only at h ⊢
  rw [holdsList_append] at h
  obtain ⟨hm, h⟩ := holdsList_true_of (osMat_noRet _ _ _) h
  have hp := osMat_sound hco hm
  generalize osMat s.cb s.co s.k = m at h hp ⊢
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, range7_mapM, List.map_cons, List.map_nil] at h
  obtain ⟨hcall, h7, h8, l6, h9, -⟩ := h
  obtain ⟨cv0, e1, e2, e3, d0, d2, hcv0, hrd, he1, he2, he3, hret⟩ := opening_fold_modelD rd hcall
  have hcv : cv0 = cv := digestScalars_injective (hcv0.symm.trans hat.fs)
  subst hcv
  simp only [List.cons.injEq] at hret
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, -⟩ := hret
  have hl0 : LoadHolds rd (σ (.n m.2.1)) 0 d0 := hrd 0 (by simp)
  have hl1 : LoadHolds rd (σ (.n m.2.1)) 1 d2 := hrd 1 (by simp)
  rw [hp, loadHolds_mul_gen_pow] at hl0 hl1
  refine ⟨d0, d2, challengeOf e1, e3, ⟨?_, readsAt_appendM hat.reads fun j hj => ?_, ?_⟩, trivial,
    ?_, ?_⟩
  · show (σ (.n (m.2.2 + 7)), σ (.n (m.2.2 + 8))) = _
    rw [h7, h8, r0, r1]
  · simp only [List.length_cons, List.length_nil] at hj
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · exact hat.load (j := 0) (by simpa using hl0)
    · exact hat.load (j := 1) hl1
  · show σ (.n (m.2.2 + 2)) * gen ^ 0 = cur * gen ^ (xs ++ [d0, d2]).length
    rw [r2, hp, pow_zero, mul_one, List.length_append, mul_assoc, ← pow_add, pow_add, ← mul_assoc,
      hat.cursor, mul_assoc, ← pow_add]
    rfl
  · rw [r3, r4, h9, r3, r5]
    exact runsToM_foldStep _ _ _ d0 d2 he1 he2 he3
  · rw [← r6]; exact l6

/-- **The fold rounds under a hash model** (G:1103-1108): `n` rounds of `osFold_soundM` are
`foldRounds n` (V:1678) over the model, their challenges stored at `fch[fo ..]`. -/
theorem osFolds_soundM {cur : E} {fch : ℕ} {kret : List E → Prop} :
    ∀ (n fo : ℕ) (s : OsSt) (cv : Digest) (xs : List E) (w : WhirState) (lf : List E),
      OsCur rd σ cur s cv xs → s.co < 2 ^ 128 → w.quad = [σ (.n s.c), σ (.n s.b), σ (.n s.a)] →
      w.target = σ (.n s.t) →
      Stmt.HoldsListB M.sem (coreProgram.RelB M.sem rd) rd σ (osFolds fch fo n s).1 True kret →
      ∃ ys cv' chs w', OsCur rd σ cur (osFolds fch fo n s).2 cv' (xs ++ ys) ∧
        RunsToM M (foldRounds n w lf) cv ys (w', lf ++ chs) cv' ∧ chs.length = n ∧
        w'.quad = [σ (.n (osFolds fch fo n s).2.c), σ (.n (osFolds fch fo n s).2.b),
          σ (.n (osFolds fch fo n s).2.a)] ∧ w'.target = σ (.n (osFolds fch fo n s).2.t) ∧
        w'.folds = w.folds ++ chs ∧ w'.glued = w.glued ∧
        (∀ j < n, LoadHolds rd (σ (.n fch)) (fo + j) (chs.getD j 0)) ∧
        (osFolds fch fo n s).2.co = if n = 0 then s.co else 0
  | 0, fo, s, cv, xs, w, lf, hat, _, hq, ht, _ =>
    ⟨[], cv, [], w, by simpa [osFolds] using hat, by simpa [foldRounds] using runsToM_ret (M := M) (w, lf) cv,
      rfl, hq, ht, by simp, rfl, fun j hj => absurd hj (Nat.not_lt_zero j), by simp [osFolds]⟩
  | n + 1, fo, s, cv, xs, w, lf, hat, hco, hq, ht, h => by
    simp only [osFolds, holdsListB_append] at h ⊢
    obtain ⟨h1, h⟩ := holdsListB_true_of (osFold_noRet _ _ _) h
    obtain ⟨d0, d2, r, cv1, hat1, hco1, hrun1, hl1⟩ := osFold_soundM hat hco h1
    let w1 : WhirState :=
      { target := σ (.n (osFold s fch fo).2.t)
        quad := [σ (.n (osFold s fch fo).2.c), σ (.n (osFold s fch fo).2.b),
          σ (.n (osFold s fch fo).2.a)]
        folds := w.folds ++ [r]
        glued := w.glued }
    have := osFolds_soundM (fch := fch) (kret := kret) n (fo + 1) (osFold s fch fo).2 _ _ w1
      (lf ++ [r]) hat1 (by rw [hco1]; decide) rfl rfl h
    obtain ⟨ys, cv', chs, w', hat', hrun', hlen, hq', ht', hf', hg', hl', hco'⟩ := this
    refine ⟨[d0, d2] ++ ys, cv', r :: chs, w', by simpa using hat', ?_,
      by simp [hlen], hq', ht', by rw [hf']; simp [w1], hg', fun j hj => ?_, ?_⟩
    · rw [foldRounds_succ, hq]
      exact hrun1.bind (hrun'.of_eq rfl (by simp) rfl)
    · rcases j with _ | j
      · simpa using hl1
      · have := hl' j (by omega)
        rwa [show fo + 1 + j = fo + (j + 1) by ring] at this
    · rw [hco']
      split <;> simp_all

/-! ## The final message, the next commitment, the proof of work -/

theorem osFinal_noBlake (name : String) (fmsg : ℕ) (s : OsSt) :
    Stmt.noBlakeList (osFinal name fmsg s).1 = true := by
  unfold osFinal
  simp only [noBlakeList_append, osMat_noBlake, Bool.true_and]
  rfl

/-- **The final message under a hash model** (`opening_final_message`, G:1110-1112): the `n`
words `ms` read at the cursor, absorbed (`readN n`, V:1726, over the model), and stored at
`final_msg`. -/
theorem osFinal_soundM {name : String} {n : ℕ}
    (hfin : ∀ a r, coreProgram.RelB M.sem rd name a r → MeaningOpeningFinalMessageWith M n rd a r)
    {cur : E} {s : OsSt} {cv : Digest} {xs : List E} (hat : OsCur rd σ cur s cv xs)
    (hco : s.co < 2 ^ 128) {fmsg : ℕ} {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem (coreProgram.RelB M.sem rd) rd σ (osFinal name fmsg s).1 True kret) :
    ∃ (ms : List E) (cv' : Digest), ms.length = n ∧ RunsToM M (Prog.readN n) cv ms ms cv' ∧
      OsCur rd σ cur (osFinal name fmsg s).2 cv' (xs ++ ms) ∧
      ReadsAt rd (σ (.n fmsg)) ms ∧ (osFinal name fmsg s).2.co = 0 := by
  rw [holdsListB_iff_of_noBlake (osFinal_noBlake _ _ _)] at h
  unfold osFinal at h ⊢
  simp only at h ⊢
  rw [holdsList_append] at h
  obtain ⟨hm, h⟩ := holdsList_true_of (osMat_noRet _ _ _) h
  have hp := osMat_sound hco hm
  generalize osMat s.cb s.co s.k = m at h hp ⊢
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at h
  obtain ⟨hcall, h3, h4, -⟩ := h
  obtain ⟨cv0, ms, cv', hcv0, hlen, hrd, hout, hrun, hret⟩ := hfin _ _ hcall
  have hcv : cv0 = cv := digestScalars_injective (hcv0.symm.trans hat.fs)
  subst hcv
  simp only [List.cons.injEq] at hret
  obtain ⟨r0, r1, r2, -⟩ := hret
  refine ⟨ms, cv', hlen, hrun, ⟨?_, readsAt_appendM hat.reads fun j hj => ?_, ?_⟩, hout, trivial⟩
  · show (σ (.n (m.2.2 + 3)), σ (.n (m.2.2 + 4))) = _
    rw [h3, h4, r0, r1]
  · have := hrd j hj
    rw [hp, loadHolds_mul_gen_pow] at this
    exact hat.load this
  · show σ (.n (m.2.2 + 2)) * gen ^ 0 = cur * gen ^ (xs ++ ms).length
    rw [r2, hp, pow_zero, mul_one, List.length_append, hlen, mul_assoc, ← pow_add, pow_add, ← mul_assoc,
      hat.cursor, mul_assoc, ← pow_add]

/-- **An out-of-domain sample under a hash model** (G:1125-1135): its point, `sampleN logCols`
(V:1732, over the model, to `cvz`), stored at `oodz·g^oz`; its value and its intro message's
`c0, c2` read, absorbed (to `cv'`) and stored at `ood[so + 1 ..]`. -/
theorem osOodSample_soundM {cur : E} {s : OsSt} {cv : Digest} {xs : List E}
    (hat : OsCur rd σ cur s cv xs) {oz so logCols oodz ood : ℕ} (hoz : oz < 2 ^ 128)
    (hl0 : 0 < logCols) (hl1 : logCols < 2 ^ 63) {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem (coreProgram.RelB M.sem rd) rd σ
      (osOodSample oz so logCols oodz ood s).1 True kret) :
    ∃ (y c0 c2 : E) (zs : List E) (cvz cv' : Digest),
      RunsToM M (Prog.sampleN logCols) cv [] zs cvz ∧ (∃ e1 e2, obsCvM M cvz y = some e1 ∧
        obsCvM M e1 c0 = some e2 ∧ obsCvM M e2 c2 = some cv') ∧
      OsCur rd σ cur (osOodSample oz so logCols oodz ood s).2 cv' (xs ++ [y, c0, c2]) ∧
      ReadsAt rd (σ (.n oodz) * gen ^ oz) zs ∧
      LoadHolds rd (σ (.n ood)) (so + 1) y ∧ LoadHolds rd (σ (.n ood)) (so + 2) c0 ∧
      LoadHolds rd (σ (.n ood)) (so + 3) c2 ∧
      (osOodSample oz so logCols oodz ood s).2.co = s.co + 3 := by
  unfold osOodSample at h ⊢
  simp only at h ⊢
  simp only [holdsListB_append] at h
  obtain ⟨hpre, hr⟩ := holdsListB_split_free rfl rfl h
  clear h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, and_true] at hpre
  obtain ⟨e0, e1, e2, hcall, e5, e6⟩ := hpre
  obtain ⟨m, hm, hng, p, hcase⟩ := opening_ood_point_model rd _ _ hcall
  rw [e2, os_gw_eq (by omega)] at hng
  have hmeq : m = logCols := gen_pow_inj hm (by omega) hng.symm
  subst hmeq
  rcases hcase with ⟨h0, -⟩ | ⟨-, cv0, rs, cvz, hcv0, hrun, hrs, -, hret⟩
  · omega
  have hcv : cv0 = cv := digestScalars_injective (hcv0.symm.trans hat.fs)
  subst hcv
  simp only [List.cons.injEq] at hret
  obtain ⟨r0, r1, -⟩ := hret
  have hat1 : OsCur rd σ cur { s with k := s.k + 7, f0 := s.k + 5, f1 := s.k + 6 } cvz xs :=
    ⟨by show (σ (.n (s.k + 5)), σ (.n (s.k + 6))) = _; rw [e5, e6, r0, r1], hat.reads, hat.cursor⟩
  obtain ⟨hy, h⟩ := holdsListB_true_of (by rfl) hr
  obtain ⟨dy, hdy, hat2⟩ := osFsNext_soundM hat1 hy
  obtain ⟨hc0, h⟩ := holdsListB_true_of (by rfl) h
  obtain ⟨dc0, hdc0, hat3⟩ := osFsNext_soundM hat2 hc0
  obtain ⟨hc2, h⟩ := holdsListB_true_of (by rfl) h
  obtain ⟨dc2, hdc2, hat4⟩ := osFsNext_soundM hat3 hc2
  simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, and_true] at h
  obtain ⟨ly, lc0, lc2⟩ := h
  refine ⟨_, _, _, rs, cvz, dc2, hrun, ⟨dy, dc0, hdy, hdc0, hdc2⟩, by simpa using hat4, ?_,
    ly, lc0, lc2, rfl⟩
  rw [e1, e0, os_gw_eq hoz] at hrs
  exact hrs

/-- **The next commitment under a hash model** (G:1113-1135), with its one out-of-domain sample:
the root's halves read, absorbed (`commitP`, V:1730), canonical, stored at
`level_roots[2lvl + 2 ..]`; then the sample. -/
theorem osCommit_soundM {lvl logCols roots oodz ood : ℕ} (hl0 : 0 < logCols) (hl1 : logCols < 2 ^ 63)
    (hlvl : (lvl + 1) * 22 < 2 ^ 128) {cur : E} {s : OsSt} {cv : Digest} {xs : List E}
    (hat : OsCur rd σ cur s cv xs) {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem (coreProgram.RelB M.sem rd) rd σ
      (osCommit lvl logCols 1 roots oodz ood s).1 True kret) :
    ∃ (x0 x1 y c0 c2 : E) (d0 d1 : Digest) (zs : List E) (cvz cv' : Digest),
      IsCanonical128 x0 ∧ IsCanonical128 x1 ∧
      LoadHolds rd (σ (.n roots)) (2 * lvl + 2) x0 ∧ LoadHolds rd (σ (.n roots)) (2 * lvl + 3) x1 ∧
      obsCvM M cv x0 = some d0 ∧ obsCvM M d0 x1 = some d1 ∧
      RunsToM M (Prog.sampleN logCols) d1 [] zs cvz ∧ (∃ e1 e2, obsCvM M cvz y = some e1 ∧
        obsCvM M e1 c0 = some e2 ∧ obsCvM M e2 c2 = some cv') ∧
      OsCur rd σ cur (osCommit lvl logCols 1 roots oodz ood s).2 cv' (xs ++ [x0, x1, y, c0, c2]) ∧
      ReadsAt rd (σ (.n oodz) * gen ^ ((lvl + 1) * 22)) zs ∧
      LoadHolds rd (σ (.n ood)) ((lvl + 1) * 4 + 1) y ∧ LoadHolds rd (σ (.n ood)) ((lvl + 1) * 4 + 2) c0 ∧
      LoadHolds rd (σ (.n ood)) ((lvl + 1) * 4 + 3) c2 ∧
      (osCommit lvl logCols 1 roots oodz ood s).2.co = s.co + 5 := by
  unfold osCommit at h ⊢
  simp only [osOods, List.append_nil] at h ⊢
  simp only [holdsListB_append] at h
  obtain ⟨ha, h⟩ := holdsListB_true_of (by rfl) h
  obtain ⟨d0, hd0, hat1⟩ := osFsNext_soundM hat ha
  obtain ⟨hb, h⟩ := holdsListB_true_of (by rfl) h
  obtain ⟨d1, hd1, hat2⟩ := osFsNext_soundM hat1 hb
  obtain ⟨hc, h⟩ := holdsListB_split_free rfl rfl h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, and_true] at hc
  obtain ⟨k0, k1, l0, l1⟩ := hc
  obtain ⟨hk0, -⟩ := (assert_canonical_iffB rd _ _).mp k0
  obtain ⟨hk1, -⟩ := (assert_canonical_iffB rd _ _).mp k1
  have hat3 : OsCur rd σ cur { (osFsNext (osFsNext s).2).2 with k := (osFsNext (osFsNext s).2).2.k + 2 }
      d1 ((xs ++ [σ (.n s.k)]) ++ [σ (.n (osFsNext s).2.k)]) := ⟨hat2.fs, hat2.reads, hat2.cursor⟩
  obtain ⟨y, c0, c2, zs, cvz, cv', hz, hobs, hat4, hrs, ly, lc0, lc2, hco⟩ :=
    osOodSample_soundM hat3 (oz := (lvl + 1 + 0) * 22) (by simpa using hlvl) hl0 hl1 h
  refine ⟨_, _, y, c0, c2, d0, d1, zs, cvz, cv', hk0, hk1, l0, l1, hd0, hd1, hz, hobs,
    by simpa using hat4, by simpa using hrs, by simpa using ly, by simpa using lc0,
    by simpa using lc2, ?_⟩
  rw [hco]; rfl

/-- **The query nonce under a hash model** (G:1136-1142): the raw word at the cursor passes
`grind_check` at `bits ≠ 0` (`powOk`, V:482, of the model's digest) and is absorbed at tag 4
(`grindP`, V:1736, over the model). -/
theorem osGrind_soundM {bits : ℕ} (hb0 : bits ≠ 0) (hb : bits < 2 ^ 63) {cur : E} {s : OsSt}
    {cv : Digest} {xs : List E} (hat : OsCur rd σ cur s cv xs) {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem (coreProgram.RelB M.sem rd) rd σ (osGrind bits s).1 True kret) :
    ∃ n cv', RunsToM M (Prog.grindP bits) cv [n] () cv' ∧
      OsCur rd σ cur (osGrind bits s).2 cv' (xs ++ [n]) ∧ (osGrind bits s).2.co = s.co + 1 := by
  unfold osGrind at h ⊢
  simp only [hb0, ↓reduceIte] at h ⊢
  simp only [holdsListB_append] at h
  obtain ⟨hp, h⟩ := holdsListB_split_free rfl rfl h
  obtain ⟨hq, h⟩ := holdsListB_split_free rfl rfl h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, List.map_cons, List.map_nil] at hp hq
  have ln := hp
  obtain ⟨e1, hcall⟩ := hq
  obtain ⟨-, m, hm, hng, cv0, B, D, hcv0, hB, hD, hpow, -⟩ := grind_check_rel_model rd _ _ hcall
  rw [e1, os_gw_eq (by omega)] at hng
  have hmeq : m = bits := gen_pow_inj hm (by omega) hng.symm
  have hcv : cv0 = cv := digestScalars_injective (hcv0.symm.trans hat.fs)
  rw [hmeq] at hpow
  subst hcv
  obtain ⟨⟨cv1, d, hcv1, hd, e⟩, -⟩ := holdsB_fsCompressT (M := M) _ _ _ _ (tag := 4) (by decide) h
  have hc1 : cv1 = cv0 := digestScalars_injective (hcv1.symm.trans hat.fs)
  subst hc1
  refine ⟨σ (.n s.k), d, runsToM_grindP hB hD hpow hd, ⟨?_, readsAt_appendM hat.reads fun j hj => ?_, ?_⟩,
    trivial⟩
  · show (σ (.n (s.k + 14)), σ (.n (s.k + 15))) = _
    rw [show s.k + 14 = s.k + 2 + 12 by ring, show s.k + 15 = s.k + 2 + 13 by ring,
      e 12 (by omega) (by omega), e 13 (by omega) (by omega)]
    rfl
  · simp only [List.length_cons, List.length_nil] at hj
    obtain rfl : j = 0 := by omega
    exact hat.load (j := 0) (by simpa using ln)
  · show σ (.n s.cb) * gen ^ (s.co + 1) = cur * gen ^ (xs ++ [σ (.n s.k)]).length
    rw [List.length_append, List.length_singleton, pow_succ, pow_succ, ← mul_assoc, ← mul_assoc,
      hat.cursor]

end
end LeanVM.Guest.B1
