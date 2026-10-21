/-
  LeanVM.Guest.B1.Whir.StackedEndM

  The tail of `open_stacked` under a hash model: the tail rounds over the model's answered hash.
-/

module

public import LeanVM.Guest.B1.Whir.StackedLevelsM
public import LeanVM.Guest.B1.Whir.StackedInner

/-!
# The tail of the stacked opening under a hash model (TRIAGE #36)

`osTail_soundM`: the tail rounds (`osTail`, G:1216-1228) against `tailRounds` (V:1689) over
`M.H`, every squeeze and read answered. The rest of `Whir/StackedEnd.lean` (the point, the basis
rows, the residual chains, the out-of-domain weights) has no `BLAKE2S` row and is used as it is.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

variable {M : HashModel} {rd : Reader} {σ : Val}

private theorem tailRounds_succ_succM (n : ℕ) (t : E) (q : List E) :
    tailRounds (n + 2) t q = (do
      let (c, target, quad) ← foldStep q
      let (rest, t') ← tailRounds (n + 1) target quad
      return (c :: rest, t')) := by
  simp only [tailRounds, foldStep, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind,
    Nat.add_one_ne_zero, ↓reduceIte]

private theorem tailRounds_oneM (t : E) (q : List E) :
    tailRounds 1 t q = (do let c ← Prog.sampleE; return ([c], polyEval q c)) := by
  simp only [tailRounds, Prog.bind_eq, Prog.pure_eq, ↓reduceIte]

/-- **The tail's folds under a hash model** (G:1217-1222): `n` rounds of `osFold_soundM`, whose
challenges are stored at `fch[fo ..]`; any run of `tailRounds 1` over the model from where they
end extends to `tailRounds (n + 1)` from where they start. -/
theorem osTailFolds_soundM {cur : E} {fch : ℕ} {kret : List E → Prop} :
    ∀ (n fo : ℕ) (s : OsSt) (cv : Digest) (xs : List E),
      OsCur rd σ cur s cv xs → s.co < 2 ^ 128 →
      Stmt.HoldsListB M.sem (coreProgram.RelB M.sem rd) rd σ (osFolds fch fo n s).1 True kret →
      ∃ ys cv' chs, OsCur rd σ cur (osFolds fch fo n s).2 cv' (xs ++ ys) ∧ chs.length = n ∧
        (∀ j < n, LoadHolds rd (σ (.n fch)) (fo + j) (chs.getD j 0)) ∧
        (osFolds fch fo n s).2.co = (if n = 0 then s.co else 0) ∧
        ∀ (L : List E) (T : E) (cv'' : Digest) (t : E),
          RunsToM M (tailRounds 1 (σ (.n (osFolds fch fo n s).2.t))
            [σ (.n (osFolds fch fo n s).2.c), σ (.n (osFolds fch fo n s).2.b),
              σ (.n (osFolds fch fo n s).2.a)]) cv' [] (L, T) cv'' →
          RunsToM M (tailRounds (n + 1) t [σ (.n s.c), σ (.n s.b), σ (.n s.a)]) cv ys (chs ++ L, T) cv''
  | 0, fo, s, cv, xs, hat, _, _ =>
    ⟨[], cv, [], by simpa [osFolds] using hat, rfl, fun j hj => absurd hj (Nat.not_lt_zero j),
      by simp [osFolds], fun L T cv'' t h => by simpa [osFolds, tailRounds] using h⟩
  | n + 1, fo, s, cv, xs, hat, hco, h => by
    simp only [osFolds, holdsListB_append] at h ⊢
    obtain ⟨h1, h⟩ := holdsListB_true_of (osFold_noRet _ _ _) h
    obtain ⟨d0, d2, r, cv1, hat1, hco1, hrun1, hl1⟩ := osFold_soundM hat hco h1
    obtain ⟨ys, cv', chs, hat', hlen, hl', hco', hrun'⟩ :=
      osTailFolds_soundM n (fo + 1) (osFold s fch fo).2 _ _ hat1 (by rw [hco1]; decide) h
    refine ⟨[d0, d2] ++ ys, cv', r :: chs, by simpa using hat', by simp [hlen],
      fun j hj => ?_, by rw [hco']; split <;> simp_all, fun L T cv'' t hT => ?_⟩
    · rcases j with _ | j
      · simpa using hl1
      · have := hl' j (by omega)
        rwa [show fo + 1 + j = fo + (j + 1) by ring] at this
    · have := hrun' L T cv'' (σ (.n (osFold s fch fo).2.t)) hT
      rw [tailRounds_succ_succM]
      exact RunsToM.of_eq (RunsToM.bind hrun1 (RunsToM.bind this (runsToM_ret _ _))) (by simp) rfl rfl

private theorem readsAt_of_getDM {p : E} {l : List E} (h : ∀ k < l.length, LoadHolds rd p k (l.getD k 0)) :
    ReadsAt rd p l := fun k hk => by
  have := h k hk
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some] at this

private theorem polyEval_threeM (c b a x : E) : polyEval [c, b, a] x = c + x * b + x * x * a := by
  simp only [polyEval, List.foldr]; ring

/-- **The tail rounds under a hash model** (G:1216-1228): `tailRounds yrLog` (V:1689) over the
model's answered hash, over the words the guest reads, its challenges at `tail_challenges`
followed by zeros up to `YR_LOG_CAP = 5`, its final claim at the returned state's `t`. -/
theorem osTail_soundM {yrLog : ℕ} (hy : 2 ≤ yrLog) (hy5 : yrLog ≤ 5) {cur : E} {s : OsSt} {cv : Digest}
    {xs : List E} (hat : OsCur rd σ cur s cv xs) (hco : s.co ≤ 8) {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem (coreProgram.RelB M.sem rd) rd σ (osTail yrLog s).1 True kret) :
    ∃ (ys tailFolds : List E) (cv' : Digest), tailFolds.length = yrLog ∧ ReadsAt rd cur (xs ++ ys) ∧
      (∀ t, RunsToM M (tailRounds yrLog t [σ (.n s.c), σ (.n s.b), σ (.n s.a)]) cv ys
        (tailFolds, σ (.n (osTail yrLog s).2.1.t)) cv') ∧
      ReadsAt rd (σ (.n (osTail yrLog s).2.2.1)) (tailFolds ++ List.replicate (5 - yrLog) 0) := by
  unfold osTail at h ⊢
  simp only at h ⊢
  simp only [holdsListB_append] at h
  obtain ⟨-, h⟩ := holdsListB_true_of (by rfl) h
  obtain ⟨hF, h⟩ := holdsListB_true_of (osFolds_noRet _ _ _ _) h
  have hat0 : OsCur rd σ cur { s with k := s.k + 2 } cv xs := ⟨hat.fs, hat.reads, hat.cursor⟩
  obtain ⟨ys, cv', chs, hat', hlen, hst, -, hcont⟩ :=
    osTailFolds_soundM (M := M) (yrLog - 1) 0 _ cv xs hat0 (by simp; omega) hF
  generalize osFolds (s.k + 1) 0 (yrLog - 1) { s with k := s.k + 2 } = fr at *
  obtain ⟨hS, h⟩ := holdsListB_true_of (by rfl) h
  obtain ⟨hA, h⟩ := holdsListB_split_free rfl rfl h
  rw [holdsListB_iff_of_noBlake (noBlakeList_flatten_range _ _ (fun _ => rfl)),
    holdsList_range_flatten _ _ (fun _ => rfl)] at h
  obtain ⟨hZ, -⟩ := h
  obtain ⟨⟨cv0, d, hcv0, hd, hv⟩, -⟩ := holdsB_squeezeT _ _ _ hS
  have hc0 : cv0 = cv' := digestScalars_injective (hcv0.symm.trans hat'.fs)
  subst hc0
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hA
  obtain ⟨llast, a1, a2, a3, a4, a5⟩ := hA
  have hlast : σ (.n (fr.2.k + 13)) = challengeOf d := hv 13 (by omega)
  refine ⟨ys, chs ++ [challengeOf d], d, by simp [hlen]; omega, hat'.reads,
    fun t => ?_, readsAt_of_getDM fun j hj => ?_⟩
  · have h1 : RunsToM M (tailRounds 1 (σ (.n fr.2.t)) [σ (.n fr.2.c), σ (.n fr.2.b), σ (.n fr.2.a)]) cv0 []
        ([challengeOf d], σ (.n (fr.2.k + 14 + 4))) d := by
      rw [tailRounds_oneM, a5, a4, a3, a2, a1, hlast]
      refine RunsToM.of_eq (RunsToM.bind (runsToM_sampleE hd) (runsToM_ret _ _)) rfl ?_ rfl
      rw [polyEval_threeM]
    have := hcont _ _ _ t h1
    rwa [show yrLog - 1 + 1 = yrLog by omega] at this
  · simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate] at hj
    rcases Nat.lt_or_ge j (yrLog - 1) with h1 | h1
    · rw [os_getD_append_lt (by simp; omega), os_getD_append_lt (by omega)]
      simpa using hst j h1
    · rcases Nat.lt_or_ge j yrLog with h2 | h2
      · obtain rfl : j = yrLog - 1 := by omega
        rw [os_getD_append_lt (by simp; omega), os_getD_append_ge (by omega), hlen, Nat.sub_self]
        simp only [List.getD_cons_zero]
        rw [← hlast]; exact llast
      · rw [os_getD_append_ge (by simp; omega)]
        simp only [List.length_append, List.length_cons, List.length_nil, hlen]
        rw [show yrLog - 1 + (0 + 1) = yrLog by omega, List.getD_eq_getElem?_getD,
          List.getElem?_replicate, ite_pos' (by omega)]
        have := hZ (j - yrLog) (by omega)
        simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
        rw [show yrLog + (j - yrLog) = j by omega, this.1, word_zero] at this
        exact this.2

end
end LeanVM.Guest.B1
