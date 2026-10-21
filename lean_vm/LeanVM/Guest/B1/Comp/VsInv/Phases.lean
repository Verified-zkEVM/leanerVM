/-
  LeanVM.Guest.B1.Comp.VsInv.Phases

  The deferring verifier's phases over a hash model, backward: Flock, GKR, the tables, the
  announced sizes, the stack's root, the ring switch, and an accepting deferred run.
-/

module

public import LeanVM.Guest.B1.Comp.VsInv.Run
public import LeanVM.Guest.B1.VerifySub.Inv6a

/-!
# The phases over a hash model, backward

`Inv2.lean`–`Inv4.lean` and `Inv6a.lean` over a hash model `M`, by the same proofs at `RunsM M`:

* `vs_flock_invM`, `vs_gkr_invM`, `vs_tables_invM`: the shapes of Flock's, GKR's and the tables'
  outputs at the claimed values, and their runs over the model at every evaluation taking the
  claimed value (`MatricesAtM`, `BytecodeAtM`);
* `vs_readSizes_invM` (the announced words absorbed by the model, `obsAllM`), `vs_commitStack_invM`,
  `vs_ringSwitch_invM` (the ring map's squeezes the model's, `sqAllM`), `vs_announcedM`
  (`announced` is the run's layout and rate);
* `verifyDeferredWith_inv`: a deferring verifier accepting over the model's hash runs its program
  from the seed's answered state to an empty stream and no openings.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {M : HashModel}

/-! ## Flock -/

/-- **Flock's run over the model, backward** (`vs_flock_inv`). -/
theorem vs_flock_invM {c : FixedClaims} {logN : ℕ} {s s' : St} {out : List E × List E}
    (h : RunsM M (verifyFlock (.claimed c) logN) s out s') :
    ∃ (zSkip : E) (chi rc : List E), out = (rc.reverse ++ chi.drop flockNumLincheckRounds, c.slices) ∧
      chi.length = 7 + (logN - flockKSkip - 7) ∧ rc.length = flockNumLincheckRounds ∧
      c.slices.length = kBits ∧ zSkip = c.zSkip ∧ chi.take flockNumLincheckRounds = c.rowPoint ∧
      rc.reverse = c.columnPoint ∧
      ∀ ev, MatricesAtM M ev c.alpha c.zSkip c.rowPoint c.columnPoint c.slices c.matrixValue →
        RunsM M (verifyFlock ev logN) s out s' := by
  unfold verifyFlock at h
  obtain ⟨zc, s1, hz, hl⟩ := RunsM.bind_inv h
  -- the zerocheck
  have hzc : zc.chi.length = 7 + (logN - flockKSkip - 7) := by
    unfold verifyFlockZerocheck at hz
    obtain ⟨sm, z1, hsm0, hz⟩ := RunsM.bind_inv hz
    obtain ⟨pc, z2, -, hz⟩ := RunsM.bind_inv hz
    obtain ⟨zs, z3, -, hz⟩ := RunsM.bind_inv hz
    obtain ⟨⟨chi, run⟩, z4, hs, hz⟩ := RunsM.bind_inv hz
    obtain ⟨va, z5, -, hz⟩ := RunsM.bind_inv hz
    obtain ⟨vb, z6, -, hz⟩ := RunsM.bind_inv hz
    obtain ⟨rfl, -⟩ := RunsM.pure_inv hz
    have := RunsM.sumcheck_inv hs
    have hsm : sm.length = logN - flockKSkip - 7 := RunsM.sampleN_length hsm0
    simp only [List.length_map, List.length_append, fixedChallenges_length] at this
    simp only
    omega
  unfold verifyFlockLincheck at hl
  obtain ⟨alpha, t1, ha, hl⟩ := RunsM.bind_inv hl
  obtain ⟨⟨rc, rLc⟩, t2, hsc, hl⟩ := RunsM.bind_inv hl
  obtain ⟨sl, t3, hsl, hl⟩ := RunsM.bind_inv hl
  obtain ⟨mv, t4, hmv, hl⟩ := RunsM.bind_inv hl
  obtain ⟨u, t5, hreq, hl⟩ := RunsM.bind_inv hl
  obtain ⟨hout, rfl⟩ := RunsM.pure_inv hl
  unfold Evaluations.claimed at hmv
  obtain ⟨u', t6, hr2, hmv2⟩ := RunsM.bind_inv hmv
  obtain ⟨⟨e1, e2, e3, e4, e5⟩, rfl⟩ := RunsM.require_inv hr2
  obtain ⟨rfl, rfl⟩ := RunsM.pure_inv hmv2
  subst e1 e5
  have hrc : rc.length = flockNumLincheckRounds := by
    have := RunsM.sumcheck_inv hsc; simpa using this
  refine ⟨zc.zSkip, zc.chi, rc, hout, hzc, hrc, (RunsM.readN_inv hsl).1, e2, e3, e4,
    fun ev hev => ?_⟩
  unfold verifyFlock verifyFlockLincheck
  exact RunsM.bind hz (RunsM.bind ha (RunsM.bind hsc (RunsM.bind hsl (RunsM.bind
    (by rw [e2, e3, e4]; exact hev _) (RunsM.bind hreq (by rw [hout]; exact RunsM.ret _ _))))))

/-! ## GKR -/

theorem vs_gkrStep_invM {step : ℕ} {g g' : GkrState} {s s' : St}
    (h : RunsM M (gkrStep step g) s g' s') :
    g'.point.length = step + g.point.length ∧ g'.values.length = 3 := by
  unfold gkrStep at h
  obtain ⟨cb, s1, -, h⟩ := RunsM.bind_inv h
  obtain ⟨⟨x, cl⟩, s2, hs, h⟩ := RunsM.bind_inv h
  obtain ⟨c0, s3, -, h⟩ := RunsM.bind_inv h
  obtain ⟨c1, s4, -, h⟩ := RunsM.bind_inv h
  obtain ⟨c2, s5, -, h⟩ := RunsM.bind_inv h
  obtain ⟨u, s6, -, h⟩ := RunsM.bind_inv h
  obtain ⟨y, s7, hy, h⟩ := RunsM.bind_inv h
  obtain ⟨rfl, -⟩ := RunsM.pure_inv h
  have h1 := RunsM.sumcheck_inv hs
  have h2 := RunsM.sampleN_length hy
  simp only [List.length_map] at h1
  simp [h1, h2]

theorem vs_gkrLayers_invM : ∀ {n : ℕ} {g g' : GkrState} {s s' : St},
    RunsM M (gkrLayers n g) s g' s' →
    g.values.length = 3 → g'.point.length = n + g.point.length ∧ g'.values.length = 3
  | 0, g, g', s, s', h, hv => by
    unfold gkrLayers at h
    obtain ⟨rfl, -⟩ := RunsM.pure_inv h
    exact ⟨by simp, hv⟩
  | 1, g, g', s, s', h, _ => by
    unfold gkrLayers at h
    obtain ⟨g1, s1, h1, h2⟩ := RunsM.bind_inv h
    obtain ⟨a1, a2⟩ := vs_gkrStep_invM h1
    obtain ⟨b1, b2⟩ := vs_gkrLayers_invM h2 a2
    exact ⟨by omega, b2⟩
  | n + 2, g, g', s, s', h, _ => by
    unfold gkrLayers at h
    split at h
    · obtain ⟨g1, s1, h1, h2⟩ := RunsM.bind_inv h
      obtain ⟨a1, a2⟩ := vs_gkrStep_invM h1
      obtain ⟨b1, b2⟩ := vs_gkrLayers_invM h2 a2
      exact ⟨by omega, b2⟩
    · obtain ⟨g1, s1, h1, h2⟩ := RunsM.bind_inv h
      obtain ⟨a1, a2⟩ := vs_gkrStep_invM h1
      obtain ⟨b1, b2⟩ := vs_gkrLayers_invM h2 a2
      exact ⟨by omega, b2⟩

/-- **GKR's run over the model, backward** (`vs_gkr_inv`). -/
theorem vs_gkr_invM {depth : ℕ} {r : E × List E × List E} {s s' : St}
    (h : RunsM M (gkrPhase depth) s r s') :
    r.1 ≠ 0 ∧ r.2.1.length = depth ∧ r.2.2.length = 3 := by
  unfold gkrPhase verifyGkrGrandProducts at h
  obtain ⟨r0, s0, h, hq⟩ := RunsM.bind_inv h
  obtain ⟨u, s5, hreq, hr⟩ := RunsM.bind_inv hq
  obtain ⟨hne, -⟩ := RunsM.require_inv hreq
  obtain ⟨rfl, -⟩ := RunsM.pure_inv hr
  obtain ⟨sh, s1, -, h⟩ := RunsM.bind_inv h
  obtain ⟨cn, s2, -, h⟩ := RunsM.bind_inv h
  obtain ⟨g, s3, hg, h⟩ := RunsM.bind_inv h
  obtain ⟨rfl, -⟩ := RunsM.pure_inv h
  obtain ⟨a1, a2⟩ := vs_gkrLayers_invM hg rfl
  exact ⟨hne, by simpa using a1, a2⟩

/-! ## The tables -/

theorem claimed_bytecode_invM {c : FixedClaims} {w : List K} {pt : List E} {v : E} {s s' : St}
    (h : RunsM M ((Evaluations.claimed c).bytecode w pt) s v s') :
    pt = c.bytecodePoint ∧ v = c.bytecodeValue ∧ s' = s := by
  by_cases hp : pt = c.bytecodePoint
  · have e : (Evaluations.claimed c).bytecode w pt = Prog.ret c.bytecodeValue := by
      simp [Evaluations.claimed, Prog.require, hp]
    rw [e] at h
    obtain ⟨rfl, rfl⟩ := RunsM.ret_inv h
    exact ⟨hp, rfl, rfl⟩
  · have e : (Evaluations.claimed c).bytecode w pt = Prog.fail := by
      simp [Evaluations.claimed, Prog.require, hp, Prog.bind]
    rw [e] at h
    unfold RunsM at h
    simp [runM, Compile.run, pure] at h

/-- **The tables' run over the model, backward** (`vs_tables_inv`). -/
theorem vs_tables_invM {c : FixedClaims} {layout : Layout} {pi : Digest} {alphas : List E}
    {beta : E} {point values : List E} {s s' : St} {out : BusResult × List ColumnClaim}
    (h : RunsM M (tablesSeg (.claimed c) layout pi alphas beta point values) s out s') :
    point.take layout.logBytecode ++ alphas = c.bytecodePoint ∧
      ∀ ev, BytecodeAtM M ev layout.bytecode c.bytecodePoint c.bytecodeValue →
        RunsM M (tablesSeg ev layout pi alphas beta point values) s out s' := by
  unfold tablesSeg at h
  obtain ⟨bus, s1, hb, h⟩ := RunsM.bind_inv h
  unfold busRest at hb
  obtain ⟨m, t1, hm, hb⟩ := RunsM.bind_inv hb
  obtain ⟨mf, t2, hmf, hb⟩ := RunsM.bind_inv hb
  obtain ⟨bf, t3, hbf, hb⟩ := RunsM.bind_inv hb
  dsimp only at hb
  obtain ⟨bv, t4, hbv, hb4⟩ := RunsM.bind_inv hb
  obtain ⟨e, rfl, rfl⟩ := claimed_bytecode_invM hbv
  refine ⟨e, fun ev hev => ?_⟩
  unfold tablesSeg busRest
  refine RunsM.bind (RunsM.bind hm (RunsM.bind hmf (RunsM.bind hbf ?_))) h
  dsimp only
  exact RunsM.bind (by rw [e]; exact hev _) hb4

/-! ## The announced sizes, the root and the ring switch -/

/-- **The announced sizes over the model, backward** (`vs_readSizes_inv`). -/
theorem vs_readSizes_invM {bytecode : List K} (hb : bytecode.length = 2 ^ 22) {s s' : St}
    {lr : Layout × ℕ} (h : RunsM M (readSizes bytecode) s lr s') :
    ∃ logMem rows rate, lr = (layoutOf bytecode logMem rows, rate) ∧
      s.stream = announce logMem rows rate ++ s'.stream ∧
      obsAllM M s.cv (announce logMem rows rate) = some s'.cv ∧ s'.openings = s.openings ∧
      s'.roots = s.roots ∧ 16 ≤ logMem ∧ logMem ≤ 32 ∧ 1 ≤ rate ∧ rate ≤ 4 ∧ rows.length = 6 ∧
      (∀ n ∈ rows, n ≤ 2 ^ 32) ∧ minStackedLog ≤ (layoutOf bytecode logMem rows).stackLog ∧
      (layoutOf bytecode logMem rows).stackLog ≤ 28 := by
  unfold readSizes at h
  obtain ⟨a, s1, hr, h⟩ := RunsM.bind_inv h
  obtain ⟨u1, s2, hq1, h⟩ := RunsM.bind_inv h
  dsimp only at h
  obtain ⟨u2, s3, hq2, h⟩ := RunsM.bind_inv h
  obtain ⟨L, s4, hlo, h⟩ := RunsM.bind_inv h
  obtain ⟨u3, s5, hq3, h⟩ := RunsM.bind_inv h
  obtain ⟨rfl, rfl⟩ := RunsM.pure_inv h
  obtain ⟨hz, rfl⟩ := RunsM.require_inv hq1
  obtain ⟨⟨hr1, hr2⟩, rfl⟩ := RunsM.require_inv hq2
  obtain ⟨hbl, rfl⟩ := RunsM.liftOption_inv hlo
  obtain ⟨⟨hs1, hs2⟩, rfl⟩ := RunsM.require_inv hq3
  obtain ⟨hal, hs, hc, ho, hro⟩ := RunsM.readN_inv hr
  obtain ⟨h1, h2, h3, h4, rfl⟩ := buildLayout_inv hb hbl
  have ha := announce_of (by rw [hal]; rfl) hz
  refine ⟨_, _, _, rfl, by rw [hs, ← ha], by rw [← ha]; exact hc, ho, hro, h1, h2, hr1, hr2, h3,
    h4, hs1, hs2⟩

/-- **`announced` is the run's layout and rate.** -/
theorem vs_announcedM {bytecode : List K} (hb : bytecode.length = 2 ^ 22) {s s' : St}
    {lr : Layout × ℕ} (h : RunsM M (readSizes bytecode) s lr s') :
    announced bytecode s.stream = some lr := by
  obtain ⟨logMem, rows, rate, rfl, hs, -, -, -, h1, h2, hr1, hr2, hl, hrows, hs1, hs2⟩ :=
    vs_readSizes_invM hb h
  rw [hs]
  exact announced_of_runs (runs_readSizes hb h1 h2 hr1 hr2 hl hrows hs1 (by
    unfold maxStackedLog Whir.maxLogStack; omega) default s'.stream [] [])

/-- **The stack's root over the model, backward** (`vs_commitStack_inv`). -/
theorem vs_commitStack_invM {μ r : ℕ} {s s' : St} {u : Unit}
    (h : RunsM M (commitStack μ r) s u s') :
    ∃ (x0 x1 : E) (root : Digest), (x0, x1) = digestScalars root ∧
      s.stream = x0 :: x1 :: s'.stream ∧ obsAllM M s.cv [x0, x1] = some s'.cv ∧
      s'.openings = s.openings ∧ s'.roots = s.roots ++ [(root, stackShape μ r)] := by
  unfold commitStack at h
  obtain ⟨cfg, s1, hc, h⟩ := RunsM.bind_inv h
  obtain ⟨hcfg, hs1⟩ := RunsM.liftOption_inv hc
  rw [hs1] at h
  cases cfg with
  | nil => unfold RunsM at h; simp [runM, Compile.run, pure] at h
  | cons level levels =>
    obtain ⟨cv, xs, os, roots⟩ := s
    match xs, h with
    | [], h => unfold RunsM at h; simp [Prog.commitP, runM, Compile.run, pure] at h
    | [_], h => unfold RunsM at h; simp [Prog.commitP, runM, Compile.run, pure] at h
    | x0 :: x1 :: xs, h =>
      unfold RunsM at h
      simp only [Prog.commitP] at h
      rw [runM_commit_consV] at h
      obtain ⟨c0, hc0, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨c1, hc1, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · rename_i root hroot
        simp only [runM, Compile.run, pure, Option.some.injEq] at h
        cases h
        refine ⟨x0, x1, root, (digestScalars_digestOfScalars hroot).symm, rfl, ?_, rfl, ?_⟩
        · show (obsCvM M cv x0).bind (fun c ↦ (obsCvM M c x1).bind fun c' ↦ some c') = _
          rw [show obsCvM M cv x0 = some c0 from hc0, Option.bind_some,
            show obsCvM M c0 x1 = some c1 from hc1]
          rfl
        · simp only [stackShape, hcfg]
      · simp at h

/-- **The ring switch over the model, backward**: the ring map's squeezes are the model's. -/
theorem vs_ringSwitch_invM {point s : List E} {st st' : St} {rs : E × (List E → E)}
    (h : RunsM M (ringSwitch point s) st rs st') :
    ∃ mcs, sqAllM M 6 st.cv = some (mcs, st'.cv) ∧ st' = { st with cv := st'.cv } ∧
      rs = (ringTarget s mcs, fun rPrime ↦ ringWeight point rPrime (ringCoefficients mcs)) := by
  unfold ringSwitch at h
  obtain ⟨mcs, s1, h1, h2⟩ := RunsM.bind_inv h
  obtain ⟨rfl, rfl⟩ := RunsM.pure_inv h2
  obtain ⟨hq, hs⟩ := RunsM.sampleN_inv h1
  exact ⟨mcs, hq, hs, rfl⟩

/-! ## The accepting run -/

/-- **A deferring verifier accepting over the model's hash** runs its program from the seed's
answered state to an empty stream and no openings (`verifyDeferred_inv`). -/
theorem verifyDeferredWith_inv {bytecode : List K} {seed pi : Digest} {c : FixedClaims} {π : Proof}
    (h : verifyDeferredWith M.H bytecode seed pi c π = some true) :
    ∃ cv0 s', M.H (digestBytes seed ++ digestBytes pi) = some cv0 ∧
      RunsM M (deferredProgram c bytecode pi) ⟨cv0, π.stream, π.openings, []⟩ true s' ∧
      s'.stream = [] ∧ s'.openings = [] := by
  unfold verifyDeferredWith runProof at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨cv0, h0, o, ho, h⟩ := h
  refine ⟨cv0, ?_⟩
  match o, h with
  | some (true, s'), h =>
    simp only [pure, Option.some.injEq, Bool.and_eq_true, List.isEmpty_iff] at h
    exact ⟨s', h0, ho, h.1, h.2⟩
  | some (false, _), h => simp [pure] at h
  | none, h => simp [pure] at h

end
end LeanVM.Guest.B1.VerifySub
