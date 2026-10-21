/-
  LeanVM.Guest.B1.Comp.FiatShamir

  The compiled Fiat-Shamir functions over a completeness model: each relation holds under the
  model's semantics when the model answers the hashes of the specification's run.
-/

module

public import LeanVM.Guest.B1.Comp.FsBlocks
public import LeanVM.Guest.B1.FiatShamir

/-!
# The compiled Fiat-Shamir functions over a completeness model

The backward halves of `FiatShamir.lean`'s iffs over a `CompModel`, from the meanings over the
model's answers `CM.hm` (the run every hash of which the model answers, `RunsToM`):

| function | lemma | meaning |
|---|---|---|
| `sumcheck_round4` | `sumcheck_round4_comp` | `MeaningSumcheckRound4With CM.hm` (W2's) |
| `sumcheck_round5` | `sumcheck_round5_comp` | `MeaningSumcheckRound5Comp CM` |
| `opening_fold` | `opening_fold_comp` | `MeaningOpeningFoldComp CM` |

Each answered run is taken apart (`RunsToM.readE_inv`, …) into its answered steps, which give
the honest values with the answered digests (`fsValsD`, `sqValsD`) and the blocks' rows
(`holdsB_fsNextT_comp`, `holdsB_squeezeT_comp`). At `CompModel.deployed` the meanings are the
deployed ones and each lemma gives the deployed backward direction (`…_of_comp`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.E2E.Complete

@[expose] public section

/-! ## `sumcheck_round4` -/

/-- The answered steps of `roundPoly 4`'s run. -/
theorem runsToM_roundPoly4_inv {M : HashModel} {cv cv' : Digest} {claim c0 c2 c3 claim' r : E}
    (h : RunsToM M (roundPoly 4 claim none) cv [c0, c2, c3] (claim', r) cv') :
    ∃ d1 d2 d3, obsCvM M cv c0 = some d1 ∧ obsCvM M d1 c2 = some d2 ∧
      obsCvM M d2 c3 = some d3 ∧ sqCvM M d3 = some cv' ∧ r = challengeOf cv' ∧
      claim' = polyEval [c0, claim + (c2 + c3), c2, c3] (challengeOf cv') := by
  unfold roundPoly sumcheckRoundPoly at h
  simp only [Prog.bind_eq, Prog.pure_eq] at h
  simp only [Prog.bind_assoc, Prog.ret_bind] at h
  obtain ⟨x, zs, d1, hxs, hd1, h⟩ := h.readE_inv
  obtain ⟨rfl, rfl⟩ := List.cons.inj hxs
  obtain ⟨ys, zs, d3, hys, hl, hd3, h⟩ := h.readN_inv
  have hl : ys.length = 2 := hl
  obtain rfl : zs = [] := by
    have := congrArg List.length hys
    simp only [List.length_append, hl, List.length_cons, List.length_nil] at this
    exact List.eq_nil_of_length_eq_zero (by omega)
  rw [List.append_nil] at hys
  subst hys
  obtain ⟨d4, hd4, h⟩ := h.sampleE_inv
  obtain ⟨-, hv, rfl⟩ := h.ret_inv
  obtain ⟨d2, hd2, hd3⟩ := Option.bind_eq_some_iff.mp hd3
  simp only [obsAllM] at hd3
  obtain ⟨d3', hd3', he⟩ := Option.bind_eq_some_iff.mp hd3
  obtain rfl := Option.some.inj he
  simp only [Prod.mk.injEq] at hv
  refine ⟨d1, d2, d3', hd1, hd2, hd3', hd4, hv.2, ?_⟩
  rw [hv.1]
  simp only [sumE, List.foldl, zero_add]

/-- **`sumcheck_round4` is complete over a completeness model** (G:845-857; TRIAGE #25): when the
model answers the round's run, the relation holds under the model's semantics. -/
theorem sumcheck_round4_comp {CM : CompModel} (rd : Reader) (args rets : List E)
    (hm : MeaningSumcheckRound4With CM.hm rd args rets) :
    coreProgram.RelB CM.sem rd "sumcheck_round4" args rets := by
  obtain ⟨s0, s1, cur, claim, rfl⟩ : ∃ s0 s1 cur claim, args = [s0, s1, cur, claim] := by
    match args, hm with
    | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
  obtain ⟨cv, c0, c2, c3, claim', r, cv', hcv, hrd, hrun, hret⟩ := hm
  obtain ⟨d1, d2, d3, hd1, hd2, hd3, hd4, rfl, rfl⟩ := runsToM_roundPoly4_inv hrun
  subst hret
  have hl : ∀ k (hk : k < 3), LoadHolds rd cur k [c0, c2, c3][k] := hrd
  set r := challengeOf cv'
  rw [relB_iff_sem find_sumcheck_round4, core6_body, core6_params]
  refine ⟨setl (setv (setl (setv (setl (setv (setl (setv (setl (Val.ofArgs [s0, s1, cur, claim])
    4 [s0, s1, c0]) 7 14 (fsValsD c0 d1 1)) 21 [c2]) 22 14 (fsValsD c2 d2 1)) 36 [c3]) 37 14
    (fsValsD c3 d3 1)) 51 [claim + c2, claim + c2 + c3]) 53 14 (sqValsD cv')) 67
    [sqValsD cv' 5, sqValsD cv' 6, word 8 0 0, cur * word 8 0 0, cur * word 8 0 0, r * c3,
      c2 + r * c3, r * (c2 + r * c3), claim + c2 + c3 + r * (c2 + r * c3),
      r * (claim + c2 + c3 + r * (c2 + r * c3)), c0 + r * (claim + c2 + c3 + r * (c2 + r * c3)),
      r], ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil]
    b1_look
  simp only [holdsListB_append, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons,
    List.map_nil]
  refine ⟨?_, ?_, holdsB_fsNextT_comp _ _ _ _ _ ⟨⟨?_, cv, d1, ?_, ?_, ?_⟩,
    holdsB_fsNextT_comp _ _ _ _ _ ⟨⟨?_, d1, d2, ?_, ?_, ?_⟩,
    holdsB_fsNextT_comp _ _ _ _ _ ⟨⟨?_, d2, d3, ?_, ?_, ?_⟩, ?_, ?_,
    holdsB_squeezeT_comp _ _ _ ⟨⟨d3, cv', ?_, hd4, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩⟩⟩⟩⟩
  all_goals try (intro k hk1 hk2)
  all_goals try (intro k hk1)
  all_goals (try b1_look)
  · exact hl 0 (by decide)
  · exact hcv
  · exact hd1
  · exact hl 1 (by decide)
  · rfl
  · exact hd2
  · exact hl 2 (by decide)
  · rfl
  · exact hd3
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp only [sqValsD, sqStateValsD, word_eight, polyEval, List.foldr, zero_mul, zero_add,
      List.cons.injEq, and_true, true_and, r]
    ring

/-! ## `sumcheck_round5` -/

/-- **`sumcheck_round5` over a completeness model** (`MeaningSumcheckRound5`, every hash answered by
the model). -/
def MeaningSumcheckRound5Comp (CM : CompModel) (rd : Reader) : List E → List E → Prop
  | [s0, s1, cur, claim, e], rets =>
      ∃ cv c1 c2 c3 c4 claim' r cv', (s0, s1) = digestScalars cv ∧
        ReadsAt rd cur [c1, c2, c3, c4] ∧
        RunsToM CM.hm (roundPoly 5 claim (some e)) cv [c1, c2, c3, c4] (claim', r) cv' ∧
        rets = [(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ 4, claim', r]
  | _, _ => False

theorem meaningSumcheckRound5Comp_deployed (rd : Reader) (args rets : List E) :
    MeaningSumcheckRound5Comp CompModel.deployed rd args rets ↔
      MeaningSumcheckRound5 rd args rets := by
  unfold MeaningSumcheckRound5Comp MeaningSumcheckRound5
  split <;> try simp only [runsToM_hm_deployed]

/-- The answered steps of `roundPoly 5`'s run. -/
theorem runsToM_roundPoly5_inv {M : HashModel} {cv cv' : Digest} {claim e c1 c2 c3 c4 claim' r : E}
    (h : RunsToM M (roundPoly 5 claim (some e)) cv [c1, c2, c3, c4] (claim', r) cv') :
    ∃ d1 d2 d3 d4, obsCvM M cv c1 = some d1 ∧ obsCvM M d1 c2 = some d2 ∧
      obsCvM M d2 c3 = some d3 ∧ obsCvM M d3 c4 = some d4 ∧ sqCvM M d4 = some cv' ∧
      r = challengeOf cv' ∧
      claim' = polyEval [claim + e * (c1 + c2 + c3 + c4), c1, c2, c3, c4] (challengeOf cv') := by
  unfold roundPoly sumcheckRoundPoly at h
  simp only [Prog.bind_eq, Prog.pure_eq] at h
  simp only [Prog.bind_assoc, Prog.ret_bind] at h
  obtain ⟨d4, hd4, h⟩ := RunsToM.readN_inv' (xs := [c1, c2, c3, c4]) (zs := []) rfl h
  obtain ⟨d5, hd5, h⟩ := h.sampleE_inv
  obtain ⟨-, hv, rfl⟩ := h.ret_inv
  obtain ⟨d1, hd1, hd4⟩ := obsAllM_cons_some hd4
  obtain ⟨d2, hd2, hd4⟩ := obsAllM_cons_some hd4
  obtain ⟨d3, hd3, hd4⟩ := obsAllM_cons_some hd4
  obtain ⟨d4', hd4', hd4⟩ := obsAllM_cons_some hd4
  obtain rfl := obsAllM_nil_some hd4
  simp only [Prod.mk.injEq] at hv
  refine ⟨d1, d2, d3, _, hd1, hd2, hd3, hd4', hd5, hv.2, ?_⟩
  rw [hv.1]
  simp only [sumE, List.foldl, zero_add]

/-- **`sumcheck_round5` is complete over a completeness model** (G:860-872; TRIAGE #26). -/
theorem sumcheck_round5_comp {CM : CompModel} (rd : Reader) (args rets : List E)
    (hm : MeaningSumcheckRound5Comp CM rd args rets) :
    coreProgram.RelB CM.sem rd "sumcheck_round5" args rets := by
  obtain ⟨s0, s1, cur, claim, e, rfl⟩ : ∃ s0 s1 cur claim e,
      args = [s0, s1, cur, claim, e] := by
    match args, hm with
    | [a, b, c, d, f], _ => exact ⟨a, b, c, d, f, rfl⟩
  obtain ⟨cv, c1, c2, c3, c4, claim', r, cv', hcv, hrd, hrun, hret⟩ := hm
  obtain ⟨d1, d2, d3, d4, hd1, hd2, hd3, hd4, hd5, rfl, rfl⟩ := runsToM_roundPoly5_inv hrun
  subst hret
  have hl : ∀ k (hk : k < 4), LoadHolds rd cur k [c1, c2, c3, c4][k] := hrd
  set r := challengeOf cv'
  set c0 := claim + e * (c1 + c2 + c3 + c4)
  rw [relB_iff_sem find_sumcheck_round5, core7_body, core7_params]
  refine ⟨setl (setv (setv (setl (setv (setl (setv (setl (setv (setl
    (Val.ofArgs [s0, s1, cur, claim, e]) 5 [s0, s1, c1]) 8 14 (fsValsD c1 d1 1)) 22 [c2]) 23 14
    (fsValsD c2 d2 1)) 37 [c3]) 38 14 (fsValsD c3 d3 1)) 52 [c4]) 53 14 (fsValsD c4 d4 1)) 67
    14 (sqValsD cv')) 81
    [c1 + c2, c1 + c2 + c3, c1 + c2 + c3 + c4, e * (c1 + c2 + c3 + c4), c0, sqValsD cv' 5,
      sqValsD cv' 6, word 16 0 0, cur * word 16 0 0, cur * word 16 0 0, r * c4, c3 + r * c4,
      r * (c3 + r * c4), c2 + r * (c3 + r * c4), r * (c2 + r * (c3 + r * c4)),
      c1 + r * (c2 + r * (c3 + r * c4)), r * (c1 + r * (c2 + r * (c3 + r * c4))),
      c0 + r * (c1 + r * (c2 + r * (c3 + r * c4))), r], ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil]
    b1_look
  simp only [holdsListB_append, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons,
    List.map_nil]
  refine ⟨?_, ?_, holdsB_fsNextT_comp _ _ _ _ _ ⟨⟨?_, cv, d1, ?_, ?_, ?_⟩,
    holdsB_fsNextT_comp _ _ _ _ _ ⟨⟨?_, d1, d2, ?_, ?_, ?_⟩,
    holdsB_fsNextT_comp _ _ _ _ _ ⟨⟨?_, d2, d3, ?_, ?_, ?_⟩,
    holdsB_fsNextT_comp _ _ _ _ _ ⟨⟨?_, d3, d4, ?_, ?_, ?_⟩,
    holdsB_squeezeT_comp _ _ _ ⟨⟨d4, cv', ?_, hd5, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩⟩⟩⟩⟩
  all_goals try (intro k hk1 hk2)
  all_goals try (intro k hk1)
  all_goals (try b1_look)
  · exact hl 0 (by decide)
  · exact hcv
  · exact hd1
  · exact hl 1 (by decide)
  · rfl
  · exact hd2
  · exact hl 2 (by decide)
  · rfl
  · exact hd3
  · exact hl 3 (by decide)
  · rfl
  · exact hd4
  · rfl
  iterate 6 (· rfl)
  simp only [sqValsD, sqStateValsD, word_sixteen, polyEval, List.foldr, zero_mul, zero_add,
    List.cons.injEq, and_true, true_and, r, c0]
  ring

/-! ## `opening_fold` -/

/-- **`opening_fold` over a completeness model** (`MeaningOpeningFold`, every hash answered by the
model). -/
def MeaningOpeningFoldComp (CM : CompModel) (rd : Reader) : List E → List E → Prop
  | [s0, s1, cur, c0, c1, c2], rets =>
      ∃ cv d0 d2 r t q cv', (s0, s1) = digestScalars cv ∧ ReadsAt rd cur [d0, d2] ∧
        RunsToM CM.hm (foldStep [c0, c1, c2]) cv [d0, d2] (r, t, q) cv' ∧
        rets = [(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ 2, t, d0, d2, r]
  | _, _ => False

theorem meaningOpeningFoldComp_deployed (rd : Reader) (args rets : List E) :
    MeaningOpeningFoldComp CompModel.deployed rd args rets ↔ MeaningOpeningFold rd args rets := by
  unfold MeaningOpeningFoldComp MeaningOpeningFold
  split <;> try simp only [runsToM_hm_deployed]

/-- The answered steps of `foldStep`'s run. -/
theorem runsToM_foldStep_inv {M : HashModel} {cv cv' : Digest} {c0 c1 c2 d0 d2 r t : E}
    {q : List E} (h : RunsToM M (foldStep [c0, c1, c2]) cv [d0, d2] (r, t, q) cv') :
    ∃ e1 e2, sqCvM M cv = some e1 ∧ obsCvM M e1 d0 = some e2 ∧ obsCvM M e2 d2 = some cv' ∧
      r = challengeOf e1 ∧ t = polyEval [c0, c1, c2] (challengeOf e1) ∧
      q = [d0, polyEval [c0, c1, c2] (challengeOf e1) + d2, d2] := by
  unfold foldStep sumcheckRoundPoly at h
  simp only [Prog.bind_eq, Prog.pure_eq] at h
  simp only [Prog.bind_assoc, Prog.ret_bind] at h
  obtain ⟨e1, he1, h⟩ := h.sampleE_inv
  obtain ⟨x, zs, e2, hxs, he2, h⟩ := h.readE_inv
  obtain ⟨rfl, rfl⟩ := List.cons.inj hxs
  obtain ⟨e3, he3, h⟩ := RunsToM.readN_inv' (xs := [d2]) (zs := []) rfl h
  obtain ⟨-, hv, rfl⟩ := h.ret_inv
  obtain ⟨e3', he3', he3⟩ := obsAllM_cons_some he3
  obtain rfl := obsAllM_nil_some he3
  simp only [Prod.mk.injEq] at hv
  obtain ⟨rfl, rfl, rfl⟩ := hv
  refine ⟨e1, e2, he1, he2, he3', rfl, rfl, ?_⟩
  simp only [sumE, List.foldl, zero_add]

/-- **`opening_fold` is complete over a completeness model** (G:917-924; TRIAGE #31). -/
theorem opening_fold_comp {CM : CompModel} (rd : Reader) (args rets : List E)
    (hm : MeaningOpeningFoldComp CM rd args rets) :
    coreProgram.RelB CM.sem rd "opening_fold" args rets := by
  obtain ⟨s0, s1, cur, c0, c1, c2, rfl⟩ : ∃ s0 s1 cur c0 c1 c2,
      args = [s0, s1, cur, c0, c1, c2] := by
    match args, hm with
    | [a, b, c, d, f, g], _ => exact ⟨a, b, c, d, f, g, rfl⟩
  obtain ⟨cv, d0, d2, r, t, q, cv', hcv, hrd, hrun, hret⟩ := hm
  obtain ⟨cv1, cv2, h1, h2, h3, rfl, rfl, rfl⟩ := runsToM_foldStep_inv hrun
  subst hret
  have hl : ∀ k (hk : k < 2), LoadHolds rd cur k [d0, d2][k] := hrd
  set r := challengeOf cv1
  rw [relB_iff_sem find_opening_fold, core8_body, core8_params]
  refine ⟨setl (setv (setl (setv (setl (setv (setl (Val.ofArgs [s0, s1, cur, c0, c1, c2]) 6
    [s0, s1]) 8 14 (sqValsD cv1)) 22 [c2 * r, c2 * r + c1, (c2 * r + c1) * r,
      (c2 * r + c1) * r + c0, d0]) 27 14 (fsValsD d0 cv2 1)) 41 [d2]) 42 14 (fsValsD d2 cv' 1)) 56
    [fsValsD d2 cv' 1 12, fsValsD d2 cv' 1 13, word 4 0 0, cur * word 4 0 0, cur * word 4 0 0,
      (c2 * r + c1) * r + c0, d0, d2, r], ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil]
    b1_look
  simp only [holdsListB_append, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons,
    List.map_nil]
  refine ⟨?_, ?_, holdsB_squeezeT_comp _ _ _ ⟨⟨cv, cv1, ?_, h1, ?_⟩, ?_, ?_, ?_, ?_,
    holdsB_fsNextT_comp _ _ _ _ _ ⟨⟨?_, cv1, cv2, ?_, ?_, ?_⟩,
    holdsB_fsNextT_comp _ _ _ _ _ ⟨⟨?_, cv2, cv', ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩⟩⟩⟩
  all_goals try (intro k hk1 hk2)
  all_goals try (intro k hk1)
  all_goals (try b1_look)
  · exact hcv
  · rfl
  · rfl
  · exact hl 0 (by decide)
  · rfl
  · exact h2
  · exact hl 1 (by decide)
  · rfl
  · exact h3
  · rfl
  · simp only [fsValsD, word_four, polyEval, List.foldr, zero_mul, zero_add, r]

/-! ## At the deployed model -/

theorem sumcheck_round4_of_comp (rd : Reader) (args rets : List E)
    (h : MeaningSumcheckRound4 rd args rets) : coreProgram.Rel rd "sumcheck_round4" args rets := by
  rw [← relB_deployed]
  exact sumcheck_round4_comp (CM := CompModel.deployed) rd args rets
    ((meaningSumcheckRound4With_deployed rd args rets).mpr h)

theorem sumcheck_round5_of_comp (rd : Reader) (args rets : List E)
    (h : MeaningSumcheckRound5 rd args rets) : coreProgram.Rel rd "sumcheck_round5" args rets := by
  rw [← relB_deployed]
  exact sumcheck_round5_comp (CM := CompModel.deployed) rd args rets
    ((meaningSumcheckRound5Comp_deployed rd args rets).mpr h)

theorem opening_fold_of_comp (rd : Reader) (args rets : List E)
    (h : MeaningOpeningFold rd args rets) : coreProgram.Rel rd "opening_fold" args rets := by
  rw [← relB_deployed]
  exact opening_fold_comp (CM := CompModel.deployed) rd args rets
    ((meaningOpeningFoldComp_deployed rd args rets).mpr h)

end
end LeanVM.Guest.B1
