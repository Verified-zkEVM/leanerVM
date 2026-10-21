/-
  LeanVM.Guest.B1.Comp.OpeningOod

  `__loop9` and `opening_ood_point` over a completeness model.
-/

module

public import LeanVM.Guest.B1.Comp.FsBlocks
public import LeanVM.Guest.B1.Comp.Digest.Common
public import LeanVM.Guest.B1.OpeningOod

/-!
# `opening_ood_point` over a completeness model

The backward half of `opening_ood_point_iff` over a `CompModel`: the `m` squeezes of
`sampleN m`, every one answered by the model (`sqAllM_sqAt`), their states `sqAt` stored in the
scratch run (`OodScratchC`, the deployed `OodScratch` at `CompModel.deployed`), each loop
iteration's row the model's (`holdsB_squeezeT_comp`): `loop9_step_bwdC`, `loop9_bodies_bwdC`,
`opening_ood_point_comp` from `MeaningOpeningOodPointComp CM`, and the form at a given buffer
`opening_ood_point_completeC` (`opening_ood_point_complete`). At `CompModel.deployed` the deployed
backward direction (`opening_ood_point_of_comp`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.E2E.Complete

@[expose] public section

/-- **`sampleN` in an answered run, whole**: the challenges and the state, every squeeze answered. -/
theorem RunsToM.sampleN_sqAll {M : HashModel} {m : ℕ} {cv cv' : Digest} {xs rs : List E}
    (h : RunsToM M (Prog.sampleN m) cv xs rs cv') : xs = [] ∧ sqAllM M m cv = some (rs, cv') := by
  rw [← Prog.bind_ret (Prog.sampleN m)] at h
  obtain ⟨cs, c, hc, h⟩ := RunsToM.sampleN_inv (by simpa using h)
  obtain ⟨rfl, rfl, rfl⟩ := h.ret_inv
  exact ⟨rfl, hc⟩

/-! ## `__loop9` -/

/-- The body of `__loop9` at `x` over a model: the state at `states·x²` is a digest's, its squeeze
the model's answer, whose challenge goes to `point·x` and whose state after it (`Loop9Body`). -/
def Loop9BodyC (M : HashModel) (rd : Reader) (st point x : E) : Prop :=
  ∃ cv d, LoadHolds rd (st * x * x) 0 (digestScalars cv).1 ∧
    LoadHolds rd (st * x * x) 1 (digestScalars cv).2 ∧ sqCvM M cv = some d ∧
    LoadHolds rd (point * x) 0 (challengeOf d) ∧
    LoadHolds rd (st * x * x) 2 (digestScalars d).1 ∧
    LoadHolds rd (st * x * x) 3 (digestScalars d).2

/-- One iteration of `__loop9` over a completeness model, backward (`loop9_step`'s backward half). -/
theorem loop9_step_bwdC {CM : CompModel} (rd : Reader) (N st point x : E)
    (h : Loop9BodyC CM.hm rd st point x) (hK : IsInK (x * gen + N))
    (hcall : x * gen + N ≠ 0 →
      coreProgram.RelB CM.sem rd "__loop9" (x * gen :: [N, st, point]) []) :
    ∃ fn, coreProgram.find? "__loop9" = some fn ∧
      fn.SemB CM.sem (coreProgram.RelB CM.sem rd) rd (x :: [N, st, point]) [] := by
  refine ⟨_, find_loop9, ?_⟩
  obtain ⟨cv, d, l6, l7, hd, l23, l24, l25⟩ := h
  simp only [Fn.SemB]
  rw [show Fn.params Data.core39 = [.n 0, .n 1, .n 2, .n 3] from rfl, core39_body]
  refine ⟨setl (setv (setl (Val.ofArgs [x, N, st, point]) 4
    [st * x, st * x * x, (digestScalars cv).1, (digestScalars cv).2, (digestScalars cv).1,
      (digestScalars cv).2]) 10 14 (sqValsD d)) 24
    [sqValsD d 5, sqValsD d 6, point * x, gen, x * gen, x * gen + N, gen, x * gen], ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil]
    b1_look
  simp only [holdsListB_append, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons,
    List.map_nil, and_true, word_gen]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, holdsB_squeezeT_comp _ _ _ ⟨⟨cv, d, ?_, hd, fun k hk => ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  all_goals (try b1_look)
  · exact l6
  · exact l7
  · exact l23
  · exact l24
  · exact l25
  · exact hK
  · exact hcall

/-! ## `opening_ood_point` -/

/-- The states of the run over a model, after each squeeze (`OodScratch`). -/
def OodScratchC (M : HashModel) (rd : Reader) (p : E) (cv : Digest) (m : ℕ) : Prop :=
  ∀ j ≤ m, LoadHolds rd p (2 * j) (digestScalars (sqAt M cv j)).1 ∧
    LoadHolds rd p (2 * j + 1) (digestScalars (sqAt M cv j)).2

theorem oodScratchC_deployed {rd : Reader} {p : E} {cv : Digest} {m : ℕ} :
    OodScratchC CompModel.deployed.hm rd p cv m ↔ OodScratch rd p cv m := by
  simp only [OodScratchC, OodScratch, sqAt_hm_deployed]

/-- **The loop's bodies over a model, backward** (`loop9_bodies_iff`'s backward half): the
scratch holding the answered states and the challenges read at `point`. -/
theorem loop9_bodies_bwdC {M : HashModel} (rd : Reader) (st point : E) {m : ℕ} {cv c : Digest}
    {cs : List E} (hsq : sqAllM M m cv = some (cs, c)) (hst : OodScratchC M rd st cv m)
    (hpt : ReadsAt rd point cs) : ∀ j < m, Loop9BodyC M rd st point (gen ^ j) := by
  obtain ⟨hs, hcs, -⟩ := sqAllM_sqAt hsq
  have hx : ∀ j k w, LoadHolds rd (st * gen ^ j * gen ^ j) k w ↔ LoadHolds rd st (2 * j + k) w :=
    fun j k w => by rw [mul_assoc, ← pow_add, loadHolds_mul_gen_pow, ← two_mul]
  have hp : ∀ j w, LoadHolds rd (point * gen ^ j) 0 w ↔ LoadHolds rd point j w :=
    fun j w => by rw [loadHolds_mul_gen_pow, Nat.add_zero]
  intro j hj
  obtain ⟨b0, b1⟩ := hst j (by omega)
  obtain ⟨c0, c1⟩ := hst (j + 1) (by omega)
  have r := hpt j (by rw [hcs, List.length_map, List.length_range]; exact hj)
  simp only [hcs, List.getElem_map, List.getElem_range] at r
  rw [show 2 * (j + 1) = 2 * j + 2 by ring] at c0 c1
  rw [show 2 * j + 2 + 1 = 2 * j + 3 by ring] at c1
  refine ⟨sqAt M cv j, sqAt M cv (j + 1), (hx j 0 _).mpr (by simpa using b0), (hx j 1 _).mpr b1,
    hs j hj, (hp j _).mpr r, (hx j 2 _).mpr c0, (hx j 3 _).mpr c1⟩

/-- **`opening_ood_point` over a completeness model** (`MeaningOpeningOodPoint`, the squeezes
answered by the model, the scratch run holding their states). -/
def MeaningOpeningOodPointComp (CM : CompModel) (rd : Reader) : List E → List E → Prop
  | [fs0, fs1, point, ng], rets =>
      ∃ m < ordG, ng = gen ^ m ∧ ∃ p,
        (m = 0 ∧ LoadHolds rd p 0 fs0 ∧ LoadHolds rd p 1 fs1 ∧ rets = [fs0, fs1]) ∨
        (0 < m ∧ ∃ cv rs cv', (fs0, fs1) = digestScalars cv ∧
          RunsToM CM.hm (Prog.sampleN m) cv [] rs cv' ∧
          ReadsAt rd point rs ∧ OodScratchC CM.hm rd p cv m ∧
          rets = [(digestScalars cv').1, (digestScalars cv').2])
  | _, _ => False

theorem meaningOpeningOodPointComp_deployed (rd : Reader) (args rets : List E) :
    MeaningOpeningOodPointComp CompModel.deployed rd args rets ↔
      MeaningOpeningOodPoint rd args rets := by
  unfold MeaningOpeningOodPointComp MeaningOpeningOodPoint
  split <;> try simp only [runsToM_hm_deployed, oodScratchC_deployed]

/-- **`opening_ood_point` is complete over a completeness model** (G:927-941). -/
theorem opening_ood_point_comp {CM : CompModel} (rd : Reader) (args rets : List E)
    (hm : MeaningOpeningOodPointComp CM rd args rets) :
    coreProgram.RelB CM.sem rd "opening_ood_point" args rets := by
  obtain ⟨fs0, fs1, point, ng, rfl⟩ : ∃ fs0 fs1 point ng, args = [fs0, fs1, point, ng] := by
    match args, hm with
    | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
  obtain ⟨m, hm, hN, p, h⟩ := hm
  have hcl : (IsInK (1 + ng) ∧
      (1 + ng ≠ 0 → coreProgram.RelB CM.sem rd "__loop9" [1, ng, p, point] [])) ∧
      LoadHolds rd p 0 fs0 ∧ LoadHolds rd p 1 fs1 ∧
      LoadHolds rd p (2 * m) (rets.getD 0 0) ∧ LoadHolds rd p (2 * m + 1) (rets.getD 1 0) ∧
      rets = [rets.getD 0 0, rets.getD 1 0] := by
    rcases h with ⟨rfl, l0, l1, rfl⟩ | ⟨h0, cv, rs, cv', hcv, hrun, hpt, hst, rfl⟩
    · exact ⟨Digest.guarded_loopB_bwd (B := Loop9BodyC CM.hm rd p point)
        (fun x hB hK hc => loop9_step_bwdC rd ng p point x hB hK hc) hN
        (fun j hj => absurd hj (Nat.not_lt_zero j)), l0, l1, l0, l1, rfl⟩
    · obtain ⟨-, hsq⟩ := hrun.sampleN_sqAll
      obtain ⟨-, -, hc'⟩ := sqAllM_sqAt hsq
      obtain ⟨s0, s1⟩ := hst 0 (by omega)
      rw [show sqAt CM.hm cv 0 = cv from rfl, Nat.mul_zero] at s0 s1
      obtain ⟨t0, t1⟩ := hst m le_rfl
      rw [← hc'] at t0 t1
      refine ⟨Digest.guarded_loopB_bwd (B := Loop9BodyC CM.hm rd p point)
        (fun x hB hK hc => loop9_step_bwdC rd ng p point x hB hK hc) hN
        (loop9_bodies_bwdC rd p point hsq hst hpt), ?_, ?_, t0, t1, rfl⟩
      · rw [show fs0 = (digestScalars cv).1 from congrArg Prod.fst hcv]; exact s0
      · rw [show fs1 = (digestScalars cv).2 from congrArg Prod.snd hcv]; exact s1
  obtain ⟨⟨hK, hcall⟩, l0, l1, l13, l14, hret⟩ := hcl
  have hx : ∀ k w, LoadHolds rd (p * ng * ng) k w ↔ LoadHolds rd p (2 * m + k) w := by
    intro k w
    rw [hN, mul_assoc, ← pow_add, loadHolds_mul_gen_pow, ← two_mul]
  rw [relB_iff_sem find_opening_ood_point,
    show Fn.params Data.core9 = [.n 0, .n 1, .n 2, .n 3] from rfl,
    show Fn.body Data.core9 = Data.core9.body from rfl, Data.core9.body]
  simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, word_one,
    word_gen, true_and]
  refine ⟨setl (Val.ofArgs [fs0, fs1, point, ng]) 4 [gen, ng * gen, ng * gen * (ng * gen), p,
    1, 1 + ng, 1, p * ng, p * ng * ng, rets.getD 0 0, rets.getD 1 0], ?_, ?_⟩
  · b1_look
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals (try b1_look)
    · exact l0
    · exact l1
    · exact hK
    · exact hcall
    · exact (hx 0 _).mpr l13
    · exact (hx 1 _).mpr l14
    · exact hret.symm

/-- `MeaningOpeningOodPointComp` at the state buffer `p` (`MeaningOpeningOodPointAt`). -/
def MeaningOpeningOodPointAtComp (CM : CompModel) (rd : Reader) (p : E) : List E → List E → Prop
  | [fs0, fs1, point, ng], rets =>
      ∃ m < ordG, ng = gen ^ m ∧
        ((m = 0 ∧ LoadHolds rd p 0 fs0 ∧ LoadHolds rd p 1 fs1 ∧ rets = [fs0, fs1]) ∨
        (0 < m ∧ ∃ cv rs cv', (fs0, fs1) = digestScalars cv ∧
          RunsToM CM.hm (Prog.sampleN m) cv [] rs cv' ∧
          ReadsAt rd point rs ∧ OodScratchC CM.hm rd p cv m ∧
          rets = [(digestScalars cv').1, (digestScalars cv').2]))
  | _, _ => False

/-- **`opening_ood_point` is complete over a completeness model at a given buffer**
(`opening_ood_point_complete`). -/
theorem opening_ood_point_completeC {CM : CompModel} (rd : Reader) (p : E) (args rets : List E)
    (h : MeaningOpeningOodPointAtComp CM rd p args rets) :
    coreProgram.RelB CM.sem rd "opening_ood_point" args rets :=
  opening_ood_point_comp rd args rets (by
    match args, h with
    | [_, _, _, _], ⟨m, hm, hn, hb⟩ => exact ⟨m, hm, hn, p, hb⟩)

/-! ## At the deployed model -/

theorem opening_ood_point_of_comp (rd : Reader) (args rets : List E)
    (h : MeaningOpeningOodPoint rd args rets) :
    coreProgram.Rel rd "opening_ood_point" args rets := by
  rw [← relB_deployed]
  exact opening_ood_point_comp (CM := CompModel.deployed) rd args rets
    ((meaningOpeningOodPointComp_deployed rd args rets).mpr h)

end
end LeanVM.Guest.B1
