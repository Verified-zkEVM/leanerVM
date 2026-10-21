/-
  LeanVM.Guest.B1.Comp.Tables.RunInv

  Answered runs over a hash model taken apart: absorbs and squeezes at the model's total hash,
  and the two sumcheck modes round by round.
-/

module

public import LeanVM.Guest.B1.Comp.Basic
public import LeanVM.Guest.B1.Tables.FlockSpecM

/-!
# Answered runs, taken apart

The backward halves of `FlockSpecM.lean`'s runs over a hash model `M`: an answered run's steps
are answered at the model's total hash (`obsCvT`, `sqCvT`).

* `obsAllT`: the words absorbed one by one at the total hash; `ObsAns M cv xs`: each absorb is
  answered; `obsAllM_T`, `obsAllM_of_ans`: an answered `obsAllM` is exactly that.
* `sqAllM_T`: answered squeezes are the iterates of `sqCvT`.
* `RunsToM.sumcheck_eq_inv`, `RunsToM.sumcheck_plain_inv`: an answered run of a sumcheck then `f`
  reads two words per round (`pairAt`), every round's hashes answered (`RoundOk`), the claims and
  states those of `scStT`, `lcStT` (`runs_sumcheck_eqM`, `runs_sumcheck_plainM` backward).
* `RunsToM.require_inv`, `RunsToM.fail_elim`: a `require` passed.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {M : HashModel}

/-! ## Absorbs and squeezes at the total hash -/

variable (M) in
/-- The words `xs` absorbed one by one from `cv` at the model's total hash (`obsAll`). -/
def obsAllT (cv : Digest) (xs : List E) : Digest := xs.foldl (obsCvT M) cv

@[simp] theorem obsAllT_nil (cv : Digest) : obsAllT M cv [] = cv := rfl

theorem obsAllT_cons (cv : Digest) (x : E) (xs : List E) :
    obsAllT M cv (x :: xs) = obsAllT M (obsCvT M cv x) xs := rfl

theorem obsAllT_append (cv : Digest) (xs ys : List E) :
    obsAllT M cv (xs ++ ys) = obsAllT M (obsAllT M cv xs) ys := List.foldl_append

theorem obsAllT_take_succ (cv : Digest) (l : List E) {i : ℕ} (hi : i < l.length) :
    obsAllT M cv (l.take (i + 1)) = obsCvT M (obsAllT M cv (l.take i)) (l.getD i 0) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, obsAllT_append,
    List.getD_eq_getElem _ _ hi]
  rfl

variable (M) in
/-- **The absorbs of `xs` from `cv` are answered**, each at the total hash. -/
def ObsAns (cv : Digest) (xs : List E) : Prop :=
  ∀ i < xs.length, obsCvM M (obsAllT M cv (xs.take i)) (xs.getD i 0) =
    some (obsAllT M cv (xs.take (i + 1)))

/-- **An answered absorb of words** is the total one, every step answered. -/
theorem obsAllM_T : ∀ {cv c : Digest} {xs : List E}, obsAllM M cv xs = some c →
    c = obsAllT M cv xs ∧ ObsAns M cv xs
  | cv, c, [], h => ⟨(Option.some.inj h).symm, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | cv, c, x :: xs, h => by
    obtain ⟨c1, hc1, h⟩ := obsAllM_cons_some h
    have e1 := obsCvT_eq hc1
    subst e1
    obtain ⟨rfl, hs⟩ := obsAllM_T h
    refine ⟨rfl, fun i hi => ?_⟩
    rcases i with _ | i
    · exact hc1
    · exact hs i (by simp at hi; omega)

/-- Answered absorbs give the answered `obsAllM`. -/
theorem obsAllM_of_ans : ∀ {cv : Digest} {xs : List E}, ObsAns M cv xs →
    obsAllM M cv xs = some (obsAllT M cv xs)
  | _, [], _ => rfl
  | cv, x :: xs, h => by
    have h0 : obsCvM M cv x = some (obsCvT M cv x) := h 0 (by simp)
    have ih := obsAllM_of_ans (cv := obsCvT M cv x) (xs := xs) fun i hi => h (i + 1) (by simp; omega)
    simp only [obsAllM, h0, Option.bind_some, ih]
    rfl

theorem obsAns_append {cv : Digest} {xs ys : List E} (h1 : ObsAns M cv xs)
    (h2 : ObsAns M (obsAllT M cv xs) ys) : ObsAns M cv (xs ++ ys) := by
  intro i hi
  rcases Nat.lt_or_ge i xs.length with h | h
  · rw [List.take_append_of_le_length (by omega), List.take_append_of_le_length (by omega),
      List.getD_append _ _ _ _ h]
    exact h1 i h
  · obtain ⟨k, rfl⟩ : ∃ k, i = xs.length + k := ⟨i - xs.length, by omega⟩
    rw [List.take_length_add_append, Nat.add_assoc, List.take_length_add_append,
      List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left, obsAllT_append,
      obsAllT_append]
    exact h2 k (by simp at hi; omega)

theorem obsAns_left {cv : Digest} {xs ys : List E} (h : ObsAns M cv (xs ++ ys)) :
    ObsAns M cv xs := fun i hi => by
  have := h i (by simp; omega)
  rwa [List.take_append_of_le_length (by omega), List.take_append_of_le_length (by omega),
    List.getD_append _ _ _ _ hi] at this

theorem obsAns_right {cv : Digest} {xs ys : List E} (h : ObsAns M cv (xs ++ ys)) :
    ObsAns M (obsAllT M cv xs) ys := fun k hk => by
  have := h (xs.length + k) (by simp; omega)
  rwa [List.take_length_add_append, Nat.add_assoc, List.take_length_add_append,
    List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left, obsAllT_append,
    obsAllT_append] at this

/-- **Answered squeezes** are the iterates of the total `sqCvT` (`sqAll_eq`), every one answered. -/
theorem sqAllM_T : ∀ {n : ℕ} {cv c : Digest} {cs : List E}, sqAllM M n cv = some (cs, c) →
    (∀ t < n, sqCvM M ((sqCvT M)^[t] cv) = some ((sqCvT M)^[t + 1] cv)) ∧
      cs = (List.range n).map (fun t => challengeOf (sqCvT M ((sqCvT M)^[t] cv))) ∧
      c = (sqCvT M)^[n] cv
  | 0, cv, c, cs, h => by
    simp only [sqAllM, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun t ht => absurd ht (Nat.not_lt_zero _), rfl, rfl⟩
  | n + 1, cv, c, cs, h => by
    obtain ⟨c1, hc1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r, hr, hrr⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hrr
    obtain ⟨rfl, rfl⟩ := hrr
    have e1 := sqCvT_eq hc1
    subst e1
    obtain ⟨hs, hcs, hc⟩ := sqAllM_T (n := n) (cv := sqCvT M cv) (c := r.2) (cs := r.1) hr
    refine ⟨fun t ht => ?_, ?_, ?_⟩
    · rcases t with _ | t
      · exact hc1
      · simp only [Function.iterate_succ_apply]
        exact hs t (by omega)
    · rw [hcs, List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [Function.iterate_zero_apply, Function.iterate_succ_apply, Function.comp_def]
    · rw [hc, Function.iterate_succ_apply]

/-! ## A `require`, passed -/

theorem RunsToM.fail_elim {β : Type} {f : Unit → Prog β} {cv cv' : Digest} {xs : List E} {b : β}
    (h : RunsToM M ((Prog.fail : Prog Unit).bind f) cv xs b cv') : False := by
  have h0 := h [] [] []
  simp [Prog.bind, runM, Compile.run] at h0

/-- An answered run past a `require`: the condition holds. -/
theorem RunsToM.require_inv {β : Type} {c : Prop} [Decidable c] {f : Unit → Prog β}
    {cv cv' : Digest} {xs : List E} {b : β}
    (h : RunsToM M ((Prog.require c).bind f) cv xs b cv') : c ∧ RunsToM M (f ()) cv xs b cv' := by
  by_cases hc : c
  · simp only [Prog.require, hc, ↓reduceIte, Prog.ret_bind] at h
    exact ⟨hc, h⟩
  · simp only [Prog.require, hc, ↓reduceIte] at h
    exact h.fail_elim.elim

/-! ## The sumchecks, round by round -/

/-- The two words of round `j` of a sumcheck's words. -/
def pairAt (ws : List E) (j : ℕ) : E × E := (ws.getD (2 * j) 0, ws.getD (2 * j + 1) 0)

theorem pairAt_cons_cons (a b : E) (ws : List E) (j : ℕ) :
    pairAt (a :: b :: ws) (j + 1) = pairAt ws j := by
  simp only [pairAt, show 2 * (j + 1) = 2 * j + 1 + 1 by ring, List.getD_cons_succ]

theorem scStT_succ' (e : ℕ → E) (g : ℕ → E × E) (s0 : E × Digest) : ∀ j,
    scStT M e g s0 (j + 1) =
      scStT M (fun i => e (i + 1)) (fun i => g (i + 1)) (scStepT M (e 0) (g 0) s0).2 j
  | 0 => rfl
  | j + 1 => by
    rw [scStT, scStT_succ' e g s0 j, scStT]

theorem scChT_succ' (e : ℕ → E) (g : ℕ → E × E) (s0 : E × Digest) (j : ℕ) :
    scChT M e g s0 (j + 1) =
      scChT M (fun i => e (i + 1)) (fun i => g (i + 1)) (scStepT M (e 0) (g 0) s0).2 j := by
  rw [scChT, scStT_succ', scChT]

theorem lcStT_succ' (g : ℕ → E × E) (s0 : E × Digest) : ∀ j,
    lcStT M g s0 (j + 1) = lcStT M (fun i => g (i + 1)) (lcStepT M (g 0) s0).2 j
  | 0 => rfl
  | j + 1 => by
    rw [lcStT, lcStT_succ' g s0 j, lcStT]

theorem lcChT_succ' (g : ℕ → E × E) (s0 : E × Digest) (j : ℕ) :
    lcChT M g s0 (j + 1) = lcChT M (fun i => g (i + 1)) (lcStepT M (g 0) s0).2 j := by
  rw [lcChT, lcStT_succ', lcChT]

theorem sumcheck_eq_cons_bind {β : Type} (claim e : E) (rest : List (Option E))
    (f : List E × E → Prog β) :
    (sumcheck claim 3 (some e :: rest)).bind f = (Prog.readN 2).bind fun tail =>
      Prog.sampleE.bind fun ch =>
        (sumcheck (polyEval ((claim + e * sumE tail) :: tail) ch) 3 rest).bind fun pf =>
          f (ch :: pf.1, pf.2) := by
  simp only [sumcheck, sumcheckRoundPoly, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc,
    Prog.ret_bind]

theorem sumcheck_plain_cons_bind {β : Type} (claim : E) (rest : List (Option E))
    (f : List E × E → Prog β) :
    (sumcheck claim 3 (none :: rest)).bind f = Prog.readE.bind fun c0 =>
      (Prog.readN 1).bind fun tail => Prog.sampleE.bind fun ch =>
        (sumcheck (polyEval (c0 :: (claim + sumE tail) :: tail) ch) 3 rest).bind fun pf =>
          f (ch :: pf.1, pf.2) := by
  simp only [sumcheck, sumcheckRoundPoly, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc,
    Prog.ret_bind]

theorem sumcheck_nil_bind {β : Type} (claim : E) (f : List E × E → Prog β) :
    (sumcheck claim 3 []).bind f = f ([], claim) := rfl

/-- **An answered equality-mode sumcheck, round by round** (`runs_sumcheck_eqM` backward): it
reads two words per round, every round's hashes are answered, and the challenges, the final claim
and state are `scStT`'s over the words read. -/
theorem RunsToM.sumcheck_eq_inv {β : Type} : ∀ (es : List E) {f : List E × E → Prog β}
    {claim : E} {cv cv' : Digest} {xs : List E} {b : β},
    RunsToM M ((sumcheck claim 3 (es.map some)).bind f) cv xs b cv' →
    ∃ ws zs, xs = ws ++ zs ∧ ws.length = 2 * es.length ∧
      (∀ j < es.length, RoundOk M (pairAt ws j)
        (scStT M (es.getD · 0) (pairAt ws) (claim, cv) j).2) ∧
      RunsToM M (f ((List.range es.length).map (scChT M (es.getD · 0) (pairAt ws) (claim, cv)),
        (scStT M (es.getD · 0) (pairAt ws) (claim, cv) es.length).1))
        (scStT M (es.getD · 0) (pairAt ws) (claim, cv) es.length).2 zs b cv'
  | [], f, claim, cv, cv', xs, b, h => ⟨[], xs, rfl, rfl, fun j hj => absurd hj (Nat.not_lt_zero _),
      h⟩
  | e :: es, f, claim, cv, cv', xs, b, h => by
    rw [List.map_cons, sumcheck_eq_cons_bind] at h
    obtain ⟨ys, zs, c, rfl, hl, hc, h⟩ := h.readN_inv
    obtain ⟨g1, g2, rfl⟩ := List.length_eq_two.mp hl
    obtain ⟨rfl, ha⟩ := obsAllM_T hc
    obtain ⟨c3, hc3, h⟩ := h.sampleE_inv
    have e3 := sqCvT_eq hc3
    subst e3
    obtain ⟨ws, zs', rfl, hwl, hok, h⟩ := RunsToM.sumcheck_eq_inv es h
    have hstep : scStepT M e (g1, g2) (claim, cv) =
        (challengeOf (sqCvT M (obsAllT M cv [g1, g2])),
          polyEval ((claim + e * sumE [g1, g2]) :: [g1, g2])
            (challengeOf (sqCvT M (obsAllT M cv [g1, g2]))),
          sqCvT M (obsAllT M cv [g1, g2])) := by
      simp only [scStepT, polyEval, sumE, List.foldr, List.foldl, obsAllT_cons, obsAllT_nil,
        Prod.mk.injEq, true_and, and_true]
      ring
    have hS : ∀ j, scStT M ((e :: es).getD · 0) (pairAt ([g1, g2] ++ ws)) (claim, cv) (j + 1) =
        scStT M (es.getD · 0) (pairAt ws) (polyEval ((claim + e * sumE [g1, g2]) :: [g1, g2])
          (challengeOf (sqCvT M (obsAllT M cv [g1, g2]))), sqCvT M (obsAllT M cv [g1, g2])) j :=
      fun j => by
        rw [scStT_succ']
        simp only [List.getD_cons_succ, List.getD_cons_zero, List.cons_append, List.nil_append,
          pairAt_cons_cons]
        rw [show pairAt (g1 :: g2 :: ws) 0 = (g1, g2) by simp [pairAt], hstep]
    have hC : ∀ j, scChT M ((e :: es).getD · 0) (pairAt ([g1, g2] ++ ws)) (claim, cv) (j + 1) =
        scChT M (es.getD · 0) (pairAt ws) (polyEval ((claim + e * sumE [g1, g2]) :: [g1, g2])
          (challengeOf (sqCvT M (obsAllT M cv [g1, g2]))), sqCvT M (obsAllT M cv [g1, g2])) j :=
      fun j => by
        rw [scChT_succ']
        simp only [List.getD_cons_succ, List.getD_cons_zero, List.cons_append, List.nil_append,
          pairAt_cons_cons]
        rw [show pairAt (g1 :: g2 :: ws) 0 = (g1, g2) by simp [pairAt], hstep]
    have hp0 : pairAt ([g1, g2] ++ ws) 0 = (g1, g2) := by simp [pairAt]
    refine ⟨[g1, g2] ++ ws, zs', by rw [List.append_assoc], by simp [hwl]; ring, fun j hj => ?_, ?_⟩
    · rcases j with _ | j
      · rw [hp0]
        refine ⟨ha 0 (by simp), ha 1 (by simp), ?_⟩
        exact hc3
      · have := hok j (by simp at hj; omega)
        rw [hS j]
        simpa only [List.cons_append, List.nil_append, pairAt_cons_cons] using this
    · rw [List.length_cons, hS, List.range_succ_eq_map, List.map_cons, List.map_map]
      have hc0 : scChT M ((e :: es).getD · 0) (pairAt ([g1, g2] ++ ws)) (claim, cv) 0 =
          challengeOf (sqCvT M (obsAllT M cv [g1, g2])) := by
        simp only [scChT, scStT, List.getD_cons_zero, hp0, hstep]
      rw [hc0]
      have hm : (List.range es.length).map
          (scChT M ((e :: es).getD · 0) (pairAt ([g1, g2] ++ ws)) (claim, cv) ∘ Nat.succ) =
          (List.range es.length).map (scChT M (es.getD · 0) (pairAt ws)
            (polyEval ((claim + e * sumE [g1, g2]) :: [g1, g2])
              (challengeOf (sqCvT M (obsAllT M cv [g1, g2]))), sqCvT M (obsAllT M cv [g1, g2]))) :=
        List.map_congr_left fun j _ => hC j
      rw [hm]
      exact h

/-- **An answered plain-mode sumcheck, round by round** (`runs_sumcheck_plainM` backward). -/
theorem RunsToM.sumcheck_plain_inv {β : Type} : ∀ (n : ℕ) {f : List E × E → Prog β}
    {claim : E} {cv cv' : Digest} {xs : List E} {b : β},
    RunsToM M ((sumcheck claim 3 (List.replicate n none)).bind f) cv xs b cv' →
    ∃ ws zs, xs = ws ++ zs ∧ ws.length = 2 * n ∧
      (∀ j < n, RoundOk M (pairAt ws j) (lcStT M (pairAt ws) (claim, cv) j).2) ∧
      RunsToM M (f ((List.range n).map (lcChT M (pairAt ws) (claim, cv)),
        (lcStT M (pairAt ws) (claim, cv) n).1)) (lcStT M (pairAt ws) (claim, cv) n).2 zs b cv'
  | 0, f, claim, cv, cv', xs, b, h => ⟨[], xs, rfl, rfl, fun j hj => absurd hj (Nat.not_lt_zero _),
      h⟩
  | n + 1, f, claim, cv, cv', xs, b, h => by
    rw [List.replicate_succ, sumcheck_plain_cons_bind] at h
    obtain ⟨c0, zs1, c1, rfl, hc1, h⟩ := h.readE_inv
    obtain ⟨ys, zs, c, rfl, hl, hc, h⟩ := h.readN_inv
    obtain ⟨c2, rfl⟩ := List.length_eq_one_iff.mp hl
    have e1 := obsCvT_eq hc1
    subst e1
    obtain ⟨rfl, ha⟩ := obsAllM_T hc
    obtain ⟨c3, hc3, h⟩ := h.sampleE_inv
    have e3 := sqCvT_eq hc3
    subst e3
    obtain ⟨ws, zs', rfl, hwl, hok, h⟩ := RunsToM.sumcheck_plain_inv n h
    have hstep : lcStepT M (c0, c2) (claim, cv) =
        (challengeOf (sqCvT M (obsAllT M (obsCvT M cv c0) [c2])),
          polyEval (c0 :: (claim + sumE [c2]) :: [c2])
            (challengeOf (sqCvT M (obsAllT M (obsCvT M cv c0) [c2]))),
          sqCvT M (obsAllT M (obsCvT M cv c0) [c2])) := by
      simp only [lcStepT, polyEval, sumE, List.foldr, List.foldl, obsAllT_cons, obsAllT_nil,
        Prod.mk.injEq, true_and, and_true]
      ring
    have hp0 : pairAt (c0 :: c2 :: ws) 0 = (c0, c2) := by simp [pairAt]
    have hS : ∀ j, lcStT M (pairAt (c0 :: c2 :: ws)) (claim, cv) (j + 1) =
        lcStT M (pairAt ws) (polyEval (c0 :: (claim + sumE [c2]) :: [c2])
          (challengeOf (sqCvT M (obsAllT M (obsCvT M cv c0) [c2]))),
            sqCvT M (obsAllT M (obsCvT M cv c0) [c2])) j := fun j => by
      rw [lcStT_succ']
      simp only [pairAt_cons_cons]
      rw [hp0, hstep]
    have hC : ∀ j, lcChT M (pairAt (c0 :: c2 :: ws)) (claim, cv) (j + 1) =
        lcChT M (pairAt ws) (polyEval (c0 :: (claim + sumE [c2]) :: [c2])
          (challengeOf (sqCvT M (obsAllT M (obsCvT M cv c0) [c2]))),
            sqCvT M (obsAllT M (obsCvT M cv c0) [c2])) j := fun j => by
      rw [lcChT_succ']
      simp only [pairAt_cons_cons]
      rw [hp0, hstep]
    refine ⟨c0 :: c2 :: ws, zs', by simp, by simp [hwl]; ring, fun j hj => ?_, ?_⟩
    · rcases j with _ | j
      · rw [hp0]
        exact ⟨hc1, ha 0 (by simp), hc3⟩
      · rw [hS j, pairAt_cons_cons]
        exact hok j (by omega)
    · rw [hS, List.range_succ_eq_map, List.map_cons, List.map_map]
      have hc0 : lcChT M (pairAt (c0 :: c2 :: ws)) (claim, cv) 0 =
          challengeOf (sqCvT M (obsAllT M (obsCvT M cv c0) [c2])) := by
        simp only [lcChT, lcStT, hp0, hstep]
      rw [hc0]
      have hm : (List.range n).map (lcChT M (pairAt (c0 :: c2 :: ws)) (claim, cv) ∘ Nat.succ) =
          (List.range n).map (lcChT M (pairAt ws) (polyEval (c0 :: (claim + sumE [c2]) :: [c2])
            (challengeOf (sqCvT M (obsAllT M (obsCvT M cv c0) [c2]))),
              sqCvT M (obsAllT M (obsCvT M cv c0) [c2]))) :=
        List.map_congr_left fun j _ => hC j
      rw [hm]
      exact h

end
end LeanVM.Guest.B1
