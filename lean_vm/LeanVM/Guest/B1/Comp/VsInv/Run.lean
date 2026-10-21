/-
  LeanVM.Guest.B1.Comp.VsInv.Run

  Runs over a hash model, backward: the elementary runs inverted, every hash answered, and the
  frames (a run reads a prefix of the stream and of the openings).
-/

module

public import LeanVM.Guest.B1.VerifySub.RunM
public import LeanVM.Guest.B1.VerifySub.Inv5
public import LeanVM.Guest.B1.VerifySub.ChallengesB

/-!
# Runs over a hash model, backward

`Inv0.lean` and `Inv2.lean` over a hash model `M` (`RunsM M`, `runM M` in place of `Runs`,
`runId`): each hash a run makes is the model's answer.

* `RunsM.bind_inv`: a run of `p >>= f` is a run of `p`, then of `f` from its end;
* the elementary runs inverted: `RunsM.ret_inv`, `.require_inv`, `.sampleE_inv` (the squeeze the
  model's answer), `.readE_inv`, `.readN_inv` (`obsAllM`), `.sampleN_inv` (`sqAllM`),
  `.sumcheck_inv`, `.liftOption_inv`;
* `runs_frameM`: a run reads a prefix of the stream and of the openings, and runs the same on
  any continuation of both (`RunsWithM`); `qfree_frameM`: a run of a program that neither commits
  nor opens (`QFree`) reads a prefix of the stream, the same from any openings and roots
  (`RunsToM`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {M : HashModel}

/-! ## The steps -/

theorem runM_read_consV {α : Type} (k : E → Prog α) (cv : Digest) (x : E) (xs : List E)
    (os : List Opening) (roots : List (Digest × ℕ × ℕ)) :
    runM M (.read k) ⟨cv, x :: xs, os, roots⟩ =
      (M.H (digestBytes cv ++ blockOf x 1)).bind fun c => runM M (k x) ⟨c, xs, os, roots⟩ := rfl

theorem runM_grind_consV {α : Type} (b : ℕ) (k : Prog α) (cv : Digest) (n : E) (xs : List E)
    (os : List Opening) (roots : List (Digest × ℕ × ℕ)) :
    runM M (.grind b k) ⟨cv, n :: xs, os, roots⟩ =
      (M.H (digestBytes cv ++ blockOf 0 3)).bind fun base =>
        (M.H (digestBytes base ++ blockOf n 4)).bind fun d =>
          (M.H (digestBytes cv ++ blockOf n 4)).bind fun c =>
            if powOk b n d then runM M k ⟨c, xs, os, roots⟩ else some none := rfl

theorem runM_commit_consV {α : Type} (hh w : ℕ) (k : Prog α) (cv : Digest) (x0 x1 : E)
    (xs : List E) (os : List Opening) (roots : List (Digest × ℕ × ℕ)) :
    runM M (.commit hh w k) ⟨cv, x0 :: x1 :: xs, os, roots⟩ =
      (M.H (digestBytes cv ++ blockOf x0 1)).bind fun c0 =>
        (M.H (digestBytes c0 ++ blockOf x1 1)).bind fun c1 =>
          match digestOfScalars (x0, x1) with
          | some root => runM M k ⟨c1, xs, os, roots ++ [(root, hh, w)]⟩
          | none => some none := rfl

/-! ## Binds and the elementary runs -/

theorem RunsM.bind_inv {α β : Type} {p : Prog α} {f : α → Prog β} {s s'' : St} {b : β}
    (h : RunsM M (p >>= f) s b s'') : ∃ a s', RunsM M p s a s' ∧ RunsM M (f a) s' b s'' := by
  unfold RunsM at *
  rw [prog_bind_eq, runM_bind] at h
  match hp : runM M p s, h with
  | some (some (a, s')), h => exact ⟨a, s', rfl, h⟩
  | some none, h => simp at h
  | none, h => simp at h

theorem RunsM.bind_inv' {α β : Type} {p : Prog α} {f : α → Prog β} {s s'' : St} {b : β}
    (h : RunsM M (p.bind f) s b s'') : ∃ a s', RunsM M p s a s' ∧ RunsM M (f a) s' b s'' :=
  RunsM.bind_inv h

theorem RunsM.bind' {α β : Type} {p : Prog α} {f : α → Prog β} {s s1 s2 : St} {a : α} {b : β}
    (h1 : RunsM M p s a s1) (h2 : RunsM M (f a) s1 b s2) : RunsM M (p.bind f) s b s2 :=
  RunsM.bind h1 h2

theorem RunsM.ret_inv {α : Type} {a b : α} {s s' : St} (h : RunsM M (Prog.ret a) s b s') :
    b = a ∧ s' = s := by
  unfold RunsM at h
  simp only [runM, Compile.run, pure, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem RunsM.pure_inv {α : Type} {a b : α} {s s' : St} (h : RunsM M (pure a : Prog α) s b s') :
    b = a ∧ s' = s := RunsM.ret_inv h

theorem RunsM.require_inv {c : Prop} [Decidable c] {s s' : St} {u : Unit}
    (h : RunsM M (Prog.require c) s u s') : c ∧ s' = s := by
  unfold Prog.require at h
  split at h
  · exact ⟨by assumption, (RunsM.ret_inv h).2⟩
  · unfold RunsM at h; simp [runM, Compile.run, pure] at h

theorem RunsM.liftOption_inv {α : Type} {o : Option α} {a : α} {s s' : St}
    (h : RunsM M (Verifier.liftOption o) s a s') : o = some a ∧ s' = s := by
  match o, h with
  | none, h => unfold RunsM at h; simp [Verifier.liftOption, runM, Compile.run, pure] at h
  | some b, h =>
    obtain ⟨rfl, rfl⟩ := RunsM.ret_inv h
    exact ⟨rfl, rfl⟩

theorem RunsM.sampleE_inv {s s' : St} {x : E} (h : RunsM M Prog.sampleE s x s') :
    ∃ c, sqCvM M s.cv = some c ∧ x = challengeOf c ∧ s' = { s with cv := c } := by
  unfold RunsM at h
  change (M.H (digestBytes s.cv ++ blockOf 0 2)).bind
    (fun c => some (some (challengeOf c, { s with cv := c }))) = _ at h
  obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨c, hc, h.1.symm, h.2.symm⟩

theorem RunsM.readE_inv {s s' : St} {x : E} (h : RunsM M Prog.readE s x s') :
    s.stream = x :: s'.stream ∧ obsCvM M s.cv x = some s'.cv ∧ s'.openings = s.openings ∧
      s'.roots = s.roots := by
  obtain ⟨cv, xs, os, roots⟩ := s
  match xs, h with
  | [], h => unfold RunsM at h; simp [runM, Compile.run, Prog.readE, pure] at h
  | y :: ys, h =>
    unfold RunsM at h
    rw [Prog.readE, runM_read_consV] at h
    obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [runM, Compile.run, pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, hc, rfl, rfl⟩

theorem RunsM.readN_inv : ∀ {n : ℕ} {s s' : St} {xs : List E}, RunsM M (Prog.readN n) s xs s' →
    xs.length = n ∧ s.stream = xs ++ s'.stream ∧ obsAllM M s.cv xs = some s'.cv ∧
      s'.openings = s.openings ∧ s'.roots = s.roots
  | 0, s, s', xs, h => by
    obtain ⟨rfl, rfl⟩ := RunsM.ret_inv h
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | n + 1, s, s', xs, h => by
    unfold Prog.readN at h
    obtain ⟨x, s1, h1, h2⟩ := RunsM.bind_inv h
    obtain ⟨ys, s2, h3, h4⟩ := RunsM.bind_inv h2
    obtain ⟨rfl, rfl⟩ := RunsM.pure_inv h4
    obtain ⟨hl, hs, hc, ho, hr⟩ := RunsM.readN_inv h3
    obtain ⟨e1, e2, e3, e4⟩ := RunsM.readE_inv h1
    refine ⟨by simp [hl], by rw [e1, hs]; rfl, ?_, by rw [ho, e3], by rw [hr, e4]⟩
    show (obsCvM M s.cv x).bind (fun cv' ↦ obsAllM M cv' ys) = _
    rw [e2, Option.bind_some, hc]

theorem RunsM.sampleN_inv : ∀ {n : ℕ} {s s' : St} {xs : List E}, RunsM M (Prog.sampleN n) s xs s' →
    sqAllM M n s.cv = some (xs, s'.cv) ∧ s' = { s with cv := s'.cv }
  | 0, s, s', xs, h => by
    obtain ⟨rfl, rfl⟩ := RunsM.ret_inv h
    exact ⟨rfl, rfl⟩
  | n + 1, s, s', xs, h => by
    unfold Prog.sampleN at h
    obtain ⟨x, s1, h1, h2⟩ := RunsM.bind_inv h
    obtain ⟨ys, s2, h3, h4⟩ := RunsM.bind_inv h2
    obtain ⟨rfl, rfl⟩ := RunsM.pure_inv h4
    obtain ⟨hq, hs⟩ := RunsM.sampleN_inv h3
    obtain ⟨c, hc, rfl, rfl⟩ := RunsM.sampleE_inv h1
    refine ⟨?_, by rw [hs]⟩
    show (sqCvM M s.cv).bind (fun cv' ↦ (sqAllM M n cv').map fun r ↦ (challengeOf cv' :: r.1, r.2)) = _
    rw [hc, Option.bind_some, hq]
    rfl

theorem RunsM.sampleN_length {n : ℕ} {s s' : St} {xs : List E}
    (h : RunsM M (Prog.sampleN n) s xs s') : xs.length = n :=
  sqAllM_length (RunsM.sampleN_inv h).1

theorem RunsM.sumcheck_inv {count : ℕ} : ∀ {eqs : List (Option E)} {claim : E} {s s' : St}
    {r : List E × E}, RunsM M (sumcheck claim count eqs) s r s' → r.1.length = eqs.length
  | [], _, s, s', r, h => by
    unfold sumcheck at h
    obtain ⟨rfl, -⟩ := RunsM.pure_inv h
    rfl
  | e :: es, claim, s, s', r, h => by
    unfold sumcheck at h
    obtain ⟨m, s1, -, h2⟩ := RunsM.bind_inv h
    obtain ⟨x, s2, -, h4⟩ := RunsM.bind_inv h2
    obtain ⟨⟨pt, f⟩, s3, h5, h6⟩ := RunsM.bind_inv h4
    obtain ⟨rfl, -⟩ := RunsM.pure_inv h6
    have := RunsM.sumcheck_inv h5
    simp only [List.length_cons] at this ⊢
    omega

/-! ## Frames -/

/-- `openAll` over the model reads a prefix of the openings, the same on any continuation. -/
theorem openAll_frameM (root : Digest) (hh w : ℕ) : ∀ (qs : List ℕ) (os rest : List Opening)
    (rows : List (List K)), openAll (m := Option) M.H root hh w qs os = some (some (rows, rest)) →
    ∃ os1, os = os1 ++ rest ∧ ∀ orest,
      openAll (m := Option) M.H root hh w qs (os1 ++ orest) = some (some (rows, orest))
  | [], os, rest, rows, h => by
    simp only [openAll, pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, fun _ => rfl⟩
  | _ :: _, [], _, _, h => by simp [openAll, pure] at h
  | q :: qs, o :: os, rest, rows, h => by
    simp only [openAll, bind, Option.bind_eq_some_iff] at h
    obtain ⟨b, hb, h⟩ := h
    cases b with
    | false => simp [pure] at h
    | true =>
      simp only [↓reduceIte, Option.bind_eq_some_iff] at h
      obtain ⟨r, hr, h⟩ := h
      match r, hr, h with
      | some (rows', rest'), hr, h =>
        simp only [pure, Option.map_some, Option.some.injEq] at h
        cases h
        obtain ⟨os1, rfl, h1⟩ := openAll_frameM root hh w qs os _ _ hr
        refine ⟨o :: os1, rfl, fun orest => ?_⟩
        simp only [List.cons_append, openAll, bind, hb, Option.bind_some, ↓reduceIte, h1 orest]
        rfl
      | none, _, h => simp [pure] at h

/-- **A run over the model reads a prefix** of the stream and of the openings, and runs the same
on any continuation of both. -/
theorem runs_frameM {α : Type} (p : Prog α) : ∀ (cv : Digest) (xs : List E) (os : List Opening)
    (roots : List (Digest × ℕ × ℕ)) (a : α) (s' : St),
    runM M p ⟨cv, xs, os, roots⟩ = some (some (a, s')) →
    ∃ ys os1, xs = ys ++ s'.stream ∧ os = os1 ++ s'.openings ∧
      RunsWithM M p cv ys os1 roots a s'.cv s'.roots := by
  induction p with
  | ret b =>
    intro cv xs os roots a s' h
    simp only [runM, Compile.run, pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], [], rfl, rfl, fun _ _ => rfl⟩
  | fail => intro _ _ _ _ _ _ h; simp [runM, Compile.run, pure] at h
  | read k ih =>
    intro cv xs os roots a s' h
    match xs, h with
    | [], h => simp [runM, Compile.run, pure] at h
    | x :: xs, h =>
      rw [runM_read_consV] at h
      obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨ys, os1, h1, h2, h3⟩ := ih x _ xs os roots a s' h
      refine ⟨x :: ys, os1, by rw [h1]; rfl, h2, fun rest orest => ?_⟩
      rw [List.cons_append, runM_read_consV, hc, Option.bind_some]
      exact h3 rest orest
  | sample k ih =>
    intro cv xs os roots a s' h
    simp only [runM, Compile.run, absorbBlock, bind, Option.bind_eq_some_iff] at h
    obtain ⟨c, hc, h⟩ := h
    obtain ⟨ys, os1, h1, h2, h3⟩ := ih _ _ xs os roots a s' h
    refine ⟨ys, os1, h1, h2, fun rest orest => ?_⟩
    simp only [runM, Compile.run, absorbBlock, bind, hc, Option.bind_some]
    exact h3 rest orest
  | grind b k ih =>
    intro cv xs os roots a s' h
    match xs, h with
    | [], h => simp [runM, Compile.run, pure] at h
    | n :: xs, h =>
      rw [runM_grind_consV] at h
      obtain ⟨c1, hc1, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨c2, hc2, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨c3, hc3, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · rename_i hpow
        obtain ⟨ys, os1, h1, h2, h3⟩ := ih _ xs os roots a s' h
        refine ⟨n :: ys, os1, by rw [h1]; rfl, h2, fun rest orest => ?_⟩
        rw [List.cons_append, runM_grind_consV, hc1, Option.bind_some, hc2, Option.bind_some, hc3,
          Option.bind_some]
        simp only [hpow, ↓reduceIte]
        exact h3 rest orest
      · simp at h
  | commit hh w k ih =>
    intro cv xs os roots a s' h
    match xs, h with
    | [], h => simp [runM, Compile.run, pure] at h
    | [_], h => simp [runM, Compile.run, pure] at h
    | x0 :: x1 :: xs, h =>
      rw [runM_commit_consV] at h
      obtain ⟨c0, hc0, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨c1, hc1, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · rename_i root hroot
        obtain ⟨ys, os1, h1, h2, h3⟩ := ih _ xs os _ a s' h
        refine ⟨x0 :: x1 :: ys, os1, by rw [h1]; rfl, h2, fun rest orest => ?_⟩
        rw [List.cons_append, List.cons_append, runM_commit_consV, hc0, Option.bind_some, hc1,
          Option.bind_some]
        simp only [hroot]
        exact h3 rest orest
      · simp at h
  | query i ps k ih =>
    intro cv xs os roots a s' h
    simp only [runM, Compile.run] at h
    split at h
    · simp at h
    · rename_i root hh w hi
      obtain ⟨o, ho, h4⟩ := Option.bind_eq_some_iff.mp h
      clear h
      split at h4
      · rename_i rows rest
        obtain ⟨os1, rfl, hf⟩ := openAll_frameM root hh w ps os rest rows ho
        obtain ⟨ys, os2, h1, h2, h3⟩ := ih rows _ xs rest roots a s' h4
        refine ⟨ys, os1 ++ os2, h1, by rw [h2, List.append_assoc], fun R O => ?_⟩
        simp only [runM, Compile.run, hi, bind, List.append_assoc, hf (os2 ++ O), Option.bind_some]
        exact h3 R O
      · simp at h4

/-- **A run over the model of a program that neither commits nor opens** reads a prefix of the
stream, the same from any openings and roots. -/
theorem qfree_frameM {α : Type} {p : Prog α} (hq : QFree p) :
    ∀ (cv : Digest) (xs : List E) (os : List Opening) (roots : List (Digest × ℕ × ℕ)) (a : α)
      (s' : St), runM M p ⟨cv, xs, os, roots⟩ = some (some (a, s')) →
      ∃ ys, xs = ys ++ s'.stream ∧ s'.openings = os ∧ s'.roots = roots ∧
        RunsToM M p cv ys a s'.cv := by
  induction hq with
  | ret b =>
    intro cv xs os roots a s' h
    simp only [runM, Compile.run, pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, rfl, rfl, fun _ _ _ => rfl⟩
  | fail => intro _ _ _ _ _ _ h; simp [runM, Compile.run, pure] at h
  | read k _ ih =>
    intro cv xs os roots a s' h
    match xs, h with
    | [], h => simp [runM, Compile.run, pure] at h
    | x :: xs, h =>
      rw [runM_read_consV] at h
      obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨ys, h1, h2, h3, h4⟩ := ih x _ xs os roots a s' h
      refine ⟨x :: ys, by rw [h1]; rfl, h2, h3, fun rest os roots => ?_⟩
      rw [List.cons_append, runM_read_consV, hc, Option.bind_some]
      exact h4 rest os roots
  | sample k _ ih =>
    intro cv xs os roots a s' h
    simp only [runM, Compile.run, absorbBlock, bind, Option.bind_eq_some_iff] at h
    obtain ⟨c, hc, h⟩ := h
    obtain ⟨ys, h1, h2, h3, h4⟩ := ih _ _ xs os roots a s' h
    refine ⟨ys, h1, h2, h3, fun rest os roots => ?_⟩
    simp only [runM, Compile.run, absorbBlock, bind, hc, Option.bind_some]
    exact h4 rest os roots
  | grind b k _ ih =>
    intro cv xs os roots a s' h
    match xs, h with
    | [], h => simp [runM, Compile.run, pure] at h
    | n :: xs, h =>
      rw [runM_grind_consV] at h
      obtain ⟨c1, hc1, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨c2, hc2, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨c3, hc3, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · rename_i hpow
        obtain ⟨ys, h1, h2, h3, h4⟩ := ih _ xs os roots a s' h
        refine ⟨n :: ys, by rw [h1]; rfl, h2, h3, fun rest os roots => ?_⟩
        rw [List.cons_append, runM_grind_consV, hc1, Option.bind_some, hc2, Option.bind_some, hc3,
          Option.bind_some]
        simp only [hpow, ↓reduceIte]
        exact h4 rest os roots
      · simp at h

/-- A `QFree` run from a state, framed. -/
theorem RunsM.qfree {α : Type} {p : Prog α} (hq : QFree p) {s s' : St} {a : α}
    (h : RunsM M p s a s') :
    ∃ ys, s.stream = ys ++ s'.stream ∧ s'.openings = s.openings ∧ s'.roots = s.roots ∧
      RunsToM M p s.cv ys a s'.cv := by
  obtain ⟨cv, xs, os, roots⟩ := s
  exact qfree_frameM hq cv xs os roots a s' h

/-- A run from a state, framed. -/
theorem RunsM.frame {α : Type} {p : Prog α} {s s' : St} {a : α} (h : RunsM M p s a s') :
    ∃ ys os1, s.stream = ys ++ s'.stream ∧ s.openings = os1 ++ s'.openings ∧
      RunsWithM M p s.cv ys os1 s.roots a s'.cv s'.roots := by
  obtain ⟨cv, xs, os, roots⟩ := s
  exact runs_frameM p cv xs os roots a s' h

/-- A run over the model of a program known to run from a state returns what it returns there. -/
theorem RunsM.det {α : Type} {p : Prog α} {cv cv' : Digest} {ys : List E} {a a' : α}
    (h : RunsToM M p cv ys a cv') {rest : List E} {os : List Opening}
    {roots : List (Digest × ℕ × ℕ)} {s' : St} (h' : RunsM M p ⟨cv, ys ++ rest, os, roots⟩ a' s') :
    a' = a ∧ s' = ⟨cv', rest, os, roots⟩ := by
  unfold RunsM at h'
  rw [h rest os roots, Option.some.injEq, Option.some.injEq, Prod.mk.injEq] at h'
  exact ⟨h'.1.symm, h'.2.symm⟩

end
end LeanVM.Guest.B1.VerifySub
