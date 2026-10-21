/-
  LeanVM.Guest.B1.Comp.Tables.RunFrameM

  Answered runs over a hash model split at binds: a run that commits nothing reads a prefix of
  its stream, and the inverses of the elementary runs.
-/

module

public import LeanVM.Guest.B1.Comp.Tables.RunInv

/-!
# Answered runs, split

`GkrRunInv.lean`'s frame argument over a hash model `M` (`runM M` in place of `runId`):

* `runM_roots_mono`: a run only appends roots; `runM_frame`: a run from no roots and no openings
  that ends with no roots reads a prefix of its stream, and the same on any continuation;
* `RunsToM.bind_inv`: an answered run of `p.bind f` is an answered run of `p` on a prefix of the
  words and of `f` on the rest (`RunsTo.bind_inv`);
* the elementary runs inverted, every hash answered: `RunsToM.pure_inv`, `.requireP_inv`,
  `.sampleEP_inv`, `.sampleNP_inv`, `.readNP_inv`, `.readEP_inv` (`RunsTo.ret_inv`, …).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {M : HashModel}

theorem runM_read_cons {α : Type} (k : E → Prog α) (cv : Digest) (x : E) (xs : List E)
    (os : List Opening) (roots : List (Digest × ℕ × ℕ)) :
    runM M (.read k) ⟨cv, x :: xs, os, roots⟩ =
      (M.H (digestBytes cv ++ blockOf x 1)).bind fun c => runM M (k x) ⟨c, xs, os, roots⟩ := rfl

theorem runM_read_nil {α : Type} (k : E → Prog α) (cv : Digest) (os : List Opening)
    (roots : List (Digest × ℕ × ℕ)) : runM M (.read k) ⟨cv, [], os, roots⟩ = some none := rfl

theorem runM_sample {α : Type} (k : E → Prog α) (cv : Digest) (xs : List E) (os : List Opening)
    (roots : List (Digest × ℕ × ℕ)) :
    runM M (.sample k) ⟨cv, xs, os, roots⟩ =
      (M.H (digestBytes cv ++ blockOf 0 2)).bind fun c =>
        runM M (k (challengeOf c)) ⟨c, xs, os, roots⟩ := rfl

theorem runM_grind_cons {α : Type} (b : ℕ) (k : Prog α) (cv : Digest) (n : E) (xs : List E)
    (os : List Opening) (roots : List (Digest × ℕ × ℕ)) :
    runM M (.grind b k) ⟨cv, n :: xs, os, roots⟩ =
      (M.H (digestBytes cv ++ blockOf 0 3)).bind fun base =>
        (M.H (digestBytes base ++ blockOf n 4)).bind fun d =>
          (M.H (digestBytes cv ++ blockOf n 4)).bind fun c =>
            if powOk b n d then runM M k ⟨c, xs, os, roots⟩ else some none := rfl

theorem runM_grind_nil {α : Type} (b : ℕ) (k : Prog α) (cv : Digest) (os : List Opening)
    (roots : List (Digest × ℕ × ℕ)) : runM M (.grind b k) ⟨cv, [], os, roots⟩ = some none := rfl

theorem runM_commit_cons {α : Type} (hh w : ℕ) (k : Prog α) (cv : Digest) (x0 x1 : E)
    (xs : List E) (os : List Opening) (roots : List (Digest × ℕ × ℕ)) :
    runM M (.commit hh w k) ⟨cv, x0 :: x1 :: xs, os, roots⟩ =
      (M.H (digestBytes cv ++ blockOf x0 1)).bind fun c0 =>
        (M.H (digestBytes c0 ++ blockOf x1 1)).bind fun c1 =>
          match digestOfScalars (x0, x1) with
          | some root => runM M k ⟨c1, xs, os, roots ++ [(root, hh, w)]⟩
          | none => some none := rfl

theorem runM_commit_short {α : Type} (hh w : ℕ) (k : Prog α) (cv : Digest) (xs : List E)
    (os : List Opening) (roots : List (Digest × ℕ × ℕ)) (hx : xs.length < 2) :
    runM M (.commit hh w k) ⟨cv, xs, os, roots⟩ = some none := by
  match xs, hx with
  | [], _ => rfl
  | [_], _ => rfl

/-- **An answered run only appends roots.** -/
theorem runM_roots_mono {α : Type} : ∀ (p : Prog α) (s : St) (a : α) (s' : St),
    runM M p s = some (some (a, s')) → ∃ l, s'.roots = s.roots ++ l
  | .ret _, _, _, _, h => by cases h; exact ⟨[], by simp⟩
  | .fail, _, _, _, h => by cases h
  | .read k, ⟨cv, xs, os, roots⟩, a, s', h => by
    match xs, h with
    | [], h => rw [runM_read_nil] at h; cases h
    | x :: xs, h =>
      rw [runM_read_cons] at h
      obtain ⟨c, -, h⟩ := Option.bind_eq_some_iff.mp h
      exact runM_roots_mono (k x) ⟨c, xs, os, roots⟩ a s' h
  | .sample k, ⟨cv, xs, os, roots⟩, a, s', h => by
    rw [runM_sample] at h
    obtain ⟨c, -, h⟩ := Option.bind_eq_some_iff.mp h
    exact runM_roots_mono _ ⟨c, xs, os, roots⟩ a s' h
  | .grind b k, ⟨cv, xs, os, roots⟩, a, s', h => by
    match xs, h with
    | [], h => rw [runM_grind_nil] at h; cases h
    | n :: xs, h =>
      rw [runM_grind_cons] at h
      obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨c, -, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · exact runM_roots_mono k ⟨c, xs, os, roots⟩ a s' h
      · cases h
  | .commit hh w k, ⟨cv, xs, os, roots⟩, a, s', h => by
    match xs, h with
    | [], h => cases h
    | [_], h => cases h
    | x0 :: x1 :: xs, h =>
      rw [runM_commit_cons] at h
      obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨c1, -, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · rename_i root _
        obtain ⟨l, hl⟩ := runM_roots_mono k ⟨c1, xs, os, roots ++ [(root, hh, w)]⟩ a s' h
        exact ⟨(root, hh, w) :: l, by rw [hl]; simp⟩
      · cases h
  | .query i ps k, ⟨cv, xs, os, roots⟩, a, s', h => by
    simp only [runM, Compile.run] at h
    split at h
    · cases h
    · obtain ⟨o, -, h⟩ := Option.bind_eq_some_iff.mp h
      match o, h with
      | some (rows, rest), h => exact runM_roots_mono (k rows) ⟨cv, xs, rest, roots⟩ a s' h
      | none, h => cases h

/-- **An answered run that commits nothing reads a prefix**, the same on any continuation of it
(`runId_frame`). -/
theorem runM_frame {α : Type} : ∀ (p : Prog α) (cv : Digest) (xs : List E) (a : α) (s' : St),
    runM M p ⟨cv, xs, [], []⟩ = some (some (a, s')) → s'.roots = [] →
      ∃ k, s'.stream = xs.drop k ∧ s'.openings = [] ∧ ∀ ys os roots,
        runM M p ⟨cv, xs.take k ++ ys, os, roots⟩ = some (some (a, ⟨s'.cv, ys, os, roots⟩))
  | .ret _, cv, xs, _, s', h, _ => by
    cases h
    exact ⟨0, by simp, rfl, fun ys os roots => by simp; rfl⟩
  | .fail, _, _, _, _, h, _ => by cases h
  | .read k, cv, xs, a, s', h, hr => by
    match xs, h with
    | [], h => rw [runM_read_nil] at h; cases h
    | x :: xs, h =>
      rw [runM_read_cons] at h
      obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k0, h1, h2, h3⟩ := runM_frame (k x) c xs a s' h hr
      refine ⟨k0 + 1, by simpa using h1, h2, fun ys os roots => ?_⟩
      rw [List.take_succ_cons, List.cons_append, runM_read_cons, hc, Option.bind_some]
      exact h3 ys os roots
  | .sample k, cv, xs, a, s', h, hr => by
    rw [runM_sample] at h
    obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨k0, h1, h2, h3⟩ := runM_frame _ c xs a s' h hr
    exact ⟨k0, h1, h2, fun ys os roots => by
      rw [runM_sample, hc, Option.bind_some]; exact h3 ys os roots⟩
  | .grind b k, cv, xs, a, s', h, hr => by
    match xs, h with
    | [], h => rw [runM_grind_nil] at h; cases h
    | n :: xs, h =>
      rw [runM_grind_cons] at h
      obtain ⟨base, hb, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · rename_i hpow
        obtain ⟨k0, h1, h2, h3⟩ := runM_frame k c xs a s' h hr
        refine ⟨k0 + 1, by simpa using h1, h2, fun ys os roots => ?_⟩
        rw [List.take_succ_cons, List.cons_append, runM_grind_cons, hb, Option.bind_some, hd,
          Option.bind_some, hc, Option.bind_some]
        simp only [hpow, ↓reduceIte]
        exact h3 ys os roots
      · cases h
  | .commit hh w k, cv, xs, a, s', h, hr => by
    exfalso
    match xs, h with
    | [], h => cases h
    | [_], h => cases h
    | x0 :: x1 :: xs, h =>
      rw [runM_commit_cons] at h
      obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · obtain ⟨l, hl⟩ := runM_roots_mono _ _ a s' h
        rw [hr] at hl
        simp at hl
      · cases h
  | .query i ps k, cv, xs, a, s', h, _ => by
    simp [runM, Compile.run] at h

/-- **An answered run of a bind splits**: `p` reads a prefix, `f` the rest (`RunsTo.bind_inv`). -/
theorem RunsToM.bind_inv {α β : Type} {p : Prog α} {f : α → Prog β} {cv cv'' : Digest}
    {xs : List E} {b : β} (h : RunsToM M (p.bind f) cv xs b cv'') :
    ∃ (xs1 xs2 : List E) (a : α) (cv1 : Digest), xs = xs1 ++ xs2 ∧ RunsToM M p cv xs1 a cv1 ∧
      RunsToM M (f a) cv1 xs2 b cv'' := by
  have h0 := h [] [] []
  rw [List.append_nil, runM_bind] at h0
  obtain ⟨o, h1, h2⟩ := Option.bind_eq_some_iff.mp h0
  match o, h1, h2 with
  | none, _, h2 => cases h2
  | some ⟨a, s1⟩, h1, h2 =>
    simp only [Option.elim] at h2
    obtain ⟨l, hl⟩ := runM_roots_mono (f a) s1 b _ h2
    have hr1 : s1.roots = [] := by
      have := congrArg List.length hl; simp at this; exact List.eq_nil_of_length_eq_zero (by omega)
    obtain ⟨k, hk1, hk2, hk3⟩ := runM_frame p cv xs a s1 h1 hr1
    obtain ⟨cv1, st1, os1, rs1⟩ := s1
    simp only at hk1 hk2 hr1 hk3
    subst hk1 hk2 hr1
    have h2' : runM M (f a) ⟨cv1, xs.drop k, [], []⟩ = some (some (b, ⟨cv'', [], [], []⟩)) := h2
    obtain ⟨k', hk1', -, hk3'⟩ := runM_frame (f a) cv1 (xs.drop k) b _ h2' rfl
    simp only at hk1'
    refine ⟨xs.take k, xs.drop k, a, cv1, (List.take_append_drop k xs).symm,
      fun ys os roots => hk3 ys os roots, fun ys os roots => ?_⟩
    have := hk3' ys os roots
    have hd : (xs.drop k).take k' = xs.drop k := by
      have hl' : ((xs.drop k).drop k').length = 0 := by rw [← hk1']; rfl
      simp only [List.length_drop] at hl'
      exact List.take_of_length_le (by simp; omega)
    rw [hd] at this
    exact this

theorem RunsToM.bind_inv' {α β : Type} {p : Prog α} {f : α → Prog β} {cv cv'' : Digest}
    {xs : List E} {b : β} (h : RunsToM M (p >>= f) cv xs b cv'') :
    ∃ (xs1 xs2 : List E) (a : α) (cv1 : Digest), xs = xs1 ++ xs2 ∧ RunsToM M p cv xs1 a cv1 ∧
      RunsToM M (f a) cv1 xs2 b cv'' := RunsToM.bind_inv h

/-! ## The elementary runs, inverted -/

theorem RunsToM.pure_inv {α : Type} {a b : α} {cv cv' : Digest} {xs : List E}
    (h : RunsToM M (pure a : Prog α) cv xs b cv') : xs = [] ∧ b = a ∧ cv' = cv :=
  RunsToM.ret_inv h

theorem RunsToM.requireP_inv {c : Prop} [Decidable c] {cv cv' : Digest} {xs : List E} {u : Unit}
    (h : RunsToM M (Prog.require c) cv xs u cv') : c ∧ xs = [] ∧ cv' = cv := by
  by_cases hc : c
  · simp only [Prog.require, hc, ↓reduceIte] at h
    obtain ⟨h1, -, h3⟩ := RunsToM.ret_inv h
    exact ⟨hc, h1, h3⟩
  · have := h [] [] []
    simp [Prog.require, hc, runM, Compile.run] at this

theorem RunsToM.sampleEP_inv {cv cv' : Digest} {xs : List E} {a : E}
    (h : RunsToM M Prog.sampleE cv xs a cv') :
    xs = [] ∧ sqCvM M cv = some cv' ∧ a = challengeOf cv' := by
  rw [← Prog.bind_ret Prog.sampleE] at h
  obtain ⟨c, hc, h⟩ := RunsToM.sampleE_inv h
  obtain ⟨rfl, rfl, rfl⟩ := RunsToM.ret_inv h
  exact ⟨rfl, hc, rfl⟩

theorem RunsToM.readEP_inv {cv cv' : Digest} {xs : List E} {a : E}
    (h : RunsToM M Prog.readE cv xs a cv') : xs = [a] ∧ obsCvM M cv a = some cv' := by
  rw [← Prog.bind_ret Prog.readE] at h
  obtain ⟨x, zs, c, rfl, hc, h⟩ := RunsToM.readE_inv h
  obtain ⟨rfl, rfl, rfl⟩ := RunsToM.ret_inv h
  exact ⟨rfl, hc⟩

theorem RunsToM.readNP_inv {n : ℕ} {cv c : Digest} {xs a : List E}
    (h : RunsToM M (Prog.readN n) cv xs a c) :
    xs.length = n ∧ a = xs ∧ obsAllM M cv xs = some c := by
  rw [← Prog.bind_ret (Prog.readN n)] at h
  obtain ⟨ys, zs, c', rfl, hl, hc, h⟩ := RunsToM.readN_inv h
  obtain ⟨rfl, rfl, rfl⟩ := RunsToM.ret_inv h
  exact ⟨by simp [hl], by simp, by simpa using hc⟩

theorem RunsToM.sampleNP_inv {n : ℕ} {cv cv' : Digest} {xs a : List E}
    (h : RunsToM M (Prog.sampleN n) cv xs a cv') : xs = [] ∧ sqAllM M n cv = some (a, cv') := by
  rw [← Prog.bind_ret (Prog.sampleN n)] at h
  obtain ⟨cs, c, hc, h⟩ := RunsToM.sampleN_inv h
  obtain ⟨rfl, rfl, rfl⟩ := RunsToM.ret_inv h
  exact ⟨rfl, hc⟩

end
end LeanVM.Guest.B1
