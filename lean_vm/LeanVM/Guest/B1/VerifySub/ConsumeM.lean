/-
  LeanVM.Guest.B1.VerifySub.ConsumeM

  How many stream words the deferring verifier's phases read, over a hash model: a run with every
  hash answered reads what the program's shape fixes.
-/

module

public import LeanVM.Guest.B1.VerifySub.Consume
public import LeanVM.Guest.B1.VerifySub.InterfaceM

/-!
# The phases' stream lengths over a hash model

`Reads Q n p` is a fact of the program alone (`Consume.lean`). `Reads.runM`: a successful run of
such a program over a hash model consumes exactly `n` words of its stream, as `Reads.run` over
the deployed hash; so does a `RunsToM` (`RunsToM.length_eq`) or a `RunsWithM`
(`RunsWithM.length_eq`). The phases' counts (`reads_gkrPhase`, `reads_tablesSeg`,
`reads_verifyFlock`, `reads_whirOpen`) then apply to the runs over the model unchanged.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {M : HashModel} {α : Type}

unseal Reads in
/-- A successful run over the model of a program reading `n` words consumes `n` words of its
stream. -/
theorem Reads.runM {Q : α → Prop} :
    ∀ {n : ℕ} {p : Prog α}, Reads Q n p → ∀ {s : St} {a : α} {s' : St},
      runM M p s = some (some (a, s')) → Q a ∧ ∃ ys : List E, ys.length = n ∧ s.stream = ys ++ s'.stream
  | _, .ret a, h, s, b, s', hr => by
    obtain ⟨rfl, hq⟩ := h
    have hr' : some (some (a, s)) = some (some (b, s')) := hr
    simp only [Option.some.injEq, Prod.mk.injEq] at hr'
    obtain ⟨rfl, rfl⟩ := hr'
    exact ⟨hq, [], rfl, rfl⟩
  | _, .fail, _, _, _, _, hr => by cases hr
  | _ + 1, .read _, _, ⟨_, [], _, _⟩, _, _, hr => by cases hr
  | _ + 1, .read k, h, ⟨cv, x :: xs, os, roots⟩, _, _, hr => by
    simp only [Compile.run, absorbBlock, Option.bind_eq_bind] at hr
    obtain ⟨c, -, hr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨hq, ys, hl, he⟩ := Reads.runM (h x) (s := ⟨c, xs, os, roots⟩) hr
    exact ⟨hq, x :: ys, by simp [hl], congrArg (x :: ·) he⟩
  | 0, .read _, h, _, _, _, _ => h.elim
  | _, .sample k, h, ⟨cv, xs, os, roots⟩, _, _, hr => by
    simp only [Compile.run, absorbBlock, Option.bind_eq_bind] at hr
    obtain ⟨c, -, hr⟩ := Option.bind_eq_some_iff.mp hr
    exact Reads.runM (h _) (s := ⟨c, xs, os, roots⟩) hr
  | _ + 1, .grind _ _, _, ⟨_, [], _, _⟩, _, _, hr => by cases hr
  | _ + 1, .grind b k, h, ⟨cv, x :: xs, os, roots⟩, a, s', hr => by
    simp only [Compile.run, absorbBlock, Option.bind_eq_bind] at hr
    obtain ⟨c1, -, hr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨c2, -, hr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨c3, -, hr⟩ := Option.bind_eq_some_iff.mp hr
    split at hr
    · obtain ⟨hq, ys, hl, he⟩ := Reads.runM (p := k) h hr
      exact ⟨hq, x :: ys, by simp [hl], congrArg (x :: ·) he⟩
    · cases hr
  | 0, .grind _ _, h, _, _, _, _ => h.elim
  | _ + 2, .commit _ _ _, _, ⟨_, [], _, _⟩, _, _, hr => by cases hr
  | _ + 2, .commit _ _ _, _, ⟨_, [_], _, _⟩, _, _, hr => by cases hr
  | _ + 2, .commit hh ww k, h, ⟨cv, x0 :: x1 :: xs, os, roots⟩, a, s', hr => by
    simp only [Compile.run, absorbBlock, Option.bind_eq_bind] at hr
    obtain ⟨c1, -, hr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨c2, -, hr⟩ := Option.bind_eq_some_iff.mp hr
    split at hr
    · obtain ⟨hq, ys, hl, he⟩ := Reads.runM (p := k) h hr
      exact ⟨hq, x0 :: x1 :: ys, by simp [hl], congrArg (fun l => x0 :: x1 :: l) he⟩
    · cases hr
  | 0, .commit _ _ _, h, _, _, _, _ => h.elim
  | 1, .commit _ _ _, h, _, _, _, _ => h.elim
  | _, .query _ ps k, h, ⟨cv, xs, os, roots⟩, a, s', hr => by
    simp only [Compile.run] at hr
    split at hr
    · cases hr
    · rename_i root hh ww _
      simp only [Option.bind_eq_bind] at hr
      obtain ⟨o, -, hr⟩ := Option.bind_eq_some_iff.mp hr
      rcases o with _ | ⟨rows, rest⟩
      · cases hr
      · exact Reads.runM (h rows) (s := ⟨cv, xs, rest, roots⟩) hr

/-- A run over the model reading exactly `xs` of a program reading `n` words: `xs` has `n`
words. -/
theorem RunsToM.length_eq {Q : α → Prop} {n : ℕ} {p : Prog α} {cv cv' : Digest} {xs : List E}
    {a : α} (h : RunsToM M p cv xs a cv') (hp : Reads Q n p) : xs.length = n ∧ Q a := by
  obtain ⟨hq, ys, hl, he⟩ := hp.runM (h [] [] [])
  simp only [List.append_nil] at he
  exact ⟨by rw [he, hl], hq⟩

/-- A run over the model reading exactly `xs` and openings of a program reading `n` words: `xs`
has `n` words. -/
theorem RunsWithM.length_eq {Q : α → Prop} {n : ℕ} {p : Prog α} {cv cv' : Digest} {xs : List E}
    {os : List Opening} {roots roots' : List (Digest × ℕ × ℕ)} {a : α}
    (h : RunsWithM M p cv xs os roots a cv' roots') (hp : Reads Q n p) : xs.length = n ∧ Q a := by
  obtain ⟨hq, ys, hl, he⟩ := hp.runM (h [] [])
  simp only [List.append_nil] at he
  exact ⟨by rw [he, hl], hq⟩

end
end LeanVM.Guest.B1.VerifySub
