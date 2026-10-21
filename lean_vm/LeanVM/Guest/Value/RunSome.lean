/-
  LeanVM.Guest.Value.RunSome

  The compiled verifier's run over an answered hash that answers every input: `some` of the run
  over the hash itself.
-/

module

public import LeanVM.Spec.Verifier

/-!
# Runs over a hash that answers everything

`Spec/Verifier.lean`'s `Compile.run` is generic in the monad of its hash. Over `Option` with a
hash that answers every input, `fun x ↦ some (f x)` (the deployed model's `H`), each function is
`some` of the one over `Id` with `f`: `climb_some`, `openOne_some`, `openAll_some`, `run_some`,
`runProof_some`. This is the bridge from a statement over an answered hash
(`Value.HashModel.H`) to the deployed one.
-/

namespace LeanVM.Guest.Value

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile

@[expose] public section

/-- A bind in `Id` is an application. -/
theorem id_bind {α β : Type} (x : Id α) (g : α → Id β) : x >>= g = g x := rfl

variable (f : Bytes → Digest)

theorem absorbBlock_some (cv : Digest) (b : Bytes) :
    absorbBlock (m := Option) (fun x ↦ some (f x)) cv b = some (absorbBlock (m := Id) f cv b) :=
  rfl

theorem climb_some : ∀ (node : Digest) (q : ℕ) (ss : List Digest),
    climb (m := Option) (fun x ↦ some (f x)) node q ss = some (climb (m := Id) f node q ss)
  | _, _, [] => rfl
  | node, q, s :: ss => by
    simp only [climb]
    split
    · exact climb_some _ _ ss
    · exact climb_some _ _ ss

theorem openOne_some (root : Digest) (height width q : ℕ) (o : Opening) :
    openOne (m := Option) (fun x ↦ some (f x)) root height width q o =
      some (openOne (m := Id) f root height width q o) := by
  simp only [openOne]
  split
  · simp only [climb_some]
    rfl
  · rfl

theorem openAll_some (root : Digest) (height width : ℕ) :
    ∀ (qs : List ℕ) (os : List Opening),
      openAll (m := Option) (fun x ↦ some (f x)) root height width qs os =
        some (openAll (m := Id) f root height width qs os)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | q :: qs, o :: os => by
    simp only [openAll, openOne_some, openAll_some root height width qs os, Option.bind_eq_bind,
      Option.bind_some, id_bind]
    split_ifs <;> rfl

/-- **The run over a hash answering everything** is `some` of the run over the hash. -/
theorem run_some {α : Type} : ∀ (p : Prog α) (s : St),
    run (m := Option) (fun x ↦ some (f x)) p s = some (run (m := Id) f p s)
  | .ret _, _ => rfl
  | .fail, _ => rfl
  | .read k, s => by
    simp only [run]
    split
    · rfl
    · exact run_some _ _
  | .sample k, s => by
    simp only [run]
    exact run_some _ _
  | .grind bits k, s => by
    simp only [run]
    split
    · rfl
    · simp only [absorbBlock_some, Option.bind_eq_bind, Option.bind_some, id_bind]
      split_ifs
      · exact run_some _ _
      · rfl
  | .commit height width k, s => by
    simp only [run]
    split
    · simp only [absorbBlock_some, Option.bind_eq_bind, Option.bind_some, id_bind]
      split
      · exact run_some _ _
      · rfl
    · rfl
  | .query i ps k, s => by
    simp only [run]
    split
    · rfl
    · simp only [openAll_some, Option.bind_eq_bind, Option.bind_some, id_bind]
      split
      · exact run_some _ _
      · rfl

/-- A proof's acceptance over a hash answering everything is `some` of it over the hash. -/
theorem runProof_some (P : Prog Bool) (seed : Digest) (π : Proof) :
    runProof (m := Option) (fun x ↦ some (f x)) P seed π = some (runProof (m := Id) f P seed π) := by
  simp only [runProof, run_some, Option.bind_eq_bind, Option.bind_some, id_bind]
  split <;> rfl

end
end LeanVM.Guest.Value
