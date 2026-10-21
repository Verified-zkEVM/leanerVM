/-
  LeanVM.Guest.B1.Comp.Whir.QueriesOfWith

  The query steps over a total hash are T6-det's: `queriesOfW` is `queriesOfWith`.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.RunW
public import LeanVM.E2E.Complete.Interfaces

/-!
# The query steps over a total hash

`queriesOfW Ht` (`Comp/Whir/RunW.lean`) and `queriesOfWith Ht` (`E2E/Complete/Interfaces.lean`,
what `CapsAgreeWith` reads) are the same function, `queriesOf` with the hash `Ht`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.E2E.Complete

@[expose] public section

/-- **`queriesOfW` is `queriesOfWith`.** -/
theorem queriesOfW_eq_queriesOfWith (Ht : Bytes → Digest) {α : Type} :
    ∀ (p : Prog α) (s : St), queriesOfW Ht p s = queriesOfWith Ht p s
  | .ret _, _ => rfl
  | .fail, _ => rfl
  | .read k, ⟨cv, stream, os, roots⟩ => by
    rcases stream with _ | ⟨x, xs⟩
    · rfl
    · simp only [queriesOfW, queriesOfWith, queriesOfW_eq_queriesOfWith]
  | .sample k, s => by simp only [queriesOfW, queriesOfWith, queriesOfW_eq_queriesOfWith]
  | .grind bits k, ⟨cv, stream, os, roots⟩ => by
    rcases stream with _ | ⟨n, xs⟩
    · rfl
    · simp only [queriesOfW, queriesOfWith, queriesOfW_eq_queriesOfWith]
  | .commit h w k, ⟨cv, stream, os, roots⟩ => by
    rcases stream with _ | ⟨x0, _ | ⟨x1, xs⟩⟩
    · rfl
    · rfl
    · simp only [queriesOfW, queriesOfWith]
      rcases digestOfScalars (x0, x1) with _ | root
      · rfl
      · simp only [queriesOfW_eq_queriesOfWith]
  | .query i ps k, ⟨cv, stream, os, roots⟩ => by
    simp only [queriesOfW, queriesOfWith]
    rcases roots[i]? with _ | ⟨root, hh, ww⟩
    · rfl
    · simp only
      rcases openAll (m := Id) Ht root hh ww ps os with _ | ⟨rows, rest⟩
      · rfl
      · simp only [queriesOfW_eq_queriesOfWith]

theorem queriesOfW_eq_queriesOfWith' (Ht : Bytes → Digest) {α : Type} :
    (queriesOfW Ht : Prog α → St → _) = queriesOfWith Ht :=
  funext fun p => funext fun s => queriesOfW_eq_queriesOfWith Ht p s

end
end LeanVM.Guest.B1
