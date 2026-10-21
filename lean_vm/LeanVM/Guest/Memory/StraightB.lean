/-
  LeanVM.Guest.Memory.StraightB

  Straight-line atoms (`Straight.lean`) under any semantics of `BLAKE2S`.
-/

module

public import LeanVM.Guest.Memory.Straight
public import LeanVM.Guest.Memory.RegionsB

/-!
# Straight-line atoms under any `BLAKE2S` semantics

`Straight.lean`'s `holds_atoms` and `atom_holds_of_ok` with `S : BlakeSem` a parameter
(`holdsB_atoms`, `atomB_holds_of_ok`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

variable {S : BlakeSem}

/-! ## Bodies of atoms -/

theorem holdsB_atoms {rd : Reader} {σ : Val} {as : List Atom} (h : ∀ a ∈ as, a.HoldsB S rd σ) :
    ∀ e ∈ as.map Ev.atom, e.HoldsB S rd σ := by
  intro e he
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
  exact h a ha

/-! ## Straight bodies with calls -/

/-- An atom of a straight body holds when its path's events are `Ok`. -/
theorem atomB_holds_of_ok {C : CallRel} {rd : Reader} {σ : Val} {pre : List Stmt} {a : Atom}
    (ha : Stmt.atom a ∈ pre) (h : ∀ e ∈ pre.flatMap (slEvs σ), e.OkB S C rd σ) : a.HoldsB S rd σ :=
  (h (.atom a) (List.mem_flatMap.mpr ⟨_, ha, by simp [slEvs]⟩)).1

end
end LeanVM.Guest.Memory
