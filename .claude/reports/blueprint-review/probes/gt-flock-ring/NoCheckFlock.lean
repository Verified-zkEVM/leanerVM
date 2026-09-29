import LeanerVM.Protocol.Spine.Toy
import LeanerVM.Protocol.Spine.Compose

/-!
Probe for the dossier gt-flock-ring (scratch, not part of the repository).

(1) On an instance whose auxiliary predicate is `True` (the toy), a Flock phase with no message,
    no challenge and no check is knowledge sound at error zero between the spine's seams.
(2) On the same instance with a nontrivial auxiliary predicate, the hypothesis under which that
    phase is knowledge sound is false.
-/

namespace GtFlockRingProbe

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Toy CompPoly CPoly OracleComp

/-- A Flock phase that does nothing: the column claims are handed on, no weighted claim. -/
def noCheckFlock : Phase.Def toy (toy.Stmt × PubOut toy) (toy.Stmt × FlockOut toy) :=
  Phase.passThrough toy fun p ↦ (p.1, ⟨p.2.columns, []⟩)

/-- (1) It has the spine's `Phase.Security` from `Seam.pub` to `Seam.flock`. -/
def noCheckFlockSecurity : Phase.Security toy noCheckFlock (Seam.pub toy) (Seam.flock toy) :=
  Phase.passThroughSecurity toy _ (fun _ _ h ↦ ⟨h.1, by simp⟩) (fun _ _ h ↦ ⟨h.1, trivial⟩)

#print axioms noCheckFlockSecurity

/-- Its error is zero at every challenge (there is none). -/
example : noCheckFlock.n = 0 := rfl

/-- The toy with a nontrivial auxiliary predicate: cell 7 of the stack is `1`. -/
abbrev toyAux : M3Instance :=
  { toy with aux := fun q ↦ q.values.get 7 = 1, decAux := fun _ ↦ inferInstance }

/-- (2) For it, "the output seam reflects into the input seam" fails for the do-nothing phase:
the honest toy stack has cell 7 equal to `0`. -/
example : ¬ (∀ (s : toyAux.Stmt × PubOut toyAux) (o : ∀ i, TheOracle toyAux i),
    (((s.1, (⟨s.2.columns, []⟩ : FlockOut toyAux)), o), ()) ∈ Seam.flock toyAux →
      ((s, o), ()) ∈ Seam.pub toyAux) := by
  intro h
  have h' := h ((1 : K), ⟨[]⟩) (fun _ ↦ honest) ⟨by simp, by simp⟩
  have h7 : honest.values.get 7 = 1 := h'.2
  revert h7
  decide +kernel

end GtFlockRingProbe
