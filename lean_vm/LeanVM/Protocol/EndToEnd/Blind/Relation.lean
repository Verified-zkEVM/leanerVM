/-
  LeanVM.Protocol.EndToEnd.Blind.Relation

  The relation the Flock-blind verifier proves knowledge of: `M3Holds` without the Flock region's
  predicate, which is `M3Holds` of the leanISA instance without a Flock region.
-/

module

public import LeanVM.Protocol.EndToEnd.Front.InstanceWith

/-!
# The relation without Flock

The Flock-blind verifier V° (`LeanVM.Spec.Ideal.Blind`, `docs/roadmap/e2e-security.md` (removed; in git at `6ffa1d1f`) D3) never
compares the lincheck's matrices with its sumcheck, so Flock's R1CS on the region `q_flock`
(`M3Instance.aux`) is not established: what V° extracts is `M3HoldsBlind`, the constraints, the
bus, the counts and the public lines.

* `M3HoldsBlind I input q`: `M3Holds` without its last clause;
* `M3Holds.blind`: `M3Holds` implies it;
* `m3Holds_none_iff`: it is `M3Holds` of the leanISA instance without a Flock region
  (`leanIsaWith F prog s none`), the instance the front phases are run at for V°.
-/

namespace LeanVM.Protocol

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.LeanIsa

@[expose] public section

/-- **`M3Holds` without Flock's R1CS**: the constraints, the bus, the counts and the public lines;
not the Flock region's predicate (`M3Instance.aux`). -/
def M3HoldsBlind (I : M3Instance) (input : I.Stmt) (q : Column I.μ) : Prop :=
  I.ConstraintsVanish q ∧ I.Balanced q ∧ I.CountsNonzero q ∧ I.PublicLinesHold input q

-- Every clause is a finite check over computable data.
deriving instance Decidable for M3HoldsBlind

/-- The relation implies the relation without Flock. -/
theorem M3Holds.blind {I : M3Instance} {input : I.Stmt} {q : Column I.μ}
    (h : M3Holds I input q) : M3HoldsBlind I input q :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- **The relation without Flock is the relation of the instance without a Flock region.** -/
theorem m3Holds_none_iff (F : FlockSpec) (prog : Program) (s : Sizes) (input : PublicInput)
    (q : Column (leanIsaμ prog s)) :
    M3Holds (leanIsaWith F prog s none) input q ↔ M3HoldsBlind (leanIsaInstance F prog s) input q :=
  have hb := balanced_with (leanIsaInstance F prog s) none q
  ⟨fun h ↦ ⟨h.1, hb.1 h.2.1, h.2.2.1, h.2.2.2.1⟩,
    fun h ↦ ⟨h.1, hb.2 h.2.1, h.2.2.1, h.2.2.2, aux_none F prog s q⟩⟩

end
end LeanVM.Protocol
