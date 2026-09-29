import LeanerVM.Protocol.Spine.Toy
import LeanerVM.Protocol.Spine.Compose

/-!
Probe P5 (code-spine): the pass-through bus phase of the repository's test (`trivPhases.bus`)
has no `Phase.Security` against the spine's seams, on the toy instance.

`badConstraint` at statement `2` is outside `M3Holds` and the pass-through's output on it (no
claim) is inside the bus seam. A knowledge state function must be true at the end of an
accepting transcript and, the phase having no round, the end is the beginning, where the state
is the input seam.
-/

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Toy CompPoly CPoly OracleComp
  OracleSpec ProtocolSpec

namespace Probe

/-- The test's stack `badConstraint`: column 2 is `[2, 0]`. -/
def badConstraint : Column 3 := ⟨#v[1, 1, 1, 1, 2, 0, 0, 0]⟩

/-- The statement map of `trivPhases.bus`: no claim. -/
def dropAll (s : K) : K × BusOut toy := (s, ⟨[], []⟩)

/-- Outside the relation. -/
theorem bad_not_m3Holds : ¬ M3Holds toy (2 : K) badConstraint := by decide +kernel

/-- Inside the bus seam, with no claim. -/
theorem bad_mem_bus :
    ((dropAll 2, fun _ : Fin 1 ↦ badConstraint), ()) ∈ Seam.bus toy :=
  ⟨by simp [dropAll], by simp [dropAll], by simp [dropAll], by decide +kernel, trivial⟩

/-- The reflection hypothesis of `Phase.passThroughSecurity` is false at the bus seam. -/
theorem not_reflects : ¬ ∀ (s : K) (o : ∀ i, TheOracle toy i),
    ((dropAll s, o), ()) ∈ Seam.bus toy → ((s, o), ()) ∈ Seam.commit toy := fun h ↦
  bad_not_m3Holds (h 2 (fun _ ↦ badConstraint) bad_mem_bus)

/-- The empty implementation of the empty shared oracle. -/
def noImpl : QueryImpl []ₒ (StateT Unit ProbComp) := fun t ↦ PEmpty.elim t

/-- No `Phase.Security` exists for the pass-through bus phase: not only the repository's
constructor fails, the type is empty. -/
theorem no_security (S : Phase.Security toy (Phase.passThrough toy dropAll) (Seam.commit toy)
    (Seam.bus toy)) : False := by
  have K := S.kSF (pure ()) noImpl
  let stmt : K × ∀ i, TheOracle toy i := (2, fun _ ↦ badConstraint)
  let tr : (Phase.passThrough toy dropAll).pSpec.FullTranscript := fun i ↦ Fin.elim0 i
  have htr : tr = (default : (Phase.passThrough toy dropAll).pSpec.Transcript 0) :=
    funext fun i ↦ Fin.elim0 i
  have hpos : Pr[fun stmtOut ↦ (stmtOut, ()) ∈ Seam.bus toy | OptionT.mk do
      (simulateQ noImpl ((Phase.passThrough toy dropAll).red.verifier.toVerifier.run stmt
        tr)).run' (← (pure () : ProbComp Unit))] > 0 := by
    have hrun : (Phase.passThrough toy dropAll).red.verifier.toVerifier.run stmt tr =
        pure (dropAll 2, fun _ ↦ badConstraint) :=
      Component.passThroughVerifier_toVerifier_run (TheOracle toy) dropAll 2
        (fun _ ↦ badConstraint) tr
    rw [hrun]
    change Pr[_ | OptionT.mk (do let st ← (pure () : ProbComp Unit); (simulateQ noImpl
      (OptionT.run (pure (dropAll 2, fun _ : Fin 1 ↦ badConstraint)))).run' st)] > 0
    rw [OptionT.run_pure, simulateQ_pure]
    rw [gt_iff_lt, probEvent_pos_iff]
    refine ⟨(dropAll 2, fun _ ↦ badConstraint), ?_, bad_mem_bus⟩
    simp
  have hfull := K.toFun_full stmt tr () hpos
  rw [htr] at hfull
  exact bad_not_m3Holds ((K.toFun_empty stmt _).mpr hfull)

#print axioms no_security

end Probe
