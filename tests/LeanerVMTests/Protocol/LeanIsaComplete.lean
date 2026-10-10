import LeanerVM.Protocol.LeanIsa.Complete
import LeanerVM.Protocol.Piop

/-!
# Tests: the adaptor, completeness, and leanVM's oracle protocol at leanISA

* **The statements, by type**, at the BLAKE2s inhabitant of `FlockSpec`: a witness satisfying the
  constraint system has its sizes, stacks into a column satisfying `M3Holds` of the leanISA
  instance, and is read back off it.
* **The round trip of the relations.** On admissible sizes, the witness read back off the stack of
  a witness satisfying the constraint system satisfies it too: completeness followed by soundness.
* **leanVM's master theorems hold at the leanISA instance**, at every size and every Flock
  specification: the instance meets the bus phase's conditions and the degree bound.
-/

namespace LeanerVMTests.Protocol.LeanIsaComplete

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization LeanerVM.Protocol
open LeanerVM.Protocol.LeanIsa OracleComp OracleSpec
open Air.Flat (EnsembleWitness)

/-- The BLAKE2s inhabitant. -/
abbrev F₀ : FlockSpec := Blake2sFlock.blake2sFlockSpec

/-- A witness satisfying the constraint system has its sizes. -/
example (prog : Program) (input : PublicInput) (w : EnsembleWitness (leanIsaEnsemble prog))
    (h : SatisfiedBy prog input w) : ∃ s, Sizes.ofWitness w = some s :=
  sizes_of_satisfiedBy h

/-- The adaptor's completeness at the BLAKE2s inhabitant. -/
example (prog : Program) (input : PublicInput) (w : EnsembleWitness (leanIsaEnsemble prog))
    (s : Sizes) (h : SatisfiedBy prog input w) (hs : Sizes.ofWitness w = some s) :
    M3Holds (leanIsaInstance F₀ prog s) input (stackOf F₀ prog s w) :=
  m3Holds_stackOf h hs

/-- The round trip: completeness, then soundness on admissible sizes. -/
example (prog : Program) (input : PublicInput) (w : EnsembleWitness (leanIsaEnsemble prog))
    (s : Sizes) (h : SatisfiedBy prog input w) (hs : Sizes.ofWitness w = some s)
    (hadm : s.Admissible prog) :
    SatisfiedBy prog input (witnessOf F₀ prog s (stackOf F₀ prog s w)) :=
  satisfiedBy_witnessOf F₀ prog s _ hadm (m3Holds_stackOf h hs)

/-- The witness read back has the witness's memory, bytecode block, public input and image. -/
example (prog : Program) (input : PublicInput) (w : EnsembleWitness (leanIsaEnsemble prog))
    (s : Sizes) (h : SatisfiedBy prog input w) (hs : Sizes.ofWitness w = some s) :
    (witnessOf F₀ prog s (stackOf F₀ prog s w)).publicInput = w.publicInput ∧
      imageOf (witnessOf F₀ prog s (stackOf F₀ prog s w)).data = imageOf w.data :=
  ⟨(witnessOf_stackOf h hs).2.2.2.1, (witnessOf_stackOf h hs).2.2.2.2⟩

/-! ## leanVM's oracle protocol at the leanISA instance -/

example (F : FlockSpec) (prog : Program) (s : Sizes) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (leanVmPiop (leanVmPhases (leanIsaInstance F prog s)
        (leanIsa_conditions F prog s))).perfectCompleteness init impl
      (M3Rel (leanIsaInstance F prog s)) (Seam.done (leanIsaInstance F prog s)) :=
  leanVm_perfectCompleteness _ (leanIsa_conditions F prog s) le_rfl init impl

example (F : FlockSpec) (prog : Program) (s : Sizes) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (leanVmVerifier (leanVmPhases (leanIsaInstance F prog s)
        (leanIsa_conditions F prog s))).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (M3Rel (leanIsaInstance F prog s)) (Seam.done (leanIsaInstance F prog s))
      (leanVmSecurity _ (leanIsa_conditions F prog s) le_rfl).extraction.witMid
      (piopExtractor _ (leanVmSecurity _ (leanIsa_conditions F prog s) le_rfl))
      ((leanVmSecurity _ (leanIsa_conditions F prog s) le_rfl).extraction.kSF init impl)
      (piopError (leanIsaInstance F prog s)) :=
  leanVm_rbrKnowledgeSoundness _ (leanIsa_conditions F prog s) le_rfl init impl

end LeanerVMTests.Protocol.LeanIsaComplete
