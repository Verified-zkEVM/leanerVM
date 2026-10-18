import LeanerVM.Protocol.LeanIsa.Complete
import LeanerVM.Protocol.Piop
import LeanerVMTests.Arithmetization.Statement

/-!
# Tests: the adaptor, completeness, and leanVM's oracle protocol at leanISA

* **The statements, by type**, at the BLAKE2s inhabitant of `FlockSpec`: a witness satisfying the
  constraint system has its sizes, stacks into a column satisfying `M3Holds` of the leanISA
  instance, and is read back off it.
* **The relation is inhabited.** The hand-built witness of the constraint statement's tests
  (`fill_satisfiedBy`) stacks into a column satisfying `M3Holds` of the leanISA instance at the
  BLAKE2s inhabitant.
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

/-- The leanISA instance's relation is inhabited: the constraint statement's fixture stacks. -/
example : ∃ s q, M3Holds (leanIsaInstance F₀ LeanerVMTests.Arithmetization.Statement.fillProg s)
    LeanerVMTests.Arithmetization.Statement.mulInput q :=
  let ⟨s, hs⟩ := sizes_of_satisfiedBy LeanerVMTests.Arithmetization.Statement.fill_satisfiedBy
  ⟨s, _, m3Holds_stackOf LeanerVMTests.Arithmetization.Statement.fill_satisfiedBy hs⟩

/-! ## leanVM's oracle protocol at the leanISA instance -/

example (F : FlockSpec) (prog : Program) (s : Sizes) (initial : PFunctor)
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (input : PublicInput)
    (q : Column (leanIsaInstance F prog s).μ)
    (h : ((input, fun i ↦ i.elim0), q) ∈ M3Rel (leanIsaInstance F prog s)) :
    Pr{let x ← (leanVmPiop (leanVmPhases (leanIsaInstance F prog s) (leanIsa_conditions F prog s))
      initial).execute impl input q}[x.2.2 = some ()] = 1 :=
  leanVm_perfectCompleteness _ (leanIsa_conditions F prog s) le_rfl initial impl input q h

example (F : FlockSpec) (prog : Program) (s : Sizes) (initial : PFunctor)
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (input : PublicInput) :
    ∃ cert : Interaction.Oracle.Security.KnowledgeCertificate
        (piopSlot (leanIsaInstance F prog s)).tree (piopSlot (leanIsaInstance F prog s)).roles
        ⟨Column (leanIsaInstance F prog s).μ, M3Holds (leanIsaInstance F prog s) input⟩,
      cert.extractor = piopExtractor _ (leanVmSecurity _ (leanIsa_conditions F prog s) le_rfl)
        input ∧
      cert.challenges = Typed.schedule (piopSlot (leanIsaInstance F prog s)).tree
        (piopSlot (leanIsaInstance F prog s)).roles (piopSlot (leanIsaInstance F prog s)).samplers
        (piopErrors (leanIsaInstance F prog s)) ∧
      Interaction.Oracle.Security.SamplesChallenges unifSpec (QueryImpl.id' unifSpec)
        (piopSlot (leanIsaInstance F prog s)).tree (piopSlot (leanIsaInstance F prog s)).roles
        (piopSlot (leanIsaInstance F prog s)).oracles initial impl _
        (leanVmVerifier (leanVmPhases _ (leanIsa_conditions F prog s)) initial input)
        cert.challenges :=
  leanVm_knowledgeSoundness _ (leanIsa_conditions F prog s) le_rfl initial impl input

end LeanerVMTests.Protocol.LeanIsaComplete
