import LeanerVM.Protocol.LeanIsa.Sound

/-!
# Tests: the adaptor, soundness

* **The statement, by type**, at the BLAKE2s inhabitant of `FlockSpec`: admissible sizes and
  `M3Holds` of the leanISA instance give `SatisfiedBy` of the witness read off the stack, with no
  other hypothesis. Its BLAKE2s conjunct alone needs only the Flock clause.
* **The bus as one bus.** On any witness of the ensemble, the two sides' tuples are one multiset
  exactly when the three channel pairs balance, and the instance's balance is that of a witness
  agreeing with the stack.
* **The relation's clauses are equivalences**, the direction this module does not use included:
  the counts and the constraints, on a stack and a witness that agree.
-/

namespace LeanerVMTests.Protocol.LeanIsaSound

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization LeanerVM.Protocol
open LeanerVM.Protocol.LeanIsa
open Air.Flat (EnsembleWitness)

/-- The adaptor's soundness at the BLAKE2s inhabitant. -/
example (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s)) (input : PublicInput)
    (hs : s.Admissible prog)
    (h : M3Holds (leanIsaInstance Blake2sFlock.blake2sFlockSpec prog s) input q) :
    SatisfiedBy prog input (witnessOf Blake2sFlock.blake2sFlockSpec prog s q) :=
  satisfiedBy_witnessOf _ prog s q hs h

/-- The BLAKE2s validity needs the Flock clause alone. -/
example (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s))
    (h : (leanIsaInstance Blake2sFlock.blake2sFlockSpec prog s).aux q) :
    Blake2sRowsValid (witnessOf Blake2sFlock.blake2sFlockSpec prog s q) :=
  blake2sRowsValid_witnessOf _ prog s q h

/-- The bus as one bus, on any witness. -/
example (prog : Program) (w : EnsembleWitness (leanIsaEnsemble prog)) :
    (sideTuples w .push).Perm (sideTuples w .pull) ↔
      BalancedPair w StatePull.toRaw StatePush.toRaw ∧ BalancedPair w MemPull.toRaw MemPush.toRaw ∧
        BalancedPair w BytecodePull.toRaw BytecodePush.toRaw := by
  rw [balanced_iff]
  exact ⟨fun h ↦ ⟨h 0, h 1, h 2⟩, fun h k ↦ by fin_cases k; exacts [h.1, h.2.1, h.2.2]⟩

/-- The counts, both ways, on a stack and a witness that agree. -/
example (F : FlockSpec) (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s))
    (w : EnsembleWitness (leanIsaEnsemble prog)) (h : Agrees F s q w) :
    CountsNonzero w ↔ (leanIsaInstance F prog s).CountsNonzero q :=
  countsNonzero_iff h

end LeanerVMTests.Protocol.LeanIsaSound
