import LeanerVM.Protocol.Core

/-!
# The core of knowledge soundness in the random-oracle model: tests

* The event the core concludes is not trivial: on a run whose logs are empty, whatever its proof
  and verdict, the hash does not misbehave. There is no collision and no hit on an empty log, and
  no group flips, since the only state with a history in an empty log is the seed, whose empty
  history announces nothing.
* `core_of_mem_support` gives the core implication in the form the base theorems use it: on every
  possible run of the game with a consistent joint log and an accepting verdict, a failed
  extraction means the hash misbehaves.
-/

namespace LeanerVMTests.Protocol.Core

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol LeanerVM.Protocol.LeanVmReader
open LeanerVM.Protocol.ProofRoots LeanerVM.Protocol.DecodeChain OracleComp OracleSpec

-- The stack's size is never computed here.
attribute [local irreducible] LeanerVM.Protocol.LeanIsa.leanIsaμ LeanerVM.Protocol.LeanIsa.blocks

-- A run with empty logs: no collision, no hit, no flip.
example (prog : Program) (input : PublicInput) (proof : Proof PrunedMerklePaths) (ok : Bool) :
    ¬ HashMisbehaves (rootsOf prog input) (leanVmReader prog input).Flip prog input
      ⟨proof, [], [], ok⟩ := by
  rintro (⟨e, he, -⟩ | (⟨⟨k, hk⟩, -⟩ | ⟨⟨k, hk⟩, -⟩) | ⟨G, hG⟩)
  · simp [Run.log] at he
  · simp [Run.log] at hk
  · simp [Run.log] at hk
  · have hann : (leanVmReader prog input).announcementOf [] = none := rfl
    have hnone : (leanVmReader prog input).groupSlot [] G = none := by
      simp only [SlotReader.groupSlot, chainHistory, HashChain.history, HashChain.walk,
        List.length_nil]
      split_ifs
      · simp only [Option.bind_eq_bind, Option.bind_some, hann, Option.bind_none]
      · rfl
    simp only [SlotReader.Flips, Run.log, List.append_nil, hnone] at hG

-- The core implication at one adversary, as the base theorems use it.
example (prog : Program) (input : PublicInput) (A : Adversary) :
    ∀ g ∈ support (loggedGame Verify.verifyWith prog input A),
      QueryLog.Consistent g.log → g.ok = true →
      ¬ Extracts Blake2sFlock.blake2sFlockSpec prog input g.proof g.logA →
      HashMisbehaves (rootsOf prog input) (leanVmReader prog input).Flip prog input g :=
  fun _ hg hc hok hX ↦ Core.core_of_mem_support hg hc hok hX

end LeanerVMTests.Protocol.Core
