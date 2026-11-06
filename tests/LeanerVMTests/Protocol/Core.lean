import LeanerVM.Protocol.Core

/-!
# The core of knowledge soundness in the random-oracle model: tests

* The event the core concludes is not trivial: on a run whose logs are empty, whatever its proof
  and verdict, the hash does not misbehave, even with the flips on every statement's chain, which
  include those on the statement's own (`SlotReader.flip_of_flipFor`). There is no collision and
  no hit on an empty log, and no group flips, since an empty log opens no statement and the empty
  history announces nothing.
* `core_of_mem_support` gives the core implication in the form the base theorems use it: on every
  possible run of the game with a consistent joint log and an accepting verdict, a failed
  extraction means the hash misbehaves, a flip being one on the chain of the statement on a group
  the verifier asked, which is a flip on the statement's chain, which is a flip.
-/

namespace LeanerVMTests.Protocol.Core

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol LeanerVM.Protocol.LeanVmReader
open LeanerVM.Protocol.ProofRoots LeanerVM.Protocol.DecodeChain OracleComp OracleSpec

-- The stack's size is never computed here.
attribute [local irreducible] LeanerVM.Protocol.LeanIsa.leanIsaμ LeanerVM.Protocol.LeanIsa.blocks

-- A run with empty logs: no collision, no hit, no flip.
example (prog : Program) (input : PublicInput) (proof : Proof PrunedMerklePaths) (ok : Bool) :
    ¬ HashMisbehavesFrom [] (rootsOf prog input) leanVmReader.Flip ⟨proof, [], [], ok⟩ := by
  rintro (⟨e, he, -⟩ | (⟨⟨k, hk⟩, -⟩ | ⟨⟨k, hk⟩, -⟩) | ⟨G, hG⟩)
  · simp [Run.log] at he
  · simp [Run.log] at hk
  · simp [Run.log] at hk
  · have hann : ∀ st, leanVmReader.announcementOf st [] = none := fun _ ↦ rfl
    have hnone : leanVmReader.groupSlot [] G = none := by
      simp only [SlotReader.groupSlot, chainHistory, HashChain.history, HashChain.walk,
        List.length_nil]
      split_ifs
      · simp only [Option.bind_eq_bind, Option.bind_some, hann, Option.bind_none]
        cases leanVmReader.stmtAt [] G.cv <;> rfl
      · rfl
    simp only [SlotReader.Flips, Run.log, List.append_nil, hnone] at hG

-- The core implication at one adversary, as the base theorems use it.
example (prog : Program) (input : PublicInput) (A : Adversary) :
    ∀ g ∈ support (loggedGame Verify.verifyWith prog input A),
      QueryLog.Consistent g.log → g.ok = true →
      ¬ Extracts Blake2sFlock.blake2sFlockSpec prog input g.proof g.logA →
      HashMisbehavesFrom [] (rootsOf prog input) (leanVmReader.VerifierFlipFor (prog, input)) g :=
  fun _ hg hc hok hX ↦ Core.core_of_mem_support hg hc hok hX

-- A flip the verifier asked for is a flip on the chain of the statement, which is a flip, so the
-- event the core concludes lies inside the one the random-oracle bound bounds.
example (prog : Program) (input : PublicInput) (g : Run)
    (h : HashMisbehavesFrom [] (rootsOf prog input) (leanVmReader.VerifierFlipFor (prog, input))
      g) :
    HashMisbehavesFrom [] (rootsOf prog input) (leanVmReader.FlipFor (prog, input)) g :=
  h.mono fun _ ↦ leanVmReader.flipFor_of_verifierFlipFor
example (prog : Program) (input : PublicInput) (g : Run)
    (h : HashMisbehavesFrom [] (rootsOf prog input) (leanVmReader.VerifierFlipFor (prog, input))
      g) :
    HashMisbehavesFrom [] (rootsOf prog input) leanVmReader.Flip g :=
  h.mono fun _ ↦ leanVmReader.flip_of_verifierFlipFor

end LeanerVMTests.Protocol.Core
