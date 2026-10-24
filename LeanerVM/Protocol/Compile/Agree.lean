/-
  LeanerVM.Protocol.Compile.Agree

  The phases agree: on every transcript of the compiled protocol its verifier accepts, the
  executable verifier's algebra accepts the transcript's wire and rows; so the honest prover's
  proof is accepted, with no hypothesis left.
-/

module

public import LeanerVM.Protocol.Compile.Front
public import LeanerVM.Protocol.Compile.Whir
public import LeanerVM.Protocol.Prove.Complete

/-!
# The phases agree

The compiled protocol (`Prove.compiledDef`, the list-binding compilation at leanVM's instance and
WHIR's deployed chain) is eight components in sequence: the level-0 commitment, the four front
phases over the word, the opening's batching, the opening's input and WHIR's opening. Its
verifier is guarded (`listBindingGuarded`, from the components' guarded forms), so its run is the
components' runs in sequence (`Component.Guarded.run_append_eq_some`).

**`phasesAgree`**: on every full transcript the compiled verifier accepts, the executable
verifier's algebra (`Verify.algebra`) accepts the transcript's wire (`DecodeChain.wireOf`) and
the rows its words have at its positions (`Prove.rowsOf`). The front phases accept their wires
with the oracle verifiers' outputs (`leanVmFront_of_checks`), the opening claim is the batch the
compiled verifier hands to WHIR (`openingClaim_eq`), and WHIR's algebra accepts its wire and
rows (`whirCheck_of_run`), level 0's rows read off the committed word.

With it the honest prover is complete with no hypothesis (`Prove.baseProver_complete`), from
`Prove.baseProver_complete_of_agree`.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization Blake2sHash LeanIsa Whir
  ProtocolSpec StepSchedule Verify DecodeChain
open Air.Flat (EnsembleWitness)

@[expose] public section

namespace Compile

/-- The list-binding compilation's guarded form, from its components'. -/
def listBindingGuarded {I : M3Instance} {sh : Whir.Shape} {κ : ℕ} (P : Phases I)
    (hμ : κ + sh.ℓ = I.μ) (L : Ladder sh κ) : Component.Guarded (listBindingDef P hμ L) :=
  (((((((Component.Guarded.ofPure Component.sendVerifierPure :
      Component.Guarded (commitWord I hμ)).append
    (Component.Front.toGuarded (P.bus.front.overFront _ _))).append
    (Component.Front.toGuarded (P.table.front.overFront _ _))).append
    (Component.Front.toGuarded (P.pub.front.overFront _ _))).append
    (Component.Front.toGuarded (P.flock.front.overFront _ _))).append
    (Component.Front.toGuarded (Component.sampleFront _ _ _ _) :
      Component.Guarded (openingBatchOver I (KOracle sh κ)))).append
    (Component.Guarded.ofPure (Component.mapOraclesPure _ _ _ _) :
      Component.Guarded (openInput I hμ))).append
    (whirOpenGuarded sh κ L)

/-- Level 0's rows read as the committed word's: the stored row, lanes in reverse, read back. -/
theorem laneRow_level0 {ℓ b t : ℕ} (x : KWord ℓ b t) (p : Fin (2 ^ b)) :
    Verify.laneRow true ℓ ((x.row p).toList.reverse) = some (x.lift.row p) := by
  simp only [Verify.laneRow, ↓reduceIte, List.reverse_reverse, KWord.lift]
  rw [← Vector.toList_map, RoundPoly.ofList?_toList]

/-- **The phases agree**: on every full transcript of the compiled protocol at leanVM's instance
and WHIR's deployed chain that its verifier accepts on the public input, the executable
verifier's algebra accepts the transcript's wire and the rows its words have at its positions. -/
theorem phasesAgree (prog : Program) (s : Sizes) (hs : s.Admissible prog) (ρ : ℕ)
    (hρ : validRate ρ) (input : PublicInput) : Prove.PhasesAgree prog s hs ρ hρ input := by
  intro tr so h
  rw [Component.Guarded.verifier_run (listBindingGuarded (leanVmPhases (leanVm prog s)
      (leanIsa_conditions Blake2sFlock.blake2sFlockSpec prog s))
    (leanIsaChain_height Blake2sFlock.blake2sFlockSpec prog s hs ρ hρ)
    (leanIsaChain prog s hs ρ hρ).ladder)] at h
  simp only [runNoOracle, simulateQ_pure, Id.run_pure] at h
  -- the transcript's eight parts
  obtain ⟨t₇', t₈, e⟩ := exists_eq_append tr
  subst tr
  obtain ⟨t₆', t₇, e⟩ := exists_eq_append t₇'
  subst t₇'
  obtain ⟨t₅', t₆, e⟩ := exists_eq_append t₆'
  subst t₆'
  obtain ⟨t₄', t₅, e⟩ := exists_eq_append t₅'
  subst t₅'
  obtain ⟨t₃', t₄, e⟩ := exists_eq_append t₄'
  subst t₄'
  obtain ⟨t₂', t₃, e⟩ := exists_eq_append t₃'
  subst t₃'
  obtain ⟨t₁, t₂, e⟩ := exists_eq_append t₂'
  subst t₂'
  -- the eight components
  obtain ⟨x₇, a₇, h₈⟩ := Component.Guarded.run_append_eq_some h
  obtain ⟨x₆, a₆, h₇⟩ := Component.Guarded.run_append_eq_some a₇
  obtain ⟨x₅, a₅, h₆⟩ := Component.Guarded.run_append_eq_some a₆
  obtain ⟨x₄, a₄, h₅⟩ := Component.Guarded.run_append_eq_some a₅
  obtain ⟨x₃, a₃, h₄⟩ := Component.Guarded.run_append_eq_some a₄
  obtain ⟨x₂, a₂, h₃⟩ := Component.Guarded.run_append_eq_some a₃
  obtain ⟨x₁, a₁, h₂⟩ := Component.Guarded.run_append_eq_some a₂
  simp only [FullTranscript.append_fst, FullTranscript.append_snd] at a₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
  obtain rfl := Component.Guarded.run_ofPure_eq_some a₁
  -- the front phases
  obtain ⟨y₂, b₂, rfl⟩ := Component.Guarded.run_toGuarded_eq_some _ h₂
  obtain ⟨c₂, rfl⟩ := (Component.Front.run_eq_some_iff _).mp b₂
  obtain ⟨y₃, b₃, rfl⟩ := Component.Guarded.run_toGuarded_eq_some _ h₃
  obtain ⟨c₃, rfl⟩ := (Component.Front.run_eq_some_iff _).mp b₃
  obtain ⟨y₄, b₄, rfl⟩ := Component.Guarded.run_toGuarded_eq_some _ h₄
  obtain ⟨c₄, rfl⟩ := (Component.Front.run_eq_some_iff _).mp b₄
  obtain ⟨y₅, b₅, rfl⟩ := Component.Guarded.run_toGuarded_eq_some _ h₅
  obtain ⟨c₅, rfl⟩ := (Component.Front.run_eq_some_iff _).mp b₅
  -- the batching challenge and the opening's input
  obtain ⟨y₆, b₆, rfl⟩ := Component.Guarded.run_toGuarded_eq_some _ h₆
  obtain ⟨-, rfl⟩ := (Component.Front.run_eq_some_iff _).mp b₆
  obtain rfl := Component.Guarded.run_ofPure_eq_some h₇
  dsimp only [Component.Front.overFront, leanVmPhases, Component.sendVerifierPure,
    Component.mapOraclesPure, Component.sampleFront, Opening.batched, kwordMap] at c₂ c₃ c₄ c₅ h₈
  have hfront := leanVmFront_of_checks prog s input t₂ t₃ t₄ t₅ c₂ c₃ c₄ c₅
  simp only [Option.bind_eq_some_iff] at hfront
  obtain ⟨p, ⟨t, ⟨b, hb, ht⟩, hp⟩, hf⟩ := hfront
  simp only [wireOf, Prove.rowsOf, Prove.level0Word, Prove.ladderPart,
    FullTranscript.append_fst, FullTranscript.append_snd, algebra, flockWireOpt, hb, ht, hp, hf,
    openingClaim_eq]
  exact whirCheck_of_run (leanIsaChain prog s hs ρ hρ).ladder
    (leanIsaChain_height Blake2sFlock.blake2sFlockSpec prog s hs ρ hρ) _ _ _
    (fun p ↦ ((t₁ 0).row p).toList.reverse) (laneRow_level0 (t₁ 0)) t₈ h₈

end Compile

namespace Prove

/-- **Completeness of the honest prover**: for every byte hash `H` and fuel, a proof
`proveWith` returns for a witness satisfying leanISA's constraint statement on the public input,
at the deployed Flock specification, is accepted by the executable verifier at `H`. -/
theorem baseProver_complete (H : List UInt8 → Digest) (fuel : ℕ) {prog : Program}
    {input : PublicInput} {w : EnsembleWitness (leanIsaEnsemble prog)} {ρ : ℕ}
    {proof : Proof PrunedMerklePaths} (hsat : SatisfiedBy prog input w)
    (hp : proveWith (m := Id) H fuel Blake2sFlock.blake2sFlockSpec prog input w ρ = some proof) :
    Verify.verifyWith (m := Id) H prog input proof = true :=
  baseProver_complete_of_agree H fuel hsat
    (fun s hs hρ ↦ Compile.phasesAgree prog s hs ρ hρ input) hp

end Prove

end
end LeanerVM.Protocol
