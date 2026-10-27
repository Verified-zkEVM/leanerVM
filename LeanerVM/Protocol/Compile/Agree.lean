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

**`compiled_of_algebra`**, the converse: on every full transcript whose round polynomials pass
their checks against the running claims (`Solved`: each phase's `BusSolved`, `TableSolved`,
`FlockSolved` and `WhirSolved`, the claims threaded through the oracle verifier's statements),
the compiled verifier accepts when the executable verifier's algebra accepts the transcript's wire
and the rows its words have at its positions. The hypothesis is needed: the wire drops a
coefficient of every round polynomial, so a transcript with another one there has the same wire,
which the algebra accepts and the oracle verifier rejects (`tests/Protocol/CompileWhir`). The
front phases' algebra is the oracle verifiers' run on solved transcripts
(`busStep_busWireOf_of_solved` and the others) and WHIR's by `whirOpenGuarded_run_of_whirCheck`.
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
  obtain ⟨t₇', t₈, e⟩ := exists_eq_append @tr
  subst tr
  obtain ⟨t₆', t₇, e⟩ := exists_eq_append @t₇'
  subst t₇'
  obtain ⟨t₅', t₆, e⟩ := exists_eq_append @t₆'
  subst t₆'
  obtain ⟨t₄', t₅, e⟩ := exists_eq_append @t₅'
  subst t₅'
  obtain ⟨t₃', t₄, e⟩ := exists_eq_append @t₄'
  subst t₄'
  obtain ⟨t₂', t₃, e⟩ := exists_eq_append @t₃'
  subst t₃'
  obtain ⟨t₁, t₂, e⟩ := exists_eq_append @t₂'
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
  have hfront := leanVmFront_of_checks prog s input @t₂ @t₃ @t₄ @t₅ c₂ c₃ c₄ c₅
  simp only [Option.bind_eq_some_iff] at hfront
  obtain ⟨p, ⟨t, ⟨b, hb, ht⟩, hp⟩, hf⟩ := hfront
  simp only [wireOf, Prove.rowsOf, Prove.level0Word, Prove.ladderPart,
    FullTranscript.append_fst, FullTranscript.append_snd, algebra, flockWireOpt, hb, ht, hp, hf,
    openingClaim_eq]
  exact whirCheck_of_run (leanIsaChain prog s hs ρ hρ).ladder
    (leanIsaChain_height Blake2sFlock.blake2sFlockSpec prog s hs ρ hρ) _ _ _
    (fun p ↦ ((t₁ 0).row p).toList.reverse) (laneRow_level0 (t₁ 0)) @t₈ h₈

/-- **The round polynomials of a transcript of the compiled protocol pass their checks**, at
leanVM's instance and WHIR's deployed chain on the public input: the bus phase's from the input,
the table sumcheck's and the Flock phase's from the oracle verifier's statements before them, and
WHIR's opening's from the opening claim on the committed word. -/
def Solved (prog : Program) (s : Sizes) (hs : s.Admissible prog) (ρ : ℕ) (hρ : validRate ρ)
    (input : PublicInput)
    (tr : (listBindingSpec (leanVm prog s) (leanIsaChain prog s hs ρ hρ).sh
      (leanIsaChain prog s hs ρ hρ).κ (leanIsaChain prog s hs ρ hρ).ladder).FullTranscript) :
    Prop :=
  let I := leanVm prog s
  let f₆ := tr.fst.fst
  let f₅ := f₆.fst
  let f₄ := f₅.fst
  let f₃ := f₄.fst
  let f₂ := f₃.fst
  let bo := (busPhase I (leanIsa_conditions _ prog s)).front.out input f₂.snd
  let tout := (TableSumcheck.tableSumcheck I).front.out bo f₃.snd
  let po := (deployedPublicInputPhase I).front.out tout f₄.snd
  let fo := (flockPhaseSome I (flockRegion prog s Blake2sFlock.blake2sFlockSpec) rfl).front.out po
    f₅.snd
  BusSolved I input f₂.snd ∧ TableSolved I bo f₃.snd ∧
    FlockSolved I (flockRegion prog s Blake2sFlock.blake2sFlockSpec) po f₅.snd ∧
    WhirSolved (leanIsaChain prog s hs ρ hρ).ladder
      (castWeight (leanIsaChain_height Blake2sFlock.blake2sFlockSpec prog s hs ρ hρ).symm
        (Opening.weight I fo (drawOf f₆.snd)))
      (powerBatch (Opening.values I fo) (drawOf f₆.snd)) (Prove.level0Word tr).lift tr.snd

/-- The algebra's front, once the algebra accepts: its four steps return some output `f`, and
WHIR's algebra accepts on the opening claim. -/
theorem front_of_algebra {prog : Program} {s : Sizes} {input : PublicInput}
    {shs : List LevelShape} {w : Wire} {rows : List (List (List K))}
    (h : algebra prog s input shs w rows = true) :
    ∃ f, ((((leanVmBus prog s input w.bus).bind fun b ↦ tableStep (leanVm prog s) b w.table).bind
        fun t ↦ pubStep (leanVm prog s) t w.pub).bind fun p ↦
        flockStep (leanVm prog s) (flockRegion prog s Blake2sFlock.blake2sFlockSpec) rfl
          blake2sRows p w.flock) = some f ∧
      whirCheck (leanVm prog s).μ shs (openingClaim (leanVm prog s) f w.lam).1
        (openingClaim (leanVm prog s) f w.lam).2 w.whirFirst w.whir rows = true := by
  unfold algebra at h
  rcases hb : leanVmBus prog s input w.bus with _ | b
  · simp [hb] at h
  rcases ht : tableStep (leanVm prog s) b w.table with _ | t
  · simp [hb, ht] at h
  rcases hp : pubStep (leanVm prog s) t w.pub with _ | p
  · simp [hb, ht, hp] at h
  rcases hf : flockStep (leanVm prog s) (flockRegion prog s Blake2sFlock.blake2sFlockSpec) rfl
      blake2sRows p w.flock with _ | f
  · simp [hb, ht, hp, hf] at h
  simp only [hb, ht, hp, hf] at h
  exact ⟨f, by simp [ht, hp, hf], h⟩

/-- **The front phases' checks, when the algebra's front returns on solved transcripts**: on
transcripts of the bus phase, the table sumcheck and the Flock phase whose round polynomials pass
their checks, each from the oracle verifier's statement before it, if the algebra's four steps
return `f` on their wires and the public input's, the four oracle verifiers accept, and `f` is
the Flock phase's output. -/
theorem leanVmFront_checks_of_solved (prog : Program) (s : Sizes) (input : PublicInput)
    (t₂ : (busSpec (leanVm prog s)).FullTranscript)
    (t₃ : (tableSpec (leanVm prog s)).FullTranscript) (t₄ : pubSpec.FullTranscript)
    (t₅ : (flockSpecOf (flockRegion prog s Blake2sFlock.blake2sFlockSpec).kBatch).FullTranscript)
    (hB : BusSolved (leanVm prog s) input t₂)
    (hT : TableSolved (leanVm prog s)
      ((busPhase (leanVm prog s) (leanIsa_conditions _ prog s)).front.out input t₂) t₃)
    (hF : FlockSolved (leanVm prog s) (flockRegion prog s Blake2sFlock.blake2sFlockSpec)
      ((deployedPublicInputPhase (leanVm prog s)).front.out
        ((TableSumcheck.tableSumcheck (leanVm prog s)).front.out
          ((busPhase (leanVm prog s) (leanIsa_conditions _ prog s)).front.out input t₂) t₃) t₄) t₅)
    {f : PublicInput × FlockOut (leanVm prog s)}
    (hf : ((((leanVmBus prog s input (busWireOf (leanVm prog s) t₂)).bind fun b ↦
        tableStep (leanVm prog s) b (tableWireOf (leanVm prog s) t₃)).bind fun t ↦
        pubStep (leanVm prog s) t (pubWireOf t₄)).bind fun p ↦
        flockStep (leanVm prog s) (flockRegion prog s Blake2sFlock.blake2sFlockSpec) rfl
          blake2sRows p
          (flockWireOf (flockRegion prog s Blake2sFlock.blake2sFlockSpec).kBatch t₅)) = some f) :
    (busPhase (leanVm prog s) (leanIsa_conditions _ prog s)).front.check input t₂ = true ∧
      (TableSumcheck.tableSumcheck (leanVm prog s)).front.check
        ((busPhase (leanVm prog s) (leanIsa_conditions _ prog s)).front.out input t₂) t₃ = true ∧
      (deployedPublicInputPhase (leanVm prog s)).front.check
        ((TableSumcheck.tableSumcheck (leanVm prog s)).front.out
          ((busPhase (leanVm prog s) (leanIsa_conditions _ prog s)).front.out input t₂) t₃) t₄ =
        true ∧
      (flockPhaseSome (leanVm prog s) (flockRegion prog s Blake2sFlock.blake2sFlockSpec)
        rfl).front.check ((deployedPublicInputPhase (leanVm prog s)).front.out
          ((TableSumcheck.tableSumcheck (leanVm prog s)).front.out
            ((busPhase (leanVm prog s) (leanIsa_conditions _ prog s)).front.out input t₂) t₃)
          t₄) t₅ = true ∧
      f = (flockPhaseSome (leanVm prog s) (flockRegion prog s Blake2sFlock.blake2sFlockSpec)
        rfl).front.out ((deployedPublicInputPhase (leanVm prog s)).front.out
          ((TableSumcheck.tableSumcheck (leanVm prog s)).front.out
            ((busPhase (leanVm prog s) (leanIsa_conditions _ prog s)).front.out input t₂) t₃)
          t₄) t₅ := by
  simp only [Option.bind_eq_some_iff] at hf
  obtain ⟨p, ⟨t, ⟨b, hb, ht⟩, hp⟩, hf⟩ := hf
  rw [leanVmBus_eq_busStep, busStep_busWireOf_of_solved _ _ _ _ hB] at hb
  obtain ⟨cb, rfl⟩ := (Component.Front.run_eq_some_iff _).mp hb
  rw [tableStep_tableWireOf_of_solved _ _ _ hT] at ht
  obtain ⟨ct, rfl⟩ := (Component.Front.run_eq_some_iff _).mp ht
  rw [pubStep_pubWireOf] at hp
  obtain ⟨cp, rfl⟩ := (Component.Front.run_eq_some_iff _).mp hp
  rw [flockStep_flockWireOf_of_solved _ _ rfl blake2sRows (blake2sRows_eq_region prog s) _ _ hF]
    at hf
  obtain ⟨cf, rfl⟩ := (Component.Front.run_eq_some_iff _).mp hf
  exact ⟨cb, ct, cp, cf, rfl⟩

/-- The wire of a transcript of the compiled protocol in its eight parts. -/
private theorem wireOf_append {I : M3Instance} {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ)
    (t₁ : (commitWordSpec sh κ).FullTranscript) (t₂ : (busSpec I).FullTranscript)
    (t₃ : (tableSpec I).FullTranscript) (t₄ : pubSpec.FullTranscript)
    (t₅ : (flockSpec I).FullTranscript) (t₆ : openingSpec.FullTranscript)
    (t₇ : (!p[] : ProtocolSpec 0).FullTranscript)
    (t₈ : (seqSpec (.skip :: .msg (SumcheckRound.Message E 2) :: L.steps)).FullTranscript) :
    wireOf I L (((((((t₁ ++ₜ t₂) ++ₜ t₃) ++ₜ t₄) ++ₜ t₅) ++ₜ t₆) ++ₜ t₇) ++ₜ t₈) =
      ⟨default, busWireOf I t₂, tableWireOf I t₃, pubWireOf t₄, flockWireOpt I I.flock t₅,
        drawOf t₆, (whirWireOf L t₈).1, (whirWireOf L t₈).2⟩ := by
  simp only [wireOf, FullTranscript.append_fst, FullTranscript.append_snd]

/-- The rows of a transcript of the compiled protocol in its eight parts. -/
private theorem rowsOf_append {I : M3Instance} {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ)
    (t₁ : (commitWordSpec sh κ).FullTranscript) (t₂ : (busSpec I).FullTranscript)
    (t₃ : (tableSpec I).FullTranscript) (t₄ : pubSpec.FullTranscript)
    (t₅ : (flockSpec I).FullTranscript) (t₆ : openingSpec.FullTranscript)
    (t₇ : (!p[] : ProtocolSpec 0).FullTranscript)
    (t₈ : (seqSpec (.skip :: .msg (SumcheckRound.Message E 2) :: L.steps)).FullTranscript) :
    Prove.rowsOf I L (((((((t₁ ++ₜ t₂) ++ₜ t₃) ++ₜ t₄) ++ₜ t₅) ++ₜ t₆) ++ₜ t₇) ++ₜ t₈) =
      Prove.ladderRows L (fun p ↦ ((t₁ 0).row p).toList.reverse) (seqTail (seqTail t₈)) := by
  simp only [Prove.rowsOf, Prove.level0Word, Prove.ladderPart, FullTranscript.append_fst,
    FullTranscript.append_snd]

/-- At leanVM's instance the Flock wire of the instance's slot is the region's. -/
private theorem flockWireOpt_leanVm (prog : Program) (s : Sizes)
    (t : (flockSpec (leanVm prog s)).FullTranscript) :
    flockWireOpt (leanVm prog s) (leanVm prog s).flock t =
      flockWireOf (flockRegion prog s Blake2sFlock.blake2sFlockSpec).kBatch t :=
  rfl

/-- A transcript of the compiled protocol in its eight parts is solved when its phases' parts
are. -/
private theorem solved_append (prog : Program) (s : Sizes) (hs : s.Admissible prog) (ρ : ℕ)
    (hρ : validRate ρ) (input : PublicInput)
    (t₁ : (commitWordSpec (leanIsaChain prog s hs ρ hρ).sh
      (leanIsaChain prog s hs ρ hρ).κ).FullTranscript)
    (t₂ : (busSpec (leanVm prog s)).FullTranscript)
    (t₃ : (tableSpec (leanVm prog s)).FullTranscript) (t₄ : pubSpec.FullTranscript)
    (t₅ : (flockSpec (leanVm prog s)).FullTranscript) (t₆ : openingSpec.FullTranscript)
    (t₇ : (!p[] : ProtocolSpec 0).FullTranscript)
    (t₈ : (seqSpec (.skip :: .msg (SumcheckRound.Message E 2) ::
      (leanIsaChain prog s hs ρ hρ).ladder.steps)).FullTranscript)
    (h : Solved prog s hs ρ hρ input
      (((((((t₁ ++ₜ t₂) ++ₜ t₃) ++ₜ t₄) ++ₜ t₅) ++ₜ t₆) ++ₜ t₇) ++ₜ t₈)) :
    BusSolved (leanVm prog s) input t₂ ∧
      TableSolved (leanVm prog s)
        ((busPhase (leanVm prog s) (leanIsa_conditions _ prog s)).front.out input t₂) t₃ ∧
      FlockSolved (leanVm prog s) (flockRegion prog s Blake2sFlock.blake2sFlockSpec)
        ((deployedPublicInputPhase (leanVm prog s)).front.out
          ((TableSumcheck.tableSumcheck (leanVm prog s)).front.out
            ((busPhase (leanVm prog s) (leanIsa_conditions _ prog s)).front.out input t₂) t₃)
          t₄) t₅ ∧
      WhirSolved (leanIsaChain prog s hs ρ hρ).ladder
        (castWeight (leanIsaChain_height Blake2sFlock.blake2sFlockSpec prog s hs ρ hρ).symm
          (Opening.weight (leanVm prog s)
            ((flockPhaseSome (leanVm prog s) (flockRegion prog s Blake2sFlock.blake2sFlockSpec)
              rfl).front.out ((deployedPublicInputPhase (leanVm prog s)).front.out
                ((TableSumcheck.tableSumcheck (leanVm prog s)).front.out
                  ((busPhase (leanVm prog s) (leanIsa_conditions _ prog s)).front.out input t₂)
                  t₃) t₄) t₅) (drawOf t₆)))
        (powerBatch (Opening.values (leanVm prog s)
            ((flockPhaseSome (leanVm prog s) (flockRegion prog s Blake2sFlock.blake2sFlockSpec)
              rfl).front.out ((deployedPublicInputPhase (leanVm prog s)).front.out
                ((TableSumcheck.tableSumcheck (leanVm prog s)).front.out
                  ((busPhase (leanVm prog s) (leanIsa_conditions _ prog s)).front.out input t₂)
                  t₃) t₄) t₅)) (drawOf t₆))
        (t₁ 0).lift t₈ := by
  simp only [Solved, FullTranscript.append_fst, FullTranscript.append_snd, Prove.level0Word] at h
  exact h

/-- The bus slot of leanVM's phases. -/
private theorem leanVmPhases_bus {I : M3Instance} (h : Bus.Conditions I) :
    (leanVmPhases I h).bus = busPhase I h :=
  rfl

/-- The table slot of leanVM's phases. -/
private theorem leanVmPhases_table {I : M3Instance} (h : Bus.Conditions I) :
    (leanVmPhases I h).table = TableSumcheck.tableSumcheck I :=
  rfl

/-- The public-input slot of leanVM's phases. -/
private theorem leanVmPhases_pub {I : M3Instance} (h : Bus.Conditions I) :
    (leanVmPhases I h).pub = deployedPublicInputPhase I :=
  rfl

/-- The Flock slot of leanVM's phases. -/
private theorem leanVmPhases_flock {I : M3Instance} (h : Bus.Conditions I) :
    (leanVmPhases I h).flock = flockPhase I :=
  rfl

/-- The list-binding run on a transcript in its eight parts, when the front phases' checks pass
and WHIR's opening accepts from the batched opening claim on the committed word. -/
private theorem listBindingGuarded_run_of_parts {I : M3Instance} {sh : Whir.Shape} {κ : ℕ}
    (P : Phases I) (hμ : κ + sh.ℓ = I.μ) (L : Ladder sh κ) (input : I.Stmt)
    (t₁ : (commitWordSpec sh κ).FullTranscript) (t₂ : (busSpec I).FullTranscript)
    (t₃ : (tableSpec I).FullTranscript) (t₄ : pubSpec.FullTranscript)
    (t₅ : (flockSpec I).FullTranscript) (t₆ : openingSpec.FullTranscript)
    (t₇ : (!p[] : ProtocolSpec 0).FullTranscript)
    (t₈ : (seqSpec (.skip :: .msg (SumcheckRound.Message E 2) :: L.steps)).FullTranscript)
    {so : Unit × ∀ i, OneW L.finShape L.finN i}
    (cb : P.bus.front.check input t₂ = true)
    (ct : P.table.front.check (P.bus.front.out input t₂) t₃ = true)
    (cp : P.pub.front.check (P.table.front.out (P.bus.front.out input t₂) t₃) t₄ = true)
    (cf : P.flock.front.check (P.pub.front.out (P.table.front.out (P.bus.front.out input t₂) t₃)
      t₄) t₅ = true)
    {fo : I.Stmt × FlockOut I}
    (hso : (whirOpenGuarded sh κ L).run
      ((castWeight hμ.symm (Opening.weight I fo (drawOf t₆)),
        powerBatch (Opening.values I fo) (drawOf t₆)), fun _ ↦ (t₁ 0).lift) t₈ = some so)
    (hfo : P.flock.front.out (P.pub.front.out (P.table.front.out (P.bus.front.out input t₂) t₃)
      t₄) t₅ = fo) :
    (listBindingGuarded P hμ L).run (input, fun i ↦ i.elim0)
      (((((((t₁ ++ₜ t₂) ++ₜ t₃) ++ₜ t₄) ++ₜ t₅) ++ₜ t₆) ++ₜ t₇) ++ₜ t₈) = some so := by
  subst hfo
  erw [Component.Guarded.run_append, Component.Guarded.run_append, Component.Guarded.run_append,
    Component.Guarded.run_append, Component.Guarded.run_append, Component.Guarded.run_append,
    Component.Guarded.run_append]
  simp only [FullTranscript.append_fst, FullTranscript.append_snd]
  erw [Component.Guarded.run_ofPure]
  simp only [Option.bind_some, Component.Guarded.run_toGuarded, Component.Front.run,
    Component.Front.overFront]
  simp only [Component.sendVerifierPure, cb, ct, cp, cf, ↓reduceIte, Option.map_some,
    Option.bind_some]
  rw [Option.bind_eq_some_iff]
  exact ⟨_, rfl, hso⟩

/-- **The compiled verifier accepts what the algebra accepts, on a solved transcript**: on every
full transcript of the compiled protocol at leanVM's instance and WHIR's deployed chain whose
round polynomials pass their checks (`Solved`), the compiled verifier accepts on the public input
when the executable verifier's algebra accepts the transcript's wire and the rows its words have
at its positions. -/
theorem compiled_of_algebra (prog : Program) (s : Sizes) (hs : s.Admissible prog) (ρ : ℕ)
    (hρ : validRate ρ) (input : PublicInput)
    (tr : (listBindingSpec (leanVm prog s) (leanIsaChain prog s hs ρ hρ).sh
      (leanIsaChain prog s hs ρ hρ).κ (leanIsaChain prog s hs ρ hρ).ladder).FullTranscript)
    (hsol : Solved prog s hs ρ hρ input @tr)
    (h : algebra prog s input (leanIsaChain prog s hs ρ hρ).ladder.shapes
      (wireOf (leanVm prog s) (leanIsaChain prog s hs ρ hρ).ladder @tr)
      (Prove.rowsOf (leanVm prog s) (leanIsaChain prog s hs ρ hρ).ladder @tr) = true) :
    ∃ so, Id.run (runNoOracle ((Prove.compiledDef prog s hs ρ hρ).red.toReduction.verifier.run
      (input, fun i ↦ i.elim0) @tr).run) = some so := by
  rw [Component.Guarded.verifier_run (listBindingGuarded (leanVmPhases (leanVm prog s)
      (leanIsa_conditions Blake2sFlock.blake2sFlockSpec prog s))
    (leanIsaChain_height Blake2sFlock.blake2sFlockSpec prog s hs ρ hρ)
    (leanIsaChain prog s hs ρ hρ).ladder)]
  simp only [runNoOracle, simulateQ_pure, Id.run_pure]
  -- the transcript's eight parts
  obtain ⟨t₇', t₈, e⟩ := exists_eq_append @tr
  subst tr
  obtain ⟨t₆', t₇, e⟩ := exists_eq_append @t₇'
  subst t₇'
  obtain ⟨t₅', t₆, e⟩ := exists_eq_append @t₆'
  subst t₆'
  obtain ⟨t₄', t₅, e⟩ := exists_eq_append @t₅'
  subst t₅'
  obtain ⟨t₃', t₄, e⟩ := exists_eq_append @t₄'
  subst t₄'
  obtain ⟨t₂', t₃, e⟩ := exists_eq_append @t₃'
  subst t₃'
  obtain ⟨t₁, t₂, e⟩ := exists_eq_append @t₂'
  subst t₂'
  obtain ⟨hB, hT, hF, hW⟩ := solved_append prog s hs ρ hρ input @t₁ @t₂ @t₃ @t₄ @t₅ @t₆ @t₇ @t₈ hsol
  rw [wireOf_append, rowsOf_append, flockWireOpt_leanVm] at h
  obtain ⟨f, hf, hw⟩ := front_of_algebra h
  -- the front phases, on their solved transcripts
  obtain ⟨cb, ct, cp, cf, rfl⟩ :=
    leanVmFront_checks_of_solved prog s input @t₂ @t₃ @t₄ @t₅ hB hT hF hf
  -- WHIR's opening
  rw [openingClaim_eq] at hw
  generalize hWW : Opening.weight (leanVm prog s) _ (drawOf t₆) = W' at hw hW
  generalize hcc : powerBatch (Opening.values (leanVm prog s) _) (drawOf t₆) = c' at hw hW
  -- each hypothesis checked on its own goal, its projections reduced first
  have hrun := whirOpenGuarded_run_of_whirCheck (leanIsaChain prog s hs ρ hρ).ladder
    (leanIsaChain_height Blake2sFlock.blake2sFlockSpec prog s hs ρ hρ) W' c' (t₁ 0).lift
    (fun p ↦ ((t₁ 0).row p).toList.reverse) (laneRow_level0 (t₁ 0)) @t₈ ?hw ?hW
  case hw =>
    dsimp only at hw
    exact hw
  case hW => exact hW
  obtain ⟨so, hso⟩ := hrun
  subst hWW hcc
  refine ⟨so, listBindingGuarded_run_of_parts (leanVmPhases (leanVm prog s)
    (leanIsa_conditions Blake2sFlock.blake2sFlockSpec prog s))
    (leanIsaChain_height Blake2sFlock.blake2sFlockSpec prog s hs ρ hρ)
    (leanIsaChain prog s hs ρ hρ).ladder input @t₁ @t₂ @t₃ @t₄ @t₅ @t₆ @t₇ @t₈ ?_ ?_ ?_ ?_ hso
    ?_⟩
  · rw [leanVmPhases_bus]
    exact cb
  · rw [leanVmPhases_table, leanVmPhases_bus]
    exact ct
  · rw [leanVmPhases_pub, leanVmPhases_table, leanVmPhases_bus]
    exact cp
  · rw [leanVmPhases_flock, leanVmPhases_pub, leanVmPhases_table, leanVmPhases_bus,
      flockPhase_leanVm]
    exact cf
  · rw [leanVmPhases_flock, leanVmPhases_pub, leanVmPhases_table, leanVmPhases_bus,
      flockPhase_leanVm]

end Compile

namespace Prove

/-- **Completeness of the honest prover from a start**: for every byte hash `H`, start and fuel,
a proof `proveFrom` returns for a witness satisfying leanISA's constraint statement on the public
input, at the deployed Flock specification, is accepted by the executable verifier at `H` from the
same start. -/
theorem baseProver_complete_from (H : List UInt8 → Digest) (seed : Id FsState) (fuel : ℕ)
    {prog : Program} {input : PublicInput} {w : EnsembleWitness (leanIsaEnsemble prog)} {ρ : ℕ}
    {proof : Proof PrunedMerklePaths} (hsat : SatisfiedBy prog input w)
    (hp : proveFrom (m := Id) H seed fuel Blake2sFlock.blake2sFlockSpec prog input w ρ =
      some proof) :
    Verify.verifyFrom (m := Id) H seed prog input proof = true :=
  baseProver_complete_of_agree_from H seed fuel hsat
    (fun s hs hρ ↦ Compile.phasesAgree prog s hs ρ hρ input) hp

/-- **Completeness of the honest prover**: for every byte hash `H` and fuel, a proof
`proveWith` returns for a witness satisfying leanISA's constraint statement on the public input,
at the deployed Flock specification, is accepted by the executable verifier at `H`. -/
theorem baseProver_complete (H : List UInt8 → Digest) (fuel : ℕ) {prog : Program}
    {input : PublicInput} {w : EnsembleWitness (leanIsaEnsemble prog)} {ρ : ℕ}
    {proof : Proof PrunedMerklePaths} (hsat : SatisfiedBy prog input w)
    (hp : proveWith (m := Id) H fuel Blake2sFlock.blake2sFlockSpec prog input w ρ = some proof) :
    Verify.verifyWith (m := Id) H prog input proof = true :=
  baseProver_complete_from H (FsState.seedWith (m := Id) H prog input) fuel hsat hp

end Prove

end
end LeanerVM.Protocol
