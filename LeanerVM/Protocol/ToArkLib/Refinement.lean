/-
  LeanerVM.Protocol.ToArkLib.Refinement

  A refinement of relations: a witness map that preserves validity, and how an extractor
  follows it. Candidate for ArkLib.
-/

module

public import ArkLib.OracleReduction.Security.Basic

/-!
# Refinements

A `Refinement R S` between two relations over the same statements is a map on witnesses that
sends every witness valid for `R` to one valid for `S`. Knowledge of `R` then yields knowledge
of `S` by applying the map to whatever an extractor returns: `map_option_valid` is that step on
an extractor's output slot (a witness, or a failure), `Extractor.Straightline.map` is the same
post-composition on ArkLib's straight-line extractor, and `knowledge_transport` is the
probabilistic statement: in the same knowledge-soundness game, with the same provers and the
same extractor, accepting while the mapped extracted witness is invalid for `S` has probability
at most the knowledge error for `R`. It is stated as that event, not as
`knowledgeSoundnessWith` for `S`: ArkLib's game fixes the malicious prover's input-witness type
to the relation's, so the game for `S` is another game.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

@[expose] public section

/-- A witness map between two relations over the same statements, preserving validity. -/
structure Refinement {Stmt : Type} {W₁ W₂ : Type _} (R : Set (Stmt × W₁))
    (S : Set (Stmt × W₂)) where
  /-- The witness map, at each statement. -/
  map : Stmt → W₁ → W₂
  /-- A witness valid for `R` maps to one valid for `S`. -/
  map_valid : ∀ x w, (x, w) ∈ R → (x, map x w) ∈ S

namespace Refinement

variable {Stmt : Type} {W₁ W₂ W₃ : Type _}

/-- The identity refinement. -/
def id (R : Set (Stmt × W₁)) : Refinement R R where
  map := fun _ w ↦ w
  map_valid := fun _ _ h ↦ h

/-- `g.comp f` is `g` after `f`. -/
def comp {R : Set (Stmt × W₁)} {S : Set (Stmt × W₂)} {T : Set (Stmt × W₃)}
    (g : Refinement S T) (f : Refinement R S) : Refinement R T where
  map := fun x w ↦ g.map x (f.map x w)
  map_valid := fun x w h ↦ g.map_valid x _ (f.map_valid x w h)

/-- On an extractor's output slot: if every witness the slot may hold is valid for `R`, every
witness the mapped slot may hold is valid for `S`. -/
theorem map_option_valid {R : Set (Stmt × W₁)} {S : Set (Stmt × W₂)} (f : Refinement R S)
    (x : Stmt) (w? : Option W₁) (h : ∀ w ∈ w?, (x, w) ∈ R) :
    ∀ w' ∈ w?.map (f.map x), (x, w') ∈ S := by
  intro w' hw'
  obtain ⟨w, hw, rfl⟩ := Option.mem_map.mp hw'
  exact f.map_valid x w (h w hw)

end Refinement

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn WitIn' WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}

/-- Post-compose a straight-line extractor with a witness map. -/
def Extractor.Straightline.map (f : StmtIn → WitIn → WitIn')
    (E : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec) :
    Extractor.Straightline oSpec StmtIn WitIn' WitOut pSpec :=
  fun stmtIn witOut tr log₁ log₂ ↦ f stmtIn <$> E stmtIn witOut tr log₁ log₂

/-- **Knowledge transports along a refinement.** In the knowledge-soundness game of a verifier
for `R`, with any prover and the certified extractor, the probability that the verifier accepts
while the extracted witness, mapped by the refinement, is invalid for `S` is at most the
knowledge error: that event is contained in the game's own bad event, since a witness whose
image is invalid for `S` is invalid for `R`. -/
theorem Refinement.knowledge_transport {StmtOut : Type} {W₁ W₂ : Type}
    {R : Set (StmtIn × W₁)} {S : Set (StmtIn × W₂)} (f : Refinement R S)
    {relOut : Set (StmtOut × WitOut)} {V : Verifier oSpec StmtIn StmtOut pSpec}
    [∀ i, SampleableType (pSpec.Challenge i)]
    {E : Extractor.Straightline oSpec StmtIn W₁ WitOut pSpec} {ε : ℝ≥0} {σ : Type}
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (h : V.knowledgeSoundnessWith init impl R relOut E ε)
    (stmtIn : StmtIn) (witIn : W₁) (prover : Prover oSpec StmtIn W₁ StmtOut WitOut pSpec) :
    let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
      impl.addLift challengeQueryImpl
    let exec := do
      let ⟨⟨⟨transcript, ⟨_, witOut⟩⟩, stmtOut⟩, proveQueryLog, verifyQueryLog⟩
        ← (Reduction.mk prover V).runWithLog stmtIn witIn
      let extractedWitIn? ←
        liftM (E stmtIn witOut transcript proveQueryLog.fst verifyQueryLog).run
      return (stmtIn, extractedWitIn?, stmtOut, witOut)
    Pr{let ⟨stmtIn, extractedWitIn?, stmtOut, witOut⟩ ← OptionT.mk do
      (simulateQ pImpl exec.run).run' (← init)}[
        (∀ extractedWitIn ∈ extractedWitIn?, (stmtIn, f.map stmtIn extractedWitIn) ∉ S) ∧
          (stmtOut, witOut) ∈ relOut] ≤ ε := by
  refine le_trans (prEvent_mono _ _ _ ?_) (h stmtIn witIn prover)
  rintro ⟨s, w?, t, w⟩ ⟨hbad, hout⟩
  exact ⟨fun w' hw' hR ↦ hbad w' hw' (f.map_valid s w' hR), hout⟩

end
end LeanerVM.Protocol
