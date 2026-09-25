/-
  LeanerVM.Protocol.Spine.Transport

  The adaptor's generic half: a refinement of relations is a witness map that preserves
  validity, and an extractor follows it by post-composition.
-/

module

public import ArkLib.OracleReduction.Security.Basic

/-!
# Refinements and the transport of extracted witnesses

Protocol roadmap, section *The spine*, the last item of *What the spine fixes*. leanth's
`Refinement` (its `Security/Relation.lean`), restated on ArkLib's relations as sets of pairs.

The adaptor of Layer 3 is a refinement from `M3Holds` (witness: the stack) to leanISA's
`SatisfiedBy` (witness: Clean's `EnsembleWitness`), through `witnessOf`. Its target lives in
`Type 1`, which ArkLib's witness types cannot (they are in `Type`), so knowledge of `SatisfiedBy`
is never an ArkLib `knowledgeSoundness` statement: T4 (Layer 13) takes the extractor of the
oracle protocol, which returns a stack, and applies the adaptor to the stack it extracted. What
that step needs from a refinement is exactly `Refinement.map_valid`, in its `Option` form
`Refinement.map_option_valid` below: a witness slot valid for `M3Holds` becomes a witness slot
valid for `SatisfiedBy`, and the failure event of the game can only shrink.

`Extractor.Straightline.map` is the same post-composition on ArkLib's straight-line extractor,
for refinements whose target is in `Type` (a phase restated on another witness type, the
recursion guest of T5). The probabilistic transport of `knowledgeSoundnessWith` along it is not
proved here: ArkLib's game fixes the malicious prover's input-witness type to the relation's, so
the transport needs a prover conversion and `Nonempty WitIn`, a small generic lemma to add when
a consumer appears.

Category A. Target: T4 (Layer 13 applies `map_option_valid` to the extracted stack).

## ArkLib's objects, introduced

* `Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec`: a function of the input statement,
  the output witness, the full transcript and the two query logs, returning an input witness or
  failing (`OptionT`), with access to the shared oracle.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec

@[expose] public section

/-- A refinement of relations over one statement type: a witness map that preserves validity. -/
structure Refinement {Stmt : Type} {W₁ W₂ : Type _} (R : Set (Stmt × W₁))
    (S : Set (Stmt × W₂)) where
  /-- The witness map, at each statement. -/
  map : Stmt → W₁ → W₂
  /-- The map carries witnesses valid for `R` to witnesses valid for `S`. -/
  map_valid : ∀ x w, (x, w) ∈ R → (x, map x w) ∈ S

namespace Refinement

variable {Stmt : Type} {W₁ W₂ W₃ : Type _}

/-- The identity refinement. -/
def id (R : Set (Stmt × W₁)) : Refinement R R where
  map := fun _ w ↦ w
  map_valid := fun _ _ h ↦ h

/-- Composition of refinements: `g.comp f` is `g` after `f`. -/
def comp {R : Set (Stmt × W₁)} {S : Set (Stmt × W₂)} {T : Set (Stmt × W₃)}
    (g : Refinement S T) (f : Refinement R S) : Refinement R T where
  map := fun x w ↦ g.map x (f.map x w)
  map_valid := fun x w h ↦ g.map_valid x _ (f.map_valid x w h)

/-- The `Option` form of `map_valid`, the shape of an extractor's output slot: if every witness
the slot may hold is valid for `R`, every witness the mapped slot may hold is valid for `S`.
Contrapositively, the event "the verifier accepted and the extracted witness is invalid" for `S`
is contained in the same event for `R`, which is how T4 transports the knowledge bound. -/
theorem map_option_valid {R : Set (Stmt × W₁)} {S : Set (Stmt × W₂)} (f : Refinement R S)
    (x : Stmt) (w? : Option W₁) (h : ∀ w ∈ w?, (x, w) ∈ R) :
    ∀ w' ∈ w?.map (f.map x), (x, w') ∈ S := by
  intro w' hw'
  obtain ⟨w, hw, rfl⟩ := Option.mem_map.mp hw'
  exact f.map_valid x w (h w hw)

end Refinement

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn WitIn' WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}

/-- Post-compose a straight-line extractor with a witness map: the extractor for a refinement of
the relation the original extracts. Computable when both are. -/
def Extractor.Straightline.map (f : StmtIn → WitIn → WitIn')
    (E : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec) :
    Extractor.Straightline oSpec StmtIn WitIn' WitOut pSpec :=
  fun stmtIn witOut tr log₁ log₂ ↦ f stmtIn <$> E stmtIn witOut tr log₁ log₂

end
end LeanerVM.Protocol
