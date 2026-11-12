/-
  LeanerVM.Protocol.ToArkLib.MapWitness

  The component with no round that maps the statement and the witness and leaves the oracles
  alone, with its completeness and knowledge-soundness proofs: ArkLib's
  `ReduceClaim.oracleReduction` at the identity on the oracles, packaged as a component.
-/

module

public import LeanerVM.Protocol.ToArkLib.PassThrough

/-!
# The map-witness component

`Component.mapWitness OStmt f g` sends nothing: the verifier outputs `f` of the statement and the
oracles it was given, and the prover outputs the witness `g` makes from the statement and its
witness. It is `Component.passThrough` with a witness that changes: the step in which the prover
replaces the table it holds by the table it folded.

Completeness (`mapWitnessComplete`): whenever `f` and `g` carry the input relation into the
output relation. Security (`mapWitnessSecurity`, at the empty error): the witness is read back by a
function the consumer gives, and the output relation at the mapped statement implies the input
relation at the witness read back.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec

@[expose] public section

namespace Component

variable {ι : Type} (OStmt : ι → Type) [∀ i, OracleInterface (OStmt i)]
  {StmtIn StmtOut W W' : Type} (f : StmtIn → StmtOut) (g : StmtIn → W → W')

/-- The prover: no message, the statement mapped, the witness `g` makes, the oracles kept. -/
def mapWitnessProver : OracleProver []ₒ StmtIn OStmt W StmtOut OStmt W' !p[] :=
  ReduceClaim.oracleProver []ₒ f g (.refl ι) fun _ ↦ rfl

/-- The map-witness component: the pass-through verifier, the witness-mapping prover. -/
def mapWitness : Def StmtIn OStmt W StmtOut OStmt W' !p[] where
  red := ⟨mapWitnessProver OStmt f g, passThroughVerifier OStmt f⟩

/-- Completeness, for any two relations `f` and `g` carry one into the other. -/
def mapWitnessComplete {relIn : Set ((StmtIn × ∀ i, OStmt i) × W)}
    {relOut : Set ((StmtOut × ∀ i, OStmt i) × W')}
    (h : ∀ s o w, ((s, o), w) ∈ relIn → ((f s, o), g s w) ∈ relOut) :
    Complete (mapWitness OStmt f g) relIn relOut where
  guarded := (passThroughPure OStmt f).toGuardedForm
  complete := fun _ _ ↦ ReduceClaim.oracleReduction_completeness _ _ h

/-- The security half of the map-witness component, at the empty error, with the extractor that
sends the output witness back by `back`: the output relation, at the statement mapped, implies the
input relation at the witness sent back. -/
def mapWitnessSecurity (back : W' → W) {relIn : Set ((StmtIn × ∀ i, OStmt i) × W)}
    {relOut : Set ((StmtOut × ∀ i, OStmt i) × W')}
    (h : ∀ s o w', ((f s, o), w') ∈ relOut → ((s, o), back w') ∈ relIn) :
    Security (mapWitness OStmt f g) relIn relOut (fun i ↦ Fin.elim0 i.1) where
  guarded := (passThroughPure OStmt f).toGuardedForm
  witMid := fun _ ↦ W
  extractor := ReduceClaim.extractor fun _ ↦ back
  kSF := fun _ _ ↦ ReduceClaim.oracleKnowledgeStateFunction (mapStmt := f) (embedIdx := .refl ι)
    (hEq := fun _ ↦ rfl) (hInterface := fun _ ↦ HEq.rfl) relIn relOut h
  rbr := fun _ _ _ i ↦ Fin.elim0 i.1

end Component

end
end LeanerVM.Protocol
