/-
  LeanerVM.Protocol.ToArkLib.PassThrough

  The component with no round that maps the statement and leaves the oracles and the witness
  alone, with its completeness and knowledge-soundness proofs: ArkLib's
  `ReduceClaim.oracleReduction` at the identity on the oracles and the witness, packaged as a
  component.
-/

module

public import ArkLib.OracleReduction.LogicStep
public import ArkLib.OracleReduction.Security.GuardedRoundByRound
public import ArkLib.ProofSystem.Component.ReduceClaim
public import LeanerVM.Protocol.ToArkLib.Component
public import LeanerVM.Protocol.ToArkLib.KeepOracles

/-!
# The pass-through component

`Component.passThrough OStmt f` sends nothing and outputs `f` of the input statement, the same
oracles and the same witness. It is the shape of every bookkeeping step (relabelling claims,
dropping a clause the previous step consumed). It is proved in both halves: complete whenever `f`
carries the input relation into the output relation, and knowledge sound at error zero, with the
extractor that keeps the witness, whenever `f` also reflects the output relation back into the
input relation (`passThroughSecurityOfIff` takes the two directions as one equivalence, for the
trivial witness).
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec

@[expose] public section

namespace Component

variable {ι : Type} (OStmt : ι → Type) [∀ i, OracleInterface (OStmt i)]
  {StmtIn StmtOut W : Type}

/-- The prover: no message, the statement mapped, oracles and witness kept. -/
def passThroughProver (f : StmtIn → StmtOut) :
    OracleProver []ₒ StmtIn OStmt W StmtOut OStmt W !p[] :=
  ReduceClaim.oracleProver []ₒ f (fun _ w ↦ w) (.refl ι) fun _ ↦ rfl

/-- The verifier: maps the statement and exposes the input oracles as the output oracles. -/
def passThroughVerifier (f : StmtIn → StmtOut) :
    OracleVerifier []ₒ StmtIn OStmt StmtOut OStmt !p[] :=
  ReduceClaim.oracleVerifier []ₒ f (.refl ι) (fun _ ↦ rfl) fun _ ↦ HEq.rfl

/-- The pass-through component: no round. -/
def passThrough (f : StmtIn → StmtOut) : Def StmtIn OStmt W StmtOut OStmt W !p[] where
  red := ⟨passThroughProver OStmt f, passThroughVerifier OStmt f⟩

/-- The pass-through verifier is pure, as data. -/
def passThroughPure (f : StmtIn → StmtOut) :
    (passThroughVerifier OStmt f).toVerifier.PureForm where
  verify := fun p _ ↦ (f p.1, p.2)
  verify_eq := fun _ _ ↦ ReduceClaim.oracleVerifier_toVerifier_run

/-- The pass-through component is front: the check always passes, the verdict is `f`. -/
def passThroughFront (f : StmtIn → StmtOut) : Front (passThrough (W := W) OStmt f) :=
  ⟨fun _ _ ↦ true, fun s _ ↦ f s, (passThroughPure OStmt f).toGuardedForm.verify_eq⟩

/-- Completeness, for any two relations `f` carries one into the other. -/
def passThroughComplete (f : StmtIn → StmtOut)
    {relIn : Set ((StmtIn × ∀ i, OStmt i) × W)} {relOut : Set ((StmtOut × ∀ i, OStmt i) × W)}
    (h : ∀ s o w, ((s, o), w) ∈ relIn → ((f s, o), w) ∈ relOut) :
    Complete (passThrough OStmt f) relIn relOut where
  guarded := (passThroughPure OStmt f).toGuardedForm
  complete := fun _ _ ↦ ReduceClaim.oracleReduction_completeness _ _ h

/-! ## Knowledge soundness -/

variable (f : StmtIn → StmtOut) {relIn : Set ((StmtIn × ∀ i, OStmt i) × W)}
  {relOut : Set ((StmtOut × ∀ i, OStmt i) × W)}

/-- The security half, at error zero, with the extractor that keeps the witness, whenever the
output relation at the mapped statement implies the input relation. -/
def passThroughSecurity (h : ∀ s o w, ((f s, o), w) ∈ relOut → ((s, o), w) ∈ relIn) :
    Security (passThrough OStmt f) relIn relOut (fun i ↦ Fin.elim0 i.1) where
  guarded := (passThroughPure OStmt f).toGuardedForm
  witMid := fun _ ↦ W
  extractor := ReduceClaim.extractor fun _ w ↦ w
  kSF := fun _ _ ↦ ReduceClaim.oracleKnowledgeStateFunction (mapStmt := f) (embedIdx := .refl ι)
    (hEq := fun _ ↦ rfl) (hInterface := fun _ ↦ HEq.rfl) relIn relOut h
  rbr := fun _ _ _ i ↦ Fin.elim0 i.1

/-- The security half with the trivial witness, whenever `f` carries a statement into the
output relation exactly when the statement is in the input relation. -/
def passThroughSecurityOfIff {rIn : Set ((StmtIn × ∀ i, OStmt i) × Unit)}
    {rOut : Set ((StmtOut × ∀ i, OStmt i) × Unit)}
    (hf : ∀ s o, ((f s, o), ()) ∈ rOut ↔ ((s, o), ()) ∈ rIn) :
    Security (passThrough OStmt f) rIn rOut (fun i ↦ Fin.elim0 i.1) :=
  passThroughSecurity OStmt f fun s o w h ↦ by cases w; exact (hf s o).mp h

end Component

end
end LeanerVM.Protocol
