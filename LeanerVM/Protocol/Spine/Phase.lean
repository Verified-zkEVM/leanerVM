/-
  LeanerVM.Protocol.Spine.Phase

  A phase of the leanVM protocol: a component over the one committed stack, with the trivial
  witness, at a slot's schedule. A front phase never queries the stack. The pass-through phase
  is the bookkeeping shape.
-/

module

public import LeanerVM.Protocol.ToArkLib.Component
public import LeanerVM.Protocol.ToArkLib.FrontVerifier
public import LeanerVM.Protocol.ToArkLib.PassThrough
public import LeanerVM.Protocol.Spine.Seams

/-!
# Phases

A phase is a `Component` (`LeanerVM.Protocol.ToArkLib.Component`) whose input and output
oracle is the stack and whose witnesses are trivial: from the commit phase on, the oracle is the
witness. `Phase.Def` is the phase's definition at a given schedule, `Phase.Complete` its
completeness against two seams, `Phase.Security` its extractor and round-by-round knowledge
soundness against two seams at a given error.

A `Phase.FrontDef` is a phase whose verifier reads the prover's messages and never the stack:
its verifier is a `FrontVerifier`, so a query to the stack is a typing error, and it hands the
stack on. Every phase before the opening is one; the compilation replaces the committed stack
by a codeword and keeps the front verifiers, which is why they may not query it. `FrontDef.toDef`
is the phase as a component, the form its proofs are stated on.

`Phase.passThrough` is the phase with no round that maps the statement: complete whenever the
map carries one seam into the other, and knowledge sound at error zero, with the extractor that
keeps the trivial witness, whenever it also reflects the second seam back into the first.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

@[expose] public section

namespace Phase

variable (I : M3Instance)

/-- A phase: a component from a statement to a statement over the stack, at a schedule. -/
abbrev Def (StmtIn StmtOut : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    [∀ i, OracleInterface (pSpec.Message i)] [∀ i, SampleableType (pSpec.Challenge i)] :
    Type 1 :=
  Component.Def StmtIn (TheOracle I) Unit StmtOut (TheOracle I) Unit pSpec

variable {StmtIn StmtOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, OracleInterface (pSpec.Message i)] [∀ i, SampleableType (pSpec.Challenge i)]

/-- The completeness half of a phase, against its two seams. -/
abbrev Complete (D : Def I StmtIn StmtOut pSpec)
    (relIn : Set ((StmtIn × ∀ i, TheOracle I i) × Unit))
    (relOut : Set ((StmtOut × ∀ i, TheOracle I i) × Unit)) : Type :=
  Component.Complete D relIn relOut

/-- The security half of a phase, against its two seams, at an error. -/
abbrev Security (D : Def I StmtIn StmtOut pSpec)
    (relIn : Set ((StmtIn × ∀ i, TheOracle I i) × Unit))
    (relOut : Set ((StmtOut × ∀ i, TheOracle I i) × Unit))
    (err : pSpec.ChallengeIdx → ℝ≥0) : Type 1 :=
  Component.Security D relIn relOut err

/-- A front phase: an honest prover and a verifier that reads the transcript and never the
stack. -/
structure FrontDef (StmtIn StmtOut : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    [∀ i, OracleInterface (pSpec.Message i)] [∀ i, SampleableType (pSpec.Challenge i)] where
  /-- The honest prover. -/
  prover : OracleProver []ₒ StmtIn (TheOracle I) Unit StmtOut (TheOracle I) Unit pSpec
  /-- The verifier, with no access to the stack. -/
  verifier : FrontVerifier []ₒ StmtIn StmtOut pSpec

/-- A front phase as a component: its verifier lifted, the stack handed on. -/
def FrontDef.toDef (P : FrontDef I StmtIn StmtOut pSpec) : Def I StmtIn StmtOut pSpec :=
  ⟨⟨P.prover, P.verifier.toOracleVerifier (TheOracle I)⟩⟩

/-- The phase with no round that maps the statement and keeps the stack. -/
abbrev passThrough (f : StmtIn → StmtOut) : Def I StmtIn StmtOut !p[] :=
  Component.passThrough (TheOracle I) f

/-- Its completeness, whenever `f` carries the input seam into the output seam. -/
def passThroughComplete (f : StmtIn → StmtOut)
    {relIn : Set ((StmtIn × ∀ i, TheOracle I i) × Unit)}
    {relOut : Set ((StmtOut × ∀ i, TheOracle I i) × Unit)}
    (h : ∀ s o, ((s, o), ()) ∈ relIn → ((f s, o), ()) ∈ relOut) :
    Complete I (passThrough I f) relIn relOut :=
  Component.passThroughComplete (TheOracle I) f fun s o _ hin ↦ h s o hin

/-- Its security, at error zero, whenever `f` carries the input seam into the output seam and
reflects the output seam back into the input seam. -/
def passThroughSecurity (f : StmtIn → StmtOut)
    {relIn : Set ((StmtIn × ∀ i, TheOracle I i) × Unit)}
    {relOut : Set ((StmtOut × ∀ i, TheOracle I i) × Unit)}
    (hc : ∀ s o, ((s, o), ()) ∈ relIn → ((f s, o), ()) ∈ relOut)
    (h : ∀ s o, ((f s, o), ()) ∈ relOut → ((s, o), ()) ∈ relIn) :
    Security I (passThrough I f) relIn relOut (fun i ↦ Fin.elim0 i.1) :=
  Component.passThroughSecurity (TheOracle I) f (fun s o _ ↦ h s o) fun s o _ ↦ hc s o

end Phase

end
end LeanerVM.Protocol
