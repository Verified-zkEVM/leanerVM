/-
  LeanerVM.Protocol.Spine.Phase

  A phase of the leanVM protocol: a component over the one committed stack, with the trivial
  witness. The pass-through phase is the bookkeeping shape.
-/

module

public import LeanerVM.Protocol.ToArkLib.Component
public import LeanerVM.Protocol.ToArkLib.PassThrough
public import LeanerVM.Protocol.Spine.Seams

/-!
# Phases

A phase is a `Component` (`LeanerVM.Protocol.ToArkLib.Component`) whose input and output
oracle is the stack and whose witnesses are trivial: from the commit phase on, the oracle is the
witness. `Phase.Def` is the phase's definition, `Phase.Complete` its completeness against two
seams, `Phase.Security` that and its round-by-round knowledge soundness. `Phase.passThrough`
is the phase with no round that maps the statement, complete whenever the map carries one seam
into the other.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec

@[expose] public section

namespace Phase

variable (I : M3Instance)

/-- A phase: a component from a statement to a statement over the stack. -/
abbrev Def (StmtIn StmtOut : Type) : Type 1 :=
  Component.Def StmtIn (TheOracle I) Unit StmtOut (TheOracle I) Unit

/-- The completeness half of a phase, against its two seams. -/
abbrev Complete {StmtIn StmtOut : Type} (D : Def I StmtIn StmtOut)
    (relIn : Set ((StmtIn × ∀ i, TheOracle I i) × Unit))
    (relOut : Set ((StmtOut × ∀ i, TheOracle I i) × Unit)) : Type :=
  Component.Complete D relIn relOut

/-- The security half of a phase, against its two seams. -/
abbrev Security {StmtIn StmtOut : Type} (D : Def I StmtIn StmtOut)
    (relIn : Set ((StmtIn × ∀ i, TheOracle I i) × Unit))
    (relOut : Set ((StmtOut × ∀ i, TheOracle I i) × Unit)) : Type :=
  Component.Security D relIn relOut

variable {StmtIn StmtOut : Type}

/-- The phase with no round that maps the statement and keeps the stack. -/
abbrev passThrough (f : StmtIn → StmtOut) : Def I StmtIn StmtOut :=
  Component.passThrough (TheOracle I) f

/-- Its completeness, whenever `f` carries the input seam into the output seam. -/
def passThroughComplete (f : StmtIn → StmtOut)
    {relIn : Set ((StmtIn × ∀ i, TheOracle I i) × Unit)}
    {relOut : Set ((StmtOut × ∀ i, TheOracle I i) × Unit)}
    (h : ∀ s o, ((s, o), ()) ∈ relIn → ((f s, o), ()) ∈ relOut) :
    Complete I (passThrough I f) relIn relOut :=
  Component.passThroughComplete (TheOracle I) f fun s o _ hin ↦ h s o hin

end Phase

end
end LeanerVM.Protocol
