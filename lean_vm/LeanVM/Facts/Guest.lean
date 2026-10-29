/-
  LeanVM.Facts.Guest

  The guest's names the proofs share, moved here from `Statement/LeanVmGuest.lean`, names kept:
  the guest's bytecode (`End.bytecode`), the public input of a digest (`End.publicInputOf`), a
  child's announced shape (`childShape`) and a node's work (`End.Work`, `End.work`), whose fields
  the two completeness statements write out.
-/

module

public import Statement.LeanVmGuest

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-- **A child's announced stack log and rate** (`readSizes`, `Verifier.announced`): the opening
arm its `verify_sub` dispatches to (G:3314-3316); `(0, 0)` if its stream announces none, which no
child of a node within `Limits`, its caps agreeing and no zero challenge, does
(`B1.Main.childShape_bounds`). -/
def childShape (bytecode : List K) (c : Child) : ℕ × ℕ :=
  match announced bytecode c.proof.stream with
  | some (layout, r) => (layout.stackLog, r)
  | none => (0, 0)

namespace End

/-- The guest's bytecode, as the verifier and `NodeRel` read it. -/
abbrev bytecode : List K := bytecodeWords guest

/-- The public input a digest is: its four words, the digest's halves in memory words `0` and `1`
(`PublicInput.ofDigest`). -/
abbrev publicInputOf (d : Digest) : PublicInput := PublicInput.ofDigest d

/-- **A node's work**: what the size of its run grows with. -/
structure Work where
  /-- The declared claims, of the two signature lists. -/
  declared : ℕ
  /-- The coverage table's slots. -/
  coverage : ℕ
  /-- The raw leanXMSS signatures. -/
  rawXmss : ℕ
  /-- The raw leanSPHINCS signatures. -/
  rawSphincs : ℕ
  /-- The blob matrix checked directly: `1`, or `0` without one. -/
  rawDa : ℕ
  /-- Their rows: the blobs held directly. -/
  rawDaRows : ℕ
  /-- Their padded heights (`LeanDa.nPad` of their rows). -/
  rawDaPad : ℕ
  /-- The children. -/
  children : ℕ
  /-- The children's declared claims, of the two signature lists. -/
  childClaims : ℕ
  /-- Each child's announced stack log and rate (`childShape`). -/
  childShapes : List (ℕ × ℕ)

/-- The work of the node `s` with the witness `w`. -/
def work (s : NodeStatement) (w : NodeWitness) : Work where
  declared := s.claims.xmss.length + s.claims.sphincs.length
  coverage := coverage s w
  rawXmss := (Hints.direct s.claims.xmss w.xmss).length
  rawSphincs := (Hints.direct s.claims.sphincs w.sphincs).length
  rawDa := (w.da.map fun _ ↦ 1).getD 0
  rawDaRows := (w.da.map fun p ↦ p.2.rows.length).getD 0
  rawDaPad := (w.da.map fun p ↦ LeanDa.nPad p.2.rows.length).getD 0
  children := w.children.length
  childClaims := (w.children.map fun c ↦ c.statement.claims.xmss.length +
    c.statement.claims.sphincs.length).sum
  childShapes := w.children.map (childShape bytecode)

end End

end
end LeanVM.Guest
