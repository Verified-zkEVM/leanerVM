/-
  LeanVM.E2E.Complete.Prover

  The honest idealized prover of T6-det: for a hash and an honest witness tree, bottom up, every
  node's deferred claim, witness, execution under the honest table, stack, V° proof and fresh
  claims, and the idealized proof of the root.
-/

module

public import LeanVM.E2E.Complete.Interfaces
public import LeanVM.E2E.Complete.Hints
public import LeanVM.E2E.Complete.Deferred
public import LeanVM.E2E.Complete.Node

/-!
# The honest idealized prover

`docs/roadmap/t6-completeness.md` §1.1. An honest witness tree (`HonestTree`) gives each node its
claims, their holders and its children; the prover `honestOut H ρ pfuel` computes the rest,
bottom up, by a node step (`honestStep`) on the children's outputs:

1. the children (`Child`: statement, fresh claims, proof);
2. the deferred claim and the batching's hints (`honestDefer`): at a leaf the bytecode's true
   value at the zero point (`leafDefer`); at an inner node the honest hints (`honestHints`, L11:
   the batching accepts them when the matrices' weights are not both zero);
3. the node's execution (`NodeExec`): the strings `D` it hashes and their codes `I`, an execution
   of the guest valid under the honest table (`CompModel.chain I H`), frames at which V_I's decoder
   reads its children back, admissible sizes and a stack satisfying the relation without Flock with
   honest padding whose candidate run is the execution (a classical choice; L2, L3, L4 show one
   exists);
4. V°'s honest proof (`prove`, `none` when a proof-of-work search exhausts `pfuel`);
5. the fresh claims for the parent (`freshFor`: the deferring verifier accepts the proof with
   them, `verifyDeferredWith_honest`, and its query steps agree in the guest's caps,
   `queriesOfWith_deferred_honest`);
6. the entries `(root, word, frames)` of the node and its descendants.

`honestIdeal` is the root's statement and its idealized proof (`idealOf`): the root's proof, and
for every node of the output the word and frames of the first entry of its stack root (the
idealized proof is keyed by node, decision E2E-8).
`RootsInj` is T6-det's third good event (decision E2E-4): entries with one root are one entry.
`honestOut ≠ none` holds under the other two good events, L2 and the limits (`honestOut_isSome`,
`Tree.lean`); T6-det itself only needs the output (`Assemble.lean`).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Node LeanVM.Guest
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd LeanVM.Protocol.Whir.Complete

@[expose] public section

/-- **An honest witness tree**: a node's claims, the holders of its leanXMSS, leanSPHINCS and DA
claims, and its children. -/
inductive HonestTree where
  | node (claims : Claims) (xmss : List (Holder LeanXmss.Signature))
      (sphincs : List (Holder Sphincs.Signature)) (da : List (Holder Da.Witness))
      (kids : List HonestTree)

/-- The tree's root claims. -/
def HonestTree.claims : HonestTree → Claims
  | .node c _ _ _ _ => c

/-- The number of nodes. -/
def HonestTree.size : HonestTree → ℕ
  | .node _ _ _ _ kids => 1 + (kids.attach.map fun k ↦ k.1.size).sum
termination_by T => sizeOf T
decreasing_by
  have := List.sizeOf_lt_of_mem k.2
  simp_wf
  omega

/-- An entry of the idealized proof: a stack root, its word, and the frames the decoder reads. -/
abbrev Entry : Type := (E × E) × Word × Frames

/-- **What the honest prover outputs for a subtree**: the root's statement, fresh claims and
proof, the entries of every node, and every node with its children's nodes. -/
structure HonestOut where
  /-- The statement. -/
  stmt : NodeStatement
  /-- The fresh claims of its proof. -/
  fresh : FixedClaims
  /-- Its proof. -/
  proof : Proof
  /-- The entries of the subtree's nodes, the root's first. -/
  entries : List Entry
  /-- The number of nodes of the subtree. -/
  size : ℕ
  /-- Every node of the subtree, with its children's nodes and its subtree's size, the root's
  first. -/
  subs : List (E2E.Node × List E2E.Node × ℕ)

variable (H : Bytes → Digest) (ρ pfuel : ℕ)

/-- The guest's IV with `H`, the seed of every node. -/
noncomputable def seedOf : Digest := Id.run (fiatShamirIvWith (fun x ↦ (pure (H x) : Id Digest)) End.bytecode)

/-- A node's statement digest with `H`. -/
noncomputable def digestOf (s : NodeStatement) : Digest :=
  Id.run (statementDigestWith (fun x ↦ (pure (H x) : Id Digest)) (seedOf H) s)

/-- **A leaf's deferred claim**: the bytecode's true value at the zero point, the matrices at the
zero point (their values unchecked). -/
def leafDefer : DeferredClaim where
  bytecodePoint := List.replicate (Nat.log2 End.bytecode.length) 0
  bytecodeValue := multilinearEval (End.bytecode.map ofK) (List.replicate (Nat.log2 End.bytecode.length) 0)
  matrixPoint := List.replicate (2 * blake2sR1csLogSize) 0
  matrixA := 0
  matrixB := 0

/-- No hints. -/
def noHints : BatchHints := ⟨[], [], 0, 0, 0⟩

open Classical in
/-- **The deferred claim and the batching's hints**: at a leaf `leafDefer`; at an inner node the
honest hints (`honestHints`, from the baked start) and the claim the batching of the children's
claims defers with them, if it accepts and the claim's bytecode part is true. -/
noncomputable def honestDefer (cs : List Child) : Option (BatchHints × DeferredClaim) :=
  if cs = [] then some (noHints, leafDefer) else
  match childClaimsWith (fun x ↦ some (H x)) (seedOf H) cs with
  | none => none
  | some ccs =>
    match batchWith (fun x ↦ some (H x)) Guest.B1.Main.aggSeedD ccs
        (honestHints H Guest.B1.Main.aggSeedD End.bytecode ccs) with
    | some (some d) =>
      if d.BytecodeHolds End.bytecode then
        some (honestHints H Guest.B1.Main.aggSeedD End.bytecode ccs, d)
      else none
    | _ => none

/-- **A node's execution under the honest table**: the strings it hashes and their codes, an
execution valid under the honest table's semantics on the statement digest's input, frames at
which V_I's decoder reads back the witness's children, admissible sizes, and a stack satisfying
the relation without Flock with honest padding whose candidate run is the execution. -/
structure NodeExec (pi : Digest) (w : NodeWitness) where
  /-- The strings the node hashes. -/
  D : List Bytes
  /-- Their prefixes' codes. -/
  I : Intermediates D
  /-- The execution. -/
  t : Trace guest
  /-- The decoder's frames. -/
  fr : Frames
  /-- The sizes. -/
  sz : Sizes
  /-- The stack. -/
  q : Column (leanIsaμ guest sz)
  /-- The execution is valid under the honest table. -/
  valid : ValidExecutionB (CompModel.chain I H).sem guest (End.publicInputOf pi) t
  /-- The children decode back. -/
  decode : DecodeHonest fr t w
  /-- The sizes are admissible. -/
  adm : sz.Admissible guest
  /-- The stack satisfies the relation without Flock. -/
  rel : Blind.M3HonestBlind (Complete.inst guest sz) (End.publicInputOf pi) q
  /-- Its candidate run is the execution. -/
  run : candidateRun guest sz q = some t

open Classical in
/-- **The fresh claims of a proof**: claims with which the deferring verifier accepts it, the
bytecode's claim true, and its query steps on the proof agreeing in the guest's caps, if there are
any. -/
noncomputable def freshFor (pi : Digest) (π : Proof) : FixedClaims :=
  if h : ∃ c : FixedClaims,
      multilinearEval (End.bytecode.map ofK) c.bytecodePoint = c.bytecodeValue ∧
      Id.run (verifyDeferredWith (m := Id) H End.bytecode (seedOf H) pi c π) = true ∧
      ∀ b ∈ queriesOfWith H (deferredProgram c End.bytecode pi)
        ⟨H (digestBytes (seedOf H) ++ digestBytes pi), π.stream, π.openings, []⟩,
        BatchAgreesWith H b.1 b.2
  then h.choose else ⟨[], 0, 0, 0, [], [], [], 0⟩

/-- The child of an output. -/
def HonestOut.child (o : HonestOut) : Child := ⟨o.stmt, o.fresh, o.proof⟩

/-- The node of an output: its statement's digest and its proof. -/
noncomputable def nodeOfOut (o : HonestOut) : E2E.Node := (digestOf H o.stmt, o.proof)

open Classical in
/-- **The honest prover's node step**, from the children's outputs. -/
noncomputable def honestStep (claims : Claims) (xs : List (Holder LeanXmss.Signature))
    (ss : List (Holder Sphincs.Signature)) (ds : List (Holder Da.Witness))
    (kos : List HonestOut) : Option HonestOut := do
  let cs := kos.map HonestOut.child
  let hd ← honestDefer H cs
  let s : NodeStatement := ⟨claims, hd.2⟩
  let w : NodeWitness := ⟨cs, xs, ss, ds, hd.1⟩
  let pi := digestOf H s
  if h : Nonempty (NodeExec H pi w) then
    let e := Classical.choice h
    let π ← prove H (blindProgram End.bytecode (publicDigest (End.publicInputOf pi)))
      (Blind.honestStrategyBlind guest e.sz ρ e.q)
      (Id.run (seedWith H End.bytecode (publicDigest (End.publicInputOf pi)))) pfuel
    some ⟨s, freshFor H pi π, π,
      ((stackRoot π).getD (0, 0), stackWord (leanIsaμ guest e.sz) e.q, e.fr) ::
        kos.flatMap HonestOut.entries,
      1 + (kos.map HonestOut.size).sum,
      ((pi, π), kos.map (nodeOfOut H), 1 + (kos.map HonestOut.size).sum) ::
        kos.flatMap HonestOut.subs⟩
  else none

/-- **The honest prover on a subtree.** -/
noncomputable def honestOut : HonestTree → Option HonestOut
  | .node claims xs ss ds kids => do
    let kos ← kids.attach.mapM fun k ↦ honestOut k.1
    honestStep H ρ pfuel claims xs ss ds kos
termination_by T => sizeOf T
decreasing_by
  have := List.sizeOf_lt_of_mem k.2
  simp_wf
  omega

/-- The stack root of a node's proof, `(0, 0)` if it has none: the key of its entry. -/
def rootKey (ν : E2E.Node) : E × E := (stackRoot ν.2).getD (0, 0)

/-- **The idealized proof of an output**: its proof, and for every node of the output the word and
frames of the first entry of the node's stack root (E2E-8: by node). -/
def idealOf (o : HonestOut) : IdealProof where
  proof := o.proof
  words := o.subs.map fun p ↦
    (p.1, ((o.entries.find? (·.1 = rootKey p.1)).map (·.2.1)).getD fun _ ↦ [])
  frames ν := ((o.entries.find? (·.1 = rootKey ν)).map (·.2.2)).getD fun _ _ ↦ none

/-- **The honest idealized prover**: the root statement and its idealized proof. -/
noncomputable def honestIdeal (T : HonestTree) : Option (NodeStatement × IdealProof) :=
  (honestOut H ρ pfuel T).map fun o ↦ (o.stmt, idealOf o)

/-- **T6-det's third good event** (E2E-4): entries with one root are one entry. -/
def RootsInj (es : List Entry) : Prop := ∀ e₁ ∈ es, ∀ e₂ ∈ es, e₁.1 = e₂.1 → e₁ = e₂

end
end LeanVM.E2E.Complete
