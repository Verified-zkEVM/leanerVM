/-
  LeanVM.E2E.Complete.Rom.ProverN

  T6-prob: the honest idealized prover with H-oblivious choices, its failures by kind.
-/

module

public import LeanVM.E2E.Complete.Rom.Chooser
public import LeanVM.E2E.Complete.Rom.Fresh
public import LeanVM.E2E.Complete.Tree

/-!
# The honest prover, H-obliviously

`docs/roadmap/t6-prob.md` §3. The prover of `Prover.lean` with its two classical choices replaced
by functions of answers it computed: the node's execution chosen from the node's log
(`execOf (logOf H (nodeLog H s w))`, `Chooser.lean`), the fresh claims read off V°'s run
(`freshRun`, `Fresh.lean`). Its failures are reported by kind (`ProverFail`): a proof-of-work search
exhausted `pfuel` (G1, with the program, strategy and seed of the search), an inner node's matrix
weights both zero (G2, with the children's claims), or `stuck` (no execution, or the batching
refuses), which a valid tree within the limits excludes (`NonVacuityN.lean`).

Every node's output lists the entries of its subtree (`EntryN`): node, word, frames, the
children's nodes and the subtree's size; V_I reads, by decision E2E-8, the word and frames of a
node from its smallest entry (`AssembleN.lean`).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Node LeanVM.Guest
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd LeanVM.Protocol.Whir.Complete

@[expose] public section

/-- **Why the honest prover fails.** -/
inductive ProverFail where
  /-- A proof-of-work search of the run of `P` with the strategy `S` from `seed` exhausted the
  fuel. -/
  | grind (P : Prog Bool) (S : Strategy) (seed : Digest)
  /-- An inner node's batching of the children's claims `cs` ends with both matrix weights zero. -/
  | weights (cs : List ChildClaims)
  /-- No execution, or the batching refuses the honest hints. -/
  | stuck

/-- **An entry**: a node, its word, its frames, its children's nodes and its subtree's size. -/
abbrev EntryN : Type := E2E.Node × Word × Frames × List E2E.Node × ℕ

/-- **What the H-oblivious prover outputs for a subtree.** -/
structure HonestOutN where
  /-- The statement. -/
  stmt : NodeStatement
  /-- The fresh claims of its proof. -/
  fresh : FixedClaims
  /-- Its proof. -/
  proof : Proof
  /-- The entries of the subtree's nodes, the root's first. -/
  entries : List EntryN
  /-- The number of nodes of the subtree. -/
  size : ℕ

variable (H : Bytes → Digest) (ρ pfuel : ℕ)

/-- The child of an output. -/
def HonestOutN.child (o : HonestOutN) : Child := ⟨o.stmt, o.fresh, o.proof⟩

/-- The node of an output. -/
noncomputable def nodeOfOutN (o : HonestOutN) : E2E.Node := (digestOf H o.stmt, o.proof)

/-- The children's claims, every hash answered by `H`. -/
noncomputable def childClaimsOf (cs : List Child) : List ChildClaims :=
  cs.map fun c ↦ ⟨digestOf H c.statement, c.fresh, c.statement.defer⟩

open Classical in
/-- **The deferred claim and hints**, failing with the children's claims when the matrices'
weights both vanish (G2). -/
noncomputable def honestDeferN (cs : List Child) : Except ProverFail (BatchHints × DeferredClaim) :=
  if cs = [] then .ok (noHints, leafDefer) else
  if honestWeights H B1.Main.aggSeedD End.bytecode (childClaimsOf H cs) = (0, 0) then
    .error (.weights (childClaimsOf H cs))
  else
    match batchWith (fun x ↦ some (H x)) B1.Main.aggSeedD (childClaimsOf H cs)
        (honestHints H B1.Main.aggSeedD End.bytecode (childClaimsOf H cs)) with
    | some (some d) =>
      if d.BytecodeHolds End.bytecode then
        .ok (honestHints H B1.Main.aggSeedD End.bytecode (childClaimsOf H cs), d)
      else .error .stuck
    | _ => .error .stuck

/-- V°'s program at a node's digest. -/
def progOf (pi : Digest) : Prog Bool :=
  blindProgram End.bytecode (publicDigest (End.publicInputOf pi))

/-- V°'s seed at a node's digest. -/
noncomputable def seedAt (pi : Digest) : Digest :=
  Id.run (seedWith H End.bytecode (publicDigest (End.publicInputOf pi)))

/-- The honest strategy of a chosen execution. -/
noncomputable def stratOf {D : List Bytes} {H' : Bytes → Digest} {pi : Digest} {w : NodeWitness}
    (ρ : ℕ) (e : NodeExecOn D H' pi w) : Strategy :=
  Blind.honestStrategyBlind guest e.1.sz ρ e.1.q

/-- A node's output from its statement, fresh claims, proof, execution and children. -/
noncomputable def outOf (s : NodeStatement) (c : FixedClaims) (π : Proof) {D : List Bytes}
    {H' : Bytes → Digest} {pi : Digest} {w : NodeWitness} (e : NodeExecOn D H' pi w)
    (kos : List HonestOutN) : HonestOutN :=
  ⟨s, c, π,
    ((digestOf H s, π), stackWord (leanIsaμ guest e.1.sz) e.1.q, e.1.fr, kos.map (nodeOfOutN H),
      1 + (kos.map HonestOutN.size).sum) :: kos.flatMap HonestOutN.entries,
    1 + (kos.map HonestOutN.size).sum⟩

/-- **A node's proof**, from its statement and witness: the execution chosen from the node's log,
V°'s honest proof of its stack, the fresh claims read off V°'s run. -/
noncomputable def proveNode (s : NodeStatement) (w : NodeWitness) (kos : List HonestOutN) :
    Except ProverFail HonestOutN :=
  match execOf (logOf H (nodeLog H s w)) (digestOf H s) w with
  | none => .error .stuck
  | some e =>
    match prove H (progOf (digestOf H s)) (stratOf ρ e) (seedAt H (digestOf H s)) pfuel with
    | none => .error (.grind (progOf (digestOf H s)) (stratOf ρ e) (seedAt H (digestOf H s)))
    | some π =>
      match freshRun H (stratOf ρ e) pfuel End.bytecode
          (publicDigest (End.publicInputOf (digestOf H s))) (seedAt H (digestOf H s)) with
      | none => .error .stuck
      | some c => .ok (outOf H s c π e kos)

/-- **The H-oblivious node step**, from the children's outputs. -/
noncomputable def honestStepN (claims : Claims) (xs : List (Holder LeanXmss.Signature))
    (ss : List (Holder Sphincs.Signature)) (ds : List (Holder Da.Witness))
    (kos : List HonestOutN) : Except ProverFail HonestOutN := do
  let hd ← honestDeferN H (kos.map HonestOutN.child)
  proveNode H ρ pfuel ⟨claims, hd.2⟩ ⟨kos.map HonestOutN.child, xs, ss, ds, hd.1⟩ kos

/-- **The H-oblivious honest prover on a subtree.** -/
noncomputable def honestOutN : HonestTree → Except ProverFail HonestOutN
  | .node claims xs ss ds kids => do
    let kos ← kids.attach.mapM fun k ↦ honestOutN k.1
    honestStepN H ρ pfuel claims xs ss ds kos
termination_by T => sizeOf T
decreasing_by
  have := List.sizeOf_lt_of_mem k.2
  simp_wf
  omega

/-- The children's outputs. -/
noncomputable def kidOutsN (kids : List HonestTree) : Except ProverFail (List HonestOutN) :=
  kids.attach.mapM fun k ↦ honestOutN H ρ pfuel k.1

theorem honestOutN_node {c : Claims} {xs : List (Holder LeanXmss.Signature)}
    {ss : List (Holder Sphincs.Signature)} {ds : List (Holder Da.Witness)} {kids : List HonestTree} :
    honestOutN H ρ pfuel (.node c xs ss ds kids) =
      (kidOutsN H ρ pfuel kids).bind (honestStepN H ρ pfuel c xs ss ds) := by
  rw [honestOutN]
  rfl

/-! ## The limits on the H-oblivious prover's outputs -/

/-- **The node within the deployed limits and the budget**, at the H-oblivious prover's
children and deferred claim (`LimitsBudgetAt`'s). -/
def HonestTree.LimitsBudgetN : HonestTree → Prop
  | .node claims xs ss ds kids =>
    ∀ kos, kidOutsN H ρ pfuel kids = .ok kos → ∀ hd,
      honestDeferN H (kos.map HonestOutN.child) = .ok hd →
      End.Limits ⟨claims, hd.2⟩ ⟨kos.map HonestOutN.child, xs, ss, ds, hd.1⟩ ∧
      B2C.b2cBudget'.size (End.work ⟨claims, hd.2⟩ ⟨kos.map HonestOutN.child, xs, ss, ds, hd.1⟩) ≤
        2 ^ 28

/-- **The tree within the deployed limits and the budget**, at every node. -/
def HonestTree.WithinLimitsN (T : HonestTree) : Prop :=
  T.AllNodes (HonestTree.LimitsBudgetN H ρ pfuel)

/-! ## The deferred claim -/

theorem childClaimsWith_childClaimsOf (cs : List Child) :
    childClaimsWith (fun x ↦ some (H x)) (seedOf H) cs = some (childClaimsOf H cs) :=
  childClaimsWith_someH H cs

/-- An accepted deferred claim is `honestDefer`'s. -/
theorem honestDefer_of_N {cs : List Child} {hd : BatchHints × DeferredClaim}
    (h : honestDeferN H cs = .ok hd) : honestDefer H cs = some hd := by
  unfold honestDeferN at h
  unfold honestDefer
  rw [childClaimsWith_childClaimsOf]
  by_cases h0 : cs = []
  · simp only [h0, ↓reduceIte] at h ⊢
    cases h; rfl
  · by_cases hw : honestWeights H B1.Main.aggSeedD End.bytecode (childClaimsOf H cs) = (0, 0)
    · simp only [h0, hw, ↓reduceIte] at h
      cases h
    · simp only [h0, hw, ↓reduceIte] at h ⊢
      cases hb : batchWith (fun x ↦ some (H x)) B1.Main.aggSeedD (childClaimsOf H cs)
          (honestHints H B1.Main.aggSeedD End.bytecode (childClaimsOf H cs)) with
      | none => rw [hb] at h; cases h
      | some r =>
        cases r with
        | none => rw [hb] at h; cases h
        | some d =>
          rw [hb] at h
          by_cases hh : d.BytecodeHolds End.bytecode
          · simp only [hh, ↓reduceIte] at h
            rw [← Except.ok.inj h]
            simp [hh]
          · simp only [hh, ↓reduceIte] at h
            cases h

/-- With the weights not both zero, `honestDefer`'s claim is accepted. -/
theorem honestDeferN_of {cs : List Child} {hd : BatchHints × DeferredClaim}
    (hw : cs ≠ [] → honestWeights H B1.Main.aggSeedD End.bytecode (childClaimsOf H cs) ≠ (0, 0))
    (h : honestDefer H cs = some hd) : honestDeferN H cs = .ok hd := by
  unfold honestDefer at h
  unfold honestDeferN
  rw [childClaimsWith_childClaimsOf] at h
  by_cases h0 : cs = []
  · simp only [h0, ↓reduceIte] at h ⊢
    cases h; rfl
  · have hw' := hw h0
    simp only [h0, hw', ↓reduceIte] at h ⊢
    cases hb : batchWith (fun x ↦ some (H x)) B1.Main.aggSeedD (childClaimsOf H cs)
        (honestHints H B1.Main.aggSeedD End.bytecode (childClaimsOf H cs)) with
    | none => rw [hb] at h; cases h
    | some r =>
      cases r with
      | none => rw [hb] at h; cases h
      | some d =>
        rw [hb] at h
        by_cases hh : d.BytecodeHolds End.bytecode
        · simp only [hh, ↓reduceIte] at h
          rw [← Option.some.inj h]
          simp [hh]
        · simp only [hh, ↓reduceIte] at h
          cases h

end
end LeanVM.E2E.Complete
