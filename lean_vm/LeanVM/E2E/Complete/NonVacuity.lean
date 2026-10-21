/-
  LeanVM.E2E.Complete.NonVacuity

  The honest prover's node step succeeds: from the guest's completeness over a model (L2), the
  node's hashed strings (L17), its relation within the limits, and the proof-of-work event, it
  has an execution under the honest table, a stack, and a proof.
-/

module

public import LeanVM.E2E.Complete.Assemble
public import LeanVM.E2E.Complete.Stack
public import LeanVM.E2E.Complete.CapsRange

/-!
# The honest step succeeds

T6-det (`Assemble.lean`) holds whenever the honest prover outputs; this module shows a node step
outputs (`honestStep_isSome`), from:

* `hL2 : GuestCompleteModel` (L2, with L9's `DecodeHonest` as its third conclusion);
* the node relation with every hash answered by `H` (`nodeRel_honest`, L12);
* `NodeSupport H s w`: the strings the node's checks hash (L17, kept as a hypothesis): a list `D`
  with fewer than `2^64` block prefixes supporting the statement's digest and the node relation;
* the deployed limits, the caps agreeing, the budget;
* `PowGood H pfuel pi`: every proof of work of V° on the node's digest finds a nonce within
  `pfuel` (the good event G1);
* the deferred claim and hints (`honestDefer`, L11 for an inner node).

The execution comes from L2 at the honest table's model (`CompModel.chain`), the stack from
`exists_stack_of_validB` (L3, L4), the proof from `prove_ne_none`.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Node LeanVM.Guest
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd LeanVM.Arithmetization

@[expose] public section

variable (H : Bytes → Digest)

/-- **The node's hashed strings** (L17, kept as a hypothesis): a list of strings with fewer than
`2^64` block prefixes that supports the statement's digest and the node relation at the guest's
IV: answered by `H` on the list alone, they hold when they hold with every string answered. A
property of the checks' queries, not of the witness's honesty. -/
def NodeSupport (s : NodeStatement) (w : NodeWitness) : Prop :=
  ∃ D : List Bytes, (prefixesOf D).length < 2 ^ 64 ∧
    statementDigestWith (answeredOn D H) (seedOf H) s = some (digestOf H s) ∧
    (NodeRelWith (fun x ↦ some (H x)) B1.Main.aggSeedD B1.Main.daPadCell B1.Main.daPadRow
        End.bytecode (seedOf H) s w →
      NodeRelWith (answeredOn D H) B1.Main.aggSeedD B1.Main.daPadCell B1.Main.daPadRow End.bytecode
        (seedOf H) s w)

/-- **The proof-of-work event G1** at a node's digest: every proof of work of V° finds a nonce
within `pfuel`. -/
def PowGood (pfuel : ℕ) (pi : Digest) : Prop :=
  ∀ hist bits k cv,
    (blindProgram End.bytecode (publicDigest (End.publicInputOf pi))).after hist =
      some (.grind bits k) → findNonce H bits cv pfuel ≠ none

/-- The honest table's semantics has canonical rows. -/
instance {D : List Bytes} (I : Intermediates D) (H : Bytes → Digest) :
    Fact (Canonical (chainSem I H)) :=
  ⟨fun h ↦ h.1⟩

/-- **A node has an execution under the honest table**, from L2. -/
theorem nodeExec_nonempty (hL2 : GuestCompleteModel) {s : NodeStatement} {w : NodeWitness}
    (hsup : NodeSupport H s w)
    (hrel0 : NodeRelWith (fun x ↦ some (H x)) B1.Main.aggSeedD B1.Main.daPadCell B1.Main.daPadRow
      End.bytecode (seedOf H) s w) (hlim : End.Limits s w) (hcaps : CapsAgreeWith H (seedOf H) w)
    (hbud : B2C.b2cBudget'.size (End.work s w) ≤ 2 ^ 28) : Nonempty (NodeExec H (digestOf H s) w) := by
  obtain ⟨D, hD, hpi, hrel⟩ := hsup
  replace hrel := hrel hrel0
  let I := intermediatesOf D hD
  obtain ⟨t, fr, hv, hsize, hdec⟩ := hL2 (CompModel.chain I H) H
    (fun _ _ h ↦ (answeredOn_some h).2) (seedOf H) s w (digestOf H s) hpi hrel hlim hcaps hbud
  obtain ⟨sz, q, hadm, hrel', hpad, hrun⟩ :=
    exists_stack_of_validB chainSem_le_free hv hsize
  exact ⟨⟨D, I, t, fr, sz, q, hv, hdec, hadm, ⟨hrel', hpad⟩, hrun⟩⟩

/-- **The honest step succeeds**: with the deferred claim and hints, an execution under the honest
table (L2, L3, L4) and the proof-of-work event, it outputs. -/
theorem honestStep_isSome (hL2 : GuestCompleteModel) (ρ pfuel : ℕ) {claims : Claims}
    {xs : List (Holder LeanXmss.Signature)} {ss : List (Holder Sphincs.Signature)}
    {ds : List (Holder Da.Witness)} {kos : List HonestOut} {hd : BatchHints × DeferredClaim}
    (hdef : honestDefer H (kos.map HonestOut.child) = some hd)
    (hsup : NodeSupport H ⟨claims, hd.2⟩ ⟨kos.map HonestOut.child, xs, ss, ds, hd.1⟩)
    (hrel : NodeRelWith (fun x ↦ some (H x)) B1.Main.aggSeedD B1.Main.daPadCell B1.Main.daPadRow
      End.bytecode (seedOf H) ⟨claims, hd.2⟩ ⟨kos.map HonestOut.child, xs, ss, ds, hd.1⟩)
    (hlim : End.Limits ⟨claims, hd.2⟩ ⟨kos.map HonestOut.child, xs, ss, ds, hd.1⟩)
    (hcaps : CapsAgreeWith H (seedOf H) ⟨kos.map HonestOut.child, xs, ss, ds, hd.1⟩)
    (hbud : B2C.b2cBudget'.size (End.work ⟨claims, hd.2⟩ ⟨kos.map HonestOut.child, xs, ss, ds, hd.1⟩)
      ≤ 2 ^ 28)
    (hpow : PowGood H pfuel (digestOf H ⟨claims, hd.2⟩)) :
    honestStep H ρ pfuel claims xs ss ds kos ≠ none := by
  have hne := nodeExec_nonempty H hL2 hsup hrel hlim hcaps hbud
  unfold honestStep
  simp only [hdef, Option.bind_eq_bind, Option.bind_some, ne_eq]
  split
  · intro h
    simp only [Option.bind_eq_none_iff] at h
    obtain ⟨π, hπ⟩ := Option.ne_none_iff_exists'.mp (prove_ne_none H _ _ _ pfuel hpow)
    exact absurd (h π hπ) (by simp)
  · exact absurd hne ‹_›

/-! ## The honest node relation (L12) -/

/-- The digest of a statement, answered by `some ∘ H`, is `digestOf`. -/
theorem statementDigestWith_someH (s : NodeStatement) :
    statementDigestWith (fun x ↦ some (H x)) (seedOf H) s = some (digestOf H s) := rfl

/-- The deferring verifier, answered by `some ∘ H`, is its `Id` run. -/
theorem verifyDeferredWith_someH (bc : List K) (iv pi : Digest) (c : FixedClaims) (π : Proof) :
    verifyDeferredWith (m := Option) (fun x ↦ some (H x)) bc iv pi c π =
      some (Id.run (verifyDeferredWith (m := Id) H bc iv pi c π)) := by
  simp only [verifyDeferredWith, Option.bind_eq_bind, Option.bind_some, Value.runProof_some]
  rfl

/-- The fresh claims of a proof meet their specification when some claims do. -/
theorem freshFor_spec {pi : Digest} {π : Proof}
    (hex : ∃ c : FixedClaims,
      multilinearEval (End.bytecode.map ofK) c.bytecodePoint = c.bytecodeValue ∧
      Id.run (verifyDeferredWith (m := Id) H End.bytecode (seedOf H) pi c π) = true ∧
      ∀ b ∈ queriesOfWith H (deferredProgram c End.bytecode pi)
        ⟨H (digestBytes (seedOf H) ++ digestBytes pi), π.stream, π.openings, []⟩,
        BatchAgreesWith H b.1 b.2) :
    multilinearEval (End.bytecode.map ofK) (freshFor H pi π).bytecodePoint =
        (freshFor H pi π).bytecodeValue ∧
      Id.run (verifyDeferredWith (m := Id) H End.bytecode (seedOf H) pi (freshFor H pi π) π) =
        true ∧
      ∀ b ∈ queriesOfWith H (deferredProgram (freshFor H pi π) End.bytecode pi)
        ⟨H (digestBytes (seedOf H) ++ digestBytes pi), π.stream, π.openings, []⟩,
        BatchAgreesWith H b.1 b.2 := by
  unfold freshFor
  split
  · rename_i h
    exact h.choose_spec
  · exact absurd hex ‹_›

/-- **What a child of the honest prover gives its parent**: its deferred claim's bytecode part is
true, the deferring verifier accepts its proof with its fresh claims, the bytecode's claim true,
and the query steps of that run on its proof agree in the guest's caps. -/
theorem honestOut_child (ρ pfuel : ℕ) (hρ : validRate ρ) {T : HonestTree} {o : HonestOut}
    (h : honestOut H ρ pfuel T = some o) :
    o.stmt.defer.BytecodeHolds End.bytecode ∧
      multilinearEval (End.bytecode.map ofK) o.fresh.bytecodePoint = o.fresh.bytecodeValue ∧
      Id.run (verifyDeferredWith (m := Id) H End.bytecode (seedOf H) (digestOf H o.stmt) o.fresh
        o.proof) = true ∧
      ∀ b ∈ queriesOfWith H (deferredProgram o.fresh End.bytecode (digestOf H o.stmt))
        ⟨H (digestBytes (seedOf H) ++ digestBytes (digestOf H o.stmt)), o.proof.stream,
          o.proof.openings, []⟩, BatchAgreesWith H b.1 b.2 := by
  refine ⟨(honestOut_root H ρ pfuel hρ h).2, ?_⟩
  cases T with
  | node claims xs ss ds kids =>
  rw [honestOut] at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨kos, -, h⟩ := h
  obtain ⟨hd, e, π, -, hπ, rfl⟩ := honestStep_spec H ρ pfuel h
  obtain ⟨c, hc, hprove, cv', h', hfs⟩ := exists_deferred_honest H e.adm hρ e.rel hπ
  have hacc := runProof_of_fsRun H _ pfuel _ _ hfs hprove
  have hcaps := queriesOfWith_deferred_honest H _ pfuel hprove hfs
  rw [End.publicDigest_publicInputOf] at hacc hcaps
  refine freshFor_spec H ⟨c, hc, ?_, ?_⟩
  · simp only [verifyDeferredWith]
    exact hacc
  · exact hcaps

/-- **The honest node's relation** (L12): with every child's facts (`honestOut_child`) and the
holders verifying with every hash answered by `H`, the node relation holds at `some ∘ H`, the
batching from the baked start. -/
theorem nodeRel_honest {claims : Claims} {xs : List (Holder LeanXmss.Signature)}
    {ss : List (Holder Sphincs.Signature)} {ds : List (Holder Da.Witness)} {kos : List HonestOut}
    {hd : BatchHints × DeferredClaim} (hdef : honestDefer H (kos.map HonestOut.child) = some hd)
    (hkids : ∀ ko ∈ kos, ko.stmt.defer.BytecodeHolds End.bytecode ∧
      Id.run (verifyDeferredWith (m := Id) H End.bytecode (seedOf H) (digestOf H ko.stmt) ko.fresh
        ko.proof) = true)
    (hx : List.Forall₂ (XmssHeldWith (fun x ↦ some (H x)) (kos.map HonestOut.child))
      claims.xmss xs)
    (hs : List.Forall₂ (SphincsHeldWith (fun x ↦ some (H x)) (kos.map HonestOut.child))
      claims.sphincs ss)
    (hda : List.Forall₂ (DaHeldWith (fun x ↦ some (H x)) B1.Main.daPadCell B1.Main.daPadRow
      (kos.map HonestOut.child)) claims.da ds) :
    NodeRelWith (fun x ↦ some (H x)) B1.Main.aggSeedD B1.Main.daPadCell B1.Main.daPadRow
      End.bytecode (seedOf H) ⟨claims, hd.2⟩ ⟨kos.map HonestOut.child, xs, ss, ds, hd.1⟩ := by
  have hspec := honestDefer_spec H hdef
  refine ⟨hspec.1.1, ?_, hx, hs, hda, ?_⟩
  · intro c hc
    obtain ⟨ko, hko, rfl⟩ := List.mem_map.mp hc
    obtain ⟨hb, hv⟩ := hkids ko hko
    refine ⟨hb.1, digestOf H ko.stmt, statementDigestWith_someH H _, ?_⟩
    rw [verifyDeferredWith_someH]
    exact congrArg some hv
  · split
    · rename_i h0
      rw [hspec.2.1 h0]
      exact ⟨by simp [leafDefer], by simp [leafDefer]⟩
    · rename_i h0
      exact hspec.2.2 h0

end
end LeanVM.E2E.Complete
