/-
  LeanVM.E2E.Complete.Tree

  T6-det's non-vacuity: for every hash and every valid honest witness tree within the limits, the
  honest prover outputs under the good events (its proofs of work found, its batchings' matrix
  weights not both zero), from the guest's completeness over a model (L2, with L9's decoding);
  and T6-det without the hypothesis that it outputs.
-/

module

public import LeanVM.E2E.Complete.NonVacuity
public import LeanVM.E2E.Budget

/-!
# The honest prover outputs

`docs/roadmap/t6-completeness.md` §1.2. The honest tree's conditions, each held at every node
(`HonestTree.AllNodes`):

* `HonestTree.Valid H`: every claim's holder verifies with every hash answered by `H` or is a
  child making the claim (`ValidAt`), and the root's DA claims carry their roots' vector digests
  (V_I's outer check);
* `HonestTree.WithinLimits H ρ pfuel`: at the node the honest prover builds from its children's
  outputs, the deployed limits, the deployed budget, and the strings its checks hash
  (`NodeSupport`, L17, kept here: a list of fewer than `2^64` block prefixes supporting the
  node's digest and relation);
* the good events, by name: `HonestTree.PowFound` (every proof of work of V° on a node's digest
  finds a nonce within `pfuel`, `PowGood`) and `HonestTree.WeightsNonzero` (every inner node's
  batching ends with matrix weights not both zero, `honestWeights`).

`honestOut_isSome`: with L2 (`GuestCompleteModel`, whose third conclusion is L9's
`DecodeHonest`) the honest prover outputs. By induction on the tree: the children output; the
batching accepts the honest hints (`batchWith_honestHints`, L11), the children's claims being true
(`honestOut_child`); the node relation holds (`nodeRel_honest`, L12), the caps agree (the
children's fresh claims, `queriesOfWith_deferred_honest`); the node step outputs
(`honestStep_isSome`).

`idealVerify_complete'`: T6-det from the tree's conditions, L2, and the three good events
(`RootsInjAt`, E2E-4, the third): the honest idealized prover outputs a statement with the tree's
claims and an idealized proof V_I accepts.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Node LeanVM.Guest
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd LeanVM.Arithmetization

@[expose] public section

/-! ## Conditions at every node -/

/-- **`P` holds at every node** of the tree. -/
def HonestTree.AllNodes (P : HonestTree → Prop) : HonestTree → Prop
  | .node c xs ss ds kids => P (.node c xs ss ds kids) ∧ ∀ k, k ∈ kids → HonestTree.AllNodes P k
termination_by T => sizeOf T
decreasing_by
  have := List.sizeOf_lt_of_mem ‹k ∈ kids›
  simp_wf
  omega

theorem HonestTree.allNodes_node {P : HonestTree → Prop} {c : Claims}
    {xs : List (Holder LeanXmss.Signature)} {ss : List (Holder Sphincs.Signature)}
    {ds : List (Holder Da.Witness)} {kids : List HonestTree} :
    HonestTree.AllNodes P (.node c xs ss ds kids) ↔
      P (.node c xs ss ds kids) ∧ ∀ k ∈ kids, HonestTree.AllNodes P k := by
  rw [HonestTree.AllNodes.eq_1]

variable (H : Bytes → Digest) (ρ pfuel : ℕ)

/-- A child standing for a subtree's claims (its other fields unread). -/
def claimChild (c : Claims) : Child := ⟨⟨c, leafDefer⟩, ⟨[], 0, 0, 0, [], [], [], 0⟩, ⟨[], []⟩⟩

/-- **The node's holders verify**: with every hash answered by `H`, or through a child making the
claim. -/
def HonestTree.ValidAt : HonestTree → Prop
  | .node claims xs ss ds kids =>
    List.Forall₂ (XmssHeldWith (fun x ↦ some (H x)) (kids.map (claimChild ·.claims)))
        claims.xmss xs ∧
      List.Forall₂ (SphincsHeldWith (fun x ↦ some (H x)) (kids.map (claimChild ·.claims)))
        claims.sphincs ss ∧
      List.Forall₂ (DaHeldWith (fun x ↦ some (H x)) B1.Main.daPadCell B1.Main.daPadRow
        (kids.map (claimChild ·.claims))) claims.da ds

/-- **A valid honest tree**: every node's holders verify, and the root's DA claims carry their
roots' vector digests. -/
def HonestTree.Valid (T : HonestTree) : Prop :=
  T.AllNodes (HonestTree.ValidAt H) ∧
    ∀ c ∈ T.claims.da,
      Da.toBytes c.2 = Id.run (Da.vectorDigestOfWith (fun x ↦ (pure (H x) : Id Digest)) c.1)

/-- The children's outputs. -/
noncomputable def kidOuts (kids : List HonestTree) : Option (List HonestOut) :=
  kids.attach.mapM fun k ↦ honestOut H ρ pfuel k.1

/-- **The node within the limits**: at the deferred claim the honest prover finds from its
children's outputs, the deployed limits, the budget, and the strings the checks hash (L17). -/
def HonestTree.LimitsAt : HonestTree → Prop
  | .node claims xs ss ds kids =>
    ∀ kos, kidOuts H ρ pfuel kids = some kos → ∀ hd, honestDefer H (kos.map HonestOut.child) = some hd →
      End.Limits ⟨claims, hd.2⟩ ⟨kos.map HonestOut.child, xs, ss, ds, hd.1⟩ ∧
      B2C.b2cBudget'.size (End.work ⟨claims, hd.2⟩ ⟨kos.map HonestOut.child, xs, ss, ds, hd.1⟩) ≤
        2 ^ 28 ∧
      NodeSupport H ⟨claims, hd.2⟩ ⟨kos.map HonestOut.child, xs, ss, ds, hd.1⟩

/-- **The tree within the limits**, at every node. -/
def HonestTree.WithinLimits (T : HonestTree) : Prop := T.AllNodes (HonestTree.LimitsAt H ρ pfuel)

/-- The node's proofs of work are found (the good event G1). -/
def HonestTree.PowAt : HonestTree → Prop
  | .node claims _ _ _ kids =>
    ∀ kos, kidOuts H ρ pfuel kids = some kos → ∀ hd, honestDefer H (kos.map HonestOut.child) = some hd →
      PowGood H pfuel (digestOf H ⟨claims, hd.2⟩)

/-- **Every node's proofs of work are found** (G1). -/
def HonestTree.PowFound (T : HonestTree) : Prop := T.AllNodes (HonestTree.PowAt H ρ pfuel)

/-- The node's batching ends with matrix weights not both zero (the good event G2). -/
def HonestTree.WeightsAt : HonestTree → Prop
  | .node _ _ _ _ kids =>
    ∀ kos, kidOuts H ρ pfuel kids = some kos → kos ≠ [] → ∀ ccs,
      childClaimsWith (fun x ↦ some (H x)) (seedOf H) (kos.map HonestOut.child) = some ccs →
      (honestWeights H B1.Main.aggSeedD End.bytecode ccs).1 ≠ 0 ∨
        (honestWeights H B1.Main.aggSeedD End.bytecode ccs).2 ≠ 0

/-- **Every inner node's batching ends with matrix weights not both zero** (G2). -/
def HonestTree.WeightsNonzero (T : HonestTree) : Prop := T.AllNodes (HonestTree.WeightsAt H ρ pfuel)

/-- **The honest commitments do not collide** (G3, E2E-4), on the prover's output. -/
def HonestTree.RootsInjAt (T : HonestTree) : Prop :=
  ∀ o, honestOut H ρ pfuel T = some o → RootsInj o.entries

/-! ## The children's outputs -/

/-- A `mapM` of answered computations answers. -/
theorem mapM_some {α β : Type} (f : α → Option β) :
    ∀ l : List α, (∀ a ∈ l, ∃ b, f a = some b) → ∃ l', l.mapM f = some l'
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a List.mem_cons_self
    obtain ⟨l', hl'⟩ := mapM_some f l fun a' ha' ↦ h a' (List.mem_cons_of_mem _ ha')
    exact ⟨b :: l', by simp [List.mapM_cons, hb, hl']⟩

/-- The children's outputs exist when each child outputs. -/
theorem kidOuts_some {kids : List HonestTree}
    (h : ∀ k ∈ kids, ∃ o, honestOut H ρ pfuel k = some o) : ∃ kos, kidOuts H ρ pfuel kids = some kos :=
  mapM_some _ _ fun k _ ↦ h k.1 k.2

/-- The children's outputs, child by child. -/
theorem forall₂_kidOuts {kids : List HonestTree} {kos : List HonestOut}
    (h : kidOuts H ρ pfuel kids = some kos) :
    List.Forall₂ (fun k o ↦ honestOut H ρ pfuel k = some o) kids kos := by
  have h2 := (List.forall₂_map_left_iff (f := Subtype.val)
    (R := fun k o ↦ honestOut H ρ pfuel k = some o)).mpr (forall₂_of_mapM h)
  rwa [List.attach_map_subtype_val] at h2

/-- The honest prover on a node. -/
theorem honestOut_node {c : Claims} {xs : List (Holder LeanXmss.Signature)}
    {ss : List (Holder Sphincs.Signature)} {ds : List (Holder Da.Witness)} {kids : List HonestTree} :
    honestOut H ρ pfuel (.node c xs ss ds kids) =
      (kidOuts H ρ pfuel kids).bind (honestStep H ρ pfuel c xs ss ds) := by
  rw [honestOut]
  rfl

/-- The output's statement makes the tree's claims. -/
theorem honestOut_claims {T : HonestTree} {o : HonestOut} (h : honestOut H ρ pfuel T = some o) :
    o.stmt.claims = T.claims := by
  cases T with
  | node c xs ss ds kids =>
  rw [honestOut_node, Option.bind_eq_some_iff] at h
  obtain ⟨kos, -, h⟩ := h
  obtain ⟨hd, e, π, -, -, rfl⟩ := honestStep_spec H ρ pfuel h
  rfl

/-- The children's outputs make the subtrees' claims. -/
theorem kidOuts_claims {kids : List HonestTree} {kos : List HonestOut}
    (h : kidOuts H ρ pfuel kids = some kos) :
    (kos.map HonestOut.child).map (·.statement.claims) =
      (kids.map (claimChild ·.claims)).map (·.statement.claims) := by
  have h2 := forall₂_kidOuts H ρ pfuel h
  clear h
  simp only [List.map_map]
  induction h2 with
  | nil => rfl
  | cons hab _ ih =>
    simp only [List.map_cons, Function.comp_apply, ih]
    rw [show (HonestOut.child _).statement.claims = _ from honestOut_claims H ρ pfuel hab]
    rfl

/-! ## The holders, transferred -/

section Transfer

variable {H' : Bytes → Option Digest} {cs cs' : List Child}
  (hc : cs.map (·.statement.claims) = cs'.map (·.statement.claims))
include hc

/-- A child's claims at an index, through a list of the same claims. -/
theorem claims_getElem? {i : ℕ} {c : Child} (h : cs[i]? = some c) :
    ∃ c', cs'[i]? = some c' ∧ c'.statement.claims = c.statement.claims := by
  have := congrArg (·[i]?) hc
  simp only [List.getElem?_map, h, Option.map_some] at this
  rcases h' : cs'[i]? with _ | c'
  · simp [h'] at this
  · simp only [h', Option.map_some, Option.some.injEq] at this
    exact ⟨c', rfl, this.symm⟩

theorem xmssHeldWith_transfer {claim : XmssClaim} {h : Holder LeanXmss.Signature}
    (hh : XmssHeldWith H' cs claim h) : XmssHeldWith H' cs' claim h := by
  cases h with
  | direct σ => exact hh
  | child i =>
    obtain ⟨c, hci, hm⟩ := hh
    obtain ⟨c', hc', he⟩ := claims_getElem? hc hci
    exact ⟨c', hc', he ▸ hm⟩

theorem sphincsHeldWith_transfer {claim : SphincsClaim} {h : Holder Sphincs.Signature}
    (hh : SphincsHeldWith H' cs claim h) : SphincsHeldWith H' cs' claim h := by
  cases h with
  | direct σ => exact hh
  | child i =>
    obtain ⟨c, hci, hm⟩ := hh
    obtain ⟨c', hc', he⟩ := claims_getElem? hc hci
    exact ⟨c', hc', he ▸ hm⟩

theorem daHeldWith_transfer {pc pr : LeanDa.Digest} {claim : DaClaim} {h : Holder Da.Witness}
    (hh : DaHeldWith H' pc pr cs claim h) : DaHeldWith H' pc pr cs' claim h := by
  cases h with
  | direct w => exact hh
  | child i =>
    obtain ⟨c, hci, hm⟩ := hh
    obtain ⟨c', hc', he⟩ := claims_getElem? hc hci
    exact ⟨c', hc', he ▸ hm⟩

end Transfer

/-! ## The deferred claim exists -/

/-- The children's claims, with every hash answered by `H`. -/
theorem childClaimsWith_someH (cs : List Child) :
    childClaimsWith (fun x ↦ some (H x)) (seedOf H) cs =
      some (cs.map fun c ↦ ⟨digestOf H c.statement, c.fresh, c.statement.defer⟩) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [childClaimsWith, List.mapM_cons, statementDigestWith_someH] at ih ⊢
    rw [ih]
    rfl

/-- **The honest prover finds the deferred claim and hints** (L11), for children whose claims are
true, under the batching's good event. -/
theorem honestDefer_some {kos : List HonestOut}
    (hkids : ∀ ko ∈ kos, ko.stmt.defer.BytecodeHolds End.bytecode ∧
      multilinearEval (End.bytecode.map ofK) ko.fresh.bytecodePoint = ko.fresh.bytecodeValue ∧
      Id.run (verifyDeferredWith (m := Id) H End.bytecode (seedOf H) (digestOf H ko.stmt) ko.fresh
        ko.proof) = true)
    (hw : kos ≠ [] → ∀ ccs,
      childClaimsWith (fun x ↦ some (H x)) (seedOf H) (kos.map HonestOut.child) = some ccs →
      (honestWeights H B1.Main.aggSeedD End.bytecode ccs).1 ≠ 0 ∨
        (honestWeights H B1.Main.aggSeedD End.bytecode ccs).2 ≠ 0) :
    ∃ hd, honestDefer H (kos.map HonestOut.child) = some hd := by
  by_cases hk : kos.map HonestOut.child = []
  · exact ⟨(noHints, leafDefer), by simp only [honestDefer, hk, ↓reduceIte]⟩
  · have hne : kos ≠ [] := fun h ↦ hk (by simp [h])
    have hccs := childClaimsWith_someH H (kos.map HonestOut.child)
    set ccs := (kos.map HonestOut.child).map fun c ↦
      (⟨digestOf H c.statement, c.fresh, c.statement.defer⟩ : ChildClaims) with hccs_def
    have hcs : ∀ c ∈ ccs, c.fresh.bytecodePoint.length = Nat.log2 End.bytecode.length ∧
        c.carried.bytecodePoint.length = Nat.log2 End.bytecode.length ∧
        multilinearEval (End.bytecode.map ofK) c.fresh.bytecodePoint = c.fresh.bytecodeValue ∧
        multilinearEval (End.bytecode.map ofK) c.carried.bytecodePoint = c.carried.bytecodeValue := by
      intro c hc
      simp only [ccs, List.map_map, List.mem_map, Function.comp_apply] at hc
      obtain ⟨ko, hko, rfl⟩ := hc
      obtain ⟨hb, hv, hacc⟩ := hkids ko hko
      have hsh := verifyDeferredWith_shaped (fun x ↦ some (H x)) (bytecode := End.bytecode)
        (show verifyDeferredWith (m := Option) (fun x ↦ some (H x)) End.bytecode (seedOf H)
          (digestOf H ko.stmt) ko.fresh ko.proof = some true by
            rw [verifyDeferredWith_someH, hacc])
      exact ⟨hsh.1, hb.1.1, hv, hb.2.2⟩
    obtain ⟨d, hbatch, hholds⟩ := batchWith_honestHints H (s0 := B1.Main.aggSeedD)
      (bytecode := End.bytecode) two_pow_log2_bytecode.symm hcs (hw hne _ hccs)
    refine ⟨(honestHints H B1.Main.aggSeedD End.bytecode ccs, d), ?_⟩
    unfold honestDefer
    simp only [hk, ↓reduceIte, hccs]
    rw [show batchWith (fun x ↦ some (H x)) B1.Main.aggSeedD ccs
      (honestHints H B1.Main.aggSeedD End.bytecode ccs) = some (some d) from hbatch]
    simp only [hholds, ↓reduceIte]

/-! ## The honest prover outputs -/

/-- **Non-vacuity of T6-det: the honest prover outputs**, for every hash, from the guest's
completeness over a model (L2, with L9's decoding as its third conclusion), for an honest tree
whose holders verify, within the limits, under the good events G1 (`PowFound`) and G2
(`WeightsNonzero`), at a valid rate. -/
theorem honestOut_isSome (hL2 : GuestCompleteModel) (hρ : validRate ρ) :
    ∀ T : HonestTree, T.AllNodes (HonestTree.ValidAt H) → T.WithinLimits H ρ pfuel →
      T.PowFound H ρ pfuel → T.WeightsNonzero H ρ pfuel → ∃ o, honestOut H ρ pfuel T = some o := by
  refine HonestTree.induct' _ fun claims xs ss ds kids ih hv hl hp hw ↦ ?_
  rw [HonestTree.WithinLimits, HonestTree.allNodes_node] at hl
  rw [HonestTree.PowFound, HonestTree.allNodes_node] at hp
  rw [HonestTree.WeightsNonzero, HonestTree.allNodes_node] at hw
  rw [HonestTree.allNodes_node] at hv
  obtain ⟨kos, hkos⟩ := kidOuts_some H ρ pfuel fun k hk ↦
    ih k hk (hv.2 k hk) (hl.2 k hk) (hp.2 k hk) (hw.2 k hk)
  have h2 := forall₂_kidOuts H ρ pfuel hkos
  have hchild : ∀ ko ∈ kos, _ := fun ko hko ↦
    (forall₂_mem_right h2 ko hko).elim fun k hk ↦ honestOut_child H ρ pfuel hρ hk.2
  obtain ⟨hd, hdef⟩ := honestDefer_some H
    (fun ko hko ↦ ⟨(hchild ko hko).1, (hchild ko hko).2.1, (hchild ko hko).2.2.1⟩)
    (hw.1 kos hkos)
  obtain ⟨hlim, hbud, hsup⟩ := hl.1 kos hkos hd hdef
  have hc := (kidOuts_claims H ρ pfuel hkos).symm
  obtain ⟨hx, hs, hda⟩ := hv.1
  have hrel := nodeRel_honest H hdef
    (fun ko hko ↦ ⟨(hchild ko hko).1, (hchild ko hko).2.2.1⟩)
    (hx.imp fun _ _ h ↦ xmssHeldWith_transfer hc h)
    (hs.imp fun _ _ h ↦ sphincsHeldWith_transfer hc h)
    (hda.imp fun _ _ h ↦ daHeldWith_transfer hc h)
  have hcaps : CapsAgreeWith H (seedOf H) ⟨kos.map HonestOut.child, xs, ss, ds, hd.1⟩ := by
    intro c hcm
    obtain ⟨ko, hko, rfl⟩ := List.mem_map.mp hcm
    exact (hchild ko hko).2.2.2
  have hstep := honestStep_isSome H hL2 ρ pfuel hdef hsup hrel hlim hcaps hbud
    (hp.1 kos hkos hd hdef)
  obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.mp hstep
  exact ⟨o, by rw [honestOut_node, hkos, Option.bind_some, ho]⟩

/-! ## T6-det from the tree's conditions -/

/-- **T6-det, from the tree's conditions**: for every hash `H`, a valid honest witness tree within
the limits, at a valid rate and a fuel at least the tree's size, under the good events G1
(`PowFound`), G2 (`WeightsNonzero`) and G3 (`RootsInjAt`), with the guest's completeness over a
model (L2, with L9's decoding): the honest idealized prover outputs a statement with the tree's
claims and an idealized proof that V_I accepts. -/
theorem idealVerify_complete' (hL2 : GuestCompleteModel) (T : HonestTree) {fuel : ℕ}
    (hρ : validRate ρ) (hv : T.Valid H) (hlim : T.WithinLimits H ρ pfuel)
    (hpow : T.PowFound H ρ pfuel) (hw : T.WeightsNonzero H ρ pfuel)
    (hroots : T.RootsInjAt H ρ pfuel) (hfuel : T.size ≤ fuel) :
    ∃ s ip, honestIdeal H ρ pfuel T = some (s, ip) ∧ s.claims = T.claims ∧
      idealVerify (m := Id) (fun x ↦ (pure (H x) : Id Digest)) guest ip fuel s = true := by
  obtain ⟨o, ho⟩ := honestOut_isSome H ρ pfuel hL2 hρ T hv.1 hlim hpow hw
  obtain ⟨hc, hacc⟩ := idealVerify_complete H T hρ ho (hroots o ho) hfuel hv.2
  exact ⟨o.stmt, idealOf o, by simp [honestIdeal, ho], hc, hacc⟩

/-- **T6-det in the game's form**: under the same conditions, the game's budgeted run of V_I on
the honest idealized proof, its oracle answering every hash query `x` with `H x` (any `impl`),
from any state whose `spent` plus V_I's query count is within the budget, accepts, `spent`
advanced by the count (L16, `run_idealVerify_budgetedQuery_of_le`). -/
theorem idealVerify_complete_budget (hL2 : GuestCompleteModel) (T : HonestTree) {fuel : ℕ}
    (hρ : validRate ρ) (hv : T.Valid H) (hlim : T.WithinLimits H ρ pfuel)
    (hpow : T.PowFound H ρ pfuel) (hw : T.WeightsNonzero H ρ pfuel)
    (hroots : T.RootsInjAt H ρ pfuel) (hfuel : T.size ≤ fuel) :
    ∃ s ip, honestIdeal H ρ pfuel T = some (s, ip) ∧ s.claims = T.claims ∧
      ∀ {nx ns : ℕ} {b : Type → Type} [Monad b] [LawfulMonad b] (impl : QueryImpl GameSpec b),
        (∀ x, simulateQ impl (liftM (HashSpec.query x) : OracleComp GameSpec Digest) =
          pure (H x)) →
        ∀ (budget : ℕ) (st : SignState nx ns), st.spent + queryCount H guest ip fuel s ≤ budget →
          simulateQ impl (((idealVerify (budgetedQuery budget) guest ip fuel s).run).run st) =
            pure (some true, { st with spent := st.spent + queryCount H guest ip fuel s }) := by
  obtain ⟨s, ip, hI, hc, hacc⟩ := idealVerify_complete' H ρ pfuel hL2 T hρ hv hlim hpow hw hroots
    hfuel
  refine ⟨s, ip, hI, hc, fun impl himpl budget st hb ↦ ?_⟩
  rw [run_idealVerify_budgetedQuery_of_le impl H himpl hb]
  exact congrArg (fun v ↦ pure (some v, _)) hacc

end
end LeanVM.E2E.Complete
