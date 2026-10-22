/-
  LeanVM.E2E.Complete.Rom.PadRec

  T6-prob, recursion to any depth: every child of the honest prover, leaf or inner node, announces
  a stack log in `[22, 28]`, so the limits on the tree give the prover's on trees of any depth.
-/

module

public import LeanVM.E2E.Complete.Rom.LimitsT
public import LeanVM.E2E.Complete.Rom.EndBudget
public import LeanVM.E2E.Complete.GuestModelBig

/-!
# The limits on the tree, at any depth

`LimitsT.lean` gives the prover's limits from the limits on the tree when every node's children
are leaves (`KidsLeaves`): a leaf's chosen execution is padded above `2^21`, so its stack has at
least `22` variables. With L2 padded (`guestCompleteModel_big`, `GuestModelBig.lean`) every node
has such an execution, children or not:

* **`nodeExec_nodeLog_bigG`**: a node, valid and within the limits, has an execution on its own
  log's strings whose stack has at least 22 variables (`nodeExec_nodeLog_big` without its leaf
  hypothesis);
* **`honestOutN_stackLog`**: on a tree valid at `H` and within `LimitsT` at every node, the
  H-oblivious prover's output announces a stack log in `[22, 28]`, by induction on the tree: the
  children's outputs announce one, so the node is within the deployed limits (`LimitsT`), so its
  chosen execution has at least 22 variables (`execOf_big`);
* **`withinLimitsN_of_TR`**: the limits on the tree give the prover's, with no condition on the
  depth;
* `ValidGenR`: `ValidGenT` without `KidsLeaves`; it gives `ValidGen` (`validGen_of_R`), hence
  T6-prob for generators of trees of any depth (**`idealVerify_complete_rom_rec`**) and with the
  game's budgeted V_I (**`idealVerify_complete_rom_rec_budget`**).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Node LeanVM.Guest
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Rom LeanVM.E2E OracleComp OracleSpec
open scoped ENNReal

@[expose] public section

/-! ## Every node has a big execution -/

/-- **A node, valid and within the limits, has an execution on its own log's strings whose stack
has at least 22 variables** (`nodeExec_nodeLog_big` for every node: L2 padded,
`guestCompleteModel_big`). -/
theorem nodeExec_nodeLog_bigG (H : Bytes → Digest)
    {s : NodeStatement} {w : NodeWitness}
    (hrel : NodeRelWith (fun x ↦ some (H x)) B1.Main.aggSeedD B1.Main.daPadCell B1.Main.daPadRow
      End.bytecode (seedOf H) s w) (hlim : End.Limits s w) (hcaps : CapsAgreeWith H (seedOf H) w)
    (hbud : B2C.b2cBudget'.size (End.work s w) ≤ 2 ^ 28) :
    ∃ e : NodeExecOn (nodeLog H s w) H (digestOf H s) w, 22 ≤ leanIsaμ guest e.1.sz := by
  have hD := nodeLog_count_lt hlim hrel
  have hpi : statementDigestWith (answeredOn (nodeLog H s w) H) (seedOf H) s =
      some (digestOf H s) := by
    rw [statementDigestWith_answeredOn _ _ fun x hx ↦ by
      simp only [nodeLog, nodeLogWith, List.mem_append]
      exact .inl (.inl (.inl (.inl (.inl (.inl hx)))))]
    exact statementDigestWith_someH H s
  have hrel' := nodeRelWith_answeredOn (D := nodeLog H s w) (fun _ hx ↦ hx) hrel
  let I := intermediatesOf (nodeLog H s w) hD
  obtain ⟨t, fr, hv, hsize, hbig, hdec⟩ := guestCompleteModel_big (CompModel.chain I H) H
    (fun _ _ h ↦ (answeredOn_some h).2) (seedOf H) s w (digestOf H s) hpi hrel' hlim hcaps hbud
  obtain ⟨sz, q, hadm, hrel'', hpad, hrun, htot⟩ :=
    exists_stack_total chainSem_le_free hv hsize
  exact ⟨⟨⟨nodeLog H s w, I, t, fr, sz, q, hv, hdec, hadm, ⟨hrel'', hpad⟩, hrun⟩, rfl⟩,
    le_leanIsaμ_of_total (htot ▸ hbig)⟩

variable (H : Bytes → Digest) (ρ pfuel : ℕ)

/-! ## Every child announces a stack log in `[22, 28]` -/

/-- **A node step announces a stack log in `[22, 28]`** when its children's outputs do, at a node
valid at `H` and within the limits on the tree. -/
theorem honestStepN_stackLog (hρ : validRate ρ) {claims : Claims}
    {xs : List (Holder LeanXmss.Signature)} {ss : List (Holder Sphincs.Signature)}
    {ds : List (Holder Da.Witness)} {kids : List HonestTree}
    (hv : (HonestTree.node claims xs ss ds kids).ValidAt H)
    (hl : (HonestTree.node claims xs ss ds kids).LimitsT) {kos : List HonestOutN}
    (hk : kidOutsN H ρ pfuel kids = .ok kos)
    (hkos : ∀ ko ∈ kos, ∀ layout r,
      Verifier.announced End.bytecode ko.proof.stream = some (layout, r) →
        22 ≤ layout.stackLog ∧ layout.stackLog ≤ 28)
    {o : HonestOutN} (h : honestStepN H ρ pfuel claims xs ss ds kos = .ok o) :
    ∀ layout r, Verifier.announced End.bytecode o.proof.stream = some (layout, r) →
      22 ≤ layout.stackLog ∧ layout.stackLog ≤ 28 := by
  obtain ⟨hd, hhd, h⟩ := honestStepN_spec H ρ pfuel h
  obtain ⟨e, π, c', he, hπ, -, rfl⟩ := proveNode_spec H ρ pfuel h
  have h2 := forall₂_kidOutsN H ρ pfuel hk
  have hchild : ∀ ko ∈ kos, _ := fun ko hko ↦
    (forall₂_mem_right h2 ko hko).elim fun k hk ↦ honestOutN_child H ρ pfuel hρ hk.2
  have hdef : honestDefer H ((kos.map HonestOutN.toOut).map HonestOut.child) = some hd := by
    rw [map_toOut_child]; exact honestDefer_of_N H hhd
  have hc := (kidOutsN_claims H ρ pfuel hk).symm
  obtain ⟨hx, hs, hda⟩ := hv
  have hc' : (kids.map (claimChild ·.claims)).map (·.statement.claims) =
      ((kos.map HonestOutN.toOut).map HonestOut.child).map (·.statement.claims) := by
    rw [map_toOut_child]; exact hc
  have hrel := nodeRel_honest H hdef
    (fun ko hko ↦ by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hko
      exact ⟨(hchild k hk).1, (hchild k hk).2.2.1⟩)
    (hx.imp fun _ _ h ↦ xmssHeldWith_transfer hc' h)
    (hs.imp fun _ _ h ↦ sphincsHeldWith_transfer hc' h)
    (hda.imp fun _ _ h ↦ daHeldWith_transfer hc' h)
  rw [map_toOut_child] at hrel
  have hcaps : CapsAgreeWith H (seedOf H) ⟨kos.map HonestOutN.child, xs, ss, ds, hd.1⟩ := by
    intro c hcm
    obtain ⟨ko, hko, rfl⟩ := List.mem_map.mp hcm
    exact (hchild ko hko).2.2.2
  obtain ⟨hlim, hbud⟩ := hl (kos.map HonestOutN.child) hd
    (by
      rw [kidOutsN_claims H ρ pfuel hk]
      simp [claimChild, Function.comp_def])
    (fun c hc ↦ by
      obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hc
      obtain ⟨k, -, hko⟩ := forall₂_mem_right h2 o ho
      exact ⟨hkos o ho, honestOutN_stream_le H hρ hko⟩)
  obtain ⟨eb, hb⟩ := nodeExec_nodeLog_bigG H hrel hlim hcaps hbud
  have hag := agrees_logOf H
    (nodeLog H ⟨claims, hd.2⟩ ⟨kos.map HonestOutN.child, xs, ss, ds, hd.1⟩)
  have hex : ∃ e' : NodeExecOn
      ((logOf H (nodeLog H ⟨claims, hd.2⟩ ⟨kos.map HonestOutN.child, xs, ss, ds, hd.1⟩)).map
        Prod.fst)
      (fillLog (logOf H (nodeLog H ⟨claims, hd.2⟩ ⟨kos.map HonestOutN.child, xs, ss, ds, hd.1⟩)))
      (digestOf H ⟨claims, hd.2⟩) ⟨kos.map HonestOutN.child, xs, ss, ds, hd.1⟩,
      22 ≤ leanIsaμ guest e'.1.sz := by
    rw [strings_logOf]
    exact ⟨⟨eb.1.transport fun _ hx ↦
      (fillLog_eq hag (by rw [strings_logOf]; exact eb.2 ▸ hx)).symm, eb.2⟩, hb⟩
  have hbig := execOf_big hex he
  intro layout r hann
  obtain ⟨-, -, -, hann', -, -⟩ := nodeHead_prove H (prog := guest)
    (input := End.publicInputOf (digestOf H ⟨claims, hd.2⟩)) e.1.adm hρ hπ
  change Verifier.announced End.bytecode π.stream = some (layout, r) at hann
  rw [show End.bytecode = bytecodeWords guest from rfl, hann'] at hann
  cases hann
  rw [Front.stackLog_verifierLayout]
  exact ⟨hbig, e.1.adm.2.2.2⟩

/-- **Every output of the H-oblivious prover announces a stack log in `[22, 28]`**, leaf or inner
node, on a tree valid at `H` and within the limits on the tree at every node. -/
theorem honestOutN_stackLog (hρ : validRate ρ) :
    ∀ T : HonestTree, T.AllNodes (HonestTree.ValidAt H) → T.AllNodes HonestTree.LimitsT →
      ∀ o, honestOutN H ρ pfuel T = .ok o →
        ∀ layout r, Verifier.announced End.bytecode o.proof.stream = some (layout, r) →
          22 ≤ layout.stackLog ∧ layout.stackLog ≤ 28 := by
  refine HonestTree.induct' _ fun claims xs ss ds kids ih hv hl o h ↦ ?_
  rw [HonestTree.allNodes_node] at hv hl
  rw [honestOutN_node] at h
  cases hk : kidOutsN H ρ pfuel kids with
  | error f => rw [hk] at h; cases h
  | ok kos =>
    rw [hk] at h
    refine honestStepN_stackLog H ρ pfuel hρ hv.1 hl.1 hk (fun ko hko ↦ ?_) h
    obtain ⟨k, hkm, hko'⟩ := forall₂_mem_right (forall₂_kidOutsN H ρ pfuel hk) ko hko
    exact ih k hkm (hv.2 k hkm) (hl.2 k hkm) ko hko'

/-! ## The limits on the tree give the prover's -/

/-- **A node within `LimitsT`, its subtrees valid and within `LimitsT`, is within the
H-oblivious prover's limits**, its children leaves or not. -/
theorem limitsBudgetN_of_TR (hρ : validRate ρ) {claims : Claims}
    {xs : List (Holder LeanXmss.Signature)} {ss : List (Holder Sphincs.Signature)}
    {ds : List (Holder Da.Witness)} {kids : List HonestTree}
    (hl : (HonestTree.node claims xs ss ds kids).LimitsT)
    (hk : ∀ k ∈ kids, k.AllNodes (HonestTree.ValidAt H) ∧ k.AllNodes HonestTree.LimitsT) :
    (HonestTree.node claims xs ss ds kids).LimitsBudgetN H ρ pfuel := by
  intro kos hkos hd _
  refine hl (kos.map HonestOutN.child) hd ?_ ?_
  · rw [kidOutsN_claims H ρ pfuel hkos]
    simp [claimChild, Function.comp_def]
  · intro c hc
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hc
    obtain ⟨k, hkm, hko⟩ := forall₂_mem_right (forall₂_kidOutsN H ρ pfuel hkos) o ho
    exact ⟨honestOutN_stackLog H ρ pfuel hρ k (hk k hkm).1 (hk k hkm).2 o hko,
      honestOutN_stream_le H hρ hko⟩

/-- **The limits on the tree give the H-oblivious prover's**, on trees of any depth. -/
theorem withinLimitsN_of_TR (hρ : validRate ρ) :
    ∀ T : HonestTree, T.AllNodes (HonestTree.ValidAt H) → T.AllNodes HonestTree.LimitsT →
      T.WithinLimitsN H ρ pfuel := by
  refine HonestTree.induct' _ fun claims xs ss ds kids ih hv hl ↦ ?_
  rw [HonestTree.allNodes_node] at hv hl
  rw [HonestTree.WithinLimitsN, HonestTree.allNodes_node]
  exact ⟨limitsBudgetN_of_TR H ρ pfuel hρ hl.1 fun k hkm ↦ ⟨hv.2 k hkm, hl.2 k hkm⟩,
    fun k hkm ↦ ih k hkm (hv.2 k hkm) (hl.2 k hkm)⟩

/-! ## Generators of valid trees of any depth -/

/-- **A valid-tree generator, the limits on the tree, any depth**: `ValidGen` with the deployed
limits and budget on claims and holders (`LimitsT`) at every node in place of the prover's limits
(`ValidGenT` without `KidsLeaves`). -/
def ValidGenR (ρ pfuel N QP : ℕ) (gen : OracleComp HashSpec (Option HonestTree)) : Prop :=
  (∀ T, some T ∈ support gen → T.proverQueries ρ pfuel ≤ QP) ∧
  ∀ z ∈ support ((simulateQ loggedRO gen).run []), ∀ T, z.1 = some T →
    T.size ≤ N ∧ T.AllNodes HonestTree.ShapeOK ∧ T.AllNodes HonestTree.LimitsT ∧
      ∀ Ht : Bytes → Digest, (∀ x u, look z.2 x = some u → Ht x = u) → T.Valid Ht

/-- `ValidGenT` is `ValidGenR` with `KidsLeaves`. -/
theorem validGenR_of_T {ρ pfuel N QP : ℕ} {gen : OracleComp HashSpec (Option HonestTree)}
    (h : ValidGenT ρ pfuel N QP gen) : ValidGenR ρ pfuel N QP gen :=
  ⟨h.1, fun z hz T hT ↦
    let ⟨hN, hsh, hl, _, hv⟩ := h.2 z hz T hT
    ⟨hN, hsh, hl, hv⟩⟩

/-- **The limits on the tree give the prover's**, at any depth. -/
theorem validGen_of_R {ρ pfuel N QP : ℕ} (hρ : validRate ρ)
    {gen : OracleComp HashSpec (Option HonestTree)} (h : ValidGenR ρ pfuel N QP gen) :
    ValidGen ρ pfuel N QP gen :=
  ⟨h.1, fun z hz T hT ↦ by
    obtain ⟨hN, hsh, hl, hv⟩ := h.2 z hz T hT
    exact ⟨hN, hsh, fun Ht hHt ↦ ⟨hv Ht hHt,
      withinLimitsN_of_TR Ht ρ pfuel hρ T (hv Ht hHt).1 hl⟩⟩⟩

/-- **T6-prob at any depth**: `idealVerify_complete_rom` for a generator whose trees, of any
depth, are within the deployed limits on their claims and holders. -/
theorem idealVerify_complete_rom_rec {ρ pfuel N QG QP fuel : ℕ}
    (hρ : validRate ρ) (hpf : pfuel ≤ 2 ^ 64) (gen : OracleComp HashSpec (Option HonestTree))
    (hQG : IsTotalQueryBound gen QG) (hgen : ValidGenR ρ pfuel N QP gen) (hfuel : N ≤ fuel) :
    Pr{let z ← completeExp ρ pfuel gen}[¬ CompleteOK fuel z] ≤ completeError (QG + QP) pfuel :=
  idealVerify_complete_rom hρ hpf gen hQG (validGen_of_R hρ hgen) hfuel

/-- **T6-prob at any depth with the game's budget**: `idealVerify_complete_rom_budget` for a
generator whose trees, of any depth, are within the deployed limits on their claims and
holders. -/
theorem idealVerify_complete_rom_rec_budget {nx ns : ℕ}
    {ρ pfuel N QG QP budget : ℕ} (hρ : validRate ρ) (hpf : pfuel ≤ 2 ^ 64)
    (gen : OracleComp HashSpec (Option HonestTree)) (hQG : IsTotalQueryBound gen QG)
    (hgen : ValidGenR ρ pfuel N QP gen) (hB : N * viNodeBound ≤ budget) :
    Pr{let z ← completeRunGame (nx := nx) (ns := ns) ρ pfuel gen N budget}[z.1 = some false] ≤
      completeError (QG + QP) pfuel :=
  idealVerify_complete_rom_budget hρ hpf gen hQG (validGen_of_R hρ hgen) hB

end
end LeanVM.E2E.Complete
