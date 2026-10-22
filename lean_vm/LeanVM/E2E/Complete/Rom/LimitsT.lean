/-
  LeanVM.E2E.Complete.Rom.LimitsT

  T6-prob, recursion: the limits as a condition on the tree alone. The children's stack logs and
  streams, which `WithinLimitsN` reads off the prover's outputs, hold of the honest prover's
  children: the stream always (`StreamCap.lean`), the stack log when the child is a leaf (the
  padded execution, `Pad.lean`).
-/

module

public import LeanVM.E2E.Complete.Rom.Pad
public import LeanVM.E2E.Complete.Rom.StreamCap
public import LeanVM.E2E.Complete.Rom.End

/-!
# The limits on the tree

`End.Limits` reads of a node's children only their statements' claims, except for two clauses on
their proofs: the announced stack log in `[22, 28]` (`stackLog`) and the stream within `8192`
words (`stream`); the budget `End.work` reads only claims and holders. So:

* `HonestTree.LimitsT`: at a node, for every list of children with the subtrees' claims and
  proofs meeting the two clauses, and every deferred claim and hints, the deployed limits and the
  budget. It names no hash and no prover.
* The honest prover's children meet the two clauses: the stream always
  (`honestOutN_stream_le`); the stack log at a leaf (`honestOutN_leaf_stackLog`): the chooser
  `execOf` takes an execution of at least 22 variables when there is one, and a leaf has one,
  padded (`nodeExec_nodeLog_big`); the verifier's own check caps it at 28.
* **`withinLimitsN_of_T`**: on a tree whose every node's children are leaves
  (`HonestTree.KidsLeaves`), valid at `H` and within `LimitsT` at every node, the H-oblivious
  prover's limits `WithinLimitsN H ρ pfuel` hold.
* `ValidGenT`: `ValidGen` with `LimitsT` and `KidsLeaves` on the tree in place of
  `WithinLimitsN`; it gives `ValidGen` (`validGen_of_T`), hence T6-prob
  (**`idealVerify_complete_rom_T`**).

For a deeper tree the one condition left is the stack log of a child that is itself an inner
node: its execution must have at least 22 variables (`docs/roadmap/t6-prob.md` §7, risk 5).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Node LeanVM.Guest
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Rom LeanVM.E2E OracleComp OracleSpec
open scoped ENNReal

@[expose] public section

/-! ## The limits on the tree -/

/-- **The node within the deployed limits and the budget, on its claims and holders**: for every
list of children making the subtrees' claims, of proofs announcing a stack log in `[22, 28]` and
within the stream cap, and every deferred claim and hints. -/
def HonestTree.LimitsT : HonestTree → Prop
  | .node claims xs ss ds kids =>
    ∀ (cs : List Child) (hd : BatchHints × DeferredClaim),
      cs.map (·.statement.claims) = kids.map HonestTree.claims →
      (∀ c ∈ cs, (∀ layout r, Verifier.announced End.bytecode c.proof.stream = some (layout, r) →
          22 ≤ layout.stackLog ∧ layout.stackLog ≤ 28) ∧ c.proof.stream.length ≤ Hints.streamCap) →
      End.Limits ⟨claims, hd.2⟩ ⟨cs, xs, ss, ds, hd.1⟩ ∧
        B2C.b2cBudget'.size (End.work ⟨claims, hd.2⟩ ⟨cs, xs, ss, ds, hd.1⟩) ≤ 2 ^ 28

/-- **The node's children are leaves.** -/
def HonestTree.KidsLeaves : HonestTree → Prop
  | .node _ _ _ _ kids => ∀ k ∈ kids, ∃ c xs ss ds, k = .node c xs ss ds []

/-! ## The chooser takes a big execution -/

/-- **When an execution of at least 22 variables exists, the chooser takes one.** -/
theorem execOf_big {L : Log} {pi : Digest} {w : NodeWitness}
    (hex : ∃ e : NodeExecOn (L.map Prod.fst) (fillLog L) pi w, 22 ≤ leanIsaμ guest e.1.sz)
    {e : NodeExecOn (L.map Prod.fst) (fillLog L) pi w} (he : execOf L pi w = some e) :
    22 ≤ leanIsaμ guest e.1.sz := by
  unfold execOf at he
  split_ifs at he
  cases he
  exact Classical.choose_spec hex

variable (H : Bytes → Digest) (ρ pfuel : ℕ)

/-- **A leaf's proof announces a stack log in `[22, 28]`**: its chosen execution is padded. -/
theorem honestOutN_leaf_stackLog (hρ : validRate ρ) {c : Claims}
    {xs : List (Holder LeanXmss.Signature)} {ss : List (Holder Sphincs.Signature)}
    {ds : List (Holder Da.Witness)} (hv : (HonestTree.node c xs ss ds []).ValidAt H)
    (hl : (HonestTree.node c xs ss ds []).LimitsT) {o : HonestOutN}
    (h : honestOutN H ρ pfuel (.node c xs ss ds []) = .ok o) :
    ∀ layout r, Verifier.announced End.bytecode o.proof.stream = some (layout, r) →
      22 ≤ layout.stackLog ∧ layout.stackLog ≤ 28 := by
  rw [honestOutN_node] at h
  have h0 : kidOutsN H ρ pfuel [] = .ok [] := rfl
  rw [h0] at h
  obtain ⟨hd, hhd, h⟩ := honestStepN_spec H ρ pfuel h
  have hd0 : hd = (noHints, leafDefer) := by
    have h1 : honestDeferN H (([] : List HonestOutN).map HonestOutN.child) =
        Except.ok (noHints, leafDefer) := by simp [honestDeferN]
    rw [h1] at hhd
    cases hhd
    rfl
  subst hd0
  obtain ⟨e, π, c', he, hπ, -, rfl⟩ := proveNode_spec H ρ pfuel h
  have hdef : honestDefer H (([] : List HonestOut).map HonestOut.child) =
      some (noHints, leafDefer) := by simp [honestDefer]
  obtain ⟨hx, hs, hda⟩ := hv
  have hrel := nodeRel_honest H hdef (fun ko hko ↦ absurd hko List.not_mem_nil)
    (by simpa using hx) (by simpa using hs) (by simpa using hda)
  obtain ⟨hlim, hbud⟩ := hl [] (noHints, leafDefer) rfl (fun _ h ↦ absurd h List.not_mem_nil)
  have hcaps : CapsAgreeWith H (seedOf H) ⟨[], xs, ss, ds, noHints⟩ :=
    fun _ h ↦ absurd h List.not_mem_nil
  obtain ⟨eb, hb⟩ := nodeExec_nodeLog_big H hrel hlim hcaps hbud rfl
  have hag := agrees_logOf H (nodeLog H ⟨c, leafDefer⟩ ⟨[], xs, ss, ds, noHints⟩)
  have hex : ∃ e' : NodeExecOn
      ((logOf H (nodeLog H ⟨c, leafDefer⟩ ⟨[], xs, ss, ds, noHints⟩)).map Prod.fst)
      (fillLog (logOf H (nodeLog H ⟨c, leafDefer⟩ ⟨[], xs, ss, ds, noHints⟩)))
      (digestOf H ⟨c, leafDefer⟩) ⟨[], xs, ss, ds, noHints⟩, 22 ≤ leanIsaμ guest e'.1.sz := by
    rw [strings_logOf]
    exact ⟨⟨eb.1.transport fun _ hx ↦
      (fillLog_eq hag (by rw [strings_logOf]; exact eb.2 ▸ hx)).symm, eb.2⟩, hb⟩
  have hbig := execOf_big hex he
  intro layout r hann
  obtain ⟨-, -, -, hann', -, -⟩ := nodeHead_prove H (prog := guest)
    (input := End.publicInputOf (digestOf H ⟨c, leafDefer⟩)) e.1.adm hρ hπ
  change Verifier.announced End.bytecode π.stream = some (layout, r) at hann
  rw [show End.bytecode = bytecodeWords guest from rfl, hann'] at hann
  cases hann
  rw [Front.stackLog_verifierLayout]
  exact ⟨hbig, e.1.adm.2.2.2⟩

/-- **A node whose children are leaves, within `LimitsT` with its leaves, is within the
H-oblivious prover's limits.** -/
theorem limitsBudgetN_of_T (hρ : validRate ρ) {claims : Claims}
    {xs : List (Holder LeanXmss.Signature)} {ss : List (Holder Sphincs.Signature)}
    {ds : List (Holder Da.Witness)} {kids : List HonestTree}
    (hl : (HonestTree.node claims xs ss ds kids).LimitsT)
    (hk : ∀ k ∈ kids, (∃ c xs ss ds, k = .node c xs ss ds []) ∧ k.ValidAt H ∧ k.LimitsT) :
    (HonestTree.node claims xs ss ds kids).LimitsBudgetN H ρ pfuel := by
  intro kos hkos hd _
  refine hl (kos.map HonestOutN.child) hd ?_ ?_
  · rw [kidOutsN_claims H ρ pfuel hkos]
    simp [claimChild, Function.comp_def]
  · intro c hc
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hc
    obtain ⟨k, hkm, hko⟩ := forall₂_mem_right (forall₂_kidOutsN H ρ pfuel hkos) o ho
    obtain ⟨⟨c, xs, ss, ds, rfl⟩, hkv, hkl⟩ := hk k hkm
    exact ⟨honestOutN_leaf_stackLog H ρ pfuel hρ hkv hkl hko, honestOutN_stream_le H hρ hko⟩

/-- **The limits on the tree give the H-oblivious prover's**, on a tree whose every node's
children are leaves. -/
theorem withinLimitsN_of_T (hρ : validRate ρ) :
    ∀ T : HonestTree, T.AllNodes (HonestTree.ValidAt H) → T.AllNodes HonestTree.LimitsT →
      T.AllNodes HonestTree.KidsLeaves → T.WithinLimitsN H ρ pfuel := by
  refine HonestTree.induct' _ fun claims xs ss ds kids ih hv hl hk ↦ ?_
  rw [HonestTree.allNodes_node] at hv hl hk
  rw [HonestTree.WithinLimitsN, HonestTree.allNodes_node]
  refine ⟨limitsBudgetN_of_T H ρ pfuel hρ hl.1 fun k hkm ↦ ⟨hk.1 k hkm, ?_, ?_⟩,
    fun k hkm ↦ ih k hkm (hv.2 k hkm) (hl.2 k hkm) (hk.2 k hkm)⟩
  · have := hv.2 k hkm
    obtain ⟨c, xs, ss, ds, rfl⟩ := hk.1 k hkm
    rw [HonestTree.allNodes_node] at this
    exact this.1
  · have := hl.2 k hkm
    obtain ⟨c, xs, ss, ds, rfl⟩ := hk.1 k hkm
    rw [HonestTree.allNodes_node] at this
    exact this.1

/-! ## Generators of valid trees, the limits on the tree -/

/-- **A valid-tree generator, the limits on the tree**: `ValidGen` with the deployed limits and
budget on claims and holders (`LimitsT`) and leaves for children (`KidsLeaves`) at every node in
place of the prover's limits. -/
def ValidGenT (ρ pfuel N QP : ℕ) (gen : OracleComp HashSpec (Option HonestTree)) : Prop :=
  (∀ T, some T ∈ support gen → T.proverQueries ρ pfuel ≤ QP) ∧
  ∀ z ∈ support ((simulateQ loggedRO gen).run []), ∀ T, z.1 = some T →
    T.size ≤ N ∧ T.AllNodes HonestTree.ShapeOK ∧ T.AllNodes HonestTree.LimitsT ∧
      T.AllNodes HonestTree.KidsLeaves ∧
      ∀ Ht : Bytes → Digest, (∀ x u, look z.2 x = some u → Ht x = u) → T.Valid Ht

/-- **The limits on the tree give the prover's.** -/
theorem validGen_of_T {ρ pfuel N QP : ℕ} (hρ : validRate ρ)
    {gen : OracleComp HashSpec (Option HonestTree)} (h : ValidGenT ρ pfuel N QP gen) :
    ValidGen ρ pfuel N QP gen :=
  ⟨h.1, fun z hz T hT ↦ by
    obtain ⟨hN, hsh, hl, hk, hv⟩ := h.2 z hz T hT
    exact ⟨hN, hsh, fun Ht hHt ↦ ⟨hv Ht hHt,
      withinLimitsN_of_T Ht ρ pfuel hρ T (hv Ht hHt).1 hl hk⟩⟩⟩

/-- **T6-prob, the limits on the tree**: `idealVerify_complete_rom` for a generator whose trees
are within the deployed limits on their claims and holders, every node's children leaves. -/
theorem idealVerify_complete_rom_T {ρ pfuel N QG QP fuel : ℕ} (hρ : validRate ρ)
    (hpf : pfuel ≤ 2 ^ 64) (gen : OracleComp HashSpec (Option HonestTree))
    (hQG : IsTotalQueryBound gen QG) (hgen : ValidGenT ρ pfuel N QP gen) (hfuel : N ≤ fuel) :
    Pr{let z ← completeExp ρ pfuel gen}[¬ CompleteOK fuel z] ≤ completeError (QG + QP) pfuel :=
  idealVerify_complete_rom hρ hpf gen hQG (validGen_of_T hρ hgen) hfuel

end
end LeanVM.E2E.Complete
