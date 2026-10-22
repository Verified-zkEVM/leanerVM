/-
  LeanVM.E2E.Complete.Rom.ViCost

  V_I's query count on the honest idealized proof: at most `13,508` at the root and
  `179,719,581 ≈ 2^27.42` per node, for every hash.
-/

module

public import LeanVM.E2E.Complete.NodeCount
public import LeanVM.E2E.Complete.Rom.AssembleN
public import LeanVM.E2E.Complete.Rom.CompCount
public import LeanVM.E2E.Complete.Rom.CompBridge

/-!
# V_I's queries on an honest proof

The game runs V_I with a budget (`budgetedQuery`); completeness in the game needs the honest
proof's queries within it. For every hash `H`, a valid rate, and an honest tree `T` of the
shape `HonestTree.ShapeOK` at every node whose root has at most `16` DA claims, if the
H-oblivious prover outputs `o`, then V_I with `H` on `idealOfN o` makes at most

    viRootBound + fuel · viStepBound,   viRootBound = 13,508,   viStepBound = 179,719,581

queries (**`queryCount_honest_le`**), `viStepBound ≈ 2^27.42`. Per node (`EntryCost`, from
`count_nodeStep_honest`):

* the stack's Merkle tree, at most `2^27 − 1` (height at most `costHeight = 26`);
* the table check of the single candidate: one query per string with a standard chain among
  its rows, which are strings of the node's log (`chainInputs_subset`), whose length is at most
  the node's checks' count (`length_nodeLogWith_le`), at most `checksBound = 45,501,774` under
  the shape (`checksQueries_le`; the shapes of the children's claims and of the batching's hints
  are the prover's, `outShapedN_of_honestOutN`, `honestDeferN_shape`);
* the children's digests, five queries each, at most sixteen children.

The root adds the IV (`2`), the root's digest (`5`), V° (`leanVmQueryBound = 13,213`) and the
outer checks (`18` per DA claim, at most `16`). The closure makes at most `fuel` node steps.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Node LeanVM.Guest
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd LeanVM.Protocol.Compile.Rom
open LeanVM.E2E OracleComp OracleSpec

@[expose] public section

/-! ## The constants -/

/-- **V_I's queries per honest node**: the stack's tree, the table check, sixteen children's
digests. -/
def viStepBound : ℕ := 2 ^ (costHeight + 1) - 1 + (checksBound + 5 * 16)

/-- `viStepBound = 2^27 − 1 + 45,501,774 + 80 ≈ 2^27.42`. -/
theorem viStepBound_eq : viStepBound = 179719581 := by
  have h : checksBound = 45501774 := by decide
  unfold viStepBound
  rw [h]
  rfl

/-- **V_I's queries at the root**: the IV, the root's digest, V°, the outer checks of at most
sixteen DA claims. -/
def viRootBound : ℕ := 2 + 5 + leanVmQueryBound + 16 * 18

theorem viRootBound_eq : viRootBound = 13508 := by
  unfold viRootBound
  rw [leanVmQueryBound_eq]

/-- **V_I's budget per node**: a node's queries and the root's, `179,733,089 ≈ 2^27.42`. -/
def viNodeBound : ℕ := viStepBound + viRootBound

theorem viNodeBound_eq : viNodeBound = 179733089 := by
  rw [viNodeBound, viStepBound_eq, viRootBound_eq]

/-! ## The honest prover's shapes, at every hash -/

/-- **A run with a hash function is a reachable outcome** of the oracle computation. -/
theorem mem_support_simulateQ_id (H : Bytes → Digest) {α : Type} (oa : OracleComp HashSpec α) :
    Id.run (simulateQ (fun x ↦ (pure (H x) : Id Digest) : QueryImpl HashSpec Id) oa) ∈
      support oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx ih =>
    rw [simulateQ_query_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id]
    change Id.run (simulateQ (fun x ↦ (pure (H x) : Id Digest) : QueryImpl HashSpec Id)
      (mx (H t))) ∈ _
    exact (mem_support_bind_iff _ _ _).mpr ⟨H t, mem_support_query t (H t), ih (H t)⟩

variable (H : Bytes → Digest) (ρ pfuel : ℕ)

/-- **The H-oblivious prover's outputs are of the bytecode's shapes.** -/
theorem outShapedN_of_honestOutN {T : HonestTree} {o : HonestOutN}
    (h : honestOutN H ρ pfuel T = .ok o) : OutShapedN o := by
  have hm := mem_support_simulateQ_id H (honestProverComp ρ pfuel T)
  rw [honestProverComp_at, h] at hm
  exact outShapedN_of_mem_support ρ pfuel T hm

/-- **The honest batching's deferred claim and hints**: of the bytecode's shapes, with the honest
rounds. -/
theorem honestDeferN_shape {cs : List Child} {hd : BatchHints × DeferredClaim}
    (h : honestDeferN H cs = .ok hd) :
    hd.2.Shaped End.bytecode ∧ hd.1.bytecodeRounds.length ≤ Nat.log2 End.bytecode.length ∧
      hd.1.matrixRounds.length ≤ 2 * blake2sR1csLogSize := by
  have hm := mem_support_simulateQ_id H (honestDeferM queryH cs).run
  have hs : simulateQ (fun x ↦ (pure (H x) : Id Digest)) (honestDeferM queryH cs).run =
      honestDeferN H cs :=
    (simulateQ_honestDeferM (fun x ↦ (pure (H x) : Id Digest)) cs).trans (honestDeferM_id H cs)
  rw [hs, h] at hm
  exact honestDeferM_shape hm

/-! ## The node's log -/

/-- **The node's log has at most the node's checks' count of strings.** -/
theorem length_nodeLogWith_le (s0 : Digest) (pc pr : LeanDa.Digest) (bytecode : List K)
    (seed : Digest) (s : NodeStatement) (w : NodeWitness) :
    (nodeLogWith H s0 pc pr bytecode seed s w).length ≤ nodeChecksQueries s w := by
  have h1 := rel_nodeChecksWith (m := Counted) (n := LogM)
    (fun x a ↦ x.val = a.val ∧ x.count = a.log.length) (fun _ ↦ ⟨rfl, rfl⟩)
    (fun x y f g hxy hfg ↦ by
      obtain ⟨hv, hc⟩ := hxy
      obtain ⟨hv', hc'⟩ := hfg x.val
      refine ⟨?_, ?_⟩
      · show (f x.val).val = (g y.val).val
        rw [← hv]
        exact hv'
      · show x.count + (f x.val).count = (y.log ++ (g y.val).log).length
        rw [List.length_append, ← hv, hc, hc'])
    (countQuery H) (LogM.hash H) (fun _ ↦ ⟨rfl, rfl⟩) s0 pc pr bytecode seed s w
  have h2 := rel_nodeChecksWith (m := OracleComp HashSpec) (n := Counted)
    (fun x y ↦ simulateQ (fun x ↦ countQuery H x : QueryImpl HashSpec Counted) x = y)
    (fun a ↦ simulateQ_pure _ a) (simulateQ_countQuery_rel_bind H)
    queryH (countQuery H) (fun x ↦ simulateQ_queryH _ x) s0 pc pr bytecode seed s w
  have h3 := count_simulateQ_le H _ (isTotalQueryBound_nodeChecksWith s0 pc pr bytecode seed s w)
  rw [h2] at h3
  rw [← nodeChecksWith_log, ← h1.2]
  exact h3

/-! ## Every honest entry -/

/-- **An entry's step costs at most `viStepBound`** under every idealized proof giving its node
its word and frames. -/
def EntryCost (r : EntryN) : Prop :=
  ∀ ip : IdealProof, ip.word r.1 = some (PWord.full r.2.1) → ip.frames r.1 = r.2.2.1 →
    (nodeStep (countQuery H) guest (seedOf H) ip r.1).count ≤ viStepBound

/-- **A node's own entry costs at most `viStepBound`**, when its log has at most `checksBound`
strings and it has at most sixteen children. -/
theorem entryCost_outOf (hρ : validRate ρ) {s : NodeStatement} {w : NodeWitness}
    {kos : List HonestOutN} (hw : w.children = kos.map HonestOutN.child)
    (hD : (nodeLog H s w).length ≤ checksBound) (hK : kos.length ≤ 16) {o : HonestOutN}
    (h : proveNode H ρ pfuel s w kos = .ok o) : ∀ r ∈ o.entries.head?, EntryCost H r := by
  obtain ⟨e, π, c, -, hπ, -, rfl⟩ := proveNode_spec H ρ pfuel h
  intro r hr ip hword hfr
  obtain rfl : _ = r := Option.some.inj hr
  have hag := agrees_logOf H (nodeLog H s w)
  have hrows : ∀ b ∈ (e.at hag).t.blakeRows blakeFree, ChainRow (e.at hag).I H b := fun b hb ↦
    (chainSem_row.mp (blakeRows_of_validB chainSem_le_free (e.at hag).valid b hb)).2
  have hDe : (e.at hag).D = nodeLog H s w := by
    show e.1.D = _
    rw [e.2, strings_logOf]
  have hsub : chainInputs ((e.at hag).t.blakeRows blakeFree) ⊆ ↑(nodeLog H s w).toFinset := by
    intro x hx
    have := chainInputs_subset hrows hx
    simpa [hDe] using this
  have htab := (count_tableOKWith_le H _ _ hsub).trans
    ((List.toFinset_card_le _).trans hD)
  have hkids : (Guest.End.decodeAt (Guest.Value.tableSem ((e.at hag).t.blakeRows blakeFree))
      (e.at hag).fr (e.at hag).t.image).witness.children.length ≤ 16 := by
    have := congrArg List.length (e.at hag).decode
    simp only [List.length_map] at this
    rw [this, hw, List.length_map]
    exact hK
  have hc := count_nodeStep_honest H (seedOf H) ip (e.at hag).adm hρ hπ (digestOf H s) hword
    (fr := e.1.fr) hfr checksBound 16 fun _ ↦ ⟨(e.at hag).t, (e.at hag).run, htab, hkids⟩
  show (nodeStep (countQuery H) guest (seedOf H) ip (digestOf H s, π)).count ≤ viStepBound
  unfold viStepBound
  omega

/-- The children's outputs relate to the children. -/
theorem length_kidOutsN {kids : List HonestTree} {kos : List HonestOutN}
    (hk : kidOutsN H ρ pfuel kids = .ok kos) : kos.length = kids.length := by
  rw [← (forall₂_of_mapM_except hk).length_eq, List.length_attach]

/-- **Every entry of an H-oblivious output costs at most `viStepBound`**, for a tree of the shape
at every node. -/
theorem honestOutN_cost (hρ : validRate ρ) (T : HonestTree) :
    T.AllNodes HonestTree.ShapeOK →
      ∀ o : HonestOutN, honestOutN H ρ pfuel T = .ok o → ∀ r ∈ o.entries, EntryCost H r := by
  induction T using HonestTree.induct' with
  | h claims xs ss ds kids ih =>
  intro hsh o h
  rw [HonestTree.allNodes_node] at hsh
  rw [honestOutN_node] at h
  cases hk : kidOutsN H ρ pfuel kids with
  | error f => rw [hk] at h; cases h
  | ok kos =>
  rw [hk] at h
  have hF := forall₂_of_mapM_except hk
  have hlen := length_kidOutsN H ρ pfuel hk
  obtain ⟨hd, hhd, h⟩ := honestStepN_spec H ρ pfuel h
  have hshk : ∀ ko ∈ kos, OutShapedN ko := by
    intro ko hko
    obtain ⟨k, -, hk'⟩ := forall₂_mem_right hF ko hko
    exact outShapedN_of_honestOutN H ρ pfuel hk'
  obtain ⟨-, hb, hm⟩ := honestDeferN_shape H hhd
  have hD : (nodeLog H ⟨claims, hd.2⟩ ⟨kos.map HonestOutN.child, xs, ss, ds, hd.1⟩).length ≤
      checksBound := by
    refine (length_nodeLogWith_le H _ _ _ _ _ _ _).trans
      ((nodeChecksQueries_le_checksQueries hshk hb hm).trans ?_)
    rw [hlen]
    exact checksQueries_le hsh.1
  have hhead := entryCost_outOf H ρ pfuel hρ rfl hD (hlen ▸ hsh.1.1) h
  obtain ⟨e, π, c, -, -, -, rfl⟩ := proveNode_spec H ρ pfuel h
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact hhead _ rfl
  · obtain ⟨ko, hko, hr⟩ := List.mem_flatMap.mp hr
    obtain ⟨k, -, hk'⟩ := forall₂_mem_right hF ko hko
    exact ih k.1 k.2 (hsh.2 k.1 k.2) ko hk' r hr

/-! ## V_I's count on the honest proof -/

/-- The root's DA claims, within the limits: at most sixteen. -/
theorem claims_da_le_of_withinLimitsN {T : HonestTree} {o : HonestOutN}
    (hlim : T.WithinLimitsN H ρ pfuel) (h : honestOutN H ρ pfuel T = .ok o) :
    T.claims.da.length ≤ 16 := by
  obtain ⟨claims, xs, ss, ds, kids⟩ := T
  have hl := ((HonestTree.allNodes_node).mp hlim).1
  rw [honestOutN_node] at h
  cases hk : kidOutsN H ρ pfuel kids with
  | error f => rw [hk] at h; cases h
  | ok kos =>
  rw [hk] at h
  obtain ⟨hd, hhd, -⟩ := honestStepN_spec H ρ pfuel h
  exact (hl kos hk hd hhd).1.daRoots.1

/-- **V_I's queries on the honest idealized proof**: at most `viRootBound + fuel · viStepBound`,
for every hash, at a valid rate, for an honest tree of the shape at every node whose root has at
most sixteen DA claims. -/
theorem queryCount_honest_le (hρ : validRate ρ) {T : HonestTree} {o : HonestOutN}
    (hI : honestOutN H ρ pfuel T = .ok o) (hsh : T.AllNodes HonestTree.ShapeOK)
    (hda : T.claims.da.length ≤ 16) (fuel : ℕ) :
    queryCount H guest (idealOfN o) fuel o.stmt ≤ viRootBound + fuel * viStepBound := by
  obtain ⟨hcl, -, ⟨w₀, fr₀, ks₀, hhead⟩, hsteps, hok⟩ := honestOutN_good H ρ pfuel hρ T o hI
  have hcost := honestOutN_cost H ρ pfuel hρ T hsh o hI
  let Good : E2E.Node → Prop := fun ν ↦ ∃ r ∈ o.entries, r.1 = ν
  have hrep : ∀ e ∈ o.entries, ∃ r ∈ o.entries, r.1 = e.1 ∧
      (idealOfN o).word e.1 = some (PWord.full r.2.1) ∧ (idealOfN o).frames e.1 = r.2.2.1 := by
    intro e he
    obtain ⟨r, -, hrm, hr1, -, hw, hf⟩ := idealOfN_rep he
    exact ⟨r, hrm, hr1, hw, hf⟩
  have hle := queryCount_le_of H guest (idealOfN o) fuel o.stmt Good viStepBound
    (fun ν ⟨e, he, hν⟩ ↦ by
      obtain ⟨r, hrm, hr1, hw, hf⟩ := hrep e he
      subst hν
      rw [← hr1] at hw hf ⊢
      exact hcost r hrm _ hw hf)
    (fun ν ⟨e, he, hν⟩ ks hks κ hκ ↦ by
      obtain ⟨r, hrm, hr1, hw, hf⟩ := hrep e he
      subst hν
      rw [← hr1] at hw hf hks
      have hseed : Id.run (fiatShamirIvWith (fun x ↦ (pure (H x) : Id Digest))
          (bytecodeWords guest)) = seedOf H := rfl
      rw [hseed, hsteps r hrm _ hw hf] at hks
      obtain rfl := Option.some.inj hks
      obtain ⟨kk, hkk, hk', -⟩ := hok r hrm
      rw [hkk] at hκ
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hκ
      obtain ⟨r', hr', e1, -⟩ := hk' k hk
      exact ⟨r', hr', e1⟩)
    ⟨_, List.mem_of_mem_head? hhead, rfl⟩
  have hda' : o.stmt.claims.da.length * 18 ≤ 16 * 18 := by
    rw [hcl]
    exact Nat.mul_le_mul_right _ hda
  unfold viRootBound
  omega

/-- A tree has at least one node. -/
theorem HonestTree.one_le_size (T : HonestTree) : 1 ≤ T.size := by
  obtain ⟨c, xs, ss, ds, kids⟩ := T
  rw [HonestTree.size]
  omega

/-- **V_I's queries on the honest proof of a tree of at most `N` nodes, run on `N` nodes**: at
most `N · viNodeBound`. -/
theorem queryCount_honest_le_mul (hρ : validRate ρ) {T : HonestTree} {o : HonestOutN} {N : ℕ}
    (hI : honestOutN H ρ pfuel T = .ok o) (hsh : T.AllNodes HonestTree.ShapeOK)
    (hlim : T.WithinLimitsN H ρ pfuel) (hN : T.size ≤ N) :
    queryCount H guest (idealOfN o) N o.stmt ≤ N * viNodeBound := by
  have h := queryCount_honest_le H ρ pfuel hρ hI hsh (claims_da_le_of_withinLimitsN H ρ pfuel hlim hI) N
  have h1 : 1 ≤ N := (HonestTree.one_le_size T).trans hN
  have h2 : viRootBound ≤ N * viRootBound := Nat.le_mul_of_pos_left _ h1
  rw [viNodeBound, Nat.mul_add]
  omega

end
end LeanVM.E2E.Complete
