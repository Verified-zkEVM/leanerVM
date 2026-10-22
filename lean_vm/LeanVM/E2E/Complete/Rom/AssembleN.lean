/-
  LeanVM.E2E.Complete.Rom.AssembleN

  T6-det for the H-oblivious prover, without a good event on roots (decision E2E-8): V_I reads
  every node's word and frames from its smallest entry, and accepts.
-/

module

public import LeanVM.E2E.Complete.Rom.NonVacuityN

/-!
# T6-det without G3

`docs/roadmap/t6-prob.md` §1.5, §4.3. By decision E2E-8 V_I reads a node's word and frames by the
node `ν = (pi, π)`. Two entries of the honest output with one node share their proof, hence their
sizes, rate and stack root; the honest idealized proof (`idealOfN`) gives every node the word and
frames of its *representative*, an entry of the node of smallest subtree (`repOf`). Each entry
steps to its own children under any idealized proof giving its node its word and frames
(`EntryStep`, from `nodeStep_honest`), so V_I steps every node of the output to its
representative's children, entries of strictly smaller subtrees, and the closure accepts by the
representatives' sizes (`closure_accepts`). No hypothesis on roots: **`idealVerify_complete_N`**.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Node LeanVM.Guest
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd LeanVM.Protocol.Whir.Complete

@[expose] public section

/-! ## Representatives and the idealized proof -/

/-- An entry's subtree size. -/
abbrev EntryN.size (r : EntryN) : ℕ := r.2.2.2.2

open Classical in
/-- **The representative of a node**: an entry of the node whose subtree is smallest. -/
noncomputable def repOf (es : List EntryN) (ν : E2E.Node) : Option EntryN :=
  if h : ∃ n, ∃ r ∈ es, r.1 = ν ∧ r.size = n then some (Classical.choose (Nat.find_spec h))
  else none

/-- A node of the entries has a representative, an entry of the node of least size. -/
theorem repOf_spec {es : List EntryN} {e : EntryN} (he : e ∈ es) :
    ∃ r, repOf es e.1 = some r ∧ r ∈ es ∧ r.1 = e.1 ∧
      ∀ e' ∈ es, e'.1 = e.1 → r.size ≤ e'.size := by
  classical
  have hex : ∃ n, ∃ r ∈ es, r.1 = e.1 ∧ r.size = n := ⟨_, e, he, rfl, rfl⟩
  obtain ⟨hr, h1, h2⟩ := Classical.choose_spec (Nat.find_spec hex)
  refine ⟨_, by simp only [repOf, hex, ↓reduceDIte], hr, h1, fun e' he' h' ↦ ?_⟩
  rw [h2]
  exact Nat.find_min' hex ⟨e', he', h', rfl⟩

/-- **The honest idealized proof of an output** (E2E-8): its proof; every node's word and frames
its representative's. -/
noncomputable def idealOfN (o : HonestOutN) : IdealProof where
  proof := o.proof
  words := o.entries.map fun e ↦ (e.1, ((repOf o.entries e.1).map (·.2.1)).getD e.2.1)
  frames ν := ((repOf o.entries ν).map (·.2.2.1)).getD fun _ _ ↦ none

/-- **The idealized proof gives a node its representative's word and frames.** -/
theorem idealOfN_rep {o : HonestOutN} {e : EntryN} (he : e ∈ o.entries) :
    ∃ r, repOf o.entries e.1 = some r ∧ r ∈ o.entries ∧ r.1 = e.1 ∧
      (∀ e' ∈ o.entries, e'.1 = e.1 → r.size ≤ e'.size) ∧
      (idealOfN o).word e.1 = some r.2.1 ∧ (idealOfN o).frames e.1 = r.2.2.1 := by
  classical
  obtain ⟨r, hr, hrm, hr1, hmin⟩ := repOf_spec he
  refine ⟨r, hr, hrm, hr1, hmin, ?_, by simp only [idealOfN, hr, Option.map_some, Option.getD_some]⟩
  have hfind : ∃ e', (o.entries.map fun e ↦
      (e.1, ((repOf o.entries e.1).map (·.2.1)).getD e.2.1)).find? (fun p ↦ decide (p.1 = e.1)) =
        some e' := by
    rcases hf : (o.entries.map fun e ↦
        (e.1, ((repOf o.entries e.1).map (·.2.1)).getD e.2.1)).find?
          (fun p ↦ decide (p.1 = e.1)) with _ | e'
    · have := List.find?_eq_none.mp hf (e.1, ((repOf o.entries e.1).map (·.2.1)).getD e.2.1)
        (List.mem_map.mpr ⟨e, he, rfl⟩)
      simp at this
    · exact ⟨e', hf⟩
  obtain ⟨e', he'⟩ := hfind
  have hp := List.find?_some he'
  have hm := List.mem_of_find?_eq_some he'
  simp only [decide_eq_true_eq] at hp
  obtain ⟨e'', -, rfl⟩ := List.mem_map.mp hm
  simp only at hp
  simp only [IdealProof.word, idealOfN]
  convert congrArg (Option.map (·.2)) he' using 2
  simp only [Option.map_some, hp, hr, Option.getD_some]

/-! ## Every entry steps to its children -/

variable (H : Bytes → Digest) (ρ pfuel : ℕ)

/-- **An entry steps to its children** under every idealized proof giving its node its word and
frames. -/
def EntryStep (r : EntryN) : Prop :=
  ∀ ip : IdealProof, ip.word r.1 = some r.2.1 → ip.frames r.1 = r.2.2.1 →
    nodeStep (m := Id) (fun x ↦ (pure (H x) : Id Digest)) guest (seedOf H) ip r.1 =
      some r.2.2.2.1

/-- **The entries are closed**: every entry's children are nodes of entries, its size one more
than theirs. -/
def EntriesOK (es : List EntryN) : Prop :=
  ∀ r ∈ es, ∃ ks : List (E2E.Node × ℕ), r.2.2.2.1 = ks.map (·.1) ∧
    (∀ k ∈ ks, ∃ r' ∈ es, r'.1 = k.1 ∧ r'.size = k.2) ∧ r.size = 1 + (ks.map (·.2)).sum

/-- What an H-oblivious output satisfies. -/
def GoodOutN (T : HonestTree) (o : HonestOutN) : Prop :=
  o.stmt.claims = T.claims ∧ o.size = T.size ∧
    (∃ w fr ks, o.entries.head? = some (nodeOfOutN H o, w, fr, ks, o.size)) ∧
    (∀ r ∈ o.entries, EntryStep H r) ∧ EntriesOK o.entries

/-- **A node's own entry steps to its children.** -/
theorem entryStep_outOf (hρ : validRate ρ) {s : NodeStatement} {w : NodeWitness}
    {kos : List HonestOutN} (hw : w.children = kos.map HonestOutN.child) {o : HonestOutN}
    (h : proveNode H ρ pfuel s w kos = .ok o) : ∀ r ∈ o.entries.head?, EntryStep H r := by
  obtain ⟨e, π, c, -, hπ, -, rfl⟩ := proveNode_spec H ρ pfuel h
  intro r hr ip hword hfr
  obtain rfl : _ = r := Option.some.inj hr
  have hag := agrees_logOf H (nodeLog H s w)
  have hstep := nodeStep_honest H (seedOf H) ip (e.at hag).adm hρ hπ (digestOf H s) hword
    (fr := e.1.fr) hfr
    (Guest.End.decodeAt (Guest.Value.tableSem ((e.at hag).t.blakeRows blakeFree)) e.1.fr
      (e.at hag).t.image).witness.children
    fun _ ↦ ⟨(e.at hag).t, (e.at hag).run, tableOKWith_of_validB (e.at hag).valid, rfl⟩
  split at hstep
  swap
  · rename_i hm
    exact absurd (by rw [inputOf_eq]; exact (e.at hag).rel.1) hm
  show nodeStep (m := Id) (fun x ↦ (pure (H x) : Id Digest)) guest (seedOf H) ip (digestOf H s, π) =
    some (kos.map (nodeOfOutN H))
  rw [hstep]
  exact congrArg some ((kidNodes_congr H (seedOf H) (e.at hag).decode).trans (by
    rw [hw]; simp [kidNodes, Function.comp_def, nodeOfOutN, HonestOutN.child]
    exact fun _ _ ↦ rfl))

/-- **Every entry of an H-oblivious output steps to its children**, and the output's entries are
closed, its statement the tree's claims, its size the tree's, its first entry its own. -/
theorem honestOutN_good (hρ : validRate ρ) (T : HonestTree) :
    ∀ o : HonestOutN, honestOutN H ρ pfuel T = .ok o → GoodOutN H T o := by
  induction T using HonestTree.induct' with
  | h claims xs ss ds kids ih =>
  intro o h
  rw [honestOutN_node] at h
  cases hk : kidOutsN H ρ pfuel kids with
  | error f => rw [hk] at h; cases h
  | ok kos =>
  rw [hk] at h
  have hF := forall₂_of_mapM_except hk
  obtain ⟨hd, -, h⟩ := honestStepN_spec H ρ pfuel h
  have hstep := entryStep_outOf H ρ pfuel hρ rfl h
  obtain ⟨e, π, c, -, -, -, rfl⟩ := proveNode_spec H ρ pfuel h
  have hG : List.Forall₂ (fun k ko ↦ GoodOutN H k.1 ko) kids.attach kos :=
    forall₂_imp_mem hF fun k ko _ hk ↦ ih k.1 k.2 ko hk
  have hmem : ∀ ko ∈ kos, ∃ k : {x // x ∈ kids}, GoodOutN H k.1 ko := by
    intro ko hko
    obtain ⟨k, -, hk⟩ := forall₂_mem_right hG ko hko
    exact ⟨k, hk⟩
  have hsub : ∀ ko ∈ kos, ∀ r ∈ ko.entries, r ∈ (outOf H ⟨claims, hd.2⟩ c π e kos).entries :=
    fun ko hko r hr ↦ List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨ko, hko, hr⟩)
  refine ⟨rfl, ?_, ⟨_, _, _, rfl⟩, ?_, ?_⟩
  · show 1 + (kos.map HonestOutN.size).sum = HonestTree.size (.node claims xs ss ds kids)
    rw [HonestTree.size]
    congr 1
    exact (forall₂_sum (hG.imp fun k ko hk ↦ hk.2.1.symm)).symm
  · intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hstep _ rfl
    · obtain ⟨ko, hko, hr⟩ := List.mem_flatMap.mp hr
      obtain ⟨_, hk⟩ := hmem ko hko
      exact hk.2.2.2.1 r hr
  · intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · refine ⟨kos.map fun ko ↦ (nodeOfOutN H ko, ko.size), by simp, ?_, by
        simp [Function.comp_def]⟩
      intro k hk
      obtain ⟨ko, hko, rfl⟩ := List.mem_map.mp hk
      obtain ⟨_, hk⟩ := hmem ko hko
      obtain ⟨w', fr', ks', hks⟩ := hk.2.2.1
      exact ⟨_, hsub ko hko _ (List.mem_of_mem_head? hks), rfl, rfl⟩
    · obtain ⟨ko, hko, hr⟩ := List.mem_flatMap.mp hr
      obtain ⟨_, hk⟩ := hmem ko hko
      obtain ⟨ks, h1, h2, h3⟩ := hk.2.2.2.2 r hr
      exact ⟨ks, h1, fun k hk ↦ by
        obtain ⟨r', hr', e1, e2⟩ := h2 k hk
        exact ⟨r', hsub ko hko r' hr', e1, e2⟩, h3⟩

/-- The root's facts: V°'s honest proof and the deferred claim's bytecode part. -/
theorem honestOutN_root (hρ : validRate ρ) {T : HonestTree} {o : HonestOutN}
    (h : honestOutN H ρ pfuel T = .ok o) :
    Id.run (verifyBlindWith (m := Id) (fun x ↦ (pure (H x) : Id Digest)) End.bytecode
      (digestOf H o.stmt) o.proof) = true ∧ o.stmt.defer.BytecodeHolds End.bytecode := by
  cases T with
  | node claims xs ss ds kids =>
  rw [honestOutN_node] at h
  cases hk : kidOutsN H ρ pfuel kids with
  | error f => rw [hk] at h; cases h
  | ok kos =>
  rw [hk] at h
  obtain ⟨hd, hhd, h⟩ := honestStepN_spec H ρ pfuel h
  obtain ⟨e, π, c, -, hπ, -, rfl⟩ := proveNode_spec H ρ pfuel h
  have hag := agrees_logOf H
    (nodeLog H ⟨claims, hd.2⟩ ⟨kos.map HonestOutN.child, xs, ss, ds, hd.1⟩)
  set e' := e.at hag
  refine ⟨?_, (honestDefer_spec H (honestDefer_of_N H hhd)).1⟩
  have hrun := runProof_prove H _ _ _ pfuel
    (fun chal ↦ (Blind.runI_blindProgram e'.adm hρ e'.rel chal).1)
    (fun chal ↦ (Blind.runI_blindProgram e'.adm hρ e'.rel chal).2) hπ
  simp only [seedAt, End.publicDigest_publicInputOf] at hrun
  exact hrun

/-! ## T6-det without G3 -/

/-- **T6-det for the H-oblivious prover, with no good event on roots** (E2E-8): for every hash,
an honest tree whose root DA claims carry their vector digests, a valid rate and a fuel at least
the tree's size, if the prover outputs `o`, the statement has the tree's claims and V_I accepts
`idealOfN o`. -/
theorem idealVerify_complete_N (T : HonestTree) {fuel : ℕ} (hρ : validRate ρ) {o : HonestOutN}
    (hI : honestOutN H ρ pfuel T = .ok o) (hfuel : T.size ≤ fuel)
    (hda : ∀ c ∈ T.claims.da,
      Da.toBytes c.2 = Id.run (Da.vectorDigestOfWith (fun x ↦ (pure (H x) : Id Digest)) c.1)) :
    o.stmt.claims = T.claims ∧
      idealVerify (m := Id) (fun x ↦ (pure (H x) : Id Digest)) guest (idealOfN o) fuel o.stmt =
        true := by
  obtain ⟨hcl, hsize, ⟨w₀, fr₀, ks₀, hhead⟩, hsteps, hok⟩ := honestOutN_good H ρ pfuel hρ T o hI
  obtain ⟨hV, hbc⟩ := honestOutN_root H ρ pfuel hρ hI
  refine ⟨hcl, idealVerify_accepts H guest (idealOfN o) fuel o.stmt hV
    (outerChecksWith_true H guest o.stmt (by rw [hcl]; exact hda) hbc) ?_⟩
  classical
  let Good : E2E.Node → Prop := fun ν ↦ ∃ r ∈ o.entries, r.1 = ν
  let kidsOf : E2E.Node → List E2E.Node := fun ν ↦
    (nodeStep (m := Id) (fun x ↦ (pure (H x) : Id Digest)) guest (seedOf H) (idealOfN o) ν).getD []
  let sz : E2E.Node → ℕ := fun ν ↦ ((repOf o.entries ν).map EntryN.size).getD 0
  -- every node steps to its representative's children
  have hrep : ∀ e ∈ o.entries, ∃ r ∈ o.entries, r.1 = e.1 ∧ sz e.1 = r.size ∧
      (∀ e' ∈ o.entries, e'.1 = e.1 → r.size ≤ e'.size) ∧
      nodeStep (m := Id) (fun x ↦ (pure (H x) : Id Digest)) guest (seedOf H) (idealOfN o) e.1 =
        some r.2.2.2.1 := by
    intro e he
    obtain ⟨r, hr, hrm, hr1, hmin, hw, hf⟩ := idealOfN_rep he
    refine ⟨r, hrm, hr1, by simp only [sz, hr, Option.map_some, Option.getD_some], hmin, ?_⟩
    rw [← hr1] at hw hf ⊢
    exact hsteps r hrm _ hw hf
  have hmem_head : (nodeOfOutN H o, w₀, fr₀, ks₀, o.size) ∈ o.entries := List.mem_of_mem_head? hhead
  have hacc := closure_accepts H guest (seedOf H) (idealOfN o) Good kidsOf sz
    (fun ν ⟨e, he, hν⟩ ↦ by
      obtain ⟨r, -, -, -, -, hs⟩ := hrep e he
      subst hν
      simp only [kidsOf, hs, Option.getD_some])
    (fun ν ⟨e, he, hν⟩ κ hκ ↦ by
      obtain ⟨r, hrm, -, -, -, hs⟩ := hrep e he
      simp only [kidsOf, ← hν, hs, Option.getD_some] at hκ
      obtain ⟨ks, hks, hk', -⟩ := hok r hrm
      rw [hks] at hκ
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hκ
      obtain ⟨r', hr', e1, -⟩ := hk' k hk
      exact ⟨r', hr', e1⟩)
    (fun ν ⟨e, he, hν⟩ ↦ by
      obtain ⟨r, hrm, -, hsz, -, hs⟩ := hrep e he
      subst hν
      simp only [kidsOf, hs, Option.getD_some, hsz]
      obtain ⟨ks, hks, hk', hsum⟩ := hok r hrm
      rw [hks, hsum, List.map_map]
      have : ((ks.map (sz ∘ (·.1)))).sum ≤ (ks.map (·.2)).sum := by
        apply List.sum_le_sum
        intro k hk
        obtain ⟨r', hr', e1, e2⟩ := hk' k hk
        obtain ⟨r'', -, -, hsz', hmin', -⟩ := hrep r' hr'
        simp only [Function.comp_apply, ← e1, ← e2, hsz']
        exact hmin' r' hr' rfl
      omega)
    fuel [nodeOfOutN H o] [] (by
      intro ν hν
      rw [List.mem_singleton.mp hν]
      exact ⟨_, hmem_head, rfl⟩) (by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      obtain ⟨r, -, -, hsz, hmin, -⟩ := hrep _ hmem_head
      rw [hsz]
      exact (hmin _ hmem_head rfl).trans (hsize ▸ hfuel))
  exact hacc

end
end LeanVM.E2E.Complete
