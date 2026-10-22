/-
  LeanVM.E2E.SanityDeployed

  The honest deployed sanity theorem (S1): the deployed honest aggregation at BLAKE2s is accepted
  by the deployed outer verifier, and by V_I with BLAKE2s up to an explicit BLAKE2s compression
  collision.
-/

module

public import LeanVM.E2E.SanityDeployed.Prover
public import LeanVM.E2E.Sanity

/-!
# S1: the deployed honest aggregation passes both verifiers

The deterministic link between V_I and the deployed system, with no heuristic hypothesis. For an
honest witness tree `T` valid at BLAKE2s, the deployed honest prover (`deployedProve ρ pfuel T`,
`SanityDeployed/Prover.lean`: the full verifier's honest proofs, Flock included, the deployed
batching's honest hints, executions from the guest's completeness at the deployed model) outputs a
root statement `s`, its proof `π` and the honest idealized proof `ip` (every node's full word, the
encoding of its stack, and the frames of its execution). Then (`sanity_deployed`):

* `s.claims = T.claims`;
* `Node.verifyAggregate guest s π`: the outer checks (the root's DA vector digests from `T`'s
  validity, the deferred claim holding by `deferDep`) and the deployed verifier
  (`runProof_prove`, `runI_leanVmProgram`);
* `idealVerify (m := Id) blakeId guest ip fuel s = true` for every `fuel ≥ T.size`, or a BLAKE2s
  compression collision (`CompressionCollision`: two rows of the compression function, neither a
  last block, with distinct inputs and equal outputs, which V_I's precheck rejects).

`sanity_deployed_of_tree` adds the prover's output (`deployedProve_isSome`): validity, the
deployed limits and budget, and the proofs of work found are its only hypotheses.

V_I here runs without a budget; `SanityDeployedBudget.lean` (`sanity_deployed_budget`) runs it as
the game does, with `budgetedQuery (viCost N)` on `N ≥ T.size` nodes, its count on this proof
bounded in `SanityDeployed/Count.lean`.

**V_I's side** goes through V_I's node step on the prover's entries (`nodeStep_dep`, the full
verifier's analogue of `Complete.nodeStep_honest`): the node's word is its stack's encoding, its
only candidate the stack (`blindCandidates_stackWord`), whose run is the execution, whose table
passes the check at BLAKE2s once the precheck holds (`Sanity.tableOKWith_run`), and whose children
decode at the node's frames (`DecodeHonest`). The idealized proof gives a node the word and frames
of one of its entries with the fewest nodes below (`bestDep`), so no event on node coincidences is
needed: the closure (`Sanity.idealVerify_of_steps`) steps a reached node to that entry's children,
and the entry's size bounds the fuel (`FuelBounds`).
-/

namespace LeanVM.E2E.SanityDeployed

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Node LeanVM.Guest
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd LeanVM.Arithmetization
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.Whir.Complete
open LeanVM.E2E.Complete LeanVM.E2E.Sanity

@[expose] public section

/-! ## The collision -/

/-- **A BLAKE2s compression collision**: two rows of the compression function (`blakeDeployed`:
the output cells are the compression of the input cells), neither the last block of its string,
with distinct inputs (message, chaining value, metadata) and equal outputs. -/
def CompressionCollision : Prop :=
  ∃ r₁ r₂ : BlakeRow, blakeDeployed.row r₁ ∧ blakeDeployed.row r₂ ∧ ¬ RowFinal r₁ ∧
    ¬ RowFinal r₂ ∧ r₁.out = r₂.out ∧ rowInput r₁ ≠ rowInput r₂

/-- **Without a compression collision, a deployed execution's rows pass the precheck.** -/
theorem precheck_of_noCollision {prog : Program} {input : PublicInput} {t : Trace prog}
    (hv : ValidExecution prog input t) (hc : ¬ CompressionCollision) :
    Precheck (t.blakeRows blakeFree) := by
  intro r₁ h₁ r₂ h₂ hf₁ hf₂ hout
  by_contra hne
  exact hc ⟨r₁, r₂, blakeRows_deployed hv r₁ h₁, blakeRows_deployed hv r₂ h₂, hf₁, hf₂, hout, hne⟩

/-! ## BLAKE2s, by name -/

/-- The honest seed at BLAKE2s is the deployed seed. -/
theorem seedOf_blake : seedOf blake2sBytes = Node.deployedSeed guest := by
  unfold seedOf Node.deployedSeed fiatShamirIv
  rfl

/-- A statement's digest at BLAKE2s is the deployed one. -/
theorem digestOf_blake (s : NodeStatement) :
    digestOf blake2sBytes s = Node.statementDigest (Node.deployedSeed guest) s := by
  unfold digestOf
  rw [seedOf_blake]
  exact statementDigestWith_id _ _

/-- The deployed verifier, from its compiled run from the deployed seed. -/
theorem verify_of_runProofDep {bc : List K} {pd : Digest} {π : Proof}
    (h : runProof (m := Id) blake2sBytes (leanVmProgram bc pd)
      (Id.run (seedWith (m := Id) blake2sBytes bc pd)) π = true) :
    Verifier.verify bc pd π = true := by
  unfold Verifier.verify Verifier.seed
  exact h

/-! ## V_I's step on a deployed node -/

/-- **V_I's step on a node of the deployed prover.** The node's proof is the full verifier's
honest proof of the stack `q` at admissible sizes and a valid rate, the idealized proof gives the
node the stack's word and names the frames `fr`, `q` satisfies the relation without Flock on the
node's input, its execution re-runs, passes the table check with `H`, and decodes the children `cs`
at `fr`. Then the step returns the children's nodes. -/
theorem nodeStep_dep (H : Bytes → Digest) {prog : Program} (seed : Digest) (ip : IdealProof)
    {s : Sizes} {ρ : ℕ} {q : Column (leanIsaμ prog s)} {input : PublicInput}
    (hs : s.Admissible prog) (hρ : validRate ρ) {sd : Digest} {fuel : ℕ} {π : Proof}
    (hπ : prove H (leanVmProgram (bytecodeWords prog) (publicDigest input))
      (Protocol.EndToEnd.Complete.leanVmProver prog s ρ q) sd fuel = some π)
    (pi : Digest) (hword : ip.word (pi, π) = some (PWord.full (stackWord (leanIsaμ prog s) q)))
    {fr : String → List E → Option ℕ} (hfr : ip.frames (pi, π) = fr) (cs : List Node.Child)
    (hm : M3HoldsBlind (leanIsaInstance Sound.F₀ prog s) (inputOf pi) q) {t : Trace prog}
    (hrun : candidateRun prog s q = some t)
    (htab : tableOKWith (m := Id) (fun x ↦ (pure (H x) : Id Digest)) (t.blakeRows blakeFree) = true)
    (hkids : (Guest.End.decodeAt (Guest.Value.tableSem (t.blakeRows blakeFree)) fr
      t.image).witness.children = cs) :
    nodeStep (m := Id) (fun x ↦ (pure (H x) : Id Digest)) prog seed ip (pi, π) =
      some (kidNodes H seed cs) := by
  obtain ⟨level, rest, hc, hann, hroot, hshape⟩ := nodeHead_prove_dep H hs hρ hπ
  have hadm := Protocol.EndToEnd.Complete.whirAdmissible prog hs hρ
  obtain ⟨hfold, -⟩ := Whir.Params.deployed_spec_hyps hadm hc
  have hW := hword
  obtain rfl := hfr
  have hshaped : WellShaped (2 ^ level.fold) (stackWord (leanIsaμ prog s) q) := by
    rw [hfold]; exact wellShaped_stackWord _ q
  unfold nodeStep
  have hw2 : (levelShape (leanIsaμ prog s) level (2 ^ level.fold)).2 = 2 ^ level.fold := rfl
  simp only [hann, sizesOf_verifierLayout hs, hroot, hshape, hW, ↓reduceIte, PWord.word_full,
    pTreeRootM_full, PWord.full_full, hw2, hshaped, not_true_eq_false, and_false]
  have hht : (levelShape (leanIsaμ prog s) level (2 ^ level.fold)).1 =
      stackHeight (leanIsaμ prog s) level := rfl
  simp only [hht, ne_eq]
  have hset := (blindCandidatesS_full prog s ρ (stackHeight (leanIsaμ prog s) level) pi
    (stackWord (leanIsaμ prog s) q)).trans (blindCandidates_stackWord hs hρ pi q)
  have hfin : (blindCandidatesS prog s ρ (stackHeight (leanIsaμ prog s) level) pi
      (PWord.full (stackWord (leanIsaμ prog s) q))).Finite := by
    rw [hset]; exact (Set.finite_singleton q).subset fun x hx ↦ hx.1
  have hlist : hfin.toFinset.toList = [q] := by
    have : hfin.toFinset = {q} := by
      ext x
      simp only [Set.Finite.mem_toFinset, hset, Set.mem_ofPred_eq, Finset.mem_singleton]
      exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hm⟩⟩
    rw [this, Finset.toList_singleton]
  rw [hlist]
  simp only [List.forIn_cons, List.forIn_nil, hrun, htab, hkids]
  rw [forIn_kids]
  show Id.run _ = _
  simp only [Id.run_bind, id_run_eq (treeRoot H _ _), ↓reduceIte, not_true_eq_false,
    List.nil_append]
  rfl

/-! ## The entries -/

variable (ρ pfuel : ℕ)

/-- **A deployed node entry**: its node's proof is the full verifier's honest proof of a stack at
admissible sizes, whose word is the entry's and which satisfies the leanISA relation with honest
padding on the node's input; its candidate run is a deployed execution, which decodes at the
entry's frames children whose nodes are the entry's children's nodes. -/
def EntryOK (e : DepEntry) : Prop :=
  ∃ (sz : Sizes) (q : Column (leanIsaμ guest sz)) (t : Trace guest) (cs : List Child),
    sz.Admissible guest ∧
    prove blake2sBytes (leanVmProgram End.bytecode (publicDigest (End.publicInputOf e.node.1)))
        (Protocol.EndToEnd.Complete.leanVmProver guest sz ρ q)
        (Id.run (seedWith blake2sBytes End.bytecode (publicDigest (End.publicInputOf e.node.1))))
        pfuel = some e.node.2 ∧
    e.word = stackWord (leanIsaμ guest sz) q ∧
    M3Honest (Protocol.EndToEnd.Complete.inst guest sz) (End.publicInputOf e.node.1) q ∧
    candidateRun guest sz q = some t ∧
    ValidExecution guest (End.publicInputOf e.node.1) t ∧
    (End.decodeAt (Value.tableSem (t.blakeRows blakeFree)) e.frames t.image).witness.children.map
      (fun c ↦ (c.statement, c.proof)) = cs.map (fun c ↦ (c.statement, c.proof)) ∧
    e.kids = kidNodes blake2sBytes (Node.deployedSeed guest) cs

/-- **The entries are closed**: every entry's children are nodes of entries, its size one more
than theirs. -/
def SubsOKDep (subs : List DepEntry) : Prop :=
  ∀ e ∈ subs, ∃ ks : List (E2E.Node × ℕ), e.kids = ks.map (·.1) ∧
    (∀ k ∈ ks, ∃ e' ∈ subs, e'.node = k.1 ∧ e'.size = k.2) ∧ e.size = 1 + (ks.map (·.2)).sum

/-- **What a deployed output satisfies**: its statement has the tree's claims, its size is the
tree's, its first entry is its own node's, every entry is a deployed node entry, and the entries
are closed. -/
def GoodDep (T : HonestTree) (o : DepOut) : Prop :=
  o.stmt.claims = T.claims ∧ o.size = T.size ∧
    (∃ e, o.subs.head? = some e ∧ e.node = nodeOfDep o ∧ e.size = o.size) ∧
    (∀ e ∈ o.subs, EntryOK ρ pfuel e) ∧ SubsOKDep o.subs

/-- A relation along two lists, weakened using the left elements' membership. -/
theorem forall₂_imp_left_dep {α β : Type} {R S : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → (∀ a ∈ l, ∀ b, R a b → S a b) →
      List.Forall₂ S l l'
  | _, _, .nil, _ => .nil
  | _, _, .cons hab h, hS =>
    .cons (hS _ List.mem_cons_self _ hab)
      (forall₂_imp_left_dep h fun a ha b hb ↦ hS a (List.mem_cons_of_mem _ ha) b hb)

/-- **Every deployed output is good.** -/
theorem deployedOut_good (T : HonestTree) :
    ∀ o, deployedOut ρ pfuel T = some o → GoodDep ρ pfuel T o := by
  induction T using HonestTree.induct' with
  | h claims xs ss ds kids ih =>
  intro o h
  rw [deployedOut_node, Option.bind_eq_some_iff] at h
  obtain ⟨kos, hkos, h⟩ := h
  have hF := forall₂_kidOutsDep ρ pfuel hkos
  obtain ⟨hd, e, π, -, hπ, rfl⟩ := deployedStep_spec ρ pfuel h
  have hG : List.Forall₂ (fun k ko ↦ GoodDep ρ pfuel k ko) kids kos :=
    forall₂_imp_left_dep hF fun k hk ko hko ↦ ih k hk ko hko
  have hmem : ∀ ko ∈ kos, ∃ k ∈ kids, GoodDep ρ pfuel k ko := fun ko hko ↦
    forall₂_mem_right hG ko hko
  have hsub : ∀ ko ∈ kos, ∀ p ∈ ko.subs, p ∈ (⟨(digestOf blake2sBytes ⟨claims, hd.2⟩, π),
      kos.map nodeOfDep, 1 + (kos.map DepOut.size).sum,
      stackWord (leanIsaμ guest e.sz) e.stack, e.fr⟩ : DepEntry) :: kos.flatMap DepOut.subs :=
    fun ko hko p hp ↦ List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨ko, hko, hp⟩)
  refine ⟨rfl, ?_, ⟨_, rfl, rfl, rfl⟩, ?_, ?_⟩
  · show 1 + (kos.map DepOut.size).sum = HonestTree.size (.node claims xs ss ds kids)
    rw [HonestTree.size]
    congr 1
    have hk : (kids.attach.map fun k ↦ k.1.size) = kids.map HonestTree.size := by
      conv_rhs => rw [← List.attach_map_subtype_val kids]
      rw [List.map_map]
      rfl
    rw [hk]
    exact (forall₂_sum (hG.imp fun k ko hk ↦ hk.2.1.symm)).symm
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · refine ⟨e.sz, e.stack, e.t, kos.map DepOut.child, e.adm, hπ, rfl, e.m3, e.run, e.valid,
        e.decode, ?_⟩
      simp only [kidNodes, List.map_map]
      rw [← seedOf_blake]
      rfl
    · obtain ⟨ko, hko, hp⟩ := List.mem_flatMap.mp hp
      obtain ⟨_, -, hk⟩ := hmem ko hko
      exact hk.2.2.2.1 p hp
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · refine ⟨kos.map fun ko ↦ (nodeOfDep ko, ko.size), by simp, ?_, by simp [Function.comp_def]⟩
      intro k hk
      obtain ⟨ko, hko, rfl⟩ := List.mem_map.mp hk
      obtain ⟨_, -, hk⟩ := hmem ko hko
      obtain ⟨e', he', e1, e2⟩ := hk.2.2.1
      exact ⟨e', hsub ko hko _ (List.mem_of_mem_head? he'), e1, e2⟩
    · obtain ⟨ko, hko, hp⟩ := List.mem_flatMap.mp hp
      obtain ⟨_, -, hk⟩ := hmem ko hko
      obtain ⟨ks, h1, h2, h3⟩ := hk.2.2.2.2 p hp
      exact ⟨ks, h1, fun k hk ↦ by
        obtain ⟨p', hp', e1, e2⟩ := h2 k hk
        exact ⟨p', hsub ko hko p' hp', e1, e2⟩, h3⟩

/-- **The head of an entry's proof**: its announced layout and rate, sizes, stack root and
commitment shape (`nodeHead_prove_dep`). -/
theorem head_of_entry (hρ : validRate ρ) {e : DepEntry} (he : EntryOK ρ pfuel e) :
    Nonempty (Head guest e.node.2) := by
  obtain ⟨sz, q, t, cs, hadm, hπ, -⟩ := he
  obtain ⟨level, rest, -, hann, hroot, hshape⟩ := nodeHead_prove_dep blake2sBytes hadm hρ hπ
  exact ⟨⟨verifierLayout guest sz, ρ, sz, _, (levelShape (leanIsaμ guest sz) level
    (2 ^ level.fold)).1, (levelShape (leanIsaμ guest sz) level (2 ^ level.fold)).2, hann,
    sizesOf_verifierLayout hadm, hroot, hshape.trans (congrArg some Prod.mk.eta.symm)⟩⟩

/-- **V_I steps a deployed entry to its children's nodes**, without a compression collision,
when the idealized proof gives the entry's node its word and frames. -/
theorem nodeStep_entry (hρ : validRate ρ) {e : DepEntry} (he : EntryOK ρ pfuel e)
    (hc : ¬ CompressionCollision) (ip : IdealProof)
    (hw : ip.word e.node = some (PWord.full e.word)) (hf : ip.frames e.node = e.frames) :
    nodeStep (m := Id) blakeId guest (Node.deployedSeed guest) ip e.node = some e.kids := by
  obtain ⟨sz, q, t, cs, hadm, hπ, hword, hm3, hrun, hv, hdec, hkids⟩ := he
  obtain ⟨⟨pi, π⟩, kids, size, word, frames⟩ := e
  simp only at hπ hword hm3 hrun hv hdec hkids hw hf ⊢
  subst hword hkids
  have hm : M3HoldsBlind (leanIsaInstance Sound.F₀ guest sz) (inputOf pi) q := by
    rw [inputOf_eq]; exact ⟨hm3.1.1, hm3.1.2.1, hm3.1.2.2.1, hm3.1.2.2.2.1⟩
  have h := nodeStep_dep blake2sBytes (Node.deployedSeed guest) ip hadm hρ hπ pi hw hf _ hm hrun
    (tableOKWith_run hv (precheck_of_noCollision hv hc)) rfl
  rw [h]
  exact congrArg some (kidNodes_congr blake2sBytes _ hdec)

/-! ## The idealized proof's lookups -/

open Classical in
/-- **The entry V_I is given** for a node with an entry: one, with fewest nodes below. -/
theorem bestDep_spec {subs : List DepEntry} {ν : E2E.Node} (h : ∃ e ∈ subs, e.node = ν) :
    ∃ b, bestDep subs ν = some b ∧ b ∈ subs ∧ b.node = ν ∧
      ∀ e ∈ subs, e.node = ν → b.size ≤ e.size := by
  have hex : ∃ n, ∃ e ∈ subs, e.node = ν ∧ e.size = n := by
    obtain ⟨e, he, hν⟩ := h
    exact ⟨_, e, he, hν, rfl⟩
  refine ⟨(Nat.find_spec hex).choose, by simp only [bestDep, hex, ↓reduceDIte], ?_⟩
  obtain ⟨hmem, hν, hsz⟩ := (Nat.find_spec hex).choose_spec
  refine ⟨hmem, hν, fun e he heν ↦ ?_⟩
  rw [hsz]
  exact Nat.find_min' hex ⟨e, he, heν, rfl⟩

/-- The idealized proof gives a node with an entry the word of its `bestDep` entry. -/
theorem idealOfDep_word {o : DepOut} {ν : E2E.Node} {b : DepEntry}
    (hb : bestDep o.subs ν = some b) (h : ∃ e ∈ o.subs, e.node = ν) :
    (idealOfDep o).word ν = some (PWord.full b.word) := by
  simp only [IdealProof.word, idealOfDep]
  cases hfind : List.find? _ (List.map _ o.subs) with
  | none =>
    obtain ⟨e, he, hν⟩ := h
    have := List.find?_eq_none.mp hfind _ (List.mem_map_of_mem (f := fun e : DepEntry ↦
      (e.node, PWord.full (((bestDep o.subs e.node).map (·.word)).getD e.word))) he)
    simp [hν] at this
  | some x =>
    have hx1 := List.find?_some hfind
    obtain ⟨e', -, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hfind)
    simp only [decide_eq_true_eq] at hx1
    simp only [Option.map_some, hx1, hb, Option.getD_some]

/-- The idealized proof gives a node the frames of its `bestDep` entry. -/
theorem idealOfDep_frames {o : DepOut} {ν : E2E.Node} {b : DepEntry}
    (hb : bestDep o.subs ν = some b) : (idealOfDep o).frames ν = b.frames := by
  simp only [idealOfDep, hb, Option.map_some, Option.getD_some]

/-! ## S1 -/

/-- **S1, the honest deployed sanity theorem.** For an honest witness tree `T` valid at BLAKE2s
and a valid rate, whenever the deployed honest prover outputs the root statement `s`, its proof
`π` and the honest idealized proof `ip` (`hout`, which includes every proof-of-work search
succeeding within `pfuel`): the statement has the tree's claims, the deployed outer verifier
accepts it (`Node.verifyAggregate`), and V_I with BLAKE2s accepts it at every fuel at least the
tree's size, unless a BLAKE2s compression collision occurs. -/
theorem sanity_deployed (T : HonestTree) (hρ : validRate ρ) (hv : T.Valid blake2sBytes)
    {s : NodeStatement} {π : Proof} {ip : IdealProof}
    (hout : deployedProve ρ pfuel T = some (s, π, ip))
    {fuel : ℕ} (hfuel : T.size ≤ fuel) :
    s.claims = T.claims ∧ Node.verifyAggregate guest s π ∧
      (idealVerify (m := Id) blakeId guest ip fuel s = true ∨ CompressionCollision) := by
  obtain ⟨o, ho, he⟩ := Option.map_eq_some_iff.mp hout
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  obtain ⟨hcl, hsize, ⟨r, hr, hrnode, hrsize⟩, hok, hsubs⟩ := deployedOut_good ρ pfuel T o ho
  have hrm := List.mem_of_mem_head? hr
  -- the deployed verifier
  have hroot := hok r hrm
  obtain ⟨sz, q, t, cs, hadm, hπ, -, hm3, -⟩ := hroot
  rw [hrnode] at hπ hm3
  have hacc := runProof_prove blake2sBytes _ _ _ pfuel
    (fun chal ↦ (Protocol.EndToEnd.Complete.runI_leanVmProgram hadm hρ hm3
      walkFaithful_blake2sFlockSpec chal).1)
    (fun chal ↦ (Protocol.EndToEnd.Complete.runI_leanVmProgram hadm hρ hm3
      walkFaithful_blake2sFlockSpec chal).2) hπ
  simp only [nodeOfDep] at hacc
  rw [End.publicDigest_publicInputOf, digestOf_blake] at hacc
  have hver : Verifier.verify (bytecodeWords guest)
      (Node.statementDigest (Node.deployedSeed guest) o.stmt) o.proof = true :=
    verify_of_runProofDep hacc
  have hholds : o.stmt.defer.Holds (bytecodeWords guest) := (deployedOut_child ρ pfuel hρ ho).1
  have hagg : Node.verifyAggregate guest o.stmt o.proof :=
    ⟨⟨fun c hc ↦ (hv.2 c (hcl ▸ hc)).trans (Da.vectorDigestOfWith_id c.1), hholds⟩, hver⟩
  refine ⟨hcl, hagg, ?_⟩
  by_cases hc : CompressionCollision
  · exact Or.inr hc
  refine Or.inl ?_
  -- V_I: every reached node has an entry, and steps to its `bestDep` entry's children
  have hstepG : ∀ ν, (∃ e ∈ o.subs, e.node = ν) → ∃ b, bestDep o.subs ν = some b ∧ b ∈ o.subs ∧
      b.node = ν ∧ (∀ e ∈ o.subs, e.node = ν → b.size ≤ e.size) ∧
      nodeStep (m := Id) blakeId guest (Node.deployedSeed guest) (idealOfDep o) ν =
        some b.kids := by
    intro ν hν
    obtain ⟨b, hb, hbm, hbν, hbmin⟩ := bestDep_spec hν
    refine ⟨b, hb, hbm, hbν, hbmin, ?_⟩
    subst hbν
    exact nodeStep_entry ρ pfuel hρ (hok b hbm) hc _ (idealOfDep_word hb hν) (idealOfDep_frames hb)
  have hrootν : rootNode guest o.stmt (idealOfDep o) = r.node := by
    rw [hrnode, nodeOfDep, digestOf_blake]
    rfl
  have hreach : ∀ ν, Reached guest (idealOfDep o) (rootNode guest o.stmt (idealOfDep o)) ν →
      ∃ e ∈ o.subs, e.node = ν := by
    intro ν hR
    induction hR with
    | root => exact ⟨r, hrm, hrootν.symm⟩
    | child _ hk hκ ih =>
      obtain ⟨b, -, hbm, -, -, hstep⟩ := hstepG _ ih
      rw [hstep, Option.some.injEq] at hk
      subst hk
      obtain ⟨ks, hks, hk', -⟩ := hsubs b hbm
      rw [hks] at hκ
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hκ
      obtain ⟨e', he', e1, -⟩ := hk' k hk
      exact ⟨e', he', e1⟩
  let sz : E2E.Node → ℕ := fun ν ↦ ((bestDep o.subs ν).map (·.size)).getD 0
  have hsz_le : ∀ e ∈ o.subs, sz e.node ≤ e.size := by
    intro e he
    obtain ⟨b, hb, -, -, hbmin⟩ := bestDep_spec ⟨e, he, rfl⟩
    simp only [sz, hb, Option.map_some, Option.getD_some]
    exact hbmin e he rfl
  refine idealVerify_of_steps hagg (fun ν hR _ ↦ ?_) ⟨sz, ?_, fun ν hR kids hk ↦ ?_⟩
  · obtain ⟨b, -, hbm, -, -, hstep⟩ := hstepG ν (hreach ν hR)
    refine ⟨b.kids, hstep, fun κ hκ ↦ ?_⟩
    obtain ⟨ks, hks, hk', -⟩ := hsubs b hbm
    rw [hks] at hκ
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hκ
    obtain ⟨e', he', e1, -⟩ := hk' k hk
    rw [← e1]
    exact head_of_entry ρ pfuel hρ (hok e' he')
  · rw [hrootν]
    calc sz r.node ≤ r.size := hsz_le r hrm
      _ = T.size := hrsize.trans hsize
      _ ≤ fuel := hfuel
  · obtain ⟨b, hb, hbm, hbν, -, hstep⟩ := hstepG ν (hreach ν hR)
    rw [hstep, Option.some.injEq] at hk
    subst hk
    obtain ⟨ks, hks, hk', hsum⟩ := hsubs b hbm
    have hszν : sz ν = b.size := by simp only [sz, hb, Option.map_some, Option.getD_some]
    rw [hszν, hks, hsum, List.map_map]
    have : (ks.map (sz ∘ (·.1))).sum ≤ (ks.map (·.2)).sum := by
      apply List.sum_le_sum
      intro k hk
      obtain ⟨e', he', e1, e2⟩ := hk' k hk
      simp only [Function.comp_apply, ← e1, ← e2]
      exact hsz_le e' he'
    omega

/-- **S1 from the tree's conditions**: for an honest witness tree valid at BLAKE2s, within the
deployed limits and budget at every node, whose proofs of work are found within `pfuel`, at a valid
rate, the deployed honest prover outputs, and its output passes both verifiers as in
`sanity_deployed`. -/
theorem sanity_deployed_of_tree (T : HonestTree) (hρ : validRate ρ) (hv : T.Valid blake2sBytes)
    (hlim : T.WithinLimitsDep ρ pfuel) (hpow : T.PowFoundDep ρ pfuel) {fuel : ℕ}
    (hfuel : T.size ≤ fuel) :
    ∃ s π ip, deployedProve ρ pfuel T = some (s, π, ip) ∧ s.claims = T.claims ∧
      Node.verifyAggregate guest s π ∧
      (idealVerify (m := Id) blakeId guest ip fuel s = true ∨ CompressionCollision) := by
  obtain ⟨s, π, ip, h⟩ := deployedProve_isSome ρ pfuel hρ T hv hlim hpow
  exact ⟨s, π, ip, h, sanity_deployed ρ pfuel T hρ hv h hfuel⟩

end
end LeanVM.E2E.SanityDeployed
