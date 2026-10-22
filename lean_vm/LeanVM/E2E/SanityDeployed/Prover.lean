/-
  LeanVM.E2E.SanityDeployed.Prover

  The deployed honest prover at BLAKE2s: every node's deferred claim with the deployed batching's
  honest hints, an execution of the guest from its completeness, the full verifier's honest proof
  (Flock included) and true fresh claims; and that it outputs on a valid tree within the limits
  whose proofs of work are found.
-/

module

public import LeanVM.E2E.SanityDeployed.Proof
public import LeanVM.E2E.SanityDeployed.Hints
public import LeanVM.E2E.Complete.Tree
public import LeanVM.E2E.Complete.DecodeFinal
public import LeanVM.Arithmetization.CompletenessB.Count

/-!
# The deployed honest prover

T6-det's honest prover (`Complete.honestOut`) proves each node for V°: its proof follows the
Flock-blind program (`honestStrategyBlind`), and its deferred claims carry unchecked matrix values
(`leafDefer`, `honestHints`). The deployed outer verifier (`Node.verifyAggregate`) runs the full
verifier and checks the root's deferred claim in full, so this module builds the prover the
deployed system runs, at BLAKE2s (`deployedOut ρ pfuel`), bottom up by a node step
(`deployedStep`) on the children's outputs:

1. the children (`Child`: statement, fresh claims, proof);
2. the deferred claim and hints (`deferDep`): at a leaf `leafDeferDep` (the zero points and the
   polynomials' true values there), at an inner node the deployed batching's honest hints
   (`honestHintsDep`), the claim kept if it holds;
3. the node's execution (`NodeExecDep`, a classical choice; `nodeExecDep_nonempty` shows one
   exists): an execution of the guest valid under the deployed semantics on the statement's digest,
   frames at which V_I's decoder reads its children back (`DecodeHonest`, from
   `guestCompleteModel` at `CompModel.deployed`), and an admissible witness representing it
   (`exists_admissible_witness`), its committed size within the cap; the stack is the witness's
   (`stackOf`);
4. the full verifier's honest proof of the stack (`leanVmProver`, `prove`, `none` when a
   proof-of-work search exhausts `pfuel`);
5. fresh claims for the parent (`freshDep`): true claims with which the deferring verifier accepts
   the proof, its query steps agreeing in the guest's caps (`exists_deferred_dep`);
6. the node entries (`DepEntry`): the node, its children's nodes, its subtree's size, its stack's
   word and its frames, for every node of the subtree.

`deployedOut_isSome`: on a tree valid at BLAKE2s (`HonestTree.Valid blake2sBytes`), within the
deployed limits and budget at every node (`WithinLimitsDep`), whose proofs of work are found
(`PowFoundDep`), at a valid rate, the prover outputs. No other event: the batching's matrix
weights may vanish (its final check is the definition of the batched polynomial).
-/

namespace LeanVM.E2E.SanityDeployed

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Node LeanVM.Guest
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd LeanVM.Arithmetization
open LeanVM.E2E.Complete
open Air.Flat (EnsembleWitness)
open LeanVM.Protocol.Whir.Complete (stackWord)

@[expose] public section

/-! ## The deferred claim -/

open Classical in
/-- **The deployed deferred claim and hints**: at a leaf `leafDeferDep`; at an inner node the
deployed honest hints from the baked start and the claim the batching of the children's claims
defers with them, if it accepts and the claim holds. -/
noncomputable def deferDep (cs : List Child) : Option (BatchHints × DeferredClaim) :=
  if cs = [] then some (noHints, leafDeferDep) else
  match childClaimsWith (fun x ↦ some (blake2sBytes x)) (seedOf blake2sBytes) cs with
  | none => none
  | some ccs =>
    match batchWith (fun x ↦ some (blake2sBytes x)) B1.Main.aggSeedD ccs
        (honestHintsDep blake2sBytes B1.Main.aggSeedD End.bytecode ccs) with
    | some (some d) =>
      if d.Holds End.bytecode then
        some (honestHintsDep blake2sBytes B1.Main.aggSeedD End.bytecode ccs, d)
      else none
    | _ => none

/-- **What the deployed deferred claim is**: it holds; at a leaf it is `leafDeferDep` without
hints; at an inner node the batching of the children's claims accepts the hints with it. -/
theorem deferDep_spec {cs : List Child} {hd : BatchHints × DeferredClaim}
    (h : deferDep cs = some hd) :
    hd.2.Holds End.bytecode ∧ (cs = [] → hd = (noHints, leafDeferDep)) ∧
      (cs ≠ [] → ∃ ccs, childClaimsWith (fun x ↦ some (blake2sBytes x)) (seedOf blake2sBytes) cs =
        some ccs ∧ batchWith (fun x ↦ some (blake2sBytes x)) B1.Main.aggSeedD ccs hd.1 =
          some (some hd.2)) := by
  unfold deferDep at h
  split at h
  · rename_i h0
    cases h
    exact ⟨leafDeferDep_holds, fun _ ↦ rfl, fun h ↦ absurd h0 h⟩
  · rename_i h0
    split at h
    · exact absurd h (by simp)
    · rename_i ccs hccs
      split at h
      · rename_i d hd
        split at h
        · rename_i hb
          have e := (Option.some.inj h).symm
          subst e
          exact ⟨hb, fun h ↦ absurd h h0, fun _ ↦ ⟨ccs, hccs, hd⟩⟩
        · exact absurd h (by simp)
      · exact absurd h (by simp)

/-- **The deployed deferred claim exists** for children whose claims are true. -/
theorem deferDep_some {cs : List Child}
    (hkids : ∀ c ∈ cs,
      ChildTrue End.bytecode ⟨digestOf blake2sBytes c.statement, c.fresh, c.statement.defer⟩) :
    ∃ hd, deferDep cs = some hd := by
  by_cases hk : cs = []
  · exact ⟨(noHints, leafDeferDep), by simp only [deferDep, hk, ↓reduceIte]⟩
  · have hccs := childClaimsWith_someH blake2sBytes cs
    set ccs := cs.map fun c ↦
      (⟨digestOf blake2sBytes c.statement, c.fresh, c.statement.defer⟩ : ChildClaims) with hccs_def
    have hcs : ∀ c ∈ ccs, ChildTrue End.bytecode c := by
      intro c hc
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
      exact hkids c' hc'
    obtain ⟨d, hbatch, hholds⟩ := batchWith_honestHintsDep blake2sBytes (s0 := B1.Main.aggSeedD)
      two_pow_log2_bytecode.symm hcs
    refine ⟨(honestHintsDep blake2sBytes B1.Main.aggSeedD End.bytecode ccs, d), ?_⟩
    unfold deferDep
    simp only [hk, ↓reduceIte, hccs]
    rw [show batchWith (fun x ↦ some (blake2sBytes x)) B1.Main.aggSeedD ccs
      (honestHintsDep blake2sBytes B1.Main.aggSeedD End.bytecode ccs) = some (some d) from hbatch]
    simp only [hholds, ↓reduceIte]

/-! ## The node's execution -/

/-- **A node's execution, deployed**: an execution of the guest valid under the deployed
semantics on the statement digest's input, of committed size within the deployed cap, frames at
which V_I's decoder reads back the witness's children, and an admissible witness of leanISA's
constraint system representing it. -/
structure NodeExecDep (pi : Digest) (w : NodeWitness) where
  /-- The execution. -/
  t : Trace guest
  /-- The decoder's frames. -/
  fr : Frames
  /-- The sizes. -/
  sz : Sizes
  /-- The witness. -/
  wit : EnsembleWitness (leanIsaEnsemble guest)
  /-- The execution is valid. -/
  valid : ValidExecution guest (End.publicInputOf pi) t
  /-- The children decode back. -/
  decode : DecodeHonest fr t w
  /-- The witness satisfies the constraint system. -/
  sat : SatisfiedBy guest (End.publicInputOf pi) wit
  /-- Its sizes. -/
  sizes : Sizes.ofWitness wit = some sz
  /-- They are admissible. -/
  adm : sz.Admissible guest
  /-- It represents the execution. -/
  rep : AssignmentRepresents wit t
  /-- The execution's committed size is within the deployed cap. -/
  small : t.committedSize ≤ 2 ^ maxMu

/-- The stack of a node's execution: its witness's (`stackOf`), the BLAKE2s Flock region
generated. -/
noncomputable def NodeExecDep.stack {pi : Digest} {w : NodeWitness} (e : NodeExecDep pi w) :
    Column (leanIsaμ guest e.sz) :=
  stackOf Blake2sFlock.blake2sFlockSpec guest e.sz e.wit

/-- The stack satisfies the leanISA relation with honest padding. -/
theorem NodeExecDep.m3 {pi : Digest} {w : NodeWitness} (e : NodeExecDep pi w) :
    M3Honest (Protocol.EndToEnd.Complete.inst guest e.sz) (End.publicInputOf pi) e.stack :=
  m3Honest_stackOf (F := Blake2sFlock.blake2sFlockSpec) e.sat e.sizes padLimbs_compress

/-- **V_I's candidate run of the stack is the execution.** -/
theorem NodeExecDep.run {pi : Digest} {w : NodeWitness} (e : NodeExecDep pi w) :
    candidateRun guest e.sz e.stack = some e.t := by
  have himg := (witnessOf_stackOf (F := Sound.F₀) e.sat e.sizes).2.2.2.2
  have hsig : imageOf e.wit.data = ⟨e.t.κ, e.t.image⟩ := by
    have hrep := e.rep
    obtain ⟨hκ, hi, -⟩ := hrep
    revert hκ hi
    generalize imageOf e.wit.data = p
    obtain ⟨κ, img⟩ := p
    intro hκ hi
    simp only at hκ hi
    subst hκ
    exact image_sigma_eq rfl _ _ fun i ↦ hi i i.isLt
  unfold candidateRun NodeExecDep.stack
  rw [himg, hsig]
  exact haltingRunB_of_validB (S := blakeDeployed) (fun _ hb ↦ canonicalCells_of_compressCells hb)
    ((validExecutionB_deployed _ _ _).mpr e.valid)

/-- **A node has a deployed execution**, from the guest's completeness at the deployed model
(`guestCompleteModel` at `CompModel.deployed`, with its frames) and an admissible witness of it
(`exists_admissible_witness`). -/
theorem nodeExecDep_nonempty {s : NodeStatement} {w : NodeWitness}
    (hrel : NodeRelWith (fun x ↦ some (blake2sBytes x)) B1.Main.aggSeedD B1.Main.daPadCell
      B1.Main.daPadRow End.bytecode (seedOf blake2sBytes) s w) (hlim : End.Limits s w)
    (hcaps : CapsAgreeWith blake2sBytes (seedOf blake2sBytes) w)
    (hbud : B2C.b2cBudget'.size (End.work s w) ≤ 2 ^ 28) :
    Nonempty (NodeExecDep (digestOf blake2sBytes s) w) := by
  obtain ⟨t, fr, hvB, hsz, hdec⟩ := guestCompleteModel CompModel.deployed blake2sBytes
    (fun _ _ h ↦ (Option.some.inj h).symm) (seedOf blake2sBytes) s w (digestOf blake2sBytes s)
    (statementDigestWith_someH blake2sBytes s) hrel hlim hcaps hbud
  have hv : ValidExecution guest (End.publicInputOf (digestOf blake2sBytes s)) t :=
    (validExecutionB_deployed _ _ t).mp hvB
  have hsize : t.committedSize ≤ 2 ^ maxMu := by
    rw [← committedSizeB_deployed]
    exact hsz
  obtain ⟨wit, sz, hw, hrep, hs, hadm⟩ :=
    Protocol.EndToEnd.Complete.exists_admissible_witness hv hsize
  exact ⟨⟨t, fr, sz, wit, hv, hdec, hw, hs, hadm, hrep, hsize⟩⟩

/-! ## The prover -/

/-- **A node entry**: the node, its children's nodes, its subtree's number of nodes, its stack's
word and the frames its execution's children decode at. -/
structure DepEntry where
  /-- The node: the statement's digest and the proof. -/
  node : E2E.Node
  /-- The children's nodes. -/
  kids : List E2E.Node
  /-- The subtree's number of nodes. -/
  size : ℕ
  /-- The stack's word. -/
  word : Word
  /-- The frames. -/
  frames : Frames

/-- **What the deployed prover outputs for a subtree**: the root's statement, fresh claims and
proof, the subtree's number of nodes, and the entries of its nodes, the root's first. -/
structure DepOut where
  /-- The statement. -/
  stmt : NodeStatement
  /-- The fresh claims of its proof. -/
  fresh : FixedClaims
  /-- Its proof. -/
  proof : Proof
  /-- The number of nodes. -/
  size : ℕ
  /-- The entries, the root's first. -/
  subs : List DepEntry

/-- The child of an output. -/
def DepOut.child (o : DepOut) : Child := ⟨o.stmt, o.fresh, o.proof⟩

/-- The node of an output: its statement's digest and its proof. -/
noncomputable def nodeOfDep (o : DepOut) : E2E.Node := (digestOf blake2sBytes o.stmt, o.proof)

open Classical in
/-- **The fresh claims of a deployed proof**: true claims with which the deferring verifier
accepts it, its query steps agreeing in the guest's caps, if there are any. -/
noncomputable def freshDep (pi : Digest) (π : Proof) : FixedClaims :=
  if h : ∃ c : FixedClaims, c.Holds End.bytecode ∧
      Id.run (verifyDeferredWith (m := Id) blake2sBytes End.bytecode (seedOf blake2sBytes) pi c π) =
        true ∧
      ∀ b ∈ queriesOfWith blake2sBytes (deferredProgram c End.bytecode pi)
        ⟨blake2sBytes (digestBytes (seedOf blake2sBytes) ++ digestBytes pi), π.stream, π.openings,
          []⟩, BatchAgreesWith blake2sBytes b.1 b.2
  then h.choose else ⟨[], 0, 0, 0, [], [], [], 0⟩

/-- The fresh claims meet their specification when some claims do. -/
theorem freshDep_spec {pi : Digest} {π : Proof}
    (hex : ∃ c : FixedClaims, c.Holds End.bytecode ∧
      Id.run (verifyDeferredWith (m := Id) blake2sBytes End.bytecode (seedOf blake2sBytes) pi c π) =
        true ∧
      ∀ b ∈ queriesOfWith blake2sBytes (deferredProgram c End.bytecode pi)
        ⟨blake2sBytes (digestBytes (seedOf blake2sBytes) ++ digestBytes pi), π.stream, π.openings,
          []⟩, BatchAgreesWith blake2sBytes b.1 b.2) :
    (freshDep pi π).Holds End.bytecode ∧
      Id.run (verifyDeferredWith (m := Id) blake2sBytes End.bytecode (seedOf blake2sBytes) pi
        (freshDep pi π) π) = true ∧
      ∀ b ∈ queriesOfWith blake2sBytes (deferredProgram (freshDep pi π) End.bytecode pi)
        ⟨blake2sBytes (digestBytes (seedOf blake2sBytes) ++ digestBytes pi), π.stream, π.openings,
          []⟩, BatchAgreesWith blake2sBytes b.1 b.2 := by
  unfold freshDep
  split
  · rename_i h
    exact h.choose_spec
  · exact absurd hex ‹_›

open Classical in
/-- **The deployed prover's node step**, from the children's outputs. -/
noncomputable def deployedStep (ρ pfuel : ℕ) (claims : Claims)
    (xs : List (Holder LeanXmss.Signature)) (ss : List (Holder Sphincs.Signature))
    (ds : List (Holder Da.Witness)) (kos : List DepOut) : Option DepOut := do
  let cs := kos.map DepOut.child
  let hd ← deferDep cs
  let s : NodeStatement := ⟨claims, hd.2⟩
  let w : NodeWitness := ⟨cs, xs, ss, ds, hd.1⟩
  let pi := digestOf blake2sBytes s
  if h : Nonempty (NodeExecDep pi w) then
    let e := Classical.choice h
    let π ← prove blake2sBytes (leanVmProgram End.bytecode (publicDigest (End.publicInputOf pi)))
      (Protocol.EndToEnd.Complete.leanVmProver guest e.sz ρ e.stack)
      (Id.run (seedWith blake2sBytes End.bytecode (publicDigest (End.publicInputOf pi)))) pfuel
    some ⟨s, freshDep pi π, π, 1 + (kos.map DepOut.size).sum,
      ⟨(pi, π), kos.map nodeOfDep, 1 + (kos.map DepOut.size).sum,
        stackWord (leanIsaμ guest e.sz) e.stack, e.fr⟩ :: kos.flatMap DepOut.subs⟩
  else none

/-- **The deployed prover on a subtree**, at BLAKE2s. -/
noncomputable def deployedOut (ρ pfuel : ℕ) : HonestTree → Option DepOut
  | .node claims xs ss ds kids => do
    let kos ← kids.attach.mapM fun k ↦ deployedOut ρ pfuel k.1
    deployedStep ρ pfuel claims xs ss ds kos
termination_by T => sizeOf T
decreasing_by
  have := List.sizeOf_lt_of_mem k.2
  simp_wf
  omega

/-- The children's outputs. -/
noncomputable def kidOutsDep (ρ pfuel : ℕ) (kids : List HonestTree) : Option (List DepOut) :=
  kids.attach.mapM fun k ↦ deployedOut ρ pfuel k.1

open Classical in
/-- **The entry V_I is given for a node**: of the entries with that node, one of the fewest
nodes in its subtree. -/
noncomputable def bestDep (subs : List DepEntry) (ν : E2E.Node) : Option DepEntry :=
  if h : ∃ n, ∃ e ∈ subs, e.node = ν ∧ e.size = n then some (Nat.find_spec h).choose else none

/-- **The deployed idealized proof of an output**: the root's proof, every node's word (full)
and frames, those of its entry `bestDep`. -/
noncomputable def idealOfDep (o : DepOut) : IdealProof where
  proof := o.proof
  words := o.subs.map fun e ↦
    (e.node, PWord.full (((bestDep o.subs e.node).map (·.word)).getD e.word))
  frames ν := ((bestDep o.subs ν).map (·.frames)).getD fun _ _ ↦ none

/-- **The deployed prover**: the root statement, its proof and the idealized proof. -/
noncomputable def deployedProve (ρ pfuel : ℕ) (T : HonestTree) :
    Option (NodeStatement × Proof × IdealProof) :=
  (deployedOut ρ pfuel T).map fun o ↦ (o.stmt, o.proof, idealOfDep o)

/-! ## What the prover outputs -/

variable (ρ pfuel : ℕ)

/-- The prover on a node. -/
theorem deployedOut_node {c : Claims} {xs : List (Holder LeanXmss.Signature)}
    {ss : List (Holder Sphincs.Signature)} {ds : List (Holder Da.Witness)}
    {kids : List HonestTree} :
    deployedOut ρ pfuel (.node c xs ss ds kids) =
      (kidOutsDep ρ pfuel kids).bind (deployedStep ρ pfuel c xs ss ds) := by
  rw [deployedOut]
  rfl

/-- **What the node step outputs**: the deferred claim and hints, the node's execution, the
deployed proof, and the output built from them. -/
theorem deployedStep_spec {claims : Claims} {xs : List (Holder LeanXmss.Signature)}
    {ss : List (Holder Sphincs.Signature)} {ds : List (Holder Da.Witness)} {kos : List DepOut}
    {o : DepOut} (h : deployedStep ρ pfuel claims xs ss ds kos = some o) :
    ∃ (hd : BatchHints × DeferredClaim)
      (e : NodeExecDep (digestOf blake2sBytes ⟨claims, hd.2⟩)
        ⟨kos.map DepOut.child, xs, ss, ds, hd.1⟩) (π : Proof),
      deferDep (kos.map DepOut.child) = some hd ∧
      prove blake2sBytes (leanVmProgram End.bytecode
          (publicDigest (End.publicInputOf (digestOf blake2sBytes ⟨claims, hd.2⟩))))
        (Protocol.EndToEnd.Complete.leanVmProver guest e.sz ρ e.stack)
        (Id.run (seedWith blake2sBytes End.bytecode
          (publicDigest (End.publicInputOf (digestOf blake2sBytes ⟨claims, hd.2⟩))))) pfuel =
          some π ∧
      o = ⟨⟨claims, hd.2⟩, freshDep (digestOf blake2sBytes ⟨claims, hd.2⟩) π, π,
        1 + (kos.map DepOut.size).sum,
        ⟨(digestOf blake2sBytes ⟨claims, hd.2⟩, π), kos.map nodeOfDep,
          1 + (kos.map DepOut.size).sum, stackWord (leanIsaμ guest e.sz) e.stack, e.fr⟩ ::
          kos.flatMap DepOut.subs⟩ := by
  unfold deployedStep at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨hd, hhd, h⟩ := h
  split at h
  · rename_i hne
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨π, hπ, h⟩ := h
    exact ⟨hd, Classical.choice hne, π, hhd, hπ, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- The children's outputs, child by child. -/
theorem forall₂_kidOutsDep {kids : List HonestTree} {kos : List DepOut}
    (h : kidOutsDep ρ pfuel kids = some kos) :
    List.Forall₂ (fun k o ↦ deployedOut ρ pfuel k = some o) kids kos := by
  have h2 := (List.forall₂_map_left_iff (f := Subtype.val)
    (R := fun k o ↦ deployedOut ρ pfuel k = some o)).mpr (forall₂_of_mapM h)
  rwa [List.attach_map_subtype_val] at h2

/-- **The output's statement makes the tree's claims.** -/
theorem deployedOut_claims {T : HonestTree} {o : DepOut} (h : deployedOut ρ pfuel T = some o) :
    o.stmt.claims = T.claims := by
  cases T with
  | node c xs ss ds kids =>
  rw [deployedOut_node, Option.bind_eq_some_iff] at h
  obtain ⟨kos, -, h⟩ := h
  obtain ⟨hd, e, π, -, -, rfl⟩ := deployedStep_spec ρ pfuel h
  rfl

/-- The children's outputs make the subtrees' claims. -/
theorem kidOutsDep_claims {kids : List HonestTree} {kos : List DepOut}
    (h : kidOutsDep ρ pfuel kids = some kos) :
    (kos.map DepOut.child).map (·.statement.claims) =
      (kids.map (claimChild ·.claims)).map (·.statement.claims) := by
  have h2 := forall₂_kidOutsDep ρ pfuel h
  clear h
  simp only [List.map_map]
  induction h2 with
  | nil => rfl
  | cons hab _ ih =>
    simp only [List.map_cons, Function.comp_apply, ih]
    rw [show (DepOut.child _).statement.claims = _ from deployedOut_claims ρ pfuel hab]
    rfl

/-- The deferring verifier's run at a hash `H`, from the compiled verifier's run from the
deferring seed (stated at any `H`, so that `blake2sBytes` is never evaluated). -/
theorem verifyDeferredWith_of_runProofDep (H : Bytes → Digest) {pd : Digest} {c : FixedClaims}
    {π : Proof}
    (h : runProof (m := Id) H (deferredProgram c End.bytecode pd)
      (Id.run (seedWith (m := Id) H End.bytecode pd)) π = true) :
    Id.run (verifyDeferredWith (m := Id) H End.bytecode (seedOf H) pd c π) = true := by
  simp only [verifyDeferredWith]
  exact h

/-- The caps' agreement at the deferring seed (stated at any `H`). -/
theorem capsAgree_of_queriesDep (H : Bytes → Digest) {pd : Digest} {c : FixedClaims} {π : Proof}
    (h : ∀ b ∈ queriesOfWith H (deferredProgram c End.bytecode pd)
      ⟨Id.run (seedWith (m := Id) H End.bytecode pd), π.stream, π.openings, []⟩,
      BatchAgreesWith H b.1 b.2) :
    ∀ b ∈ queriesOfWith H (deferredProgram c End.bytecode pd)
      ⟨H (digestBytes (seedOf H) ++ digestBytes pd), π.stream, π.openings, []⟩,
      BatchAgreesWith H b.1 b.2 := h

/-- **What a child of the deployed prover gives its parent**: its deferred claim holds, its fresh
claims are true, the deferring verifier accepts its proof with them, and the query steps of that
run on its proof agree in the guest's caps. -/
theorem deployedOut_child (hρ : validRate ρ) {T : HonestTree} {o : DepOut}
    (h : deployedOut ρ pfuel T = some o) :
    o.stmt.defer.Holds End.bytecode ∧ o.fresh.Holds End.bytecode ∧
      Id.run (verifyDeferredWith (m := Id) blake2sBytes End.bytecode (seedOf blake2sBytes)
        (digestOf blake2sBytes o.stmt) o.fresh o.proof) = true ∧
      ∀ b ∈ queriesOfWith blake2sBytes (deferredProgram o.fresh End.bytecode
          (digestOf blake2sBytes o.stmt))
        ⟨blake2sBytes (digestBytes (seedOf blake2sBytes) ++
          digestBytes (digestOf blake2sBytes o.stmt)),
          o.proof.stream, o.proof.openings, []⟩, BatchAgreesWith blake2sBytes b.1 b.2 := by
  cases T with
  | node claims xs ss ds kids =>
  rw [deployedOut_node, Option.bind_eq_some_iff] at h
  obtain ⟨kos, -, h⟩ := h
  obtain ⟨hd, e, π, hhd, hπ, rfl⟩ := deployedStep_spec ρ pfuel h
  obtain ⟨c, hc, hprove, cv', h', hfs⟩ := exists_deferred_dep blake2sBytes e.adm hρ e.m3 hπ
  have hacc := runProof_of_fsRun blake2sBytes _ pfuel _ _ hfs hprove
  have hcaps := queriesOfWith_deferred_honest blake2sBytes _ pfuel hprove hfs
  rw [End.publicDigest_publicInputOf] at hacc hcaps
  exact ⟨(deferDep_spec hhd).1, freshDep_spec ⟨c, hc, verifyDeferredWith_of_runProofDep _ hacc,
    capsAgree_of_queriesDep _ hcaps⟩⟩

/-- **A child's claims are true**, from its facts: the shapes of an accepted proof's claims
(`verifyDeferredWith_shaped`), the statement's deferred claim holding, the fresh claims true. -/
theorem childTrue_of_facts {o : DepOut} (hd : o.stmt.defer.Holds End.bytecode)
    (hf : o.fresh.Holds End.bytecode)
    (hv : Id.run (verifyDeferredWith (m := Id) blake2sBytes End.bytecode (seedOf blake2sBytes)
      (digestOf blake2sBytes o.stmt) o.fresh o.proof) = true) :
    ChildTrue End.bytecode ⟨digestOf blake2sBytes o.stmt, o.fresh, o.stmt.defer⟩ := by
  have hsh := verifyDeferredWith_shaped (fun x ↦ some (blake2sBytes x)) (bytecode := End.bytecode)
    (show verifyDeferredWith (m := Option) (fun x ↦ some (blake2sBytes x)) End.bytecode
      (seedOf blake2sBytes) (digestOf blake2sBytes o.stmt) o.fresh o.proof = some true by
        rw [verifyDeferredWith_someH, hv])
  obtain ⟨hbp, hrow, hcol, hsl⟩ := hsh
  exact ⟨hbp, hd.1.1, hf.1, hd.2.2.1, ⟨hrow, hcol, hsl, hd.1.2⟩, hf.2, hd.2.2.2⟩

/-- **The deployed node relation**: with every child's facts and the holders verifying at
BLAKE2s, the node relation holds at `some ∘ blake2sBytes`, the batching from the baked start. -/
theorem nodeRelDep {claims : Claims} {xs : List (Holder LeanXmss.Signature)}
    {ss : List (Holder Sphincs.Signature)} {ds : List (Holder Da.Witness)} {kos : List DepOut}
    {hd : BatchHints × DeferredClaim} (hdef : deferDep (kos.map DepOut.child) = some hd)
    (hkids : ∀ ko ∈ kos, ko.stmt.defer.Holds End.bytecode ∧
      Id.run (verifyDeferredWith (m := Id) blake2sBytes End.bytecode (seedOf blake2sBytes)
        (digestOf blake2sBytes ko.stmt) ko.fresh ko.proof) = true)
    (hx : List.Forall₂ (XmssHeldWith (fun x ↦ some (blake2sBytes x)) (kos.map DepOut.child))
      claims.xmss xs)
    (hs : List.Forall₂ (SphincsHeldWith (fun x ↦ some (blake2sBytes x)) (kos.map DepOut.child))
      claims.sphincs ss)
    (hda : List.Forall₂ (DaHeldWith (fun x ↦ some (blake2sBytes x)) B1.Main.daPadCell
      B1.Main.daPadRow (kos.map DepOut.child)) claims.da ds) :
    NodeRelWith (fun x ↦ some (blake2sBytes x)) B1.Main.aggSeedD B1.Main.daPadCell
      B1.Main.daPadRow End.bytecode (seedOf blake2sBytes) ⟨claims, hd.2⟩
      ⟨kos.map DepOut.child, xs, ss, ds, hd.1⟩ := by
  have hspec := deferDep_spec hdef
  refine ⟨hspec.1.1, ?_, hx, hs, hda, ?_⟩
  · intro c hc
    obtain ⟨ko, hko, rfl⟩ := List.mem_map.mp hc
    obtain ⟨hb, hv⟩ := hkids ko hko
    refine ⟨hb.1, digestOf blake2sBytes ko.stmt, statementDigestWith_someH blake2sBytes _, ?_⟩
    rw [verifyDeferredWith_someH]
    exact congrArg some hv
  · split
    · rename_i h0
      have e := hspec.2.1 h0
      subst e
      exact leafDeferDep_atZero
    · rename_i h0
      exact hspec.2.2 h0

/-! ## The prover outputs -/

/-- **The proof-of-work event** at a node's digest: every proof of work of the deployed verifier
program on it finds a nonce within `pfuel`. -/
def PowGoodDep (pi : Digest) : Prop :=
  ∀ hist bits k cv,
    (leanVmProgram End.bytecode (publicDigest (End.publicInputOf pi))).after hist =
      some (.grind bits k) → findNonce blake2sBytes bits cv pfuel ≠ none

/-- **The node step outputs**: with the deferred claim and hints, the node relation, the limits,
the caps, the budget and the proof-of-work event. -/
theorem deployedStep_isSome {claims : Claims} {xs : List (Holder LeanXmss.Signature)}
    {ss : List (Holder Sphincs.Signature)} {ds : List (Holder Da.Witness)} {kos : List DepOut}
    {hd : BatchHints × DeferredClaim} (hdef : deferDep (kos.map DepOut.child) = some hd)
    (hrel : NodeRelWith (fun x ↦ some (blake2sBytes x)) B1.Main.aggSeedD B1.Main.daPadCell
      B1.Main.daPadRow End.bytecode (seedOf blake2sBytes) ⟨claims, hd.2⟩
      ⟨kos.map DepOut.child, xs, ss, ds, hd.1⟩)
    (hlim : End.Limits ⟨claims, hd.2⟩ ⟨kos.map DepOut.child, xs, ss, ds, hd.1⟩)
    (hcaps : CapsAgreeWith blake2sBytes (seedOf blake2sBytes)
      ⟨kos.map DepOut.child, xs, ss, ds, hd.1⟩)
    (hbud : B2C.b2cBudget'.size (End.work ⟨claims, hd.2⟩
      ⟨kos.map DepOut.child, xs, ss, ds, hd.1⟩) ≤ 2 ^ 28)
    (hpow : PowGoodDep pfuel (digestOf blake2sBytes ⟨claims, hd.2⟩)) :
    deployedStep ρ pfuel claims xs ss ds kos ≠ none := by
  have hne := nodeExecDep_nonempty hrel hlim hcaps hbud
  unfold deployedStep
  simp only [hdef, Option.bind_eq_bind, Option.bind_some, ne_eq]
  split
  · intro h
    simp only [Option.bind_eq_none_iff] at h
    obtain ⟨π, hπ⟩ := Option.ne_none_iff_exists'.mp (prove_ne_none blake2sBytes _ _ _ pfuel hpow)
    exact absurd (h π hπ) (by simp)
  · exact absurd hne ‹_›

/-- **The node within the deployed limits and budget**, at the deferred claim the deployed
prover finds from its children's outputs. -/
def _root_.LeanVM.E2E.Complete.HonestTree.LimitsDepAt : HonestTree → Prop
  | .node claims xs ss ds kids =>
    ∀ kos, SanityDeployed.kidOutsDep ρ pfuel kids = some kos → ∀ hd,
      SanityDeployed.deferDep (kos.map SanityDeployed.DepOut.child) = some hd →
      End.Limits ⟨claims, hd.2⟩ ⟨kos.map SanityDeployed.DepOut.child, xs, ss, ds, hd.1⟩ ∧
      B2C.b2cBudget'.size
        (End.work ⟨claims, hd.2⟩ ⟨kos.map SanityDeployed.DepOut.child, xs, ss, ds, hd.1⟩) ≤
        2 ^ 28

/-- **The tree within the deployed limits and budget**, at every node. -/
def _root_.LeanVM.E2E.Complete.HonestTree.WithinLimitsDep (T : HonestTree) : Prop :=
  T.AllNodes (HonestTree.LimitsDepAt ρ pfuel)

/-- The node's proofs of work are found. -/
def _root_.LeanVM.E2E.Complete.HonestTree.PowDepAt : HonestTree → Prop
  | .node claims _ _ _ kids =>
    ∀ kos, SanityDeployed.kidOutsDep ρ pfuel kids = some kos → ∀ hd,
      SanityDeployed.deferDep (kos.map SanityDeployed.DepOut.child) = some hd →
      SanityDeployed.PowGoodDep pfuel (digestOf blake2sBytes ⟨claims, hd.2⟩)

/-- **Every node's proofs of work are found.** -/
def _root_.LeanVM.E2E.Complete.HonestTree.PowFoundDep (T : HonestTree) : Prop :=
  T.AllNodes (HonestTree.PowDepAt ρ pfuel)

/-- **The deployed prover outputs** on a tree whose holders verify at BLAKE2s, within the
deployed limits and budget, whose proofs of work are found, at a valid rate. -/
theorem deployedOut_isSome (hρ : validRate ρ) :
    ∀ T : HonestTree, T.AllNodes (HonestTree.ValidAt blake2sBytes) → T.WithinLimitsDep ρ pfuel →
      T.PowFoundDep ρ pfuel → ∃ o, deployedOut ρ pfuel T = some o := by
  refine HonestTree.induct' _ fun claims xs ss ds kids ih hv hl hp ↦ ?_
  rw [HonestTree.WithinLimitsDep, HonestTree.allNodes_node] at hl
  rw [HonestTree.PowFoundDep, HonestTree.allNodes_node] at hp
  rw [HonestTree.allNodes_node] at hv
  obtain ⟨kos, hkos⟩ : ∃ kos, kidOutsDep ρ pfuel kids = some kos :=
    mapM_some _ _ fun k _ ↦ ih k.1 k.2 (hv.2 k.1 k.2) (hl.2 k.1 k.2) (hp.2 k.1 k.2)
  have h2 := forall₂_kidOutsDep ρ pfuel hkos
  have hchild : ∀ ko ∈ kos, _ := fun ko hko ↦
    (forall₂_mem_right h2 ko hko).elim fun k hk ↦ deployedOut_child ρ pfuel hρ hk.2
  obtain ⟨hd, hdef⟩ := deferDep_some (cs := kos.map DepOut.child) fun c hc ↦ by
    obtain ⟨ko, hko, rfl⟩ := List.mem_map.mp hc
    exact childTrue_of_facts (hchild ko hko).1 (hchild ko hko).2.1 (hchild ko hko).2.2.1
  obtain ⟨hlim, hbud⟩ := hl.1 kos hkos hd hdef
  have hc := (kidOutsDep_claims ρ pfuel hkos).symm
  obtain ⟨hx, hs, hda⟩ := hv.1
  have hrel := nodeRelDep hdef
    (fun ko hko ↦ ⟨(hchild ko hko).1, (hchild ko hko).2.2.1⟩)
    (hx.imp fun _ _ h ↦ xmssHeldWith_transfer hc h)
    (hs.imp fun _ _ h ↦ sphincsHeldWith_transfer hc h)
    (hda.imp fun _ _ h ↦ daHeldWith_transfer hc h)
  have hcaps : CapsAgreeWith blake2sBytes (seedOf blake2sBytes)
      ⟨kos.map DepOut.child, xs, ss, ds, hd.1⟩ := by
    intro c hcm
    obtain ⟨ko, hko, rfl⟩ := List.mem_map.mp hcm
    exact (hchild ko hko).2.2.2
  have hstep := deployedStep_isSome ρ pfuel hdef hrel hlim hcaps hbud (hp.1 kos hkos hd hdef)
  obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.mp hstep
  exact ⟨o, by rw [deployedOut_node, hkos, Option.bind_some, ho]⟩

/-- **The deployed prover outputs**, in `deployedProve`'s form. -/
theorem deployedProve_isSome (hρ : validRate ρ) (T : HonestTree)
    (hv : T.Valid blake2sBytes) (hlim : T.WithinLimitsDep ρ pfuel)
    (hpow : T.PowFoundDep ρ pfuel) : ∃ s π ip, deployedProve ρ pfuel T = some (s, π, ip) := by
  obtain ⟨o, ho⟩ := deployedOut_isSome ρ pfuel hρ T hv.1 hlim hpow
  exact ⟨o.stmt, o.proof, idealOfDep o, by simp [deployedProve, ho]⟩

end
end LeanVM.E2E.SanityDeployed
