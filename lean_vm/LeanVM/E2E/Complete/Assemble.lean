/-
  LeanVM.E2E.Complete.Assemble

  T6-det: V_I accepts the honest idealized prover's output, for every hash, when the prover
  succeeds and the honest commitments do not collide.
-/

module

public import LeanVM.E2E.Complete.Prover

/-!
# T6-det, assembled

`idealVerify_complete` (`docs/roadmap/t6-completeness.md` §1.2): for every hash `H`, every honest
witness tree `T`, a valid rate and a fuel at least the tree's size, if the honest prover outputs
`o` (`honestOut`, which fails only when a proof-of-work search exhausts its fuel, the batching
finds no hints or a node has no execution under the honest table) and its entries satisfy
`RootsInj` (E2E-4), and the root's DA claims carry their roots' vector digests, then V_I accepts
the root statement with the idealized proof `idealOf o`, and the statement's claims are the
tree's.

The proof: every node of the tree steps, under V_I, to its children's nodes (`nodeStep_out`,
from `nodeStep_honest`: the node's word and frames are its entry's by `RootsInj`, its stack is
the only candidate, its execution passes the table check (`tableOKWith_of_validB`) and decodes
its children (`DecodeHonest`)); the closure over the nodes accepts within the tree's size
(`closure_accepts`); the root's proof is V°'s honest proof (`runProof_prove`, `runI_blindProgram`)
and its outer checks pass (`outerChecksWith_true`).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Node LeanVM.Guest
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd LeanVM.Protocol.Whir.Complete

@[expose] public section

/-! ## Small facts -/

/-- A lane read back from its two words. -/
theorem ofBits_words (lo hi : UInt32) : K.ofBits (lo.toNat + 2 ^ 32 * hi.toNat) = ofWords lo hi := by
  unfold K.ofBits ofWords
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.toNat_ofNat]
  have h1 := lo.toNat_lt
  have h2 := hi.toNat_lt
  simp only [UInt32.toNat_toBitVec]
  rw [Nat.shiftLeft_eq, show hi.toNat * 2 ^ 32 = 2 ^ 32 * hi.toNat from Nat.mul_comm _ _,
    ← Nat.two_pow_add_eq_or_of_lt (i := 32) h1]
  omega

/-- **V_I's input of a digest is the guest's.** -/
theorem inputOf_eq (d : Digest) : inputOf d = End.publicInputOf d := by
  simp only [inputOf, End.publicInputOf, Front.publicInputOfDigest]
  congr 1
  funext i
  fin_cases i <;> exact ofBits_words _ _

/-- A successful `mapM` in `Option` relates the lists pointwise. -/
theorem forall₂_of_mapM {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → List.Forall₂ (fun a b ↦ f a = some b) l l'
  | [], l', h => by
    simp only [List.mapM_nil] at h
    cases h
    exact List.Forall₂.nil
  | a :: l, l', h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨b, hb, bs, hbs, he⟩ := h
    simp only [Option.pure_def, Option.some.injEq] at he
    subst he
    exact List.Forall₂.cons hb (forall₂_of_mapM hbs)

/-- The decoded children's nodes depend only on their statements and proofs. -/
theorem kidNodes_congr (H : Bytes → Digest) (seed : Digest) {cs cs' : List Child}
    (h : cs.map (fun c ↦ (c.statement, c.proof)) = cs'.map fun c ↦ (c.statement, c.proof)) :
    kidNodes H seed cs = kidNodes H seed cs' := by
  have e : ∀ l : List Child, kidNodes H seed l = (l.map fun c ↦ (c.statement, c.proof)).map
      fun p ↦ (Id.run (Node.statementDigestWith (fun x ↦ (pure (H x) : Id Digest)) seed p.1), p.2) := by
    intro l; simp [kidNodes, Function.comp_def]
  rw [e, e, h]

/-- The guest's bytecode has a power of two of words. -/
theorem length_bytecodeWords (prog : Program) :
    (bytecodeWords prog).length = 2 ^ (prog.logSize + 4) := by
  simp only [bytecodeWords, List.length_flatMap, List.length_map, List.length_finRange,
    List.map_const', List.sum_replicate, smul_eq_mul]
  ring

theorem two_pow_log2_bytecode : 2 ^ Nat.log2 End.bytecode.length = End.bytecode.length := by
  rw [show End.bytecode = bytecodeWords guest from rfl, length_bytecodeWords, Nat.log2_two_pow]

/-- A leaf's deferred claim's bytecode part is true. -/
theorem leafDefer_holds : leafDefer.BytecodeHolds End.bytecode := by
  refine ⟨⟨?_, ?_⟩, ?_, by simp only [leafDefer]⟩
  · simp only [leafDefer, List.length_replicate]
  · simp only [leafDefer, List.length_replicate]
  · simp only [leafDefer, List.length_replicate]
    exact two_pow_log2_bytecode

/-! ## One node -/

variable (H : Bytes → Digest) (ρ pfuel : ℕ)

/-- **What the deferred claim and hints are**: the claim's bytecode part is true; at a leaf it is
`leafDefer`; at an inner node the batching of the children's claims accepts the hints with it. -/
theorem honestDefer_spec {cs : List Child} {hd : BatchHints × DeferredClaim}
    (h : honestDefer H cs = some hd) :
    hd.2.BytecodeHolds End.bytecode ∧ (cs = [] → hd.2 = leafDefer) ∧
      (cs ≠ [] → ∃ ccs, childClaimsWith (fun x ↦ some (H x)) (seedOf H) cs = some ccs ∧
        batchWith (fun x ↦ some (H x)) B1.Main.aggSeedD ccs hd.1 = some (some hd.2)) := by
  unfold honestDefer at h
  split at h
  · rename_i h0
    cases h
    exact ⟨leafDefer_holds, fun _ ↦ rfl, fun h ↦ absurd h0 h⟩
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

/-- **What the honest step outputs**: the deferred claim and hints, the node's execution, V°'s
honest proof, and the output built from them. -/
theorem honestStep_spec {claims : Claims} {xs : List (Holder LeanXmss.Signature)}
    {ss : List (Holder Sphincs.Signature)} {ds : List (Holder Da.Witness)} {kos : List HonestOut}
    {o : HonestOut} (h : honestStep H ρ pfuel claims xs ss ds kos = some o) :
    ∃ (hd : BatchHints × DeferredClaim)
      (e : NodeExec H (digestOf H ⟨claims, hd.2⟩) ⟨kos.map HonestOut.child, xs, ss, ds, hd.1⟩)
      (π : Proof),
      honestDefer H (kos.map HonestOut.child) = some hd ∧
      prove H (blindProgram End.bytecode
          (publicDigest (End.publicInputOf (digestOf H ⟨claims, hd.2⟩))))
        (Blind.honestStrategyBlind guest e.sz ρ e.q)
        (Id.run (seedWith H End.bytecode
          (publicDigest (End.publicInputOf (digestOf H ⟨claims, hd.2⟩))))) pfuel = some π ∧
      o = ⟨⟨claims, hd.2⟩, freshFor H (digestOf H ⟨claims, hd.2⟩) π, π,
        ((stackRoot π).getD (0, 0), stackWord (leanIsaμ guest e.sz) e.q, e.fr) ::
          kos.flatMap HonestOut.entries,
        1 + (kos.map HonestOut.size).sum,
        ((digestOf H ⟨claims, hd.2⟩, π), kos.map (nodeOfOut H), 1 + (kos.map HonestOut.size).sum) ::
          kos.flatMap HonestOut.subs⟩ := by
  unfold honestStep at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨hd, hhd, h⟩ := h
  split at h
  · rename_i hne
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨π, hπ, h⟩ := h
    exact ⟨hd, Classical.choice hne, π, hhd, hπ, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- **V_I steps an honest node to its children's nodes**, when the idealized proof gives the
node's root its entry's word and frames. -/
theorem nodeStep_out {claims : Claims} {xs : List (Holder LeanXmss.Signature)}
    {ss : List (Holder Sphincs.Signature)} {ds : List (Holder Da.Witness)} {kos : List HonestOut}
    {o : HonestOut} (hρ : validRate ρ) (h : honestStep H ρ pfuel claims xs ss ds kos = some o)
    (ip : IdealProof) (hip : ∀ e ∈ o.entries.head?, ip.word e.1 = some e.2.1 ∧ ip.frames e.1 = e.2.2) :
    nodeStep (m := Id) (fun x ↦ (pure (H x) : Id Digest)) guest (seedOf H) ip (nodeOfOut H o) =
      some (kos.map (nodeOfOut H)) := by
  obtain ⟨hd, e, π, -, hπ, rfl⟩ := honestStep_spec H ρ pfuel h
  have hip' := hip _ rfl
  simp only at hip'
  have hstep := nodeStep_honest H (seedOf H) ip e.adm hρ hπ
    (fun r hr ↦ by rw [hr] at hip'; exact hip'.1) (fr := e.fr)
    (fun r hr ↦ by rw [hr] at hip'; exact hip'.2) (digestOf H ⟨claims, hd.2⟩)
    (Guest.End.decodeAt (Guest.Value.tableSem (e.t.blakeRows blakeFree)) e.fr e.t.image).witness.children
    fun _ ↦ ⟨e.t, e.run, tableOKWith_of_validB e.valid, rfl⟩
  have hm : M3HoldsBlind (leanIsaInstance Sound.F₀ guest e.sz) (inputOf (digestOf H ⟨claims, hd.2⟩)) e.q := by
    rw [inputOf_eq]; exact e.rel.1
  simp only [hm, ↓reduceIte] at hstep
  rw [show nodeOfOut H ⟨⟨claims, hd.2⟩, _, π, _, _, _⟩ = (digestOf H ⟨claims, hd.2⟩, π) from rfl, hstep,
    kidNodes_congr H (seedOf H) e.decode]
  simp only [kidNodes, List.map_map]
  rfl

/-! ## The tree -/

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ b ∈ l', ∃ a ∈ l, R a b
  | _, _, .nil, _, hb => absurd hb (by simp)
  | a :: _, _ :: _, .cons hab h, b, hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨a, List.mem_cons_self, hab⟩
    · obtain ⟨a', ha', h'⟩ := forall₂_mem_right h b hb
      exact ⟨a', List.mem_cons_of_mem _ ha', h'⟩

theorem forall₂_sum {α β : Type} {f : α → ℕ} {g : β → ℕ} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ (fun a b ↦ f a = g b) l l' →
      (l.map f).sum = (l'.map g).sum
  | _, _, .nil => rfl
  | _, _, .cons hab h => by simp only [List.map_cons, List.sum_cons, hab, forall₂_sum h]

/-- **The nodes' list is closed**: every node's children are nodes of the list, its size one more
than theirs. -/
def SubsOK (subs : List (E2E.Node × List E2E.Node × ℕ)) : Prop :=
  ∀ p ∈ subs, ∃ ks : List (E2E.Node × ℕ), p.2.1 = ks.map (·.1) ∧
    (∀ k ∈ ks, ∃ p' ∈ subs, p'.1 = k.1 ∧ p'.2.2 = k.2) ∧ p.2.2 = 1 + (ks.map (·.2)).sum

/-- Induction over honest trees. -/
theorem HonestTree.induct' (P : HonestTree → Prop)
    (h : ∀ c xs ss ds kids, (∀ k ∈ kids, P k) → P (.node c xs ss ds kids)) : ∀ T, P T
  | .node c xs ss ds kids => h c xs ss ds kids fun k _hk ↦ HonestTree.induct' P h k
termination_by T => sizeOf T
decreasing_by
  have := List.sizeOf_lt_of_mem ‹k ∈ kids›
  simp_wf
  omega

theorem forall₂_imp_mem {α β : Type} {R S : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → (∀ a b, b ∈ l' → R a b → S a b) →
      List.Forall₂ S l l'
  | _, _, .nil, _ => .nil
  | _, _, .cons hab h, hS =>
    .cons (hS _ _ List.mem_cons_self hab)
      (forall₂_imp_mem h fun a b hb ↦ hS a b (List.mem_cons_of_mem _ hb))

/-- What an honest output satisfies, under an idealized proof giving its entries their words and
frames. -/
def GoodOut (ip : IdealProof) (T : HonestTree) (o : HonestOut) : Prop :=
  o.stmt.claims = T.claims ∧ o.size = T.size ∧
    (∃ ks, o.subs.head? = some (nodeOfOut H o, ks, o.size)) ∧
    (∀ p ∈ o.subs, nodeStep (m := Id) (fun x ↦ (pure (H x) : Id Digest)) guest (seedOf H) ip p.1 =
      some p.2.1) ∧ SubsOK o.subs

/-- **Every node of an honest output steps to its children's nodes**, under an idealized proof
giving every entry its word and frames; the output's statement has the tree's claims, its size is
the tree's, its first node is its own, and its nodes' list is closed. -/
theorem honestOut_good (hρ : validRate ρ) (ip : IdealProof) (T : HonestTree) :
    ∀ o : HonestOut, honestOut H ρ pfuel T = some o →
      (∀ e ∈ o.entries, ip.word e.1 = some e.2.1 ∧ ip.frames e.1 = e.2.2) → GoodOut H ip T o := by
  induction T using HonestTree.induct' with
  | h claims xs ss ds kids ih =>
  intro o h hip
  rw [honestOut] at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨kos, hkos, h⟩ := h
  have hF := forall₂_of_mapM hkos
  have hstep := nodeStep_out H ρ pfuel hρ h ip fun e he ↦ hip e (List.mem_of_mem_head? he)
  obtain ⟨hd, e, π, -, -, rfl⟩ := honestStep_spec H ρ pfuel h
  have hipk : ∀ ko ∈ kos, ∀ e ∈ ko.entries, ip.word e.1 = some e.2.1 ∧ ip.frames e.1 = e.2.2 :=
    fun ko hko e he ↦ hip e (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨ko, hko, he⟩))
  have hG : List.Forall₂ (fun k ko ↦ GoodOut H ip k.1 ko) kids.attach kos :=
    forall₂_imp_mem hF fun k ko hko hk ↦ ih k.1 k.2 ko hk (hipk ko hko)
  have hmem : ∀ ko ∈ kos, ∃ k : {x // x ∈ kids}, GoodOut H ip k.1 ko := by
    intro ko hko
    obtain ⟨k, -, hk⟩ := forall₂_mem_right hG ko hko
    exact ⟨k, hk⟩
  refine ⟨rfl, ?_, ⟨_, rfl⟩, ?_, ?_⟩
  · show 1 + (kos.map HonestOut.size).sum = HonestTree.size (.node claims xs ss ds kids)
    rw [HonestTree.size]
    congr 1
    exact (forall₂_sum (hG.imp fun k ko hk ↦ hk.2.1.symm)).symm
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hstep
    · obtain ⟨ko, hko, hp⟩ := List.mem_flatMap.mp hp
      obtain ⟨_, hk⟩ := hmem ko hko
      exact hk.2.2.2.1 p hp
  · intro p hp
    have hsub : ∀ ko ∈ kos, ∀ p ∈ ko.subs, p ∈ ((digestOf H ⟨claims, hd.2⟩, π), kos.map (nodeOfOut H),
        1 + (kos.map HonestOut.size).sum) :: kos.flatMap HonestOut.subs :=
      fun ko hko p hp ↦ List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨ko, hko, hp⟩)
    rcases List.mem_cons.mp hp with rfl | hp
    · refine ⟨kos.map fun ko ↦ (nodeOfOut H ko, ko.size), by simp, ?_, by simp [Function.comp_def]⟩
      intro k hk
      obtain ⟨ko, hko, rfl⟩ := List.mem_map.mp hk
      obtain ⟨_, hk⟩ := hmem ko hko
      obtain ⟨ks, hks⟩ := hk.2.2.1
      exact ⟨(nodeOfOut H ko, ks, ko.size), hsub ko hko _ (List.mem_of_mem_head? hks), rfl, rfl⟩
    · obtain ⟨ko, hko, hp⟩ := List.mem_flatMap.mp hp
      obtain ⟨_, hk⟩ := hmem ko hko
      obtain ⟨ks, h1, h2, h3⟩ := hk.2.2.2.2 p hp
      exact ⟨ks, h1, fun k hk ↦ by
        obtain ⟨p', hp', e1, e2⟩ := h2 k hk
        exact ⟨p', hsub ko hko p' hp', e1, e2⟩, h3⟩

/-! ## T6-det -/

/-- Under `RootsInj`, an entry is the first of its root. -/
theorem find?_entry {es : List Entry} (hr : RootsInj es) {e : Entry} (he : e ∈ es) :
    es.find? (fun e' ↦ decide (e'.1 = e.1)) = some e := by
  cases hf : es.find? (fun e' ↦ decide (e'.1 = e.1)) with
  | none =>
    have := List.find?_eq_none.mp hf e he
    simp at this
  | some e' =>
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [decide_eq_true_eq] at hp
    rw [hr e' hm e he hp]

/-- **The idealized proof gives every entry its word and frames**, under `RootsInj`. -/
theorem idealOf_entries {o : HonestOut} (hr : RootsInj o.entries) :
    ∀ e ∈ o.entries, (idealOf o).word e.1 = some e.2.1 ∧ (idealOf o).frames e.1 = e.2.2 := by
  intro e he
  have hf := find?_entry hr he
  refine ⟨?_, ?_⟩
  · simp only [IdealProof.word, idealOf, List.find?_map, Function.comp_def]
    rw [hf]
    rfl
  · simp only [idealOf, hf]
    rfl

/-- The root's facts: V°'s honest proof and the deferred claim's bytecode part. -/
theorem honestOut_root (hρ : validRate ρ) {T : HonestTree} {o : HonestOut}
    (h : honestOut H ρ pfuel T = some o) :
    Id.run (verifyBlindWith (m := Id) (fun x ↦ (pure (H x) : Id Digest)) End.bytecode
      (digestOf H o.stmt) o.proof) = true ∧ o.stmt.defer.BytecodeHolds End.bytecode := by
  cases T with
  | node claims xs ss ds kids =>
  rw [honestOut] at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨kos, -, h⟩ := h
  obtain ⟨hd, e, π, hhd, hπ, rfl⟩ := honestStep_spec H ρ pfuel h
  refine ⟨?_, ?_⟩
  · have hrun := runProof_prove H _ _ _ pfuel
      (fun chal ↦ (Blind.runI_blindProgram e.adm hρ e.rel chal).1)
      (fun chal ↦ (Blind.runI_blindProgram e.adm hρ e.rel chal).2) hπ
    rw [End.publicDigest_publicInputOf] at hrun
    exact hrun
  · exact (honestDefer_spec H hhd).1

/-- **T6-det: V_I accepts the honest idealized prover's output**, for every hash `H`. For an
honest witness tree whose root DA claims carry their roots' vector digests, at a valid rate and a
fuel at least the tree's size: if the honest prover outputs `o` (it fails only when a
proof-of-work search exhausts `pfuel`, the batching finds no hints, or a node has no execution
under the honest table, the good events and L2–L4, L11 excluding these) and the honest
commitments do not collide (`RootsInj`, E2E-4), then the output's statement has the tree's claims
and V_I accepts it with the idealized proof `idealOf o`. -/
theorem idealVerify_complete (H : Bytes → Digest) (T : HonestTree) {ρ pfuel fuel : ℕ}
    (hρ : validRate ρ) {o : HonestOut} (hI : honestOut H ρ pfuel T = some o)
    (hroots : RootsInj o.entries) (hfuel : T.size ≤ fuel)
    (hda : ∀ c ∈ T.claims.da,
      Da.toBytes c.2 = Id.run (Da.vectorDigestOfWith (fun x ↦ (pure (H x) : Id Digest)) c.1)) :
    o.stmt.claims = T.claims ∧
      idealVerify (m := Id) (fun x ↦ (pure (H x) : Id Digest)) guest (idealOf o) fuel o.stmt =
        true := by
  have hip := idealOf_entries hroots
  obtain ⟨hcl, hsize, ⟨ks, hhead⟩, hsteps, hsubs⟩ := honestOut_good H ρ pfuel hρ (idealOf o) T o hI hip
  obtain ⟨hV, hbc⟩ := honestOut_root H ρ pfuel hρ hI
  refine ⟨hcl, idealVerify_accepts H guest (idealOf o) fuel o.stmt hV
    (outerChecksWith_true H guest o.stmt (by rw [hcl]; exact hda) hbc) ?_⟩
  -- the closure, over the output's nodes
  classical
  let Good : E2E.Node → Prop := fun ν ↦ ∃ p ∈ o.subs, p.1 = ν
  let kidsOf : E2E.Node → List E2E.Node := fun ν ↦
    (nodeStep (m := Id) (fun x ↦ (pure (H x) : Id Digest)) guest (seedOf H) (idealOf o) ν).getD []
  let sz : E2E.Node → ℕ := fun ν ↦
    if h : ∃ n, ∃ p ∈ o.subs, p.1 = ν ∧ p.2.2 = n then Nat.find h else 0
  have hstep' : ∀ p ∈ o.subs, kidsOf p.1 = p.2.1 := fun p hp ↦ by
    simp only [kidsOf, hsteps p hp, Option.getD_some]
  have hsz_le : ∀ p ∈ o.subs, sz p.1 ≤ p.2.2 := fun p hp ↦ by
    have hex : ∃ n, ∃ p' ∈ o.subs, p'.1 = p.1 ∧ p'.2.2 = n := ⟨_, p, hp, rfl, rfl⟩
    simp only [sz, hex, ↓reduceDIte]
    exact Nat.find_min' hex ⟨p, hp, rfl, rfl⟩
  have hmem_head : (nodeOfOut H o, ks, o.size) ∈ o.subs := List.mem_of_mem_head? hhead
  have hacc := closure_accepts H guest (seedOf H) (idealOf o) Good kidsOf sz
    (fun ν ⟨p, hp, hν⟩ ↦ by rw [← hν, hsteps p hp, hstep' p hp])
    (fun ν ⟨p, hp, hν⟩ κ hκ ↦ by
      rw [← hν, hstep' p hp] at hκ
      obtain ⟨ks', hks', hk', -⟩ := hsubs p hp
      rw [hks'] at hκ
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hκ
      obtain ⟨p', hp', e1, -⟩ := hk' k hk
      exact ⟨p', hp', e1⟩)
    (fun ν ⟨p₀, hp₀, hν⟩ ↦ by
      have hex : ∃ n, ∃ p ∈ o.subs, p.1 = ν ∧ p.2.2 = n := ⟨_, p₀, hp₀, hν, rfl⟩
      obtain ⟨p, hp, hpν, hpn⟩ := Nat.find_spec hex
      have hszν : sz ν = Nat.find hex := by simp only [sz, hex, ↓reduceDIte]
      rw [hszν, ← hpn, ← hpν, hstep' p hp]
      obtain ⟨ks', hks', hk', hsum⟩ := hsubs p hp
      rw [hks', hsum, List.map_map]
      have : ((ks'.map (sz ∘ (·.1)))).sum ≤ (ks'.map (·.2)).sum := by
        apply List.sum_le_sum
        intro k hk
        obtain ⟨p', hp', e1, e2⟩ := hk' k hk
        simp only [Function.comp_apply, ← e1, ← e2]
        exact hsz_le p' hp'
      omega)
    fuel [nodeOfOut H o] [] (by
      intro ν hν
      rw [List.mem_singleton.mp hν]
      exact ⟨_, hmem_head, rfl⟩) (by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      exact (hsz_le _ hmem_head).trans (hsize ▸ hfuel))
  exact hacc

end
end LeanVM.E2E.Complete
