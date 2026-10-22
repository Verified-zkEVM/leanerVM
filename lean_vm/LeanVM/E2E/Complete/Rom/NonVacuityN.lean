/-
  LeanVM.E2E.Complete.Rom.NonVacuityN

  T6-prob: what the H-oblivious prover's outputs satisfy, and that on a valid tree within the
  limits it fails only at a proof-of-work search (G1) or at vanishing matrix weights (G2).
-/

module

public import LeanVM.E2E.Complete.Rom.ProverN

/-!
# The H-oblivious prover's outputs and failures

* `proveNode_spec`, `honestStepN_spec`: an output is built from the deferred claim, the execution
  `execOf` chose, V°'s honest proof and `freshRun`'s claims;
* `honestOutN_claims`, `honestOutN_child`: an output's statement makes the tree's claims, and its
  child is accepted by the deferring verifier with true bytecode claims and agreeing caps (the
  facts `honestOut_child` gives of the classical prover);
* **`honestOutN_ne_stuck`**: on a valid tree within the limits (`WithinLimitsN`) the prover's
  failure, if any, is a proof-of-work search or vanishing weights.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Node LeanVM.Guest
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd LeanVM.Protocol.Whir.Complete

@[expose] public section

variable (H : Bytes → Digest) (ρ pfuel : ℕ)

/-! ## Outputs -/

/-- **What a node's proof is built from.** -/
theorem proveNode_spec {s : NodeStatement} {w : NodeWitness} {kos : List HonestOutN}
    {o : HonestOutN} (h : proveNode H ρ pfuel s w kos = .ok o) :
    ∃ (e : NodeExecOn ((logOf H (nodeLog H s w)).map Prod.fst) (fillLog (logOf H (nodeLog H s w)))
        (digestOf H s) w) (π : Proof) (c : FixedClaims),
      execOf (logOf H (nodeLog H s w)) (digestOf H s) w = some e ∧
      prove H (progOf (digestOf H s)) (stratOf ρ e) (seedAt H (digestOf H s)) pfuel = some π ∧
      freshRun H (stratOf ρ e) pfuel End.bytecode (publicDigest (End.publicInputOf (digestOf H s)))
        (seedAt H (digestOf H s)) = some c ∧
      o = outOf H s c π e kos := by
  unfold proveNode at h
  split at h
  · cases h
  · rename_i e he
    split at h
    · cases h
    · rename_i π hπ
      split at h
      · cases h
      · rename_i c hc
        exact ⟨e, π, c, he, hπ, hc, (Except.ok.inj h).symm⟩

/-- **What a node step is built from.** -/
theorem honestStepN_spec {claims : Claims} {xs : List (Holder LeanXmss.Signature)}
    {ss : List (Holder Sphincs.Signature)} {ds : List (Holder Da.Witness)} {kos : List HonestOutN}
    {o : HonestOutN} (h : honestStepN H ρ pfuel claims xs ss ds kos = .ok o) :
    ∃ hd : BatchHints × DeferredClaim, honestDeferN H (kos.map HonestOutN.child) = .ok hd ∧
      proveNode H ρ pfuel ⟨claims, hd.2⟩ ⟨kos.map HonestOutN.child, xs, ss, ds, hd.1⟩ kos = .ok o := by
  unfold honestStepN at h
  cases hd : honestDeferN H (kos.map HonestOutN.child) with
  | error f => rw [hd] at h; cases h
  | ok hd' => exact ⟨hd', rfl, by rw [hd] at h; exact h⟩

/-- An output's statement is its node's. -/
theorem outOf_stmt {s : NodeStatement} {c : FixedClaims} {π : Proof} {D : List Bytes}
    {H' : Bytes → Digest} {pi : Digest} {w : NodeWitness} (e : NodeExecOn D H' pi w)
    (kos : List HonestOutN) : (outOf H s c π e kos).stmt = s := rfl

/-- **The output's statement makes the tree's claims.** -/
theorem honestOutN_claims {T : HonestTree} {o : HonestOutN} (h : honestOutN H ρ pfuel T = .ok o) :
    o.stmt.claims = T.claims := by
  cases T with
  | node c xs ss ds kids =>
  rw [honestOutN_node] at h
  cases hk : kidOutsN H ρ pfuel kids with
  | error f => rw [hk] at h; cases h
  | ok kos =>
    rw [hk] at h
    obtain ⟨hd, -, h⟩ := honestStepN_spec H ρ pfuel h
    obtain ⟨e, π, c, -, -, -, rfl⟩ := proveNode_spec H ρ pfuel h
    rfl

/-- The H-oblivious prover's child, as a classical output (its entries unread). -/
def HonestOutN.toOut (o : HonestOutN) : HonestOut := ⟨o.stmt, o.fresh, o.proof, [], 0, []⟩

theorem map_toOut_child (kos : List HonestOutN) :
    (kos.map HonestOutN.toOut).map HonestOut.child = kos.map HonestOutN.child := by
  simp only [List.map_map]
  rfl

/-- **What a child of the H-oblivious prover gives its parent** (`honestOut_child`'s facts). -/
theorem honestOutN_child (hρ : validRate ρ) {T : HonestTree} {o : HonestOutN}
    (h : honestOutN H ρ pfuel T = .ok o) :
    o.stmt.defer.BytecodeHolds End.bytecode ∧
      multilinearEval (End.bytecode.map ofK) o.fresh.bytecodePoint = o.fresh.bytecodeValue ∧
      Id.run (verifyDeferredWith (m := Id) H End.bytecode (seedOf H) (digestOf H o.stmt) o.fresh
        o.proof) = true ∧
      ∀ b ∈ queriesOfWith H (deferredProgram o.fresh End.bytecode (digestOf H o.stmt))
        ⟨H (digestBytes (seedOf H) ++ digestBytes (digestOf H o.stmt)), o.proof.stream,
          o.proof.openings, []⟩, BatchAgreesWith H b.1 b.2 := by
  cases T with
  | node claims xs ss ds kids =>
  rw [honestOutN_node] at h
  cases hk : kidOutsN H ρ pfuel kids with
  | error f => rw [hk] at h; cases h
  | ok kos =>
    rw [hk] at h
    obtain ⟨hd, hhd, h⟩ := honestStepN_spec H ρ pfuel h
    obtain ⟨e, π, c, -, hπ, hc, rfl⟩ := proveNode_spec H ρ pfuel h
    have hag := agrees_logOf H (nodeLog H ⟨claims, hd.2⟩ ⟨kos.map HonestOutN.child, xs, ss, ds, hd.1⟩)
    set e' := e.at hag
    obtain ⟨c', hc', hbc, hprove, cv', h', hfs⟩ :=
      exists_deferred_honest_run H e'.adm hρ e'.rel (q := e'.q) hπ
    have hcc : c' = c := Option.some.inj (hc'.symm.trans hc)
    subst hcc
    have hacc := runProof_of_fsRun H _ pfuel _ _ hfs hprove
    have hcaps := queriesOfWith_deferred_honest H _ pfuel hprove hfs
    rw [End.publicDigest_publicInputOf] at hacc hcaps
    refine ⟨(honestDefer_spec H (honestDefer_of_N H hhd)).1, hbc, ?_, hcaps⟩
    simp only [verifyDeferredWith]
    exact hacc

/-! ## The prover fails only at G1 or G2 -/

/-- A `mapM` in `Except` relates the lists pointwise. -/
theorem forall₂_of_mapM_except {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = .ok l' → List.Forall₂ (fun a b ↦ f a = .ok b) l l'
  | [], l', h => by
    simp only [List.mapM_nil] at h
    cases h
    exact List.Forall₂.nil
  | a :: l, l', h => by
    simp only [List.mapM_cons] at h
    cases ha : f a with
    | error e => rw [ha] at h; cases h
    | ok b =>
      rw [ha] at h
      cases hl : l.mapM f with
      | error e => rw [hl] at h; cases h
      | ok bs =>
        rw [hl] at h
        cases h
        exact List.Forall₂.cons ha (forall₂_of_mapM_except hl)

/-- A `mapM` in `Except` fails with one of its elements' failures. -/
theorem mapM_error_mem {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {e : ε}, l.mapM f = .error e → ∃ a ∈ l, f a = .error e
  | [], e, h => by simp only [List.mapM_nil] at h; cases h
  | a :: l, e, h => by
    simp only [List.mapM_cons] at h
    cases ha : f a with
    | error e' => rw [ha] at h; cases h; exact ⟨a, List.mem_cons_self, ha⟩
    | ok b =>
      rw [ha] at h
      cases hl : l.mapM f with
      | error e' =>
        rw [hl] at h; cases h
        obtain ⟨a', ha', h'⟩ := mapM_error_mem hl
        exact ⟨a', List.mem_cons_of_mem _ ha', h'⟩
      | ok bs => rw [hl] at h; cases h

/-- The children's outputs, child by child. -/
theorem forall₂_kidOutsN {kids : List HonestTree} {kos : List HonestOutN}
    (h : kidOutsN H ρ pfuel kids = .ok kos) :
    List.Forall₂ (fun k o ↦ honestOutN H ρ pfuel k = .ok o) kids kos := by
  have h2 := (List.forall₂_map_left_iff (f := Subtype.val)
    (R := fun k o ↦ honestOutN H ρ pfuel k = .ok o)).mpr (forall₂_of_mapM_except h)
  rwa [List.attach_map_subtype_val] at h2

/-- The children's outputs make the subtrees' claims. -/
theorem kidOutsN_claims {kids : List HonestTree} {kos : List HonestOutN}
    (h : kidOutsN H ρ pfuel kids = .ok kos) :
    (kos.map HonestOutN.child).map (·.statement.claims) =
      (kids.map (claimChild ·.claims)).map (·.statement.claims) := by
  have h2 := forall₂_kidOutsN H ρ pfuel h
  clear h
  simp only [List.map_map]
  induction h2 with
  | nil => rfl
  | cons hab _ ih =>
    simp only [List.map_cons, Function.comp_apply, ih]
    rw [show (HonestOutN.child _).statement.claims = _ from honestOutN_claims H ρ pfuel hab]
    rfl

/-- **The deferred claim fails only at the weights**, for children of the honest prover. -/
theorem honestDeferN_ne_stuck {kos : List HonestOutN}
    (hkids : ∀ ko ∈ kos, ko.stmt.defer.BytecodeHolds End.bytecode ∧
      multilinearEval (End.bytecode.map ofK) ko.fresh.bytecodePoint = ko.fresh.bytecodeValue ∧
      Id.run (verifyDeferredWith (m := Id) H End.bytecode (seedOf H) (digestOf H ko.stmt) ko.fresh
        ko.proof) = true) :
    honestDeferN H (kos.map HonestOutN.child) ≠ .error .stuck := by
  intro hst
  by_cases hw : kos.map HonestOutN.child ≠ [] →
      honestWeights H B1.Main.aggSeedD End.bytecode (childClaimsOf H (kos.map HonestOutN.child)) ≠
        (0, 0)
  · obtain ⟨hd, hhd⟩ := honestDefer_some H (kos := kos.map HonestOutN.toOut)
      (fun ko hko ↦ by
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hko
        exact hkids k hk)
      (fun hne ccs hccs ↦ by
        rw [map_toOut_child, childClaimsWith_childClaimsOf] at hccs
        cases hccs
        have hw' := hw (by
          intro h0; apply hne; simpa [HonestOutN.toOut] using congrArg List.length h0)
        by_contra hc
        push Not at hc
        exact hw' (Prod.ext hc.1 hc.2))
    rw [map_toOut_child] at hhd
    rw [honestDeferN_of H hw hhd] at hst
    cases hst
  · push Not at hw
    obtain ⟨hne, hz⟩ := hw
    unfold honestDeferN at hst
    simp only [hne, ↓reduceIte, hz] at hst
    cases hst

/-- **The H-oblivious prover never gets stuck** on a valid tree within the limits: it outputs, or
a proof-of-work search exhausts the fuel, or an inner node's matrix weights vanish. -/
theorem honestOutN_ne_stuck (hρ : validRate ρ) :
    ∀ T : HonestTree, T.AllNodes (HonestTree.ValidAt H) → T.WithinLimitsN H ρ pfuel →
      honestOutN H ρ pfuel T ≠ .error .stuck := by
  refine HonestTree.induct' _ fun claims xs ss ds kids ih hv hl ↦ ?_
  rw [HonestTree.WithinLimitsN, HonestTree.allNodes_node] at hl
  rw [HonestTree.allNodes_node] at hv
  rw [honestOutN_node]
  cases hk : kidOutsN H ρ pfuel kids with
  | error f =>
    intro h
    simp only [Except.bind] at h
    cases h
    obtain ⟨k, -, hf⟩ := mapM_error_mem hk
    exact ih k.1 k.2 (hv.2 k.1 k.2) (hl.2 k.1 k.2) hf
  | ok kos =>
    simp only [Except.bind]
    have h2 := forall₂_kidOutsN H ρ pfuel hk
    have hchild : ∀ ko ∈ kos, _ := fun ko hko ↦
      (forall₂_mem_right h2 ko hko).elim fun k hk ↦ honestOutN_child H ρ pfuel hρ hk.2
    unfold honestStepN
    cases hdN : honestDeferN H (kos.map HonestOutN.child) with
    | error f =>
      intro h
      simp only [bind, Except.bind] at h
      cases h
      exact honestDeferN_ne_stuck H (fun ko hko ↦
        ⟨(hchild ko hko).1, (hchild ko hko).2.1, (hchild ko hko).2.2.1⟩) hdN
    | ok hd =>
      simp only [bind, Except.bind]
      obtain ⟨hlim, hbud⟩ := hl.1 kos hk hd hdN
      have hdef : honestDefer H ((kos.map HonestOutN.toOut).map HonestOut.child) = some hd := by
        rw [map_toOut_child]; exact honestDefer_of_N H hdN
      have hc := (kidOutsN_claims H ρ pfuel hk).symm
      obtain ⟨hx, hs, hda⟩ := hv.1
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
      have hsome := execOf_isSome H hrel hlim hcaps hbud
      unfold proveNode
      obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hsome
      simp only [he]
      cases hπ : prove H (progOf (digestOf H ⟨claims, hd.2⟩)) (stratOf ρ e)
          (seedAt H (digestOf H ⟨claims, hd.2⟩)) pfuel with
      | none => simp
      | some π =>
        have hag := agrees_logOf H
          (nodeLog H ⟨claims, hd.2⟩ ⟨kos.map HonestOutN.child, xs, ss, ds, hd.1⟩)
        obtain ⟨c, hc, -⟩ := exists_deferred_honest_run H (e.at hag).adm hρ (e.at hag).rel
          (q := (e.at hag).q) hπ
        have hc' : freshRun H (stratOf ρ e) pfuel End.bytecode
            (publicDigest (End.publicInputOf (digestOf H ⟨claims, hd.2⟩)))
            (seedAt H (digestOf H ⟨claims, hd.2⟩)) = some c := hc
        rw [hc']
        simp

end
end LeanVM.E2E.Complete
