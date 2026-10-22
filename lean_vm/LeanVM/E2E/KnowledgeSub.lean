/-
  LeanVM.E2E.KnowledgeSub

  T4 at a sub-log: on a log without the chain's bad events, V_I's acceptance with the answers of
  a sub-log gives every root signature claim a signature valid under the sub-log's answers.
-/

module

public import LeanVM.E2E.Knowledge
public import LeanVM.E2E.Rel

/-!
# Aggregate knowledge at a sub-log

T4 (`aggregate_knowledge_cache`) reads V_I's acceptance with the answers of the oracle's log `ℓ`
and gives every root signature claim a signature valid under `ℓ`'s answers. The per-key
reductions of T5 need the signature from what they see: V_I's own queries, a log `ℓK` whose
answers are `ℓ`'s (`LookSub (look ℓK) (look ℓ)`). The same induction gives it
(`aggregate_knowledge_sub`): V_I's checks at `ℓK` hold at `ℓ` (monotonicity, `LeanVM.E2E.Rel`),
so T1, T3 and the bad events run at `ℓ` as in T4; T2 runs at the oracle models of both logs (a
table check at `ℓK` passes at `ℓ`), and the directly held signatures of the model at `ℓK` are
valid under `ℓK`'s answers. DA claims stay backed by `ℓ`.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.EndToEnd.Blind LeanVM.Protocol.EndToEnd.Sound LeanVM.Protocol.Rom LeanVM.Node
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

/-- **A statement's claims are held directly, the signatures under a sub-log**: every
leanXMSS and leanSPHINCS claim by a signature valid under the answers of `ℓK`, every DA claim by
a matrix opening under the log `ℓ`'s answers (the guest's padding digests). -/
def HeldDirectSub (ℓK ℓ : Log) (s : NodeStatement) : Prop :=
  (∀ c ∈ s.claims.xmss, ∃ σ, xmssVerifyWith (look ℓK) c.1 c.2 σ = some true) ∧
    (∀ c ∈ s.claims.sphincs, ∃ σ, sphincsVerifyWith (look ℓK) c.1 c.2 σ = some true) ∧
    ∀ c ∈ s.claims.da, ∃ w : Da.Witness,
      w.OpensWith (look ℓ) Guest.B1.Main.daPadCell Guest.B1.Main.daPadRow c.1 c.2

section Induction

variable {ℓ : Log} {seed : Digest} {ip : IdealProof} {D : List Node}

/-- **Every node V_I checked at a sub-log holds its statement's claims directly, the signatures
under the sub-log** (T4's induction, `heldDirect_of_node`, at two logs). On a log `ℓ` without the
chain's bad events, for a log `ℓK` whose answers are `ℓ`'s and a set `D` of nodes each checked by
V_I with `ℓK`'s answers, its children in `D`: a node of `D` whose digest is the answer of `ℓ`'s
`n`-th entry, accepted by V°, with a statement of that digest whose deferred claim's bytecode
part holds, has its signature claims held by signatures valid under `ℓK` and its DA claims by
openings under `ℓ`. -/
theorem heldDirectSub_of_node {ℓK : Log}
    (hG : ∀ (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    (hGK : ∀ (rows : List BlakeRow) (h : TableOK (look ℓK) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓK h))
    (hbad : ¬ AggBad ℓ) (hsub : LookSub (look ℓK) (look ℓ))
    (hseed : fiatShamirIvWith (look ℓ) (bytecodeWords Guest.guest) = some seed)
    (hD : ∀ ν ∈ D, ∃ kids, nodeStep (look ℓK) Guest.guest seed ip ν = some (some kids) ∧
      ∀ κ ∈ kids, κ ∈ D) :
    ∀ (n : ℕ) (hn : n < ℓ.length) (π : Proof) (st : NodeStatement), (ℓ[n].2, π) ∈ D →
      statementDigestWith (look ℓ) seed st = some ℓ[n].2 →
      verifyBlindWith (look ℓ) (bytecodeWords Guest.guest) ℓ[n].2 π = some true →
      st.defer.BytecodeHolds (bytecodeWords Guest.guest) → HeldDirectSub ℓK ℓ st := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn π st hmem hsd hv hbh
  have hT1 : ¬ 1 ≤ pot anyCertBlind.D leanVmSeeds anyProgramBlind ℓ := fun h ↦ hbad (Or.inl h)
  have hF : ¬ Fail leanVmSeeds ℓ := fun h ↦ hbad (Or.inr (Or.inl h))
  have hB : ¬ BatchBad Guest.B1.Main.aggSeedD (bytecodeWords Guest.guest) ℓ :=
    fun h ↦ hbad (Or.inr (Or.inr (Or.inl h)))
  have hP : ¬ Pred (predOffset (bytecodeWords Guest.guest)) ℓ :=
    fun h ↦ hbad (Or.inr (Or.inr (Or.inr (Or.inr h))))
  -- T1 at the node.
  have hv1 : verifyBlindWith (look ℓ) (bytecodeWords (Guest.guest, inputOf ℓ[n].2).1)
      (EndToEnd.Complete.publicDigest (Guest.guest, inputOf ℓ[n].2).2) π = some true := by
    rw [publicDigest_inputOf]
    exact hv
  rcases blind_knowledge_cache' hF hv1 with hpot | hx
  · exact absurd hpot hT1
  -- What V_I checked at the node.
  obtain ⟨kids, hstep, hkids⟩ := hD _ hmem
  obtain ⟨layout, ρ, s, r, ht, w, W, root, hann, hs, hr, hsh, hW, hws, hroot, hrr, hcand⟩ :=
    nodeStep_some hstep
  obtain ⟨hadm, q, hq⟩ :=
    mem_blindCandidates_of_extractedBlind hF hv hann hs hr hsh hws (treeRootM_mono hsub hroot) hrr hx
  obtain ⟨t, htr, htab, hch⟩ := hcand q hq
  -- The candidate's execution, valid under the oracle model of its table (C5).
  obtain ⟨t', hrep, hvalid⟩ := execution_of_extractedBlind F₀ Guest.guest_sentinelSafe hadm hq.2
  obtain ⟨t'', hrun, hvalid'⟩ := haltingRunB_valid hrep hvalid
  have htt : t = t'' := by
    rw [candidateRun, haltingRunB_eq] at htr
    rw [htr] at hrun
    exact Option.some.inj hrun
  subst htt
  have hokK := tableOK_of_tableOKWith htab
  have hok := TableOK.mono hsub hokK
  have hvm := Guest.Value.validExecutionB_oracle hok hvalid'
  have hvmK := Guest.Value.validExecutionB_oracle hokK hvalid'
  -- T2 at both models.
  obtain ⟨hdig, hrel⟩ :=
    Guest.End.guest_knowledge_model_at _ (hG _ hok) (ip.frames (ℓ[n].2, π)) (inputOf ℓ[n].2) t hvm
  obtain ⟨-, hrelK⟩ :=
    Guest.End.guest_knowledge_model_at _ (hGK _ hokK) (ip.frames (ℓ[n].2, π)) (inputOf ℓ[n].2) t hvmK
  change statementDigestWith (look ℓ) _ _ = some _ at hdig
  change NodeRelWith (look ℓ) _ _ _ _ _ _ _ at hrel
  change NodeRelWith (look ℓK) _ _ _ _
    (Guest.End.decodeAt (Guest.Value.HashModel.oracle (t.blakeRows blakeFree) ℓ hok).sem
      (ip.frames (ℓ[n].2, π)) t.image).seed
    (Guest.End.decodeAt (Guest.Value.HashModel.oracle (t.blakeRows blakeFree) ℓ hok).sem
      (ip.frames (ℓ[n].2, π)) t.image).statement
    (Guest.End.decodeAt (Guest.Value.HashModel.oracle (t.blakeRows blakeFree) ℓ hok).sem
      (ip.frames (ℓ[n].2, π)) t.image).witness at hrelK
  rw [publicDigest_inputOf] at hdig
  -- The decoded statement is the node's.
  have hsh0 := hrel.1
  obtain ⟨hseq, hsteq⟩ := statement_eq_of_digest hF (hbh.1.1.trans hsh0.1.symm)
    (hbh.1.2.trans hsh0.2.symm) hsd hdig
  rw [← hseq, ← hsteq] at hrel hrelK
  change NodeRelWith (look ℓ) Guest.B1.Main.aggSeedD Guest.B1.Main.daPadCell Guest.B1.Main.daPadRow
    (bytecodeWords Guest.guest) seed st
    (Guest.End.decodeAt (Guest.Value.tableSem (t.blakeRows blakeFree)) (ip.frames (ℓ[n].2, π))
      t.image).witness at hrel
  change NodeRelWith (look ℓK) Guest.B1.Main.aggSeedD Guest.B1.Main.daPadCell
    Guest.B1.Main.daPadRow (bytecodeWords Guest.guest) seed st
    (Guest.End.decodeAt (Guest.Value.tableSem (t.blakeRows blakeFree)) (ip.frames (ℓ[n].2, π))
      t.image).witness at hrelK
  have hlen := length_decodeAt_children_lt (Guest.Value.tableSem (t.blakeRows blakeFree))
    (ip.frames (ℓ[n].2, π)) t.image
  generalize
    (Guest.End.decodeAt (Guest.Value.tableSem (t.blakeRows blakeFree)) (ip.frames (ℓ[n].2, π))
      t.image).witness = wit
    at hrel hrelK hch hlen
  obtain ⟨-, hchild, -, -, hDa, hbat⟩ := id hrel
  obtain ⟨-, -, hX, hS, -, -⟩ := id hrelK
  -- The offset of the node's last matrix coordinate is the guest's.
  have hP' :
      ¬ Pred (96 + 24 * (st.defer.bytecodePoint.length + st.defer.matrixPoint.length)) ℓ := by
    rw [hbh.1.1, hbh.1.2]
    rw [predOffset] at hP
    exact hP
  have hm : st.defer.matrixPoint ≠ [] := by
    intro he
    have := hbh.1.2
    rw [he, List.length_nil] at this
    exact absurd this (by unfold blake2sR1csLogSize; omega)
  -- The children hold their claims directly.
  have hkid : ∀ c ∈ wit.children, HeldDirectSub ℓK ℓ c.statement := by
    intro c hc
    obtain ⟨-, pc, hpc, hvd⟩ := hchild c hc
    have hbc := children_bytecodeHolds hB hrel hbh hlen c hc
    have hvb := verifyBlindWith_of_verifyDeferredWith hbc.1 hseed hvd
    obtain ⟨pc', hpc'K, hmemk⟩ := hch c hc
    have hpc' := statementDigestWith_mono hsub hpc'K
    rw [hpc, Option.some.injEq] at hpc'
    subst hpc'
    obtain ⟨i, hi, hci⟩ := exists_index_of_statementDigestWith hpc
    have hlt : i < n := by
      have hne : wit.children ≠ [] := List.ne_nil_of_mem hc
      simp only [hne, ↓reduceIte] at hbat
      obtain ⟨cs, hcs, hbw⟩ := hbat
      obtain ⟨cc, hcc, hccpi⟩ := childClaimsWith_mem hcs c hc pc hpc
      obtain ⟨sd, dd, -, -, hpi⟩ := statementDigestWith_eq_some hsd
      exact rank_lt_of_child hF hP' hpi hm hbw hcc hi hn (hci.trans hccpi.symm) rfl
    have hmemD := hkids _ hmemk
    rw [← hci] at hmemD hpc hvb
    exact ih i hlt hi c.proof c.statement hmemD hpc hvb hbc.2
  -- The node's claims.
  refine ⟨fun cl hcl ↦ ?_, fun cl hcl ↦ ?_, fun cl hcl ↦ ?_⟩
  · obtain ⟨hold, -, hheld⟩ := exists_of_forall₂_left hX cl hcl
    cases hold with
    | direct σ => exact ⟨σ, hheld⟩
    | child i =>
      obtain ⟨c, hci, hcl'⟩ := hheld
      exact (hkid c (List.mem_of_getElem? hci)).1 cl hcl'
  · obtain ⟨hold, -, hheld⟩ := exists_of_forall₂_left hS cl hcl
    cases hold with
    | direct σ => exact ⟨σ, hheld⟩
    | child i =>
      obtain ⟨c, hci, hcl'⟩ := hheld
      exact (hkid c (List.mem_of_getElem? hci)).2.1 cl hcl'
  · obtain ⟨hold, -, hheld⟩ := exists_of_forall₂_left hDa cl hcl
    cases hold with
    | direct w' => exact ⟨w', hheld⟩
    | child i =>
      obtain ⟨c, hci, hcl'⟩ := hheld
      exact (hkid c (List.mem_of_getElem? hci)).2.2 cl hcl'

end Induction

/-- **T4, aggregate knowledge, cache form, at a sub-log.** On an oracle log `ℓ` without the
chain's bad events (`AggBad`), for a log `ℓK` whose answers are `ℓ`'s: if V_I accepts the root
statement `s` with the idealized proof `ip` and every hash answered by `ℓK`, and the guest's open
callees are sound over the oracle models of both logs, then every leanXMSS and leanSPHINCS claim
of `s` has a signature valid under `ℓK`'s answers, and every DA claim of `s` is backed by codeword
rows whose commitment and vector digest `ℓ` answers (`DaBacked`, at the deployed padding
digests). -/
theorem aggregate_knowledge_sub {ℓ ℓK : Log}
    (hG : ∀ (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    (hGK : ∀ (rows : List BlakeRow) (h : TableOK (look ℓK) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓK h))
    (hbad : ¬ AggBad ℓ) (hsub : LookSub (look ℓK) (look ℓ)) {ip : IdealProof} {fuel : ℕ}
    {s : NodeStatement} (hv : idealVerify (look ℓK) Guest.guest ip fuel s = some true) :
    (∀ c ∈ s.claims.xmss, ∃ σ, xmssVerifyWith (look ℓK) c.1 c.2 σ = some true) ∧
    (∀ c ∈ s.claims.sphincs, ∃ σ, sphincsVerifyWith (look ℓK) c.1 c.2 σ = some true) ∧
    ∀ c ∈ s.claims.da, DaBacked ℓ deployedPads.1 deployedPads.2 c := by
  have hDA : ¬ DaBad deployedPads.1 ℓ := fun h ↦ hbad (Or.inr (Or.inr (Or.inr (Or.inl h))))
  unfold idealVerify at hv
  simp only [bind, Option.bind_eq_some_iff] at hv
  obtain ⟨seed, hseed, pi, hpi, b, hb, hv⟩ := hv
  cases b
  · simp [pure] at hv
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff] at hv
  obtain ⟨o, ho, hv⟩ := hv
  cases o
  · simp [pure] at hv
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hv
  obtain ⟨hout, hbh⟩ := outerChecksWith_some (outerChecksWith_mono hsub ho)
  obtain ⟨D, hroot, -, hD⟩ := closure_checked _ _ _ hv
  have hpi' := statementDigestWith_mono hsub hpi
  obtain ⟨n, hn, hnpi⟩ := exists_index_of_statementDigestWith hpi'
  subst hnpi
  have hheld := heldDirectSub_of_node hG hGK hbad hsub (fiatShamirIvWith_mono hsub hseed)
    (fun ν hν ↦ hD ν hν List.not_mem_nil) n hn ip.proof s (hroot _ List.mem_cons_self) hpi'
    (verifyBlindWith_mono hsub hb) hbh
  refine ⟨hheld.1, hheld.2.1, fun c hc ↦ ?_⟩
  obtain ⟨w, hw⟩ := hheld.2.2 c hc
  rw [deployedPads_eq] at hDA ⊢
  exact daBacked_of_not_daBad hDA hw (hout c hc)

end
end LeanVM.E2E
