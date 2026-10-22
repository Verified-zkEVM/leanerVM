/-
  LeanVM.E2E.Vis.Knowledge

  W-vis, P5: T4 at V_I's trace. On a log without T1's, W6's and E5's bad events and with T3's
  conclusion (`RankOK`), V_I's acceptance with the answers of its own trace gives every root
  signature claim a signature valid under the trace, and every root DA claim codeword rows the
  trace backs.
-/

module

public import LeanVM.E2E.KnowledgeSub
public import LeanVM.E2E.Reduction.Record
public import LeanVM.E2E.Vis.Rank

/-!
# T4 at V_I's trace (W-vis, P5)

The plan is `docs/roadmap/w-vis.md` §3 P5. Route B's extractor reads V_I's trace `tr` (the
second component of `gameRec`'s outcome), a log whose answers are the final log's
(`LookSub (look tr) (look ℓ)`).

* **The bad events** (`AggBadT`): T1's, W6's and E5's on the final log `ℓ`, as in `AggBad`. T3 is
  not an event here: the theorems take its conclusion, `RankOK ℓ` (`Vis/Rank.lean`), which P4
  derives from `PredS` and `FormatT` (`rankOK_of_vis`) and P6 assembles with `AggBadV`.
* **The induction** (`heldDirectTrace_of_node`): `heldDirectSub_of_node`'s, with the children's
  ranks from `RankOK`, and every claim, the DA ones too, held under the trace: T2 at the oracle
  model of the trace gives the trace's `NodeRelWith`, whose DA openings are answered by the trace.
* **The DA leg at the trace** (`daBacked_trace`): an opening and an outer check answered by the
  trace are answered by `ℓ` (monotonicity, `openingsWith_mono`, `vectorDigestOfWith_mono`), so
  on a log that is not DA-bad the witness's rows are codewords (`rows_codewords_of_not_daBad`,
  the argument of `daBacked_of_not_daBad` with its rows exposed); the commitment and the vector
  digest are the trace's.
* **T4 at the trace** (`aggregate_knowledge_trace`), and **in the game** (`gameRec_knows`): on
  a reachable outcome of `gameRec` where V_I accepted, with no `AggBadT` and `RankOK` on the final
  log, the root's claims are known under V_I's trace (`ClaimsKnownTrace`).
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.EndToEnd.Blind LeanVM.Protocol.EndToEnd.Sound LeanVM.Protocol.Rom LeanVM.Node
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

/- The enumeration of `Digest` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest

/-! ## The DA openings are monotone in the lookup -/

section Mono

variable {H H' : Bytes → Option Digest} (h : LookSub H H')
include h

/-- LeanDA's hash on a lookup is monotone in it. -/
theorem daHash_optLE (x : List UInt8) : OptLE (Da.daHash H x) (Da.daHash H' x) := by
  intro d hd
  simp only [Da.daHash, Option.map_eq_map, Option.map_eq_some_iff] at hd ⊢
  obtain ⟨e, he, rfl⟩ := hd
  exact ⟨e, h _ _ he, rfl⟩

/-- A DA tree's level is monotone in the lookup. -/
theorem treeLevelWith_optLE (nodes : List LeanDa.Digest) :
    OptLE (Da.treeLevelWith (Da.daHash H) nodes) (Da.treeLevelWith (Da.daHash H') nodes) :=
  rel_mapM (fun x x' ↦ OptLE x x') optLE_pure optLE_bind _ _ (fun _ ↦ daHash_optLE h _) _

/-- A DA tree's root is monotone in the lookup. -/
theorem treeRootFuel_optLE :
    ∀ (fuel : ℕ) (nodes : List LeanDa.Digest),
      OptLE (Da.treeRootFuel (Da.daHash H) fuel nodes) (Da.treeRootFuel (Da.daHash H') fuel nodes)
  | 0, _ => optLE_pure _
  | fuel + 1, nodes => by
    simp only [Da.treeRootFuel]
    split
    · exact optLE_pure _
    · exact optLE_bind _ _ _ _ (treeLevelWith_optLE h nodes) fun _ ↦ treeRootFuel_optLE fuel _

/-- **A DA commitment is monotone in the lookup.** -/
theorem commitCodewordsWith_optLE (pc pr : LeanDa.Digest) (rows : List (List K)) :
    OptLE (Da.commitCodewordsWith (Da.daHash H) pc pr rows)
      (Da.commitCodewordsWith (Da.daHash H') pc pr rows) := by
  unfold Da.commitCodewordsWith
  refine optLE_bind _ _ _ _ (rel_mapM (fun x x' ↦ OptLE x x') optLE_pure optLE_bind _ _
    (fun row ↦ optLE_bind _ _ _ _ (rel_mapM (fun x x' ↦ OptLE x x') optLE_pure optLE_bind _ _
      (fun _ ↦ daHash_optLE h _) _) fun _ ↦ daHash_optLE h _) _) fun _ ↦ ?_
  refine optLE_bind _ _ _ _ (treeRootFuel_optLE h _ _) fun _ ↦ ?_
  refine optLE_bind _ _ _ _ (rel_mapM (fun x x' ↦ OptLE x x') optLE_pure optLE_bind _ _
    (fun ij ↦ ?_) _) fun _ ↦ ?_
  · split
    · exact daHash_optLE h _
    · exact optLE_pure _
  · exact optLE_bind _ _ _ _ (treeRootFuel_optLE h _ _) fun _ ↦ daHash_optLE h _

/-- **A DA opening is monotone in the lookup.** -/
theorem openingsWith_mono {pc pr : LeanDa.Digest} {r v : Digest} {w : Da.Witness}
    (hw : w.OpensWith H pc pr r v) : w.OpensWith H' pc pr r v := by
  obtain ⟨h1, h2, h3, hcom, h5, hvd, horth⟩ := hw
  exact ⟨h1, h2, h3, commitCodewordsWith_optLE h pc pr _ _ hcom, h5,
    daHash_optLE h _ _ hvd, horth⟩

/-- **The vector digest of a root is monotone in the lookup.** -/
theorem vectorDigestOfWith_mono {r : Digest} {vd : LeanDa.Digest}
    (hv : Da.vectorDigestOfWith H r = some vd) : Da.vectorDigestOfWith H' r = some vd := by
  have hHD : ∀ x, OptLE (Da.daHash H x) (Da.daHash H' x) := daHash_optLE h
  revert hv vd
  change OptLE _ _
  unfold Da.vectorDigestOfWith Da.membershipVectorWith Da.membershipChallengesWith
  exact optLE_bind _ _ _ _ (rel_map (fun x x' ↦ OptLE x x') optLE_pure optLE_bind _ _ _
    (optLE_bind _ _ _ _ (hHD _) fun _ ↦ optLE_bind _ _ _ _ (hHD _) fun _ ↦
      optLE_bind _ _ _ _ (hHD _) fun _ ↦
        rel_squeezesWith (fun x x' ↦ OptLE x x') optLE_pure optLE_bind _ _ hHD _ _))
    fun _ ↦ hHD _

end Mono

/-! ## The DA leg at the trace -/

section Da

variable {ℓ : Log}

/-- **The DA leg's codeword argument, the rows exposed** (`daBacked_of_not_daBad`'s proof). On a
log that is not DA-bad, a witness opening a claim `(r, v)` with the log's answers, `r`
outer-checked with them, has codeword rows. -/
theorem rows_codewords_of_not_daBad {pc pr : LeanDa.Digest} (h : ¬ DaBad pc ℓ) {r v : Digest}
    {w : Da.Witness} (hw : w.OpensWith (look ℓ) pc pr r v)
    (hout : Da.vectorDigestOfWith (look ℓ) r = some (Da.toBytes v)) :
    ∀ row ∈ w.rows, rowFn row ∈ LeanDa.rsCode := by
  have hF : ¬ FailDA pc ℓ := fun hf ↦ h (Or.inl hf)
  have hH : ¬ DaHit pc ℓ := fun hh ↦ h (Or.inr hh)
  obtain ⟨h1, h2, h3, hcom, -, hvd, horth⟩ := hw
  set ρ := Da.toBytes r
  obtain ⟨d0, d1, d2, zs, hd0, hd1, hd2, hzs, hvd'⟩ := vectorDigestOfWith_eq_some hout
  -- The witness's vector is the dual codeword of the challenges.
  have hvec : w.vector = LeanDa.dualCodeword zs :=
    vecBytes_injective (daHash_inj_of_not_failDA hF hvd hvd')
  have hlen : zs.length = 14 := length_squeezesWith _ _ _ hzs
  set z : Fin 14 → E := fun i ↦ zs[(i : ℕ)]'(by omega)
  have hz : zs = List.ofFn z :=
    List.ext_getElem (by rw [List.length_ofFn, hlen]) fun i _ _ ↦ by
      simp only [List.getElem_ofFn, z]
  have hdual : w.vector = List.ofFn (LeanDa.dual z) := by
    rw [hvec, hz, LeanDa.dualCodeword_eq_dual]
  have hacc : ∀ row ∈ w.rows, Accepts zs row := fun row hrow ↦
    ⟨z, hz, by have := horth row hrow; rwa [hdual, getD_ofFn_dual] at this⟩
  -- Otherwise, a DA hit.
  by_contra hcw
  push Not at hcw
  refine hH ?_
  -- The anchor: the entry observing the root's second half.
  obtain ⟨i, hi, hei, hni⟩ := (look_eq_some_iff ℓ _ d2).mp hd2
  obtain ⟨j1, hj1, hej1, -⟩ := (look_eq_some_iff ℓ _ d1).mp hd1
  have hj1i : j1 < i := lt_of_chunk_da hF hj1 hi (Or.inl (by
    rw [hei, hej1, chunk0_append]))
  -- The root is completed in every prefix past the first observation.
  have hroot : ∀ m, j1 < m → m ≤ ℓ.length →
      DaRootOf (ℓ.take m) (digestBytes d1 ++ obsBlock ρ 1) ρ := by
    intro m hm hml
    refine ⟨d1, ℓ[j1], rfl, ?_, by rw [hej1, List.drop_left' (digestBytes_length d0)]⟩
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨by simp [hej1], j1, by simp; omega, by simp, fun j hj ↦ ?_⟩
    have := output_ne_da hF (by omega) hj1 hj
    simp only [List.getElem_take, hej1] at this ⊢
    simpa using this
  have hri : DaRootOf (ℓ.take i) ℓ[i].1 ρ := by
    rw [hei]; exact hroot i hj1i hi.le
  refine ⟨i, hi, ρ, zs, hri, by rw [hei]; exact hzs, ?_⟩
  -- The rows are committed before the anchor.
  obtain ⟨rt, c, hcol, hrc⟩ := commitCodewordsWith_eq_some hcom
  obtain ⟨vr, hvr, hρ⟩ := daHash_eq_some hrc
  obtain ⟨jr, hjr, hejr, hnjr⟩ := (look_eq_some_iff ℓ _ vr).mp hvr
  have hjri : jr < i := by
    by_contra hge
    push Not at hge
    refine not_daRootOf_of_not_failDA hF hjr ℓ[i].1 (mem_inputs_of_le_da hjr hge) ?_
    rw [hejr, ← hρ, hei]
    exact hroot jr (by omega) hjr.le
  have hrc' : Da.daHash (look (ℓ.take i)) (LeanDa.pairBytes rt c) = some ρ := by
    rw [Da.daHash, look_take_of_first hjr hejr hnjr hjri]
    simp [hρ]
  exact ⟨w.rows, ⟨⟨h1, h2, h3⟩, rt, c, colTree_take hF hi.le hrc' hcol, hrc'⟩, hcw, hacc⟩

/-- **A DA claim opened and outer-checked under the trace is backed by the trace**, on a final
log that is not DA-bad and whose answers extend the trace's. -/
theorem daBacked_trace {ℓK : Log} {pc pr : LeanDa.Digest} (h : ¬ DaBad pc ℓ)
    (hsub : LookSub (look ℓK) (look ℓ)) {r v : Digest} {w : Da.Witness}
    (hw : w.OpensWith (look ℓK) pc pr r v)
    (hout : Da.vectorDigestOfWith (look ℓK) r = some (Da.toBytes v)) : DaBacked ℓK pc pr (r, v) := by
  have hcw := rows_codewords_of_not_daBad h (openingsWith_mono hsub hw)
    (vectorDigestOfWith_mono hsub hout)
  obtain ⟨h1, h2, h3, hcom, -, -, -⟩ := hw
  refine ⟨w.rows, h1, h2, fun row hrow ↦ ⟨h3 row hrow, ?_⟩, hcom, hout⟩
  have hmem : rowFn row ∈ (LeanDa.rsCode : Set LeanDa.Row) := hcw row hrow
  rw [← LeanDa.range_encodeRow] at hmem
  obtain ⟨p, hp⟩ := hmem
  exact ⟨p, hp.symm⟩

end Da

/-! ## The bad events and the induction -/

/-- **The bad events of T4 at the trace, on the final log `ℓ`**: T1's (V°'s certificate's
potential at least one, or a failure), W6's (the batching from the baked start), E5's (DA at the
deployed cell padding). T3's is replaced by its conclusion, `RankOK`. -/
def AggBadT (ℓ : Log) : Prop :=
  1 ≤ pot anyCertBlind.D leanVmSeeds anyProgramBlind ℓ ∨ Fail leanVmSeeds ℓ ∨
    BatchBad Guest.B1.Main.aggSeedD (bytecodeWords Guest.guest) ℓ ∨ DaBad deployedPads.1 ℓ

section Induction

variable {ℓ : Log} {seed : Digest} {ip : IdealProof} {D : List Node}

/-- **Every node V_I checked at the trace holds its statement's claims directly under the
trace** (T4's induction at V_I's trace). On a log `ℓ` without T1's and W6's bad events and with
T3's conclusion (`RankOK ℓ`), for a log `ℓK` whose answers are `ℓ`'s and a set `D` of nodes each
checked by V_I with `ℓK`'s answers, its children in `D`: a node of `D` whose digest is the
answer of `ℓ`'s `n`-th entry, accepted by V°, with a statement of that digest whose deferred
claim's bytecode part holds, has its claims held directly under `ℓK`: its signature claims by
signatures valid under `ℓK`, its DA claims by openings under `ℓK`. -/
theorem heldDirectTrace_of_node {ℓK : Log}
    (hG : ∀ (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    (hGK : ∀ (rows : List BlakeRow) (h : TableOK (look ℓK) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓK h))
    (hT1 : ¬ 1 ≤ pot anyCertBlind.D leanVmSeeds anyProgramBlind ℓ) (hF : ¬ Fail leanVmSeeds ℓ)
    (hB : ¬ BatchBad Guest.B1.Main.aggSeedD (bytecodeWords Guest.guest) ℓ) (hrank : RankOK ℓ)
    (hsub : LookSub (look ℓK) (look ℓ))
    (hseed : fiatShamirIvWith (look ℓ) (bytecodeWords Guest.guest) = some seed)
    (hD : ∀ ν ∈ D, ∃ kids, nodeStep (look ℓK) Guest.guest seed ip ν = some (some kids) ∧
      ∀ κ ∈ kids, κ ∈ D) :
    ∀ (n : ℕ) (hn : n < ℓ.length) (π : Proof) (st : NodeStatement), (ℓ[n].2, π) ∈ D →
      statementDigestWith (look ℓ) seed st = some ℓ[n].2 →
      verifyBlindWith (look ℓ) (bytecodeWords Guest.guest) ℓ[n].2 π = some true →
      st.defer.BytecodeHolds (bytecodeWords Guest.guest) → HeldDirect ℓK st := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn π st hmem hsd hv hbh
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
  obtain ⟨-, hchild, -, -, -, hbat⟩ := id hrel
  obtain ⟨-, -, hX, hS, hDa, -⟩ := id hrelK
  -- The offset of the node's last matrix coordinate is the guest's.
  have ho : 96 + 24 * (st.defer.bytecodePoint.length + st.defer.matrixPoint.length) =
      predOffset (bytecodeWords Guest.guest) := by
    rw [hbh.1.1, hbh.1.2, predOffset]
  have hm : st.defer.matrixPoint ≠ [] := by
    intro he
    have := hbh.1.2
    rw [he, List.length_nil] at this
    exact absurd this (by unfold blake2sR1csLogSize; omega)
  -- The children hold their claims directly.
  have hkid : ∀ c ∈ wit.children, HeldDirect ℓK c.statement := by
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
      exact hrank ho hseed hpi hm hbw hcc hi hn (hci.trans hccpi.symm) rfl
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

/-! ## T4 at the trace -/

/-- **The aggregate's claims are known under V_I's trace `tr`**: every leanXMSS and leanSPHINCS
claim of `s` by a signature valid under the trace's answers, every DA claim backed by the trace
(`DaBacked`, at the deployed padding digests). -/
def ClaimsKnownTrace (tr : Log) (s : NodeStatement) : Prop :=
  (∀ c ∈ s.claims.xmss, ∃ σ, xmssVerifyWith (look tr) c.1 c.2 σ = some true) ∧
    (∀ c ∈ s.claims.sphincs, ∃ σ, sphincsVerifyWith (look tr) c.1 c.2 σ = some true) ∧
    ∀ c ∈ s.claims.da, DaBacked tr deployedPads.1 deployedPads.2 c

/-- **T4, aggregate knowledge, at V_I's trace.** On an oracle log `ℓ` without T1's, W6's and E5's
bad events and with T3's conclusion (`RankOK ℓ`), for a log `ℓK` whose answers are `ℓ`'s: if V_I
accepts the root statement `s` with the idealized proof `ip` and every hash answered by `ℓK`, and
the guest's open callees are sound over the oracle models of both logs, then every leanXMSS and
leanSPHINCS claim of `s` has a signature valid under `ℓK`'s answers, and every DA claim of `s` is
backed by codeword rows whose commitment and vector digest `ℓK` answers. -/
theorem aggregate_knowledge_trace {ℓ ℓK : Log}
    (hG : ∀ (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    (hGK : ∀ (rows : List BlakeRow) (h : TableOK (look ℓK) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓK h))
    (hT1 : ¬ 1 ≤ pot anyCertBlind.D leanVmSeeds anyProgramBlind ℓ) (hF : ¬ Fail leanVmSeeds ℓ)
    (hB : ¬ BatchBad Guest.B1.Main.aggSeedD (bytecodeWords Guest.guest) ℓ)
    (hDA : ¬ DaBad deployedPads.1 ℓ) (hrank : RankOK ℓ) (hsub : LookSub (look ℓK) (look ℓ))
    {ip : IdealProof} {fuel : ℕ} {s : NodeStatement}
    (hv : idealVerify (look ℓK) Guest.guest ip fuel s = some true) :
    (∀ c ∈ s.claims.xmss, ∃ σ, xmssVerifyWith (look ℓK) c.1 c.2 σ = some true) ∧
    (∀ c ∈ s.claims.sphincs, ∃ σ, sphincsVerifyWith (look ℓK) c.1 c.2 σ = some true) ∧
    ∀ c ∈ s.claims.da, DaBacked ℓK deployedPads.1 deployedPads.2 c := by
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
  obtain ⟨hout, hbh⟩ := outerChecksWith_some ho
  obtain ⟨D, hroot, -, hD⟩ := closure_checked _ _ _ hv
  have hpi' := statementDigestWith_mono hsub hpi
  obtain ⟨n, hn, hnpi⟩ := exists_index_of_statementDigestWith hpi'
  subst hnpi
  have hheld := heldDirectTrace_of_node hG hGK hT1 hF hB hrank hsub
    (fiatShamirIvWith_mono hsub hseed) (fun ν hν ↦ hD ν hν List.not_mem_nil) n hn ip.proof s
    (hroot _ List.mem_cons_self) hpi' (verifyBlindWith_mono hsub hb) hbh
  refine ⟨hheld.1, hheld.2.1, fun c hc ↦ ?_⟩
  obtain ⟨w, hw⟩ := hheld.2.2 c hc
  rw [deployedPads_eq] at hDA ⊢
  exact daBacked_trace hDA hsub hw (hout c hc)

/-- **T4 at the trace, from `¬ AggBadT`.** -/
theorem aggregate_knowledge_trace_of_not_aggBadT {ℓ ℓK : Log}
    (hG : ∀ (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    (hGK : ∀ (rows : List BlakeRow) (h : TableOK (look ℓK) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓK h))
    (hbad : ¬ AggBadT ℓ) (hrank : RankOK ℓ) (hsub : LookSub (look ℓK) (look ℓ))
    {ip : IdealProof} {fuel : ℕ} {s : NodeStatement}
    (hv : idealVerify (look ℓK) Guest.guest ip fuel s = some true) : ClaimsKnownTrace ℓK s :=
  aggregate_knowledge_trace hG hGK (fun h ↦ hbad (Or.inl h)) (fun h ↦ hbad (Or.inr (Or.inl h)))
    (fun h ↦ hbad (Or.inr (Or.inr (Or.inl h)))) (fun h ↦ hbad (Or.inr (Or.inr (Or.inr h))))
    hrank hsub hv

/-! ## In the game with V_I's trace -/

section Game

variable {nx ns : ℕ} [Sphincs.Params]

/-- **On `gameRec`, a good log gives the trace the claims.** On a reachable outcome of the game
with V_I's trace where V_I accepted, with no `AggBadT` and with `RankOK` on the final log, every
claim of the root statement is known under V_I's trace, if the guest's open callees are sound over
every oracle model of every log. -/
theorem gameRec_knows
    (hG : ∀ (ℓ : Log) (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    {fuel budget : ℕ} {A : GameAdversary nx ns} {p : (GameOutcome nx ns × Log) × Log}
    (hp : p ∈ support (gameRec Guest.guest fuel budget A)) (ha : p.1.1.accepted = true)
    (hbad : ¬ AggBadT p.2) (hrank : RankOK p.2) : ClaimsKnownTrace p.1.2 p.1.1.statement := by
  obtain ⟨hsub, hacc⟩ := gameRec_trace hp
  exact aggregate_knowledge_trace_of_not_aggBadT (hG p.2) (hG p.1.2) hbad hrank hsub.lookSub
    (hacc ha)

end Game

end
end LeanVM.E2E
