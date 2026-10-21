/-
  LeanVM.E2E.Knowledge

  The aggregate knowledge theorem in cache form (T4 of `docs/roadmap/e2e-security.md`): on an
  oracle log without the chain's bad events, V_I's acceptance of a root statement gives every
  leanXMSS and leanSPHINCS claim a signature valid under the log's answers, and every DA claim
  codeword rows the log backs.
-/

module

public import LeanVM.E2E.Knowledge.Node
public import LeanVM.E2E.Termination
public import LeanVM.E2E.Da
public import LeanVM.Guest.Binding
public import LeanVM.Guest.B1.Da.Link

/-!
# Aggregate knowledge (T4), cache form

**The statement** (`aggregate_knowledge_cache`). Let `ℓ` be the oracle's log, with none of the
bad events (`AggBad`):

* T1's: V°'s certificate's potential at least one, or a failure of the log (`Fail leanVmSeeds`);
* W6's: the batching's bad event from the guest's baked start (`BatchBad aggSeedD`);
* E5's: the DA bad event at the deployed cell padding (`DaBad`);
* T3's: a prediction of a batching's last challenge at the guest's offset
  (`Pred (predOffset bytecode)`).

If V_I accepts a root statement with every hash answered by `look ℓ`, and the guest's open
callees are sound over every hash model (`∀ M, Located.GuestHypsM M`, which W2 proves), then every
leanXMSS claim `(pk, m)` of the root has a signature `σ` with `xmssVerifyWith (look ℓ) pk m σ =
some true`, likewise every leanSPHINCS claim, and every DA claim is `DaBacked ℓ` at the deployed
padding digests.

**The proof**: an induction over the nodes V_I checked (`closure_checked`), on the rank of a
node, the log index of its statement digest's entry (T3). At a node `(pi, π)` with statement
`s` whose digest is `pi`, accepted by V° and with its deferred claim's bytecode part true:

1. T1 (`blind_knowledge_cache'`): the extractor reading the log finds a stack satisfying the
   relation without Flock, which is one of the candidates V_I enumerated
   (`mem_blindCandidates_of_extractedBlind`).
2. V_I ran that candidate under the Flock-blind semantics (`execution_of_extractedBlind`, the
   execution is valid) and checked its table (`tableOK_of_tableOKWith`); so the execution is
   valid under the oracle model of its table (C5, `validExecutionB_oracle`).
3. T2 (`guest_knowledge_model`) at that model: the decoded statement's digest is `pi`, and the
   decoded witness holds it (`NodeRelWith (look ℓ)`). Without collisions the decoded seed and
   statement are V_I's (`statement_eq_of_digest`).
4. A claim held directly is a signature valid under the log, or a DA opening; a claim held by a
   child is a claim of the child's statement. Each child is a node V_I queued
   (`nodeStep_some`), accepted by V° (its deferred proof, its bytecode claim true by W6's
   `children_bytecodeHolds`, `verifyBlindWith_of_verifyDeferredWith`), of smaller rank
   (`rank_lt_of_child`): by induction its claims are held directly.
5. At the root, a DA claim's opening and the outer check's vector digest give `DaBacked`
   (`daBacked_of_not_daBad`); a child's DA claims are the root's (copied down, design D7), so
   the root's outer check covers them.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.EndToEnd.Blind LeanVM.Protocol.EndToEnd.Sound LeanVM.Protocol.Rom LeanVM.Node
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

/-! ## The statement digest binds, on a log without collisions -/

section Binding

open LeanVM.Guest.Binding

/-- The statement's bytes determine the seed, the two nested digests and, at fixed point
lengths, the deferred claim. -/
theorem stmtInput_inj {seed sd dd seed' sd' dd' : Digest} {d d' : DeferredClaim}
    (hb : d.bytecodePoint.length = d'.bytecodePoint.length)
    (hm : d.matrixPoint.length = d'.matrixPoint.length)
    (h : stmtInput seed sd dd d = stmtInput seed' sd' dd' d') :
    seed = seed' ∧ sd = sd' ∧ dd = dd' ∧ d = d' := by
  have hc : d.cells.length = d'.cells.length := by
    simp [DeferredClaim.cells, hb, hm]
  have hpad : (d.cells ++ if d.cells.length % 2 = 1 then [0] else []).length =
      (d'.cells ++ if d'.cells.length % 2 = 1 then [0] else []).length := by
    rw [List.length_append, List.length_append, hc]
  have hlen : (digestBytes seed ++ digestBytes sd ++ digestBytes dd ++
      (d.cells ++ if d.cells.length % 2 = 1 then [0] else []).flatMap eBytes).length =
      (digestBytes seed' ++ digestBytes sd' ++ digestBytes dd' ++
      (d'.cells ++ if d'.cells.length % 2 = 1 then [0] else []).flatMap eBytes).length := by
    simp only [List.length_append, length_digestBytes, length_flatMap_const length_eBytes]
    rw [← List.length_append, ← List.length_append, hpad]
  unfold stmtInput at h
  obtain ⟨hB, -⟩ := List.append_inj h hlen
  obtain ⟨h123, h4⟩ := List.append_inj hB (by simp [length_digestBytes])
  obtain ⟨h12, h3⟩ := List.append_inj h123 (by simp [length_digestBytes])
  obtain ⟨h1, h2⟩ := List.append_inj h12 (by simp [length_digestBytes])
  have hp := flatMap_inj (n := 24) (by decide) length_eBytes (fun _ _ ↦ eBytes_inj) h4
  obtain ⟨hcells, -⟩ := List.append_inj hp hc
  exact ⟨digestBytes_inj h1, digestBytes_inj h2, digestBytes_inj h3, cells_inj hb hm hcells⟩

variable {X : Type} {σ : Seeds X} {ℓ : Log}

/-- **On a log without failure, a statement digest binds** the seed and the statement, at
deferred points of equal lengths. -/
theorem statement_eq_of_digest (hf : ¬ Fail σ ℓ) {seed seed' pi : Digest}
    {s s' : NodeStatement}
    (hb : s.defer.bytecodePoint.length = s'.defer.bytecodePoint.length)
    (hm : s.defer.matrixPoint.length = s'.defer.matrixPoint.length)
    (h : statementDigestWith (look ℓ) seed s = some pi)
    (h' : statementDigestWith (look ℓ) seed' s' = some pi) : seed = seed' ∧ s = s' := by
  have hH := answersInj_look hf
  obtain ⟨sd, dd, hsd, hdd, hpi⟩ := statementDigestWith_eq_some h
  obtain ⟨sd', dd', hsd', hdd', hpi'⟩ := statementDigestWith_eq_some h'
  obtain ⟨rfl, rfl, rfl, hd⟩ := stmtInput_inj hb hm (hH _ _ _ hpi hpi')
  simp only [signersDigestWith, xmssListDigestWith, sphincsListDigestWith, bind,
    Option.bind_eq_some_iff] at hsd hsd'
  obtain ⟨x, hx, y, hy, hxy⟩ := hsd
  obtain ⟨x', hx', y', hy', hxy'⟩ := hsd'
  obtain ⟨h1, h2⟩ := List.append_inj (hH _ _ _ hxy hxy')
    (by rw [length_digestBytes, length_digestBytes])
  obtain rfl := digestBytes_inj h1
  obtain rfl := digestBytes_inj h2
  have hX : s.claims.xmss = s'.claims.xmss := xmssPreimage_inj (hH _ _ _ hx hx')
  have hS : s.claims.sphincs = s'.claims.sphincs := sphincsPreimage_inj (hH _ _ _ hy hy')
  have hD : s.claims.da = s'.claims.da := daPreimage_inj (hH _ _ _ hdd hdd')
  refine ⟨rfl, ?_⟩
  obtain ⟨⟨x1, s1, d1⟩, e1⟩ := s
  obtain ⟨⟨x2, s2, d2⟩, e2⟩ := s'
  simp only at hX hS hD hd
  subst hX hS hD hd
  rfl

end Binding

/-! ## Facts the induction reads -/

/-- **A child's claims under its digest**: the batched claims list every child under its
statement's answered digest. -/
theorem childClaimsWith_mem {H : Bytes → Option Digest} {seed : Digest} :
    ∀ {children : List Child} {cs : List ChildClaims}, childClaimsWith H seed children = some cs →
      ∀ c ∈ children, ∀ pc, statementDigestWith H seed c.statement = some pc →
        ∃ cc ∈ cs, cc.publicInput = pc
  | [], cs, _, c, hc, _, _ => absurd hc List.not_mem_nil
  | c :: children, cs, h, c', hc', pc, hpc => by
    simp only [childClaimsWith, List.mapM_cons, bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Option.map_eq_map, Option.map_eq_some_iff] at h
    obtain ⟨cc, ⟨pi, hpi, rfl⟩, ccs, hccs, rfl⟩ := h
    rcases List.mem_cons.mp hc' with rfl | hc'
    · rw [hpi, Option.some.injEq] at hpc
      exact ⟨_, List.mem_cons_self, hpc⟩
    · obtain ⟨cc', hcc', he⟩ := childClaimsWith_mem hccs c' hc' pc hpc
      exact ⟨cc', List.mem_cons_of_mem _ hcc', he⟩

/-- The guest's decoded children are fewer than `2^18`: their count is a logarithm below the
table's size. -/
theorem length_decodeB_children_lt (S : BlakeSem) {κ : ℕ} (L : MemImage κ) :
    (Guest.End.decodeB S L).witness.children.length < 2 ^ 64 - 1 := by
  have hg : ∀ x : E, Guest.B1.Main.gLog x < 2 ^ 18 := by
    intro x
    unfold Guest.B1.Main.gLog
    cases hf : (List.range (2 ^ 18)).find? (fun n ↦ decide (gen ^ n = x)) with
    | none => simp
    | some n =>
      simpa using List.mem_range.mp (List.mem_of_find?_eq_some hf)
  simp only [Guest.End.decodeB, Guest.B1.Main.decWit, Guest.B1.Main.decKids, List.length_map,
    List.length_range]
  exact (hg _).trans (by norm_num)

/-- **The outer checks, answered**: every DA claim's vector digest, answered, is its root's,
and the deferred claim's bytecode part holds. -/
theorem outerChecksWith_some {H : Bytes → Option Digest} {prog : Program} {s : NodeStatement}
    (h : outerChecksWith H prog s = some true) :
    (∀ c ∈ s.claims.da, Da.vectorDigestOfWith H c.1 = some (Da.toBytes c.2)) ∧
      s.defer.BytecodeHolds (bytecodeWords prog) := by
  unfold outerChecksWith at h
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Bool.and_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨ok, hok, rfl, hb⟩ := h
  refine ⟨fun c hc ↦ ?_, hb⟩
  have := allM_some_true hok c hc
  simp only [Option.bind_eq_some_iff, Option.some.injEq, decide_eq_true_eq] at this
  obtain ⟨v, hv, he⟩ := this
  rw [hv, he]

/-- The two executions of a memory image under a semantics are one. -/
theorem haltingRunB_eq (S : BlakeSem) (prog : Program) {κ : ℕ} (image : MemImage κ) :
    haltingRunB S prog image = EndToEnd.Blind.haltingRunB S prog image := rfl

/-- An answered digest is the answer of an entry of the log. -/
theorem exists_index_of_look {ℓ : Log} {x : Bytes} {v : Digest} (h : look ℓ x = some v) :
    ∃ (i : ℕ) (hi : i < ℓ.length), ℓ[i].2 = v := by
  obtain ⟨i, hi, hei, -⟩ := (look_eq_some_iff ℓ x v).mp h
  exact ⟨i, hi, by rw [hei]⟩

/-- An answered statement digest is the answer of an entry of the log. -/
theorem exists_index_of_statementDigestWith {ℓ : Log} {seed pi : Digest} {s : NodeStatement}
    (h : statementDigestWith (look ℓ) seed s = some pi) :
    ∃ (i : ℕ) (hi : i < ℓ.length), ℓ[i].2 = pi := by
  obtain ⟨_, _, _, _, hpi⟩ := statementDigestWith_eq_some h
  exact exists_index_of_look hpi

/-! ## The bad events and the statement -/

/-- **The bad events of the chain on the log `ℓ`** for the guest: T1's (V°'s certificate's
potential at least one, or a failure), W6's (the batching from the baked start), E5's (DA at the
deployed cell padding), T3's (a prediction at the offset of the last matrix coordinate). -/
def AggBad (ℓ : Log) : Prop :=
  1 ≤ pot anyCertBlind.D leanVmSeeds anyProgramBlind ℓ ∨ Fail leanVmSeeds ℓ ∨
    BatchBad Guest.B1.Main.aggSeedD (bytecodeWords Guest.guest) ℓ ∨
    DaBad deployedPads.1 ℓ ∨ Pred (predOffset (bytecodeWords Guest.guest)) ℓ

/-- **A statement's claims are held directly** under the log `ℓ`: every leanXMSS and leanSPHINCS
claim by a signature valid under the log's answers, every DA claim by a matrix opening under the
log's answers (the guest's padding digests). -/
def HeldDirect (ℓ : Log) (s : NodeStatement) : Prop :=
  (∀ c ∈ s.claims.xmss, ∃ σ, xmssVerifyWith (look ℓ) c.1 c.2 σ = some true) ∧
    (∀ c ∈ s.claims.sphincs, ∃ σ, sphincsVerifyWith (look ℓ) c.1 c.2 σ = some true) ∧
    ∀ c ∈ s.claims.da, ∃ w : Da.Witness,
      w.OpensWith (look ℓ) Guest.B1.Main.daPadCell Guest.B1.Main.daPadRow c.1 c.2

/-! ## The induction over the nodes -/

section Induction

variable {ℓ : Log} {seed : Digest} {ip : IdealProof} {D : List Node}

/-- The deployed DA padding digests are the guest's. -/
theorem deployedPads_eq : deployedPads = (Guest.B1.Main.daPadCell, Guest.B1.Main.daPadRow) := by
  rw [deployedPads, Guest.B1.Digest.paddingCell_eq, Guest.B1.Digest.paddingRow_eq]

/-- **Every node V_I checked holds its statement's claims directly** (the induction of T4). On a
log without the chain's bad events, for a set `D` of nodes each checked by V_I with its children
in `D` (`closure_checked`), from the guest's seed: a node of `D` whose digest is the answer of
the log's `n`-th entry, accepted by V°, with a statement of that digest whose deferred claim's
bytecode part holds, has its statement's claims held directly. By strong induction on `n`: the
node's children have smaller ranks (T3). -/
theorem heldDirect_of_node
    (hG : ∀ (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    (hbad : ¬ AggBad ℓ)
    (hseed : fiatShamirIvWith (look ℓ) (bytecodeWords Guest.guest) = some seed)
    (hD : ∀ ν ∈ D, ∃ kids, nodeStep (look ℓ) Guest.guest seed ip ν = some (some kids) ∧
      ∀ κ ∈ kids, κ ∈ D) :
    ∀ (n : ℕ) (hn : n < ℓ.length) (π : Proof) (st : NodeStatement), (ℓ[n].2, π) ∈ D →
      statementDigestWith (look ℓ) seed st = some ℓ[n].2 →
      verifyBlindWith (look ℓ) (bytecodeWords Guest.guest) ℓ[n].2 π = some true →
      st.defer.BytecodeHolds (bytecodeWords Guest.guest) → HeldDirect ℓ st := by
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
    mem_blindCandidates_of_extractedBlind hF hv hann hs hr hsh hws hroot hrr hx
  obtain ⟨t, htr, htab, hch⟩ := hcand q hq
  -- The candidate's execution, valid under the oracle model of its table (C5).
  obtain ⟨t', hrep, hvalid⟩ := execution_of_extractedBlind F₀ Guest.guest_sentinelSafe hadm hq.2
  obtain ⟨t'', hrun, hvalid'⟩ := haltingRunB_valid hrep hvalid
  have htt : t = t'' := by
    rw [candidateRun, haltingRunB_eq] at htr
    rw [htr] at hrun
    exact Option.some.inj hrun
  subst htt
  have hok := tableOK_of_tableOKWith htab
  have hvm := Guest.Value.validExecutionB_oracle hok hvalid'
  -- T2 at that model.
  obtain ⟨hdig, hrel⟩ := Guest.End.guest_knowledge_model _ (hG _ hok) (inputOf ℓ[n].2) t hvm
  change statementDigestWith (look ℓ) _ _ = some _ at hdig
  change NodeRelWith (look ℓ) _ _ _ _ _ _ _ at hrel
  rw [publicDigest_inputOf] at hdig
  -- The decoded statement is the node's.
  have hsh0 := hrel.1
  obtain ⟨hseq, hsteq⟩ := statement_eq_of_digest hF (hbh.1.1.trans hsh0.1.symm)
    (hbh.1.2.trans hsh0.2.symm) hsd hdig
  rw [← hseq, ← hsteq] at hrel
  change NodeRelWith (look ℓ) Guest.B1.Main.aggSeedD Guest.B1.Main.daPadCell Guest.B1.Main.daPadRow
    (bytecodeWords Guest.guest) seed st
    (Guest.End.decodeB (Guest.Value.tableSem (t.blakeRows blakeFree)) t.image).witness at hrel
  have hlen := length_decodeB_children_lt (Guest.Value.tableSem (t.blakeRows blakeFree)) t.image
  generalize
    (Guest.End.decodeB (Guest.Value.tableSem (t.blakeRows blakeFree)) t.image).witness = wit
    at hrel hch hlen
  obtain ⟨-, hchild, hX, hS, hDa, hbat⟩ := id hrel
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
  have hkid : ∀ c ∈ wit.children, HeldDirect ℓ c.statement := by
    intro c hc
    obtain ⟨-, pc, hpc, hvd⟩ := hchild c hc
    have hbc := children_bytecodeHolds hB hrel hbh hlen c hc
    have hvb := verifyBlindWith_of_verifyDeferredWith hbc.1 hseed hvd
    obtain ⟨pc', hpc', hmemk⟩ := hch c hc
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

/-! ## T4 -/

/-- **T4, aggregate knowledge, cache form.** On an oracle log `ℓ` without the chain's bad events
(`AggBad`: T1's potential or failure, W6's batching, E5's DA, T3's prediction), if V_I accepts
the root statement `s` with the idealized proof `ip` and every hash answered by the log, and the
guest's open callees are sound over the log's oracle models (`HashModel.oracle rows ℓ h`, every
table the log passes), then every leanXMSS and leanSPHINCS claim of `s` has a signature valid
under the log's answers, and every DA claim of `s` is backed by codeword rows whose commitment
and vector digest the log answers (`DaBacked`, at the deployed padding digests). -/
theorem aggregate_knowledge_cache {ℓ : Log}
    (hG : ∀ (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    (hbad : ¬ AggBad ℓ) {ip : IdealProof} {fuel : ℕ} {s : NodeStatement}
    (hv : idealVerify (look ℓ) Guest.guest ip fuel s = some true) :
    (∀ c ∈ s.claims.xmss, ∃ σ, xmssVerifyWith (look ℓ) c.1 c.2 σ = some true) ∧
    (∀ c ∈ s.claims.sphincs, ∃ σ, sphincsVerifyWith (look ℓ) c.1 c.2 σ = some true) ∧
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
  obtain ⟨hout, hbh⟩ := outerChecksWith_some ho
  obtain ⟨D, hroot, -, hD⟩ := closure_checked _ _ _ hv
  obtain ⟨n, hn, hnpi⟩ := exists_index_of_statementDigestWith hpi
  subst hnpi
  have hheld := heldDirect_of_node hG hbad hseed (fun ν hν ↦ hD ν hν List.not_mem_nil) n hn
    ip.proof s (hroot _ List.mem_cons_self) hpi hb hbh
  refine ⟨hheld.1, hheld.2.1, fun c hc ↦ ?_⟩
  obtain ⟨w, hw⟩ := hheld.2.2 c hc
  rw [deployedPads_eq] at hDA ⊢
  exact daBacked_of_not_daBad hDA hw (hout c hc)

/-- **T4, with the callees sound over every hash model** (what W2 proves). -/
theorem aggregate_knowledge_cache' (hG : ∀ M, Guest.Located.GuestHypsM M) {ℓ : Log}
    (hbad : ¬ AggBad ℓ) {ip : IdealProof} {fuel : ℕ} {s : NodeStatement}
    (hv : idealVerify (look ℓ) Guest.guest ip fuel s = some true) :
    (∀ c ∈ s.claims.xmss, ∃ σ, xmssVerifyWith (look ℓ) c.1 c.2 σ = some true) ∧
    (∀ c ∈ s.claims.sphincs, ∃ σ, sphincsVerifyWith (look ℓ) c.1 c.2 σ = some true) ∧
    ∀ c ∈ s.claims.da, DaBacked ℓ deployedPads.1 deployedPads.2 c :=
  aggregate_knowledge_cache (fun _ _ ↦ hG _) hbad hv

/-! ## In the game -/

section Game

variable {nx ns : ℕ} [Sphincs.Params]

/-- **T1's bad event in the game**: V°'s certificate's potential at least one, or a failure of
the log, with probability at most `Q (2^-128 + failBound Q)`, for a game with at most `Q` hash
queries (`romSound`'s bound, in the game's engine). -/
theorem prEvent_game_blindBad_le (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns)
    (Q : ℕ) (hQ : IsQueryBoundP (gameComp guest fuel budget A) IsHash Q) :
    Pr{let z ← game guest fuel budget A}[1 ≤ pot anyCertBlind.D leanVmSeeds anyProgramBlind z.2 ∨
      Fail leanVmSeeds z.2] ≤ Q * (εLean + failBound leanVmSeeds Q) := by
  have h := prEvent_game_le_of_freshStepBelow
    (Φ := pot anyCertBlind.D leanVmSeeds anyProgramBlind) (δ := εLean + failBound leanVmSeeds Q) Q
    (fun ℓ t hℓ ht ↦ by
      refine (step_ineq anyCertBlind anyCertBlind_bound ℓ t ht).trans
        (add_le_add le_rfl (add_le_add le_rfl ?_))
      rw [failBound, card_digest, Nat.cast_pow, Nat.cast_ofNat]
      refine ENNReal.div_le_div_right ?_ _
      exact_mod_cast Nat.mul_le_mul_left _ hℓ)
    guest fuel budget A Q hQ le_rfl
    (fun _ ℓ ↦ 1 ≤ pot anyCertBlind.D leanVmSeeds anyProgramBlind ℓ ∨ Fail leanVmSeeds ℓ)
    (fun z _ hz ↦ by
      rcases hz with hz | hz
      · exact hz
      · simp only [pot, hz, ↓reduceIte, le_refl])
  rwa [pot_nil, zero_add] at h

/-- **The chain's bad events in the game**, with probability at most the sum of T1's, W6's, E5's
and T3's terms, for a game with at most `Q` hash queries. -/
theorem prEvent_game_aggBad_le (fuel budget : ℕ) (A : GameAdversary nx ns) (Q : ℕ)
    (hQ : IsQueryBoundP (gameComp Guest.guest fuel budget A) IsHash Q) :
    Pr{let z ← game Guest.guest fuel budget A}[AggBad z.2] ≤
      Q * (εLean + failBound leanVmSeeds Q) + Q * (2 / 2 ^ 192 + 4 * (Q + 1) / 2 ^ 256) +
        Q * (14 / 2 ^ 192 + 4 * Q / 2 ^ 256) + Q * (Q + 1) / 2 ^ 193 := by
  set g := game Guest.guest fuel budget A
  have e : Pr{let z ← g}[AggBad z.2] ≤ Pr{let z ← g}[(((1 ≤ pot anyCertBlind.D leanVmSeeds
      anyProgramBlind z.2 ∨ Fail leanVmSeeds z.2) ∨
        BatchBad Guest.B1.Main.aggSeedD (bytecodeWords Guest.guest) z.2) ∨
      DaBad deployedPads.1 z.2) ∨ Pred (predOffset (bytecodeWords Guest.guest)) z.2] :=
    prEvent_mono_of_support _ _ _ fun z _ hz ↦ by
      rcases hz with h | h | h | h | h
      · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
      · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  refine e.trans ((prEvent_or_le _ _ _).trans (add_le_add ((prEvent_or_le _ _ _).trans
    (add_le_add ((prEvent_or_le _ _ _).trans (add_le_add ?_ ?_)) ?_)) ?_))
  · exact prEvent_game_blindBad_le Guest.guest fuel budget A Q hQ
  · exact prEvent_game_batchBad_le _ _ Guest.guest fuel budget A Q hQ
  · exact prEvent_game_daBad_le _ Guest.guest fuel budget A Q hQ
  · exact prEvent_game_pred_le _ Guest.guest fuel budget A Q hQ

/-- **The aggregate's claims are known under the log `ℓ`**: every leanXMSS and leanSPHINCS claim
of `s` by a signature valid under the log's answers, every DA claim backed (`DaBacked`). -/
def ClaimsKnown (ℓ : Log) (s : NodeStatement) : Prop :=
  (∀ c ∈ s.claims.xmss, ∃ σ, xmssVerifyWith (look ℓ) c.1 c.2 σ = some true) ∧
    (∀ c ∈ s.claims.sphincs, ∃ σ, sphincsVerifyWith (look ℓ) c.1 c.2 σ = some true) ∧
    ∀ c ∈ s.claims.da, DaBacked ℓ deployedPads.1 deployedPads.2 c

/-- **T4 in the game, cache form.** For a game of the deployed guest with at most `Q` hash
queries, V_I accepting the adversary's root statement and idealized proof with every hash
answered by the final log, while some claim of the statement is not known under that log, has
probability at most the sum of T1's, W6's, E5's and T3's terms, if the guest's open callees are
sound over every oracle model of every log. -/
theorem prEvent_game_aggregate_le
    (hG : ∀ (ℓ : Log) (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    (fuel budget : ℕ) (A : GameAdversary nx ns) (Q : ℕ)
    (hQ : IsQueryBoundP (gameComp Guest.guest fuel budget A) IsHash Q) :
    Pr{let z ← game Guest.guest fuel budget A}[
        idealVerify (look z.2) Guest.guest z.1.proof fuel z.1.statement = some true ∧
          ¬ ClaimsKnown z.2 z.1.statement] ≤
      Q * (εLean + failBound leanVmSeeds Q) + Q * (2 / 2 ^ 192 + 4 * (Q + 1) / 2 ^ 256) +
        Q * (14 / 2 ^ 192 + 4 * Q / 2 ^ 256) + Q * (Q + 1) / 2 ^ 193 := by
  refine le_trans (prEvent_mono_of_support _ _ _ fun z _ hz ↦ ?_)
    (prEvent_game_aggBad_le fuel budget A Q hQ)
  obtain ⟨hv, hn⟩ := hz
  by_contra hbad
  exact hn (aggregate_knowledge_cache (hG z.2) hbad hv)

end Game

end
end LeanVM.E2E
