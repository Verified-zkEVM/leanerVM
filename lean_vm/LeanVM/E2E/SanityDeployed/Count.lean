/-
  LeanVM.E2E.SanityDeployed.Count

  V_I's query count on the deployed honest idealized proof: at most `13,508` at the root and
  `134,742,095 ≈ 2^27.01` per node, within `viNodeBound` per node.
-/

module

public import LeanVM.E2E.SanityDeployed
public import LeanVM.E2E.Complete.Rom.ViCost

/-!
# V_I's queries on the deployed honest proof

`queryCount_honest_le` (`Complete/Rom/ViCost.lean`) bounds V_I's queries on the H-oblivious
prover's proof, whose `BLAKE2S` rows chain over the node's log. The deployed prover's rows are
the compression function's (`blakeRows_deployed`), so its table check is bounded otherwise:

* **the table check makes at most one query per row** (`count_tableOKWith_le_length`): under the
  precheck, a standard chain's last row determines its string (`eq_of_stdChain_last`: walking back
  from a common last row, the precheck makes the rows' inputs agree, the counter of the last row
  fixes the length, and the blocks the messages), so the strings with a chain are at most the
  rows; without the precheck it makes none;
* **a deployed execution performs at most `2^19` `BLAKE2S` rows** (`length_blakeRows_le`,
  `count_blake2s_le`): its rows are its `BLAKE2S` instructions, whose table and Flock's region
  (`2^8` rows per row) the committed size counts, at most `2^28` (`NodeExecDep.small`), so
  `275 · 2^⌈log₂ n⌉ ≤ 2^28`.

Per node (`count_nodeStep_dep`, `count_nodeStep_honest` for the deployed proof): the stack's
Merkle tree `2^27 − 1`, the table check `2^19`, sixteen children's digests `80`, so
`depStepBound = 134,742,095 ≤ viStepBound` (`depStepBound_le`), within the limits
(`WithinLimitsDep`: at most sixteen children and sixteen DA claims at the root). So
**`queryCount_deployed_le`**: V_I with BLAKE2s on the deployed idealized proof makes at most
`viRootBound + fuel · depStepBound` queries, whatever the rows (no collision event), and
`queryCount_deployed_le_mul`: at most `N · viNodeBound` on `N ≥ T.size` nodes, the budget the
headline gives V_I (`viCost N`).
-/

namespace LeanVM.E2E.SanityDeployed

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Node LeanVM.Guest
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd LeanVM.Arithmetization
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.Whir.Complete
open LeanVM.E2E.Complete LeanVM.E2E.Sanity

@[expose] public section

/-! ## The table check: one query per row -/

/-- Entries of a list at equal indices are equal. -/
theorem getElem_eq_of_idx_eq {α : Type} (l : List α) {i j : ℕ} (hi : i < l.length)
    (hj : j < l.length) (h : i = j) : l[i] = l[j] := by
  subst h
  rfl

/-- **Under the precheck, a standard chain's last row determines its string**, among fewer than
`2^57` rows: walking back from the common last row, each previous row is non-final with the
output the next row's chaining value, so the precheck gives it the other chain's inputs; the last
row's counter fixes the length (below `2^64`, the chains being short, `length_le_of_stdChain`),
and the rows' messages the blocks. -/
theorem eq_of_stdChain_last {rows : List BlakeRow} (hpre : Precheck rows)
    (hN : rows.length < 2 ^ 57) {x y : List UInt8} {c c' : List BlakeRow} (hc : 0 < c.length)
    (hc' : 0 < c'.length) (hsub : ∀ r ∈ c, r ∈ rows) (hsub' : ∀ r ∈ c', r ∈ rows)
    (hs : StdChain x c) (hs' : StdChain y c')
    (hlast : c[c.length - 1] = c'[c'.length - 1]) : x = y := by
  have hcard : (rows.map (·.md)).toFinset.card ≤ rows.length :=
    (List.toFinset_card_le _).trans (List.length_map _).le
  have hn := length_le_of_stdChain hN hcard hsub hs
  have hn' := length_le_of_stdChain hN hcard hsub' hs'
  have h1 := hs.1
  have h1' := hs'.1
  have h57 : (2 : ℕ) ^ 57 = 144115188075855872 := by norm_num
  have h64 : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
  have hx : x.length < 2 ^ 64 := by omega
  have hy : y.length < 2 ^ 64 := by omega
  obtain ⟨hw, hmd⟩ := hs.2.2.2 hc
  obtain ⟨hw', hmd'⟩ := hs'.2.2.2 hc'
  rw [hlast, hmd'] at hmd
  rw [hlast] at hw
  have hl : x.length.toUInt64 = y.length.toUInt64 := (Prod.mk.inj hmd).1.symm
  have hlen : x.length = y.length := by
    have e := congrArg UInt64.toNat hl
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat'] at e
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at e
  have hcl : c'.length = c.length := by omega
  -- walking back from the last row
  have hback : ∀ k i (hi : i < c.length) (hi' : i < c'.length), i + k = c.length - 1 →
      rowInput c[i] = rowInput c'[i] := by
    intro k
    induction k with
    | zero =>
      intro i hi hi' hik
      rw [getElem_eq_of_idx_eq c hi (by omega) (show i = c.length - 1 by omega), hlast,
        getElem_eq_of_idx_eq c' (by omega) hi' (show c'.length - 1 = i by omega)]
    | succ k ih =>
      intro i hi hi' hik
      have hr := ih (i + 1) (by omega) (by omega) (by omega)
      have hcv := hs.2.1 (i + 1) (by omega)
      have hcv' := hs'.2.1 (i + 1) (by omega)
      simp only [Nat.add_one_ne_zero, ↓reduceDIte, Nat.add_sub_cancel] at hcv hcv'
      have hout : c[i].out = c'[i].out := by
        rw [← hcv, ← hcv']
        simp only [rowInput, Prod.mk.injEq] at hr
        simp only [BlakeRow.cv, hr.2.1, hr.2.2.1]
      have hnf : ¬ RowFinal c[i] := by
        rw [RowFinal, (hs.2.2.1 i (by omega)).2]
        exact fun h ↦ lastBlock_ne_zero h.symm
      have hnf' : ¬ RowFinal c'[i] := by
        rw [RowFinal, (hs'.2.2.1 i (by omega)).2]
        exact fun h ↦ lastBlock_ne_zero h.symm
      exact hpre _ (hsub _ (List.getElem_mem _)) _ (hsub' _ (List.getElem_mem _)) hnf hnf' hout
  -- the blocks
  have hnb : nBlocks x = nBlocks y := by unfold nBlocks; rw [hlen]
  have hcn : c.length - 1 = nBlocks x := by unfold nBlocks; omega
  have hblock : ∀ i, i < nBlocks x → blockAt x i = blockAt y i := by
    intro i hi
    have hr := hback (c.length - 1 - i) i (by omega) (by omega) (by omega)
    have hm : c[i].m = c'[i].m := congrArg (fun r ↦ r.1) hr
    have hmw := (hs.2.2.1 i (by omega)).1
    have hmw' := (hs'.2.2.1 i (by omega)).1
    refine eq_of_blockWords_eq ?_ (by rw [length_blockAt hi, length_blockAt (hnb ▸ hi)])
      (by rw [length_blockAt hi])
    unfold blockAt
    rw [← hmw, ← hmw', hm]
  have hp : prefixAt x (nBlocks x) = prefixAt y (nBlocks y) := by
    rw [← hnb]
    unfold prefixAt
    exact List.map_congr_left fun i hi ↦ hblock i (List.mem_range.mp hi)
  have hwt : blockWords (tailOf x) = blockWords (tailOf y) := by
    unfold tailOf
    have e1 : 64 * nBlocks x = 64 * (c'.length - 1) := by omega
    have e2 : 64 * nBlocks y = 64 * (c'.length - 1) := by omega
    have e3 : 64 * (c.length - 1) = 64 * (c'.length - 1) := by omega
    rw [e3] at hw
    rw [e1, e2, ← hw, ← hw']
  exact eq_of_prefix_tail hp hl hwt

/-- A row standing for no string. -/
def zeroRow : BlakeRow := ⟨fun _ ↦ 0, 0, 0, 0, 0, 0⟩

open Classical in
/-- The last row of a chosen standard chain of a string with one among the rows. -/
noncomputable def lastRowOf (rows : List BlakeRow) (x : List UInt8) : BlakeRow :=
  if h : x ∈ chainInputs rows then
    h.choose[h.choose.length - 1]'(by have := h.choose_spec.1; omega)
  else zeroRow

/-- **The table check makes at most one query per row**, among fewer than `2^57` rows: under the
precheck the strings with a standard chain inject into the rows by their chains' last rows
(`eq_of_stdChain_last`); otherwise it makes none. -/
theorem count_tableOKWith_le_length (H : Bytes → Digest) (rows : List BlakeRow)
    (hN : rows.length < 2 ^ 57) : (tableOKWith (countQuery H) rows).count ≤ rows.length := by
  classical
  unfold tableOKWith
  split
  · rename_i hpre
    split
    · rename_i hfin
      refine (count_allM_le _ 1 (fun x ↦ ?_) _).trans ?_
      · simp
      · rw [Nat.mul_one, Finset.length_toList]
        refine le_trans (Finset.card_le_card_of_injOn (lastRowOf rows) (t := rows.toFinset)
          (fun x hx ↦ ?_) (fun x hx y hy hxy ↦ ?_)) (List.toFinset_card_le _)
        · have hx' : x ∈ chainInputs rows := (Set.Finite.mem_toFinset hfin).mp hx
          simp only [lastRowOf, hx', ↓reduceDIte]
          exact List.mem_toFinset.mpr (hx'.choose_spec.2.1 _ (List.getElem_mem _))
        · have hx' : x ∈ chainInputs rows :=
            (Set.Finite.mem_toFinset hfin).mp (Finset.mem_coe.mp hx)
          have hy' : y ∈ chainInputs rows :=
            (Set.Finite.mem_toFinset hfin).mp (Finset.mem_coe.mp hy)
          simp only [lastRowOf, hx', hy', ↓reduceDIte] at hxy
          exact eq_of_stdChain_last hpre hN hx'.choose_spec.1 hy'.choose_spec.1
            hx'.choose_spec.2.1 hy'.choose_spec.2.1 hx'.choose_spec.2.2 hy'.choose_spec.2.2 hxy
    · simp
  · simp

/-! ## A deployed execution's rows -/

/-- A step lists at most one row, and only at a `BLAKE2S` instruction. -/
theorem length_blakeRowAt_le (read : K → Option E) (r : Regs K) (i : Instr) :
    (blakeRowAt read r i).toList.length ≤ if i.opcode = .blake2s then 1 else 0 := by
  cases i with
  | blake2s om ocv oout omd =>
    simp only [Instr.opcode, ↓reduceIte]
    cases blakeRowAt read r (.blake2s om ocv oout omd) <;> simp
  | _ => simp [blakeRowAt]

/-- **The rows a run lists are at most its `BLAKE2S` instructions.** -/
theorem length_runRows_le (S : BlakeSem) {κ : ℕ} (prog : Program) (L : MemImage κ) :
    ∀ (n : ℕ) (r : Regs K), (runRows S prog L n r).length ≤ runCountB S prog L .blake2s n r
  | 0, _ => by simp [runRows]
  | n + 1, r => by
    by_cases hpc : r.pc = prog.finalPc
    · simp [runRows, hpc]
    cases hf : prog.fetch r.pc with
    | none => simp [runRows, hpc, hf]
    | some i =>
      cases hs : stepB S prog L r with
      | none => simp [runRows, hpc, hf, hs]
      | some r' =>
        rw [Guest.Value.runRows_succ hpc hf hs, List.length_append]
        simp only [runCountB, hf, hs]
        exact Nat.add_le_add (length_blakeRowAt_le _ _ _) (length_runRows_le S prog L n r')

/-- **A deployed execution lists at most its `BLAKE2S` instructions as rows.** -/
theorem length_blakeRows_le {prog : Program} {input : PublicInput} {t : Trace prog}
    (hv : ValidExecution prog input t) : (t.blakeRows blakeFree).length ≤ t.count .blake2s := by
  have hvB := (validExecutionB_deployed _ _ _).mpr hv
  unfold Trace.blakeRows
  rw [runRows_eq_of_runB (S := blakeDeployed) (S' := blakeFree) (fun _ hb ↦ canonicalCells_of_compressCells hb)
    hvB.2]
  exact (length_runRows_le _ _ _ _ _).trans_eq (runCountB_deployed _ _ _ _ _)

/-- **Within the committed-size cap, at most `2^19` `BLAKE2S` instructions**: the committed size
counts `19 + 2^8` cells per row of the `BLAKE2S` table's height, so `275 · 2^τ ≤ 2^28`. -/
theorem count_blake2s_le {prog : Program} {t : Trace prog} (h : t.committedSize ≤ 2 ^ maxMu) :
    t.count .blake2s ≤ 2 ^ 19 := by
  have hle := Nat.le_pow_clog (b := 2) (by norm_num) (t.count .blake2s)
  have key : 275 * 2 ^ Nat.clog 2 (t.count .blake2s) ≤ 2 ^ 28 := by
    simp only [Semantics.Trace.committedSize] at h
    have hm : (2 : ℕ) ^ maxMu = 2 ^ 28 := rfl
    rw [hm] at h
    have : 0 < 2 ^ prog.logSize := Nat.two_pow_pos _
    generalize 2 ^ Nat.clog 2 (t.count .blake2s) = a at h ⊢
    omega
  have ha : Nat.clog 2 (t.count .blake2s) ≤ 19 := by
    by_contra hc
    have : 2 ^ 20 ≤ 2 ^ Nat.clog 2 (t.count .blake2s) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    generalize 2 ^ Nat.clog 2 (t.count .blake2s) = a at this key
    norm_num at this key
    omega
  exact hle.trans (Nat.pow_le_pow_right (by norm_num) ha)

/-! ## V_I's step on a deployed node -/

/-- **V_I's queries on a deployed node**: the word's Merkle tree, the single candidate's table
check (at most `T`) and its decoded children's digests (at most `K` children, five queries
each); `count_nodeStep_honest` for the full verifier's honest proof. -/
theorem count_nodeStep_dep (H : Bytes → Digest) {prog : Program} (seed : Digest)
    (ip : IdealProof) {s : Sizes} {ρ : ℕ} {q : Column (leanIsaμ prog s)} {input : PublicInput}
    (hs : s.Admissible prog) (hρ : validRate ρ) {sd : Digest} {fuel : ℕ} {π : Proof}
    (hπ : prove H (leanVmProgram (bytecodeWords prog) (publicDigest input))
      (Protocol.EndToEnd.Complete.leanVmProver prog s ρ q) sd fuel = some π)
    (pi : Digest) (hword : ip.word (pi, π) = some (PWord.full (stackWord (leanIsaμ prog s) q)))
    {fr : String → List E → Option ℕ} (hfr : ip.frames (pi, π) = fr) (T K : ℕ)
    (hcand : M3HoldsBlind (leanIsaInstance Sound.F₀ prog s) (inputOf pi) q →
      ∃ t, candidateRun prog s q = some t ∧
        (tableOKWith (countQuery H) (t.blakeRows blakeFree)).count ≤ T ∧
        (Guest.End.decodeAt (Guest.Value.tableSem (t.blakeRows blakeFree)) fr
          t.image).witness.children.length ≤ K) :
    (nodeStep (countQuery H) prog seed ip (pi, π)).count + 1 ≤
      2 ^ (costHeight + 1) + (T + 5 * K) := by
  obtain ⟨level, rest, hc, hann, hroot, hshape⟩ := nodeHead_prove_dep H hs hρ hπ
  have hadm := Protocol.EndToEnd.Complete.whirAdmissible prog hs hρ
  obtain ⟨hfold, -⟩ := Whir.Params.deployed_spec_hyps hadm hc
  have hW := hword
  obtain rfl := hfr
  have hshaped : WellShaped (2 ^ level.fold) (stackWord (leanIsaμ prog s) q) := by
    rw [hfold]; exact wellShaped_stackWord _ q
  have hht := stackShape_height_le hshape
  have hht' : stackHeight (leanIsaμ prog s) level =
      (levelShape (leanIsaμ prog s) level (2 ^ level.fold)).1 := rfl
  rw [hht'] at hroot
  unfold nodeStep
  have hw2 : (levelShape (leanIsaμ prog s) level (2 ^ level.fold)).2 = 2 ^ level.fold := rfl
  simp only [hann, sizesOf_verifierLayout hs, hroot, hshape, hW, ↓reduceIte, PWord.word_full,
    PWord.full_full, hw2, hshaped, not_true_eq_false, and_false]
  rw [Counted.count_bind]
  have hp := count_pTreeRootM_le H (levelShape (leanIsaμ prog s) level (2 ^ level.fold)).1
    (PWord.full (stackWord (leanIsaμ prog s) q))
  have hpow : 2 ^ ((levelShape (leanIsaμ prog s) level (2 ^ level.fold)).1 + 1) ≤
      2 ^ (costHeight + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by unfold levelShape; simp only; omega)
  rw [val_pTreeRootM, pTreeRootM_full]
  simp only [ne_eq, not_true_eq_false, ↓reduceIte]
  refine (fun (x : Counted (Option (List E2E.Node))) (hx : x.count ≤ T + 5 * K) ↦
    (show _ + x.count + 1 ≤ _ by omega)) _ ?_
  have hset : blindCandidatesS prog s ρ (levelShape (leanIsaμ prog s) level (2 ^ level.fold)).1 pi
      (PWord.full (stackWord (leanIsaμ prog s) q)) =
        {q' | q' = q ∧ M3HoldsBlind (leanIsaInstance Sound.F₀ prog s) (inputOf pi) q} :=
    (blindCandidatesS_full prog s ρ (stackHeight (leanIsaμ prog s) level) pi
      (stackWord (leanIsaμ prog s) q)).trans (blindCandidates_stackWord hs hρ pi q)
  split
  · rename_i hfin
    rw [Counted.count_bind]
    by_cases hm : M3HoldsBlind (leanIsaInstance Sound.F₀ prog s) (inputOf pi) q
    · have hlist : hfin.toFinset.toList = [q] := by
        have : hfin.toFinset = {q} := by
          ext x
          simp only [Set.Finite.mem_toFinset, hset, Set.mem_ofPred_eq, Finset.mem_singleton]
          exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hm⟩⟩
        rw [this, Finset.toList_singleton]
      obtain ⟨t, hrun, htab, hkids⟩ := hcand hm
      rw [hlist, List.forIn_cons, Counted.count_bind]
      simp only [hrun, List.forIn_nil, Counted.count_bind, Counted.val_bind]
      split
      · simp
        omega
      · simp only [Counted.count_bind, Counted.count_pure, Counted.val_bind, Counted.val_pure,
          Nat.add_zero]
        have hf := count_forIn_le (fun (c : Node.Child) (acc : List E2E.Node) ↦
          (do
            let pc ← Node.statementDigestWith (countQuery H) seed c.statement
            pure (ForInStep.yield (acc ++ [(pc, c.proof)])) : Counted _)) (fun _ ↦ 5)
          (fun a b ↦ by simp [count_statementDigestWith])
          (Guest.End.decodeAt (Guest.Value.tableSem (Trace.blakeRows blakeFree t))
            (ip.frames (pi, π)) t.image).witness.children []
        simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hf
        omega
    · have hlist : hfin.toFinset.toList = [] := by
        have : hfin.toFinset = ∅ := by
          ext x
          simp only [Set.Finite.mem_toFinset, hset, Set.mem_ofPred_eq, Finset.notMem_empty,
            iff_false, not_and]
          exact fun _ ↦ hm
        rw [this, Finset.toList_empty]
      rw [hlist]
      simp
  · simp

/-- **V_I's step on a deployed node rejects when the table check fails**: the hypotheses of
`nodeStep_dep`, the table check false. -/
theorem nodeStep_dep_false (H : Bytes → Digest) {prog : Program} (seed : Digest) (ip : IdealProof)
    {s : Sizes} {ρ : ℕ} {q : Column (leanIsaμ prog s)} {input : PublicInput}
    (hs : s.Admissible prog) (hρ : validRate ρ) {sd : Digest} {fuel : ℕ} {π : Proof}
    (hπ : prove H (leanVmProgram (bytecodeWords prog) (publicDigest input))
      (Protocol.EndToEnd.Complete.leanVmProver prog s ρ q) sd fuel = some π)
    (pi : Digest) (hword : ip.word (pi, π) = some (PWord.full (stackWord (leanIsaμ prog s) q)))
    (hm : M3HoldsBlind (leanIsaInstance Sound.F₀ prog s) (inputOf pi) q) {t : Trace prog}
    (hrun : candidateRun prog s q = some t)
    (htab : tableOKWith (m := Id) (fun x ↦ (pure (H x) : Id Digest)) (t.blakeRows blakeFree) =
      false) :
    nodeStep (m := Id) (fun x ↦ (pure (H x) : Id Digest)) prog seed ip (pi, π) = none := by
  obtain ⟨level, rest, hc, hann, hroot, hshape⟩ := nodeHead_prove_dep H hs hρ hπ
  have hadm := Protocol.EndToEnd.Complete.whirAdmissible prog hs hρ
  obtain ⟨hfold, -⟩ := Whir.Params.deployed_spec_hyps hadm hc
  have hW := hword
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
  split
  · rw [hlist]
    simp only [List.forIn_cons, hrun, htab]
    show Id.run _ = _
    simp only [Id.run_bind, id_run_eq (treeRoot H _ _), ↓reduceIte, not_true_eq_false]
    rfl
  · exact absurd hfin ‹_›

/-- **V_I steps a deployed entry only to its children's nodes**: whatever the rows, a step that
accepts returns the entry's children (`nodeStep_dep`, or `nodeStep_dep_false` when the table
check fails). -/
theorem nodeStep_entry_kids (ρ pfuel : ℕ) (hρ : validRate ρ) {e : DepEntry}
    (he : EntryOK ρ pfuel e) (ip : IdealProof) (hw : ip.word e.node = some (PWord.full e.word))
    (hf : ip.frames e.node = e.frames) {ks : List E2E.Node}
    (h : nodeStep (m := Id) blakeId guest (Node.deployedSeed guest) ip e.node = some ks) :
    ks = e.kids := by
  obtain ⟨sz, q, t, cs, hadm, hπ, hword, hm3, hrun, hv, hdec, hkids⟩ := he
  obtain ⟨⟨pi, π⟩, kids, size, word, frames⟩ := e
  simp only at hπ hword hm3 hrun hv hdec hkids hw hf h ⊢
  subst hword hkids
  have hm : M3HoldsBlind (leanIsaInstance Sound.F₀ guest sz) (inputOf pi) q := by
    rw [inputOf_eq]; exact ⟨hm3.1.1, hm3.1.2.1, hm3.1.2.2.1, hm3.1.2.2.2.1⟩
  cases hb : tableOKWith (m := Id) blakeId (t.blakeRows blakeFree) with
  | false =>
    rw [nodeStep_dep_false blake2sBytes (Node.deployedSeed guest) ip hadm hρ hπ pi hw hm hrun hb]
      at h
    cases h
  | true =>
    rw [nodeStep_dep blake2sBytes (Node.deployedSeed guest) ip hadm hρ hπ pi hw hf _ hm hrun hb rfl,
      Option.some.injEq] at h
    rw [← h]
    exact kidNodes_congr blake2sBytes _ hdec

/-! ## Every deployed entry -/

/-- **V_I's queries per deployed node**: the stack's tree, at most `2^19` rows' table check,
sixteen children's digests, `134,742,095 ≈ 2^27.01`. -/
def depStepBound : ℕ := 2 ^ (costHeight + 1) - 1 + (2 ^ 19 + 5 * 16)

theorem depStepBound_eq : depStepBound = 134742095 := rfl

/-- The deployed per-node bound is within the H-oblivious prover's, so within `viNodeBound`. -/
theorem depStepBound_le : depStepBound ≤ viStepBound := by
  rw [depStepBound_eq, viStepBound_eq]
  norm_num

/-- **An entry's step costs at most `depStepBound`** under every idealized proof giving its node
its word and frames. -/
def EntryCostDep (e : DepEntry) : Prop :=
  ∀ ip : IdealProof, ip.word e.node = some (PWord.full e.word) → ip.frames e.node = e.frames →
    (nodeStep (countQuery blake2sBytes) guest (seedOf blake2sBytes) ip e.node).count ≤
      depStepBound

variable (ρ pfuel : ℕ)

/-- **Every entry of a deployed output costs at most `depStepBound`**, for a tree within the
deployed limits: its execution's rows are at most `2^19` (`NodeExecDep.small`), its children at
most sixteen (`End.Limits.children`). -/
theorem deployedOut_cost (hρ : validRate ρ) (T : HonestTree) :
    T.WithinLimitsDep ρ pfuel →
      ∀ o, deployedOut ρ pfuel T = some o → ∀ e ∈ o.subs, EntryCostDep e := by
  induction T using HonestTree.induct' with
  | h claims xs ss ds kids ih =>
  intro hl o h
  rw [HonestTree.WithinLimitsDep, HonestTree.allNodes_node] at hl
  rw [deployedOut_node, Option.bind_eq_some_iff] at h
  obtain ⟨kos, hkos, h⟩ := h
  have hF := forall₂_kidOutsDep ρ pfuel hkos
  obtain ⟨hd, e, π, hhd, hπ, rfl⟩ := deployedStep_spec ρ pfuel h
  obtain ⟨hlim, -⟩ := hl.1 kos hkos hd hhd
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · intro ip hword hfr
    simp only at hword hfr ⊢
    have hrows : (e.t.blakeRows blakeFree).length ≤ 2 ^ 19 :=
      (length_blakeRows_le e.valid).trans (count_blake2s_le e.small)
    have htab := (count_tableOKWith_le_length blake2sBytes (e.t.blakeRows blakeFree)
      (lt_of_le_of_lt hrows (by norm_num))).trans hrows
    have hkids : (Guest.End.decodeAt (Guest.Value.tableSem (e.t.blakeRows blakeFree)) e.fr
        e.t.image).witness.children.length ≤ 16 := by
      have := congrArg List.length e.decode
      simp only [List.length_map] at this
      have hc := hlim.children
      simp only [List.length_map] at this hc
      rw [this]
      exact hc
    have hc := count_nodeStep_dep blake2sBytes (seedOf blake2sBytes) ip e.adm hρ hπ _ hword
      (fr := e.fr) hfr (2 ^ 19) 16 fun _ ↦ ⟨e.t, e.run, htab, hkids⟩
    unfold depStepBound
    omega
  · obtain ⟨ko, hko, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨k, hk, hk'⟩ := forall₂_mem_right hF ko hko
    exact ih k hk (hl.2 k hk) ko hk' p hp

/-- The root's DA claims, within the deployed limits: at most sixteen. -/
theorem claims_da_le_of_withinLimitsDep {T : HonestTree} {o : DepOut}
    (hlim : T.WithinLimitsDep ρ pfuel) (h : deployedOut ρ pfuel T = some o) :
    T.claims.da.length ≤ 16 := by
  obtain ⟨claims, xs, ss, ds, kids⟩ := T
  have hl := ((HonestTree.allNodes_node).mp hlim).1
  rw [deployedOut_node, Option.bind_eq_some_iff] at h
  obtain ⟨kos, hkos, h⟩ := h
  obtain ⟨hd, -, -, hhd, -, -⟩ := deployedStep_spec ρ pfuel h
  exact (hl kos hkos hd hhd).1.daRoots.1

/-! ## V_I's count on the deployed proof -/

/-- **V_I's queries on the deployed honest idealized proof**: at most
`viRootBound + fuel · depStepBound`, at a valid rate, for a tree within the deployed limits,
whatever the rows (no collision event: a failed table check only stops V_I). -/
theorem queryCount_deployed_le (hρ : validRate ρ) {T : HonestTree}
    (hlim : T.WithinLimitsDep ρ pfuel) {s : NodeStatement} {π : Proof} {ip : IdealProof}
    (hout : deployedProve ρ pfuel T = some (s, π, ip)) (fuel : ℕ) :
    queryCount blake2sBytes guest ip fuel s ≤ viRootBound + fuel * depStepBound := by
  obtain ⟨o, ho, he⟩ := Option.map_eq_some_iff.mp hout
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  obtain ⟨hcl, -, ⟨r, hr, hrnode, -⟩, hok, hsubs⟩ := deployedOut_good ρ pfuel T o ho
  have hcost := deployedOut_cost ρ pfuel hρ T hlim o ho
  have hseed : Id.run (fiatShamirIvWith (fun x ↦ (pure (blake2sBytes x) : Id Digest))
      (bytecodeWords guest)) = Node.deployedSeed guest :=
    (show _ = seedOf blake2sBytes from rfl).trans seedOf_blake
  let Good : E2E.Node → Prop := fun ν ↦ ∃ e ∈ o.subs, e.node = ν
  have hle := queryCount_le_of blake2sBytes guest (idealOfDep o) fuel o.stmt Good depStepBound
    (fun ν hν ↦ by
      obtain ⟨b, hb, hbm, hbν, -⟩ := bestDep_spec hν
      subst hbν
      exact hcost b hbm _ (idealOfDep_word hb hν) (idealOfDep_frames hb))
    (fun ν hν ks hks κ hκ ↦ by
      obtain ⟨b, hb, hbm, hbν, -⟩ := bestDep_spec hν
      subst hbν
      rw [hseed] at hks
      obtain rfl := nodeStep_entry_kids ρ pfuel hρ (hok b hbm) _ (idealOfDep_word hb hν)
        (idealOfDep_frames hb) hks
      obtain ⟨ks', hks', hk', -⟩ := hsubs b hbm
      rw [hks'] at hκ
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hκ
      obtain ⟨e', he', e1, -⟩ := hk' k hk
      exact ⟨e', he', e1⟩)
    ⟨r, List.mem_of_mem_head? hr, by rw [hrnode]; rfl⟩
  have hda : o.stmt.claims.da.length * 18 ≤ 16 * 18 := by
    rw [hcl]
    exact Nat.mul_le_mul_right _ (claims_da_le_of_withinLimitsDep ρ pfuel hlim ho)
  unfold viRootBound
  omega

/-- **V_I's queries on the deployed proof of a tree of at most `N` nodes, run on `N` nodes**: at
most `N · viNodeBound`, the H-oblivious prover's bound (`queryCount_honest_le_mul`). -/
theorem queryCount_deployed_le_mul (hρ : validRate ρ) {T : HonestTree}
    (hlim : T.WithinLimitsDep ρ pfuel) {s : NodeStatement} {π : Proof} {ip : IdealProof}
    (hout : deployedProve ρ pfuel T = some (s, π, ip)) {N : ℕ} (hN : T.size ≤ N) :
    queryCount blake2sBytes guest ip N s ≤ N * viNodeBound := by
  have h := queryCount_deployed_le ρ pfuel hρ hlim hout N
  have h1 : 1 ≤ N := (HonestTree.one_le_size T).trans hN
  have h2 : viRootBound ≤ N * viRootBound := Nat.le_mul_of_pos_left _ h1
  have h3 : N * depStepBound ≤ N * viStepBound := Nat.mul_le_mul_left _ depStepBound_le
  rw [viNodeBound, Nat.mul_add]
  omega

end
end LeanVM.E2E.SanityDeployed
