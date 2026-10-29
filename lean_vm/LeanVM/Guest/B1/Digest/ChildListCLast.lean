/-
  LeanVM.Guest.B1.Digest.ChildListCLast

  `child_claim_list_last__L{k}` and `__loop16`'s block, completely.
-/

module

public import LeanVM.Guest.B1.Digest.ChildListCChk1
public import LeanVM.Guest.B1.Digest.ChildListCRec

/-!
# The last child claims and a group of child claims, completely

`ccLast_complete`: from a state at `sp` after whole blocks `pre` and `k` honest records
(`RecMem`: slots `os j` below the bound `g^L`, marks `marks · g^j`, cells), with the words the
range checks read defined (`BoundMem`), `child_claim_list_last__L{k}` returns the digest of
`pre ++` the cells. `l17_block`: `__loop16`'s block at the counter `x` holds on 17 honest records
with the marks `base · x^17`, the state after `pre` at `chain · x^13` and the state after the
cells at offset `13`. Both evaluate the body (`Fwd.ev`), the slots' hints from the oracle
`slotW`.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

variable {rd : Reader}

theorem ccc_all {k : ℕ} (hk : k < 17) : cccOk k (coreProgram.getD (339 + k) default) = true := by
  rcases Nat.lt_or_ge k 9 with h | h
  · exact ccc_lo k h
  · have := ccc_hi (k - 9) (by omega)
    rwa [show 9 + (k - 9) = k by omega, show 348 + (k - 9) = 339 + k by omega] at this

theorem storesOf_load : ∀ {c : ℕ} {ss : List Stmt} {a : Atom}, a ∈ storesOf c ss →
    ∃ d p o, a = .load d p o
  | _, [], _, h => by simp [storesOf] at h
  | c, s :: ss, a, h => by
    simp only [storesOf, List.mem_append] at h
    rcases h with h | h
    · unfold storeHd at h
      split at h
      · split at h
        · rename_i d p o _
          exact ⟨d, p, o, List.mem_singleton.mp h⟩
        · simp at h
      · simp at h
    · exact storesOf_load h

/-- A load found among the atoms but the stores reads memory. -/
theorem load_val_filter {A S : List Atom} {w : ℕ → E} {σ : Val} {x p : V} {o : ℕ}
    (h : (A.filter fun a => decide (a ∉ S)).any (isLoadAt x p o) = true)
    (hg : ∀ a ∈ A, Good rd S w σ a) : σ x = rdAt rd (σ p) o := by
  obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
  obtain ⟨ha1, ha2⟩ := List.mem_filter.mp ha
  cases a <;> simp only [isLoadAt, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hp
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hp
  rcases hg _ ha1 with h' | h'
  · exact absurd h' (by simpa using ha2)
  · exact h'

theorem recC_parts {A F S : List Atom} {P : ClaimVs} {o0 j : ℕ} (h : recC A F S P o0 j = true) :
    A.any (isWitO (ccOV o0 j)) = true ∧ markC F P j (ccMark o0 P.marks j) = true ∧
      ∀ c < 4, A.any (isCellRead F S P o0 j c) = true := by
  simp only [recC, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem w_slot (o0 : ℕ) (os : ℕ → ℕ) (j : ℕ) : slotW o0 os (ccOV o0 j).idx = gen ^ os j := by
  rw [slotW, slotOf_ccOV]

theorem mem_ccA {st : List V} {o0 K i : ℕ} (h : i ∈ ccA st o0 K) :
    (∃ v ∈ st, i = v.idx) ∨ ∃ j < K, ∃ c < 4, i = ccCell o0 j c := by
  rcases List.mem_append.mp h with h | h
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h
    exact Or.inl ⟨v, hv, rfl⟩
  · obtain ⟨j, hj, h⟩ := List.mem_flatMap.mp h
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
    exact Or.inr ⟨j, List.mem_range.mp hj, c, List.mem_range.mp hc, rfl⟩

/-- The records' message is their cells. -/
theorem ccMsg_vals {σ : Val} {o0 K : ℕ} {cells : List E} (hl : cells.length = 4 * K)
    (hv : ∀ j < K, ∀ c < 4, σ (.n (ccCell o0 j c)) = cells.getD (4 * j + c) 0) :
    (ccMsg o0 K).map (srcVal σ) = cells := by
  refine List.ext_getElem (by simp [ccMsg, hl]) fun i h1 h2 => ?_
  have hi : i < 4 * K := by simpa [ccMsg] using h1
  simp only [ccMsg, List.getElem_map, List.getElem_range, srcVal]
  rw [hv (i / 4) (by omega) (i % 4) (by omega), show 4 * (i / 4) + i % 4 = i by omega,
    List.getD_eq_getElem _ _ h2]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- **`child_claim_list_last__L{k}` is complete**: from the state after whole blocks `pre` at
`sp` and `k` honest records, it returns the digest of `pre ++` their cells. -/
theorem ccLast_complete {k : ℕ} (hk : k < 17) {sp entries cover marks origin limit : E} {n : ℕ}
    {pre : List UInt8} (hpre : pre.length = rate * n)
    (hS : StateAt rd sp 0 (absorbChunks n zeroState pre)) {os : ℕ → ℕ} {cells : List E}
    (hl : cells.length = 4 * k) (hc : AllCanonical cells)
    (hrec : RecMem rd cover origin limit entries marks k os cells) {L : ℕ}
    (hL : limit = gen ^ L) (hL33 : L < 2 ^ 33) (hdef : BoundMem rd L) :
    coreProgram.Rel rd (cclNames.getD k "") [sp, entries, cover, marks, origin, limit]
      (digestCells (keccak256 (pre ++ cellsBytes cells))) := by
  have hf := find_of_idx (ccl_idx k hk) (by rw [coreProgram_length]; omega)
  have hok := ccl_all k hk
  have hcok := ccc_all hk
  set fn := coreProgram.getD (339 + k) default
  simp only [cclOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hpar, hok⟩ := hok
  simp only [cccOk, Bool.and_eq_true, Option.isSome_iff_exists] at hcok
  obtain ⟨⟨c', hchk⟩, hcok⟩ := hcok
  split at hok
  · rename_i atoms r0 r1 hsb
    rw [hsb] at hcok
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_true_eq, List.mem_range] at hok hcok
    obtain ⟨⟨⟨hck, hret⟩, -⟩, hst⟩ := hok
    obtain ⟨⟨⟨hcan, hneeds⟩, hrc⟩, hstF⟩ := hcok
    set S := storesOf 6 fn.body with hSdef
    let args : List E := [sp, entries, cover, marks, origin, limit]
    obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = B1.Val.ofArgs (ev rd (slotW 6 os) args fn.body) := ⟨_, rfl⟩
    have hidx : ∀ v, σ v = σ (.n v.idx) := fun v => by rw [hσ]; rfl
    obtain ⟨-, -, hgs⟩ := ev_spec rd (slotW 6 os) fn.body args hchk
    rw [show args.length = 6 from rfl, ← hσ] at hgs
    have hbody := splitBody_eq hsb
    have hg : ∀ a ∈ atoms, Good rd S (slotW 6 os) σ a := fun a ha =>
      hgs (.atom a) (by rw [hbody]; exact List.mem_append_left _ (List.mem_map_of_mem ha))
    have par : ∀ i (hi : i < 6), σ (.n i) = args.getD i 0 := fun i hi => by
      rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args]; omega)
    have e0 : σ (.n 0) = sp := par 0 (by omega)
    have e1 : σ (.n 1) = entries := par 1 (by omega)
    have e2 : σ (.n 2) = cover := par 2 (by omega)
    have e3 : σ (.n 3) = marks := par 3 (by omega)
    have e4 : σ (.n 4) = origin := par 4 (by omega)
    have e5 : σ (.n 5) = limit := par 5 (by omega)
    have hF := pure_holds hg
    have hwit : ∀ j < k, σ (ccOV 6 j) = gen ^ os j := fun j hj =>
      (wit_val (recC_parts (hrc j hj)).1 hg).trans (w_slot 6 os j)
    have hmark : ∀ j < k, σ (ccMark 6 cclP.marks j) = σ cclP.marks * gen ^ j := fun j hj =>
      markC_val (by omega) (recC_parts (hrc j hj)).2.1 hF
    have hrec' : RecMem rd (σ cclP.cover) (σ cclP.origin) (σ cclP.limit) (σ cclP.entries)
        (σ cclP.marks) k os cells := by
      show RecMem rd (σ (.n 2)) (σ (.n 4)) (σ (.n 5)) (σ (.n 1)) (σ (.n 3)) k os cells
      rw [e2, e4, e5, e1, e3]; exact hrec
    have hL' : σ cclP.limit = gen ^ L := e5.trans hL
    have vst : ∀ c : Fin 13, σ ((cclSt k).getD c default) =
        cellsOfState (absorbChunks n zeroState pre) false c := by
      intro c
      simp only [stLoadsOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hstF
      rw [load_val_filter (hstF.2 c c.isLt) hg, e0, rdAt_of_load (hS c)]
    have vc : ∀ j < k, ∀ c < 4, σ (.n (ccCell 6 j c)) = cells.getD (4 * j + c) 0 := by
      intro j hj c hc4
      exact cellRead_val ((recC_parts (hrc j hj)).2.2 c hc4) hF hg
        (hwit j hj) ((hrec' j hj).2.2 c hc4)
    have hA : ∀ i ∈ ccA (cclSt k) 6 k, IsCanonical128 (σ (.n i)) := by
      intro i hi
      rcases mem_ccA hi with ⟨v, hv, rfl⟩ | ⟨j, hj, c, hc4, rfl⟩
      · obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hv
        have hc13 := List.mem_range.mp hc'
        have := vst ⟨c, hc13⟩
        simp only [cclSt, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range hc13, Option.map_some, Option.getD_some] at this
        rw [← hidx, this]
        exact canon_cellsOfState _ _ _
      · rw [vc j hj c hc4, List.getD_eq_getElem _ _ (by omega)]
        exact hc _ (List.getElem_mem _)
    have hside : ∀ a ∈ atoms, recSide (atoms.filter pureB) cclP 6 k S a = true → a.Holds rd σ :=
      fun a ha hs => recSide_holds hF hg hwit hmark hrec' hL' hL33 hdef ha hs
    have hat : ∀ a ∈ atoms, a.Holds rd σ := by
      refine atoms_holds_stores (S := S) (w := slotW 6 os) hidx hcan hg hA
        (fun a ha hnS hns => Or.inl ?_) (fun _ a ha haS => ?_)
      · rcases hneeds a ha with (h | ⟨h, -⟩) | h
        · rw [hns] at h; exact absurd h (by simp)
        · cases a <;> simp only [isLoadBelow, Bool.false_eq_true, Bool.and_eq_true,
            decide_eq_true_eq] at h
          rename_i d p o
          obtain ⟨rfl, ho⟩ := h
          have hv := hS ⟨o, ho⟩
          rw [Nat.zero_add, ← e0] at hv
          exact load_holds_of hnS (hg _ ha) hv
        · exact hside a ha h
      · obtain ⟨d, p, o, rfl⟩ := storesOf_load haS
        rcases hneeds _ ha with (h | ⟨-, h⟩) | h
        · simp [needsSide] at h
        · exact absurd haS h
        · exact hside _ ha h
    obtain ⟨hd, -⟩ := chain_final hck rfl hat hpre (initCell_of_loads rfl hst hat (by rw [e0]; exact hS))
    have hv : ((cclSpec k atoms).vals σ).take ((cclSpec k atoms).len / 16) = cells := by
      have : (cclSpec k atoms).vals σ = cells := ccMsg_vals hl vc
      rw [this, List.take_of_length_le (by simp only [cclSpec]; omega)]
    rw [hv] at hd
    simp only [retOk, Bool.and_eq_true] at hret
    refine (rel_iff_sem hf _ _).mpr ⟨σ, ?_, ?_⟩
    · rw [hpar]
      simp only [List.map_cons, List.map_nil, e0, e1, e2, e3, e4, e5]
    · rw [hbody, holdsList_atoms_ret]
      refine ⟨hat, ?_⟩
      rw [List.map_cons, List.map_cons, List.map_nil, copy_sound hret.1 hat, copy_sound hret.2 hat,
        digestCells, ← hd]
  · exact absurd hok (by simp)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- **A group of child claims** (`__loop16`'s block at the counter `x`): the state after whole
blocks `pre` at `chain · x^13`, 17 honest records with the marks `base · x^17`, the state after
their cells at `chain · x^13` from offset `13`. -/
theorem l17_block {x N chain entries cover base origin limit : E} {n : ℕ} {pre : List UInt8}
    (hpre : pre.length = rate * n) (hS : StateAt rd (chain * x ^ 13) 0 (absorbChunks n zeroState pre))
    {os : ℕ → ℕ} {cells : List E} (hl : cells.length = 68) (hc : AllCanonical cells)
    (hrec : RecMem rd cover origin limit entries (base * x ^ 17) 17 os cells) {L : ℕ}
    (hL : limit = gen ^ L) (hL33 : L < 2 ^ 33) (hdef : BoundMem rd L)
    (hS' : StateAt rd (chain * x ^ 13) 13
      (absorbChunks (n + 8) zeroState (pre ++ cellsBytes cells))) :
    LoopBlock rd (coreProgram.getD 338 default) x N [chain, entries, cover, base, origin, limit] := by
  have hok := l17_ok
  have hcok := l17c_ok
  have hnb := l17_nb
  set fn := coreProgram.getD 338 default
  set A := loopAtoms fn with hAdef
  set S := storesOf 8 fn.body with hSdef
  simp only [l17Ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨-, hlen8⟩, hck⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hok
  simp only [l17cOk, Bool.and_eq_true, Option.isSome_iff_exists, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, List.mem_range] at hcok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape, c', hchk⟩, hpreA⟩, heqA⟩, hSL⟩, hcan⟩, hneeds⟩, hrc⟩, hstF⟩, hm13⟩,
    hm19⟩ := hcok
  have heqA' := atomsEqbL_sound heqA
  let args : List E := [x, N, chain, entries, cover, base, origin, limit]
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = B1.Val.ofArgs (ev rd (slotW 20 os) args fn.body) := ⟨_, rfl⟩
  have hidx : ∀ v, σ v = σ (.n v.idx) := fun v => by rw [hσ]; rfl
  obtain ⟨-, -, hgs⟩ := ev_spec rd (slotW 20 os) fn.body args hchk
  rw [show args.length = 8 from rfl, ← hσ] at hgs
  have hg : ∀ a ∈ A, Good rd S (slotW 20 os) σ a := fun a ha =>
    hgs (.atom a) (cl_pre_mem (cl_atom_mem (by rw [heqA']; exact ha)))
  have hpar : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7] := by
    have hs2 := hshape
    simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs2
    rw [hs2.1.2, hlen8]; rfl
  have par : ∀ i (hi : i < 8), σ (.n i) = args.getD i 0 := fun i hi => by
    rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args]; omega)
  have e0 : σ (.n 0) = x := par 0 (by omega)
  have e2 : σ (.n 2) = chain := par 2 (by omega)
  have e3 : σ (.n 3) = entries := par 3 (by omega)
  have e4 : σ (.n 4) = cover := par 4 (by omega)
  have e5 : σ (.n 5) = base := par 5 (by omega)
  have e6 : σ (.n 6) = origin := par 6 (by omega)
  have e7 : σ (.n 7) = limit := par 7 (by omega)
  have hF := pure_holds hg
  have v13 : σ (.n 13) = chain * x ^ 13 := by rw [monoIs_sound hm13 hF, e2, e0]
  have v19 : σ (.n 19) = base * x ^ 17 := by rw [monoIs_sound hm19 hF, e5, e0]
  have hwit : ∀ j < 17, σ (ccOV 20 j) = gen ^ os j := fun j hj =>
    (wit_val (recC_parts (hrc j hj)).1 hg).trans (w_slot 20 os j)
  have hmark : ∀ j < 17, σ (ccMark 20 l17P.marks j) = σ l17P.marks * gen ^ j := fun j hj =>
    markC_val (by omega) (recC_parts (hrc j hj)).2.1 hF
  have hrec' : RecMem rd (σ l17P.cover) (σ l17P.origin) (σ l17P.limit) (σ l17P.entries)
      (σ l17P.marks) 17 os cells := by
    show RecMem rd (σ (.n 4)) (σ (.n 6)) (σ (.n 7)) (σ (.n 3)) (σ (.n 19)) 17 os cells
    rw [e4, e6, e7, e3, v19]; exact hrec
  have hL' : σ l17P.limit = gen ^ L := e7.trans hL
  have vst : ∀ c : Fin 13, σ (l17St.getD c default) =
      cellsOfState (absorbChunks n zeroState pre) false c := by
    intro c
    simp only [stLoadsOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hstF
    rw [load_val_filter (hstF.2 c c.isLt) hg, v13, rdAt_of_load (hS c)]
  have vc : ∀ j < 17, ∀ c < 4, σ (.n (ccCell 20 j c)) = cells.getD (4 * j + c) 0 := by
    intro j hj c hc4
    exact cellRead_val ((recC_parts (hrc j hj)).2.2 c hc4) hF hg (hwit j hj) ((hrec' j hj).2.2 c hc4)
  have hA : ∀ i ∈ ccA l17St 20 17, IsCanonical128 (σ (.n i)) := by
    intro i hi
    rcases mem_ccA hi with ⟨v, hv, rfl⟩ | ⟨j, hj, c, hc4, rfl⟩
    · obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hv
      have hc13 := List.mem_range.mp hc'
      have := vst ⟨c, hc13⟩
      simp only [l17St, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range hc13, Option.map_some, Option.getD_some] at this
      rw [← hidx, this]
      exact canon_cellsOfState _ _ _
    · rw [vc j hj c hc4, List.getD_eq_getElem _ _ (by omega)]
      exact hc _ (List.getElem_mem _)
  have hside : ∀ a ∈ A, recSide (A.filter pureB) l17P 20 17 S a = true → a.Holds rd σ :=
    fun a ha hs => recSide_holds hF hg hwit hmark hrec' hL' hL33 hdef ha hs
  have hq : ∀ a, isLoadB a = false → decide (a ∉ S) = true := by
    intro a ha
    simp only [decide_eq_true_eq]
    intro hm
    rw [hSL a hm] at ha
    exact absurd ha (by simp)
  have hat : ∀ a ∈ A, a.Holds rd σ := by
    refine atoms_holds_stores (S := S) (w := slotW 20 os) hidx hcan hg hA
      (fun a ha hnS hns => Or.inl ?_) (fun h1 a ha haS => ?_)
    · rcases hneeds a ha with ((h | ⟨h, -⟩) | h) | h
      · rw [hns] at h; exact absurd h (by simp)
      · cases a <;> simp only [isLoadBelow, Bool.false_eq_true, Bool.and_eq_true,
          decide_eq_true_eq] at h
        rename_i d p o
        obtain ⟨rfl, ho⟩ := h
        have hv := hS ⟨o, ho⟩
        rw [Nat.zero_add, ← v13] at hv
        exact load_holds_of hnS (hg _ ha) hv
      · obtain ⟨c, hc', he⟩ := List.any_eq_true.mp h
        have hc13 := List.mem_range.mp hc'
        rw [atomEqb_sound he] at hnS ha ⊢
        have hv := hS' ⟨c, hc13⟩
        rw [← v13] at hv
        exact load_holds_of hnS (hg _ ha) hv
      · exact hside a ha h
    · rcases hneeds a ha with ((h | ⟨-, h⟩) | h) | h
      · obtain ⟨d, p, o, rfl⟩ := storesOf_load haS
        simp [needsSide] at h
      · exact absurd haS h
      · obtain ⟨c, hc', he⟩ := List.any_eq_true.mp h
        have hc13 := List.mem_range.mp hc'
        rw [atomEqb_sound he]
        have hG : ∀ b ∈ A.filter (fun a => decide (a ∉ S)), b.Holds rd σ :=
          fun b hb => h1 b (List.mem_filter.mp hb).1 (by simpa using (List.mem_filter.mp hb).2)
        have hchk' : (l17Spec A).check (A.filter (fun a => decide (a ∉ S))) = true := by
          rw [check_filter hq]; exact hck
        have h0 := initCell_of_loads (s := l17Spec A) rfl hstF hG
          (S := absorbChunks n zeroState pre) (by rw [v13]; exact hS)
        obtain ⟨hw, -, -⟩ := chain_whole hchk' rfl hG hpre h0
        have hv : (l17Spec A).vals σ = cells := ccMsg_vals hl vc
        show LoadHolds rd (σ (.n 13)) (13 + c) (σ ((l17Spec A).outV ((l17Spec A).nb - 1) c))
        have hwc := hw ⟨c, hc13⟩
        rw [hv, hnb, show ((⟨c, hc13⟩ : Fin 13) : ℕ) = c from rfl] at hwc
        rw [hnb, hwc, v13]
        exact hS' ⟨c, hc13⟩
      · exact hside a ha h
  refine ⟨σ, ?_, fun s hs => ?_⟩
  · rw [hpar]
    simp only [List.map_cons, List.map_nil]
    rw [e0, par 1 (by omega), e2, e3, e4, e5, e6, e7]
    rfl
  · have := hpreA s hs
    cases s <;> simp only [isAtomS, Bool.false_eq_true] at this
    rename_i a
    exact ⟨hat a (by have := cl_mem_atoms hs; rwa [heqA'] at this), trivial⟩

end
end LeanVM.Guest.B1.Digest
