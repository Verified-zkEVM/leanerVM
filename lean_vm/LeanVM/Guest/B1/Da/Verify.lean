/-
  LeanVM.Guest.B1.Da.Verify

  `da_verify`'s core IR gives its meaning (TRIAGE G #90).
-/

module

public import LeanVM.Guest.B1.Da.VerifyHelp
public import LeanVM.Guest.B1.Da.VerifyChain0
public import LeanVM.Guest.B1.Da.VerifyChain1
public import LeanVM.Guest.B1.Da.VerifyChain2
public import LeanVM.Guest.B1.Da.VerifyChain3

/-!
# `da_verify`, sound

`da_verify_holds : da_verify_sound_Spec`: with the exponent table, a run of `da_verify` returns
the cells of a root and a vector digest that a witness opens (`opens_of`). The witness's rows are
the symbols the cell checks hinted, its vector the weights the column checks hinted; the run's
loops make the returned root the hash of the row tree's root and the column tree's over those
cells (`levels_root_of`, `cellRoot_mRoot`), the returned vector digest the hash of the columns'
digests, and every row's running sum of its cells' dot products zero.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

theorem list_eq_getD {l1 l2 : List E} {n : ℕ} (h1 : l1.length = n) (h2 : l2.length = n)
    (h : ∀ c < n, l1.getD c 0 = l2.getD c 0) : l1 = l2 :=
  List.ext_getElem (by omega) fun c hc1 hc2 => by
    have := h c (by omega)
    rwa [List.getD_eq_getElem _ _ hc1, List.getD_eq_getElem _ _ hc2] at this

theorem ordG_of {x : ℕ} (h : x ≤ 4096) : x < ordG := by unfold ordG; omega

set_option maxHeartbeats 4000000 in
/-- **`da_verify`'s core IR gives its meaning.** -/
theorem da_verify_holds : da_verify_sound_Spec := by
  intro rd hm args rets hrel
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_da_verify _ _).mp hrel
  have hok := dv_ok
  unfold dvOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hparams, hbody⟩, hflat⟩, hcrs⟩, hm11⟩, hg18⟩, hm25⟩, hg19⟩,
    hc32⟩, hc20⟩, hc33⟩, hc21⟩, hg22⟩, hc7⟩, hm40⟩, hg23⟩, hg24⟩, hdisp⟩, hroot⟩, hcp993⟩,
    hcp994⟩, hld17⟩, hvshape⟩, hvnb⟩, hcp995⟩, hcp996⟩ := hok
  rw [hparams] at hpar
  simp only [List.map_cons, List.map_nil] at hpar
  subst hpar
  rw [stmtsEqb_sound hbody, holdsList_append] at hb
  obtain ⟨hall, hret⟩ := holdsList_flat dvP hflat _ _ hb
  simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hret
  have hat := atoms_of_flat hall
  simp only [MeaningDaVerify]
  intro hsq
  -- the shape
  have hrs := da_row_shape_holds rd hm _ _ (call_of_flat hall hcrs)
  simp only [List.map_cons, List.map_nil, MeaningDaRowShape] at hrs
  obtain ⟨r, L, hr1, hr, hL, h1, h2, hnp, h34⟩ := hrs hsq
  simp only [List.cons.injEq, and_true] at h34
  obtain ⟨h3, h4⟩ := h34
  unfold LeanDa.maxRows at hr
  have hL2 : 2 ^ L ≤ 1024 := by
    calc 2 ^ L ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) hL
      _ = 1024 := by norm_num
  have hrL : r ≤ 2 ^ L := by
    rw [hnp, LeanDa.nPad, LeanDa.logPad]; exact Nat.le_pow_clog (by norm_num) r
  -- the prefix bases and the running sums
  have L18 : ∀ i < r, LoadHolds rd (σ (.n 13) * gen ^ i) 0 (σ (.n 12) * (gen ^ i) ^ 128) :=
    loop_sound (f := "__loop18") (ps := [σ (.n 1), σ (.n 13), σ (.n 12)]) (ordG_of (by omega)) h1
      (fun y hy => by
        obtain ⟨k1, k2⟩ := l18_step hy
        exact ⟨k1 _ _ _ rfl, k2⟩)
      (fun hne => by simpa using guardK_sound hg18 hall hne)
  have L19 : ∀ i < r, LoadHolds rd (σ (.n 27) * gen ^ i) 0 (σ (.n 26) * (gen ^ i) ^ 129) ∧
      LoadHolds rd (σ (.n 26) * (gen ^ i) ^ 129) 0 0 :=
    loop_sound (f := "__loop19") (ps := [σ (.n 1), σ (.n 26), σ (.n 27)]) (ordG_of (by omega)) h1
      (fun y hy => by
        obtain ⟨k1, k2⟩ := l19_step hy
        exact ⟨k1 _ _ _ rfl, k2⟩)
      (fun hne => by simpa using guardK_sound hg19 hall hne)
  have L22 : ∀ i < r, ∃ ch, LoadHolds rd (σ (.n 27) * gen ^ i) 0 ch ∧ LoadHolds rd ch 128 0 :=
    loop_sound (f := "__loop22") (ps := [σ (.n 1), σ (.n 27)]) (ordG_of (by omega)) h1
      (fun y hy => by
        obtain ⟨k1, k2⟩ := l22_step hy
        exact ⟨k1 _ _ rfl, k2⟩)
      (fun hne => by simpa using guardK_sound hg22 hall hne)
  -- the columns
  have c20 := call_of_flat hall hc20
  have c21 := call_of_flat hall hc21
  simp only [List.map_cons, List.map_nil] at c20 c21
  rw [const_sound hc32 hat, word_one, ← pow_zero gen] at c20
  rw [const_sound hc33 hat, word_g64] at c21
  rw [h1, h2, h3, h4] at c20 c21
  have C1 : ∀ j < 64, coreProgram.Rel rd "da_verify_column__L1" (gen ^ j :: [gen ^ r, gen ^ 2 ^ L,
      gen ^ (2 ^ L - r), gen ^ L, σ (.n 13), σ (.n 31), σ (.n 27), σ (.n 17)]) [] := fun j hj =>
    loop_from (f := "__loop20") (N := gen ^ 64) (m := 64) (a := 0) (ordG_of (by omega)) rfl
      (fun y hy => by
        obtain ⟨k1, k2⟩ := col_loop_step (by rw [coreProgram_length]; omega) l20_ok hy
        exact ⟨k1, by rw [← word_g64]; exact k2⟩) c20 j (Nat.zero_le _) hj
  have C0 : ∀ j, 64 ≤ j → j < 128 → coreProgram.Rel rd "da_verify_column__L0" (gen ^ j ::
      [gen ^ r, gen ^ 2 ^ L, gen ^ (2 ^ L - r), gen ^ L, σ (.n 13), σ (.n 31), σ (.n 27),
        σ (.n 17)]) [] :=
    loop_from (f := "__loop21") (N := gen ^ 128) (m := 128) (a := 64) (ordG_of (by omega)) rfl
      (fun y hy => by
        obtain ⟨k1, k2⟩ := col_loop_step (by rw [coreProgram_length]; omega) l21_ok hy
        exact ⟨k1, by rw [← word_g128]; exact k2⟩) c21
  have hr' : r < ordG := ordG_of (by omega)
  have hg' : 2 ^ L - r < ordG := ordG_of (by omega)
  have colF : ∀ j, ∃ lv node c0 c1 : E, j < 128 →
      coreProgram.Rel rd "da_vector_cell" [σ (.n 17) * (gen ^ j) ^ 2] [lv] ∧
      (∀ i < r, RowStepC rd lv (σ (.n 27)) (gen ^ j) node (σ (.n 13)) (decide (j < 64)) (gen ^ i)) ∧
      (∀ d < 2 ^ L - r, GapStepC rd node (gen ^ r) (gen ^ d)) ∧
      (∃ k < 11, gen ^ L = ofK (Parameters.gpow k) ∧
        coreProgram.Rel rd (daLevelsName k) [node] [c0, c1]) ∧
      LoadHolds rd (σ (.n 31) * (gen ^ j) ^ 2) 0 c0 ∧ LoadHolds rd (σ (.n 31) * (gen ^ j) ^ 2) 1 c1 := by
    intro j
    by_cases hj : j < 128
    · by_cases hj64 : j < 64
      · obtain ⟨lv, node, c0, c1, k⟩ := col_step (store := true) (by rw [coreProgram_length]; omega)
          (by rw [coreProgram_length]; omega) (by rw [coreProgram_length]; omega) col1_ok row417_ok
          gap418_ok hr' hg' (C1 j hj64)
        exact ⟨lv, node, c0, c1, fun _ => by simpa [hj64] using k⟩
      · obtain ⟨lv, node, c0, c1, k⟩ := col_step (store := false) (by rw [coreProgram_length]; omega)
          (by rw [coreProgram_length]; omega) (by rw [coreProgram_length]; omega) col0_ok row419_ok
          gap420_ok hr' hg' (C0 j (by omega) hj)
        exact ⟨lv, node, c0, c1, fun _ => by simpa [hj64] using k⟩
    · exact ⟨0, 0, 0, 0, fun h => absurd h hj⟩
  choose lv node c0 c1 hcol using colF
  -- the columns' weights
  have vecF : ∀ j, ∃ ws : List E, j < 128 → ws.length = 256 ∧
      (∀ k < 256, ∀ w, rd ((lv j).limb 0 * Parameters.gpow k) = some w → w = ws.getD k 0) ∧
      ReadsAt rd (σ (.n 17) * (gen ^ j) ^ 2) (digestCells (keccak256 (ws.flatMap Node.eBytes))) := by
    intro j
    by_cases hj : j < 128
    · have := da_vector_cell_holds rd _ _ (hcol j hj).1
      obtain ⟨ws, hl, -, hfr, hrd⟩ := this
      exact ⟨ws, fun _ => ⟨hl, hfr, hrd⟩⟩
    · exact ⟨[], fun h => absurd h hj⟩
  choose ws hws using vecF
  -- the cells
  have cellF : ∀ i j, ∃ (sy : List K) (s : E), i < r → j < 128 → sy.length = 256 ∧
      s = ∑ e ∈ Finset.range 256, (ws j).getD e 0 * ofK (sy.getD e 0) ∧
      LoadHolds rd (node j * (gen ^ i) ^ 2) 0 (digestScalars (keccak256 (sy.flatMap kBytes))).1 ∧
      LoadHolds rd (node j * (gen ^ i) ^ 2) 1 (digestScalars (keccak256 (sy.flatMap kBytes))).2 ∧
      LoadHolds rd (memAt rd (σ (.n 27) * gen ^ i) 0 * gen ^ j) 1
        (memAt rd (memAt rd (σ (.n 27) * gen ^ i) 0 * gen ^ j) 0 + s) ∧
      (j < 64 → LoadHolds rd (memAt rd (σ (.n 13) * gen ^ i) 0 * (gen ^ j) ^ 2) 0
          (digestScalars (keccak256 (sy.flatMap kBytes))).1 ∧
        LoadHolds rd (memAt rd (σ (.n 13) * gen ^ i) 0 * (gen ^ j) ^ 2) 1
          (digestScalars (keccak256 (sy.flatMap kBytes))).2) := by
    intro i j
    by_cases hij : i < r ∧ j < 128
    · obtain ⟨d0, d1, s, hc, -, hch, hn0, hn1, hst⟩ := (hcol j hij.2).2.1 i hij.1
      obtain ⟨sy, wc, hsl, hwrd, hwl, hrets⟩ := da_verify_cell_holds rd _ _ hc
      simp only [digestCells, List.cons_append, List.nil_append, List.cons.injEq, and_true] at hrets
      obtain ⟨e0, e1, es⟩ := hrets
      obtain ⟨-, hfr, -⟩ := hws j hij.2
      have hwc : ∀ e < 256, wc.getD e 0 = (ws j).getD e 0 := by
        intro e he
        have := hwrd e (by unfold LeanDa.cellSymbols at hwl; omega)
        rw [List.getD_eq_getElem _ _ (by unfold LeanDa.cellSymbols at hwl; omega)]
        exact hfr e he _ this.2
      refine ⟨sy, s, fun _ _ => ⟨hsl, ?_, ?_, ?_, hch, fun h64 => ?_⟩⟩
      · rw [es, list_sum_range]
        exact Finset.sum_congr rfl fun e he => by rw [hwc e (Finset.mem_range.mp he)]
      · rw [← e0]; exact hn0
      · rw [← e1]; exact hn1
      · obtain ⟨k0, k1⟩ := hst (by simp [h64])
        rw [← e0, ← e1]; exact ⟨k0, k1⟩
    · exact ⟨[], 0, fun h1 h2 => absurd ⟨h1, h2⟩ hij⟩
  choose syms s hcell using cellF
  -- the witness's data, padded outside the run's ranges
  let symsP : ℕ → ℕ → List K := fun i j => if i < r ∧ j < 128 then syms i j else List.replicate 256 0
  let wsP : ℕ → List E := fun j => if j < 128 then ws j else List.replicate 256 0
  have hsP : ∀ i j, i < r → j < 128 → symsP i j = syms i j := fun i j hi hj => by
    simp only [symsP, hi, hj, and_self, ite_true]
  have hwP : ∀ j, j < 128 → wsP j = ws j := fun j hj => by simp only [wsP, hj, ite_true]
  have hsL : ∀ i j, (symsP i j).length = 256 := fun i j => by
    by_cases h : i < r ∧ j < 128
    · rw [hsP i j h.1 h.2]; exact (hcell i j h.1 h.2).1
    · simp only [symsP, h, ite_false, List.length_replicate]
  have hwL : ∀ j, (wsP j).length = 256 := fun j => by
    by_cases h : j < 128
    · rw [hwP j h]; exact (hws j h).1
    · simp only [wsP, h, ite_false, List.length_replicate]
  -- the rows' sums
  have hdot : ∀ i < r, ∑ j ∈ Finset.range 128, ∑ e ∈ Finset.range 256,
      (wsP j).getD e 0 * ofK ((symsP i j).getD e 0) = 0 := by
    intro i hi
    obtain ⟨hb0, hz⟩ := L19 i hi
    have hm27 := memAt_of_load hb0
    have acc : ∀ j ≤ 128, LoadHolds rd (σ (.n 26) * (gen ^ i) ^ 129) j
        (∑ j' ∈ Finset.range j, s i j') := by
      intro j
      induction j with
      | zero => intro _; simpa using hz
      | succ j ih =>
        intro hj
        have ih' := ih (by omega)
        obtain ⟨-, -, -, -, hst, -⟩ := hcell i j hi (by omega)
        rw [hm27] at hst
        have e0 := memAt_of_load ((loadHolds_mul_gen_pow rd _ j 0 _).mpr ih')
        rw [e0] at hst
        rw [Finset.sum_range_succ]
        exact (loadHolds_mul_gen_pow rd _ j 1 _).mp hst
    obtain ⟨ch, hc1, hc2⟩ := L22 i hi
    rw [loadHolds_unique hc1 hb0] at hc2
    have hsum := loadHolds_unique (acc 128 le_rfl) hc2
    refine (Finset.sum_congr rfl fun j hj => ?_).trans hsum
    have hj' := Finset.mem_range.mp hj
    rw [(hcell i j hi hj').2.1, hsP i j hi hj', hwP j hj']
  -- the columns' roots
  have hcr : ∀ j < 128, (c0 j, c1 j) = digestScalars (mRoot L (cellLeaf r symsP j)) := by
    intro j hj
    obtain ⟨-, -, hgaps, ⟨k, hk, hkL, hrel⟩, -, -⟩ := hcol j hj
    refine levels_root_of hk hL hkL.symm hrel fun i hi => ?_
    by_cases hir : i < r
    · obtain ⟨-, -, hn0, hn1, -, -⟩ := hcell i j hir hj
      rw [shift2] at hn0 hn1
      simp only [cellLeaf, hir, ite_true, cellD, hsP i j hir hj]
      exact ⟨by simpa using hn0, hn1⟩
    · obtain ⟨g0, g1⟩ := hgaps (i - r) (by omega)
      rw [← pow_mul, shift, show r * 2 + 2 * (i - r) = 2 * i by omega] at g0 g1
      simp only [cellLeaf, hir, ite_false]
      exact ⟨by simpa using g0, g1⟩
  -- the column tree
  have hct : (σ (.n 37), σ (.n 38)) = digestScalars (mRoot 7 fun j => mRoot L (cellLeaf r symsP j)) := by
    have c7 := call_of_flat hall hc7
    simp only [List.map_cons, List.map_nil] at c7
    refine levels_root_of (k := 7) (L := 7) (by norm_num) (by norm_num) (gen_pow_eq_ofK 7).symm c7
      fun j hj => ?_
    obtain ⟨-, -, -, -, s0, s1⟩ := hcol j (by simpa using hj)
    rw [shift2] at s0 s1
    have e := hcr j (by simpa using hj)
    simp only [Prod.ext_iff] at e
    rw [← e.1, ← e.2]
    exact ⟨by simpa using s0, s1⟩
  -- the row tree
  have L23 : ∀ i < r, ∃ run, LoadHolds rd (σ (.n 13) * gen ^ i) 0 run ∧
      ReadsAt rd run (memRun rd run 128) ∧
      LoadHolds rd (σ (.n 41) * (gen ^ i) ^ 2) 0
        (digestScalars (keccak256 (cellsBytes (memRun rd run 128)))).1 ∧
      LoadHolds rd (σ (.n 41) * (gen ^ i) ^ 2) 1
        (digestScalars (keccak256 (cellsBytes (memRun rd run 128)))).2 :=
    loop_sound (f := "__loop23") (ps := [σ (.n 1), σ (.n 13), σ (.n 41)]) (ordG_of (by omega)) h1
      (fun y hy => by
        obtain ⟨k1, k2⟩ := l23_step hy
        exact ⟨k1 _ _ _ rfl, k2⟩)
      (fun hne => by simpa using guardK_sound hg23 hall hne)
  have L24 : ∀ d < 2 ^ L - r, GapRowC rd (σ (.n 41)) (σ (.n 1)) (gen ^ d) :=
    loop_sound (f := "__loop24") (ps := [σ (.n 4), σ (.n 41), σ (.n 1)]) hg' h4
      (fun y hy => by
        obtain ⟨k1, k2⟩ := l24_step hy
        exact ⟨k1 _ _ _ rfl, k2⟩)
      (fun hne => by simpa using guardK_sound hg24 hall hne)
  have hrowd : ∀ i < r, LoadHolds rd (σ (.n 41)) (2 * i) (digestScalars (rowD symsP i)).1 ∧
      LoadHolds rd (σ (.n 41)) (2 * i + 1) (digestScalars (rowD symsP i)).2 := by
    intro i hi
    obtain ⟨run, hrun, -, k0, k1⟩ := L23 i hi
    have hm13 := memAt_of_load hrun
    have hmem : memRun rd run 128 = (List.range 64).flatMap fun j => digestCells (cellD symsP i j) := by
      refine list_eq_getD (n := 128) (by simp) (by
        rw [length_flatMap_range _ 2 _ (fun j => rfl)]) fun c hc => ?_
      have hc' : c = 2 * (c / 2) + c % 2 := by omega
      rw [hc', flatMap_getD (fun j => digestCells (cellD symsP i j)) 2 (fun j => rfl) 0 64 (c / 2)
        (c % 2) (by omega) (by omega)]
      simp only [memRun, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range (show 2 * (c / 2) + c % 2 < 128 by omega), Option.map_some,
        Option.getD_some]
      obtain ⟨-, -, -, -, -, hpre⟩ := hcell i (c / 2) hi (by omega)
      obtain ⟨p0, p1⟩ := hpre (by omega)
      rw [hm13, shift2] at p0 p1
      have e2 : cellD symsP i (c / 2) = keccak256 ((syms i (c / 2)).flatMap kBytes) := by
        rw [cellD, hsP i (c / 2) hi (by omega)]
      rcases (show c % 2 = 0 ∨ c % 2 = 1 by omega) with h | h
      · rw [h, memAt_of_load (by simpa using p0), e2]; rfl
      · rw [h, memAt_of_load p1, e2]; rfl
    have hbytes : cellsBytes (memRun rd run 128) =
        (List.range 64).flatMap fun j => digestBytes (cellD symsP i j) := by
      rw [hmem, cellsBytes, List.flatMap_assoc]
      refine List.flatMap_congr fun j _ => ?_
      rw [digestBytes_eq_cells, cellsBytes]; rfl
    rw [hbytes, shift2] at k0 k1
    exact ⟨by simpa [rowD] using k0, by simpa [rowD] using k1⟩
  have hrt : (σ (.n 48), σ (.n 49)) = digestScalars (mRoot L (rowLeaf r symsP)) := by
    obtain ⟨k, hk, hk2, hrel⟩ := dispatch_of_flat hall hdisp
    simp only [dlNames, List.length_map, List.length_range] at hk
    simp only [dlNames, List.getElem_map, List.getElem_range, List.map_cons, List.map_nil] at hrel
    refine levels_root_of hk hL (by rw [← hk2, h2]) hrel fun i hi => ?_
    by_cases hir : i < r
    · simp only [rowLeaf, hir, ite_true]
      exact hrowd i hir
    · obtain ⟨g0, g1⟩ := L24 (i - r) (by omega)
      rw [h1, ← pow_mul, shift, show r * 2 + 2 * (i - r) = 2 * i by omega] at g0 g1
      simp only [rowLeaf, hir, ite_false]
      exact ⟨by simpa using g0, g1⟩
  -- the root
  have hrootd : [σ (.n 993), σ (.n 994)] = digestCells (daRoot r L symsP) := by
    obtain ⟨hd, -⟩ := chain_final hroot rfl hat (pre := []) (n := 0) rfl
      (fun c => (cellsOfState_zero false c).symm)
    have hv : ((rootSpec (atomsIn dvP)).vals σ).take ((rootSpec (atomsIn dvP)).len / 16) =
        [σ (.n 48), σ (.n 49), σ (.n 37), σ (.n 38)] := by
      simp [rootSpec, ChainSpec.vals, srcVal]
    rw [hv, List.nil_append] at hd
    simp only [Prod.ext_iff] at hrt hct
    rw [hrt.1, hrt.2, hct.1, hct.2] at hd
    have hb : cellsBytes [(digestScalars (mRoot L (rowLeaf r symsP))).1,
        (digestScalars (mRoot L (rowLeaf r symsP))).2,
        (digestScalars (mRoot 7 fun j => mRoot L (cellLeaf r symsP j))).1,
        (digestScalars (mRoot 7 fun j => mRoot L (cellLeaf r symsP j))).2] =
        digestBytes (mRoot L (rowLeaf r symsP)) ++
          digestBytes (mRoot 7 fun j => mRoot L (cellLeaf r symsP j)) := by
      rw [digestBytes_eq_cells, digestBytes_eq_cells]
      simp [cellsBytes]
    rw [hb, ← daRoot] at hd
    rw [copy_sound hcp993 hat, copy_sound hcp994 hat, digestCells]
    simp only [Prod.ext_iff] at hd
    rw [← hd.1, ← hd.2]
  -- the vector's digest
  have hvd : [σ (.n 995), σ (.n 996)] = digestCells (daVd wsP) := by
    have hchk : (vdSpec (atomsIn dvP)).check (atomsIn dvP) = true :=
      ChainSpec.check_of_parts hvshape fun k hk => by
        rcases Nat.lt_or_ge k 8 with a | a
        · exact ChainSpec.partOk_sound vd_chain0_ok k (by omega) a
        rcases Nat.lt_or_ge k 16 with b | b
        · exact ChainSpec.partOk_sound vd_chain1_ok k a b
        rcases Nat.lt_or_ge k 24 with c | c
        · exact ChainSpec.partOk_sound vd_chain2_ok k b c
        · exact ChainSpec.partOk_sound vd_chain3_ok k c (by omega)
    obtain ⟨hd, -⟩ := chain_final hchk rfl hat (pre := []) (n := 0) rfl
      (fun c => (cellsOfState_zero false c).symm)
    have hr := loads_sound hld17 hat
    have hv0 : (((List.range 256).map fun i => some (V.n (69 + i))).map (srcVal σ)) =
        memRun rd (σ (.n 17)) 256 := by
      have := readsAt_memRun hr
      simpa using this
    have hv : ((vdSpec (atomsIn dvP)).vals σ).take ((vdSpec (atomsIn dvP)).len / 16) =
        memRun rd (σ (.n 17)) 256 := by
      rw [← hv0, show (vdSpec (atomsIn dvP)).len / 16 = 256 by simp [vdSpec]]
      simp [vdSpec, ChainSpec.vals]
    have hmem : memRun rd (σ (.n 17)) 256 =
        (List.range 128).flatMap fun j => digestCells (colD wsP j) := by
      refine list_eq_getD (n := 256) (by simp) (by
        rw [length_flatMap_range _ 2 _ (fun j => rfl)]) fun c hc => ?_
      have hc' : c = 2 * (c / 2) + c % 2 := by omega
      rw [hc', flatMap_getD (fun j => digestCells (colD wsP j)) 2 (fun j => rfl) 0 128 (c / 2)
        (c % 2) (by omega) (by omega)]
      simp only [memRun, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range (show 2 * (c / 2) + c % 2 < 256 by omega), Option.map_some,
        Option.getD_some]
      obtain ⟨-, -, hrd⟩ := hws (c / 2) (by omega)
      have p0 := hrd 0 (by simp [digestCells])
      have p1 := hrd 1 (by simp [digestCells])
      rw [shift2] at p0 p1
      have e2 : colD wsP (c / 2) = keccak256 ((ws (c / 2)).flatMap Node.eBytes) := by
        rw [colD, hwP (c / 2) (by omega)]
      rcases (show c % 2 = 0 ∨ c % 2 = 1 by omega) with h | h
      · rw [h, memAt_of_load (by simpa using p0), e2]; rfl
      · rw [h, memAt_of_load p1, e2]; rfl
    have hbytes : cellsBytes ((List.range 128).flatMap fun j => digestCells (colD wsP j)) =
        (List.range 128).flatMap fun j => digestBytes (colD wsP j) := by
      rw [cellsBytes, List.flatMap_assoc]
      refine List.flatMap_congr fun j _ => ?_
      rw [digestBytes_eq_cells, cellsBytes]; rfl
    rw [hv, hmem, hbytes, List.nil_append, ← daVd] at hd
    rw [copy_sound hcp995 hat, copy_sound hcp996 hat, digestCells]
    simp only [Prod.ext_iff] at hd
    rw [← hd.1, ← hd.2]
  refine ⟨⟨daRows r symsP, daVector wsP⟩, daRoot r L symsP, daVd wsP,
    opens_of hr1 (by unfold LeanDa.maxRows; exact hr) hnp.symm hrL hsL hwL hdot, ?_⟩
  rw [← hret, ← hrootd, ← hvd]
  rfl

end
end LeanVM.Guest.B1.Da
