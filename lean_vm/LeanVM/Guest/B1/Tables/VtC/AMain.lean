/-
  LeanVM.Guest.B1.Tables.VtC.AMain

  **`verify_tables` is complete at the `Rel` level**: on the honest memory and oracle, every
  statement holds, its loads read inside the layout, its allocations are the allocator's and it
  returns the honest words.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.ADefs
public import LeanVM.Guest.B1.Tables.VtC.AOracle
public import LeanVM.Guest.B1.Tables.VtC.AGlue
public import LeanVM.Guest.B1.Tables.VtC.SLoads
public import LeanVM.Guest.B1.Tables.VtC.ZTail
public import LeanVM.Guest.B1.Tables.VtC.ZInBuf
public import LeanVM.Guest.B1.Tables.VtC.FComplete
public import LeanVM.Guest.B1.Tables.VtC.FInBuf

/-!
# Assembly

`VtShape`: the deployed shapes the ranges need. `vt_rel_complete`: from the specification's
accepting run (`VtHonest.Ok`), on a memory defined below `2^8` holding the caller's buffers
(`linL`) and the own buffers at the allocator's positions (`ownL`), with the oracle's answers
(`VtWOk`), the honest valuation satisfies every statement of `verify_tables`, its loads read inside
the layout, and it returns the honest words. `vt_rel_complete_vtW`: the same with the explicit
oracle `vtW`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (termsPure blockSel)
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- **The deployed shapes.** -/
structure VtShape (H : VtHonest) : Prop where
  hlm : H.lm ≤ 32
  hlmμ : H.lm ≤ H.point.length
  h19 : 19 ≤ H.point.length
  hμ33 : H.point.length < 33
  hr : H.rows.length = 6
  hτ29 : ∀ t < 6, vtHt H.rows t < 29
  hτμ : ∀ t < 6, vtHt H.rows t ≤ H.point.length
  hal : H.alphas.length = 4
  hf : H.f.length = 5
  hfcan : ∀ i < 5, IsCanonical128 (H.f.getD i 0)
  hfitP : ((vtSizesP H.lm (vtHt H.rows)).map (2 ^ ·)).sum ≤ 2 ^ H.point.length
  hfitC : ((vtSizesC (vtHt H.rows)).map (2 ^ ·)).sum ≤ 2 ^ H.point.length
  hbc : H.bc.length = 2 ^ 23

/-! ## Facts of the data -/

theorem vtKap_src_adj : ∀ b < 153, blockKappaAdj b ≠ 0 → blockKappaSrc.getD b 0 = 0 := by decide

/-- A block's log-size is below `34`. -/
theorem vtKap_lt {lm : ℕ} {τ : ℕ → ℕ} (hlm : lm ≤ 32) (hτ : ∀ t < 6, τ t < 29) {b : ℕ}
    (hb : b < 153) : vtKap lm τ b < 34 := by
  unfold vtKap
  have hs := vt_src_lt b hb
  by_cases ha : blockKappaAdj b = 0
  · rw [ha, Nat.add_zero]
    generalize hsrc : blockKappaSrc.getD b 0 = s at hs
    match s, hs with
    | 0, _ => simp
    | 1, _ => simpa using (by omega : lm < 34)
    | t + 2, h => rw [vt_tau_getD lm τ (by omega)]; have := hτ t (by omega); omega
  · rw [vtKap_src_adj b hb ha]
    have : blockKappaAdj b ≤ 19 := by unfold blockKappaAdj; split_ifs <;> omega
    simp; omega

theorem vtHt_eq {rows : List ℕ} (hr : rows.length = 6) {t : ℕ} (ht : t < 6) :
    vtHt rows t = max (log2Ceil (vtRw rows t)) (tableLogFloors.getD t 0) := by
  unfold vtHt vtRw tableHeightsOf
  rw [List.getD_eq_getElem _ _ (by simp [hr, tableLogFloors]; omega)]
  simp only [List.getElem_zipWith]
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by simp [tableLogFloors]; omega)]

theorem ownW_length (H : VtHonest) (B : VtBases) : (H.ownW B).length = 110 := by
  simp [VtHonest.ownW]

theorem ownB_length (H : VtHonest) (B : VtBases) : (H.ownB B).length = 110 := by
  simp [VtHonest.ownB, VtHonest.sizes, LeanVM.Guest.Memory.length_bases]

theorem offBits_length (off : ℕ) : (offBits off).length = 34 := by simp [offBits]

theorem cap0_length (H : VtHonest) : H.cap0.length = 5 := by
  simp [VtHonest.cap0, Fs.squeeze, capOf]

/-- The own buffers' honest words fill their allocations. -/
theorem ownW_lengths (H : VtHonest) (B : VtBases) : (H.ownW B).map List.length = H.sizes := by
  have h5 := cap0_length H
  have r : ∀ (m : ℕ) (f : ℕ → ℕ), ((List.range m).map fun i ↦ offBits (f i)).map List.length =
      List.replicate m 34 := fun m f ↦ by
    apply List.ext_getElem (by simp)
    intro k _ _
    simp [offBits_length]
  simp only [VtHonest.ownW, VtHonest.sizes, List.map_append, r]
  rw [show List.replicate 99 34 = List.replicate 54 34 ++ List.replicate 45 34 from
    (List.replicate_add 54 45 34).symm]
  simp [VtHonest.μ, vtSortW, vtSideW, vtOffW, vtIdxcW, vtShEqW_length, vtShGW_length, vtIdxBufW,
    zcRoundsW_len h5, zcCprodW]

theorem tb_load_of {rd : Reader} {p : E} {l : List E} (h : TbReadsAt rd p l) {k : ℕ}
    (hk : k < l.length) : LoadHolds rd p k (l.getD k 0) := by
  rw [List.getD_eq_getElem _ _ hk]; exact h k hk

theorem vtAllocVars_F : ∀ b < 3, vtAllocVars.getD (8 + b) 0 = vtFwV.getD b 0 + 6 := by decide
theorem vtAllocVars_P : ∀ i < 51, vtAllocVars.getD (11 + i) 0 = (vtPushSel.getD i default).2.2.1 + 6 := by
  decide
theorem vtAllocVars_C : ∀ i < 45, vtAllocVars.getD (62 + i) 0 =
    (vtCountSel.getD i default).2.2.1 + 6 := by decide

theorem ownW_getD_P (H : VtHonest) (B : VtBases) {i : ℕ} (hi : i < 54) :
    (H.ownW B).getD (8 + i) [] = offBits (H.offP.getD i 0) := by
  unfold VtHonest.ownW
  rw [List.append_assoc, List.append_assoc, List.getD_append_right _ _ _ _ (by simp),
    show 8 + i - [vtSortW H.κ, vtSideW, vtOffW H.κ, vtIdxcW, H.point.map (1 + ·),
      vtShEqW H.point H.τ, vtShGW H.point H.τ, vtIdxBufW H.point H.lm].length = i by simp,
    List.getD_append _ _ _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega)]
  simp

theorem ownW_getD_C (H : VtHonest) (B : VtBases) {i : ℕ} (hi : i < 45) :
    (H.ownW B).getD (8 + (54 + i)) [] = offBits (H.offC.getD i 0) := by
  unfold VtHonest.ownW
  rw [List.append_assoc, List.append_assoc, List.getD_append_right _ _ _ _ (by simp),
    show 8 + (54 + i) - [vtSortW H.κ, vtSideW, vtOffW H.κ, vtIdxcW, H.point.map (1 + ·),
      vtShEqW H.point H.τ, vtShGW H.point H.τ, vtIdxBufW H.point H.lm].length = 54 + i by simp,
    List.getD_append_right _ _ _ _ (by simp), List.getD_append _ _ _ _ (by simp; omega)]
  simp [List.getD_eq_getElem?_getD, hi]

theorem ownW_getD_Z (H : VtHonest) (B : VtBases) {k : ℕ} (_hk : k < 3) :
    (H.ownW B).getD (107 + k) [] =
      [zcRoundsW H.cap0 H.target (ofK (gpow B.cur) * gen ^ 5) H.xsR H.n,
        zcCprodW H.cap0 H.target H.xsR H.n,
        (List.range (H.n + 1)).map (prefixProd 1 H.chiW ((H.point.map (1 + ·)).take H.n))].getD k
        [] := by
  unfold VtHonest.ownW
  rw [List.getD_append_right _ _ _ _ (by simp)]
  congr 1
  simp

theorem foldl_max_ge : ∀ (l : List ℕ) (a : ℕ), a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a
  | [], a => ⟨le_rfl, by simp⟩
  | y :: l, a => by
    obtain ⟨h1, h2⟩ := foldl_max_ge l (max a y)
    refine ⟨le_trans (le_max_left _ _) h1, fun x hx ↦ ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_trans (le_max_right _ _) h1
    · exact h2 x hx

theorem foldl_max_mem : ∀ (l : List ℕ) (a : ℕ), l.foldl max a = a ∨ l.foldl max a ∈ l
  | [], a => Or.inl rfl
  | y :: l, a => by
    rcases foldl_max_mem l (max a y) with h | h
    · simp only [List.foldl_cons, h]
      rcases max_choice a y with e | e
      · exact Or.inl e
      · exact Or.inr (by rw [e]; exact List.mem_cons_self)
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem vt_n_ge {H : VtHonest} (hr : H.rows.length = 6) {t : ℕ} (ht : t < 6) : H.τ t ≤ H.n := by
  have := (foldl_max_ge (tableHeightsOf H.rows) 0).2 (H.τ t) (by
    rw [vt_tableHeights_eq hr]; exact List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩)
  exact this

theorem vt_n_ex {H : VtHonest} (hr : H.rows.length = 6) : ∃ t < 6, H.τ t = H.n := by
  rcases foldl_max_mem (tableHeightsOf H.rows) 0 with h | h
  · refine ⟨0, by norm_num, ?_⟩
    have := vt_n_ge hr (t := 0) (by norm_num)
    unfold VtHonest.n at this ⊢; rw [h] at this ⊢; omega
  · rw [vt_tableHeights_eq hr] at h
    obtain ⟨t, ht, e⟩ := List.mem_map.mp h
    refine ⟨t, List.mem_range.mp ht, ?_⟩
    show vtHt H.rows t = (tableHeightsOf H.rows).foldl max 0
    rw [vt_tableHeights_eq hr]; exact e

theorem vt_target_eq (H : VtHonest) (ξ T0 T1 T2 : E)
    (h0 : T0 = H.busH.totals.getD 0 0) (h1 : T1 = H.busH.totals.getD 1 0)
    (h2 : T2 = H.busH.totals.getD 2 0) (hξ : ξ = H.ξ) :
    ξ ^ 2 * T0 + ξ ^ 3 * T1 + ξ ^ 4 * T2 = H.target := by
  subst h0 h1 h2 hξ
  simp only [VtHonest.target, VtHonest.busH, vtBus, vt_nConstraints, Nat.reduceAdd, vt_powers5, dot]
  simp only [List.drop_succ_cons, List.drop_zero, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.foldl_cons, List.foldl_nil, List.getD_cons_zero, List.getD_cons_succ]
  ring

theorem lists_eq_of_flatten : ∀ (l1 l2 : List (List E)), l1.length = l2.length →
    (∀ i, (l1.getD i []).length = (l2.getD i []).length) → l1.flatten = l2.flatten → l1 = l2
  | [], [], _, _, _ => rfl
  | a :: l1, b :: l2, hl, hi, hf => by
    have hab : a.length = b.length := by simpa using hi 0
    simp only [List.flatten_cons] at hf
    have ha : a = b := by
      have := congrArg (List.take a.length) hf
      rwa [List.take_left' rfl, hab, List.take_left' rfl] at this
    subst ha
    rw [lists_eq_of_flatten l1 l2 (by simpa using hl) (fun i ↦ by simpa using hi (i + 1))
      (List.append_cancel_left hf)]
  | [], _ :: _, hl, _, _ => absurd hl (by simp)
  | _ :: _, [], hl, _, _ => absurd hl (by simp)

theorem tables_widths : ∀ t < 6, (tables.getD t default).width = vtW6.getD t 0 := by decide

theorem vt_rowsT_length {H : VtHonest} (hr : H.rows.length = 6) : H.rowsT.length = 6 := by
  have hf : H.busH.forms.length = 6 :=
    (vt_forms3_shape H.bc H.lm hr H.alphas H.beta H.point (H.xs5.take 3) (H.xs5.getD 3 0)
      (H.xs5.getD 4 0) H.bv (H.values.getD 0 0) (H.values.getD 1 0) (H.values.getD 2 0)).1
  have hh : H.L.tableLogHeights.length = 6 := vt_tableHeights_length hr
  have ht : tables.length = 6 := rfl
  simp only [VtHonest.rowsT, vtRows, List.length_zip, hh, hf, ht,
    LeanVM.Protocol.EndToEnd.Complete.length_tableWeights]
  rfl

theorem vt_evsT_shape {H : VtHonest} (h : H.Ok) (hr : H.rows.length = 6) :
    H.evsT.length = 6 ∧ ∀ t < 6, (H.evsT.getD t []).length = vtW6.getD t 0 := by
  have hl := h.hevl
  rw [vt_rowsT_length hr] at hl
  refine ⟨hl, fun t ht ↦ ?_⟩
  have hz : (H.rowsT[t]'(by rw [vt_rowsT_length hr]; exact ht), H.evsT[t]'(by omega)) ∈
      List.zip H.rowsT H.evsT := by
    rw [List.mem_iff_getElem]
    exact ⟨t, by simp [vt_rowsT_length hr, hl, ht], by simp⟩
  have hw := h.hevw _ hz
  simp only at hw
  have ht1 : (H.rowsT[t]'(by rw [vt_rowsT_length hr]; exact ht)).1 = tables.getD t default := by
    simp [VtHonest.rowsT, vtRows, List.getElem_zip, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show t < tables.length from ht)]
  rw [List.getD_eq_getElem _ _ (by omega), hw, ht1, tables_widths t ht]

theorem loadsInBuf_mono {σ : Val} {b1 b2 : List (E × ℕ)} {blk : List Stmt}
    (hsub : ∀ q ∈ b1, ∃ q' ∈ b2, q'.1 = q.1 ∧ q.2 ≤ q'.2) (h : LoadsInBuf σ b1 blk) :
    LoadsInBuf σ b2 blk := by
  intro d p off hm
  obtain ⟨q, hq, j, hp, hj⟩ := h d p off hm
  obtain ⟨q', hq', e1, e2⟩ := hsub q hq
  exact ⟨q', hq', j, by rw [e1]; exact hp, by omega⟩

theorem forall_vtPre {P : Stmt → Prop} (h1 : ∀ s ∈ (vtPre.drop 0).take 2404, P s)
    (h2 : ∀ s ∈ (vtPre.drop 2404).take 2748, P s) (h3 : ∀ s ∈ (vtPre.drop 5152).take 107, P s)
    (h4 : ∀ s ∈ (vtPre.drop 5259).take (10209 - 5259), P s)
    (h5 : ∀ s ∈ (vtPre.drop 10209).take 42, P s) : ∀ s ∈ vtPre, P s := by
  have hlen : vtPre.length = 10251 := by decide +kernel
  have h := forall_slice_split 0 2404 (2748 + (107 + (4950 + 42))) h1
    (forall_slice_split 2404 2748 (107 + (4950 + 42)) h2
      (forall_slice_split 5152 107 (4950 + 42) h3 (forall_slice_split 5259 4950 42 h4 h5)))
  intro s hs
  apply h
  rw [List.drop_zero, List.take_of_length_le (by omega)]
  exact hs

theorem multilinearEval_zero2 (x : E) : multilinearEval [0, 0] [x] = 0 := by
  simp [multilinearEval, foldPairs]

theorem vt_alloc_vals {rd : Reader} {w : ℕ → E} {args : List E} (hl : args.length = 22) :
    ∀ x ∈ vtPre.filterMap LeanVM.Guest.Memory.Stmt.allocSz, vtσ rd w args x.1 = w x.1.idx := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := List.mem_filterMap.mp hx
  have hg := vt_goodS (rd := rd) (w := w) hl hs
  cases s with
  | atom a =>
    cases a with
    | hint hk =>
      cases hk with
      | alloc d n =>
        simp only [LeanVM.Guest.Memory.Stmt.allocSz, Option.some.injEq] at hsx
        subst hsx; exact hg
      | allocDyn d n =>
        simp only [LeanVM.Guest.Memory.Stmt.allocSz, Option.some.injEq] at hsx
        subst hsx; exact hg
      | _ => simp [LeanVM.Guest.Memory.Stmt.allocSz] at hsx
    | _ => simp [LeanVM.Guest.Memory.Stmt.allocSz] at hsx
  | _ => simp [LeanVM.Guest.Memory.Stmt.allocSz] at hsx

theorem vt_alloc_var {rd : Reader} {w : ℕ → E} {args : List E} (hl : args.length = 22) {v : ℕ}
    (hv : v ∈ vtAllocVars) : vtσ rd w args (.n v) = w v := by
  have : V.n v ∈ (vtPre.filterMap LeanVM.Guest.Memory.Stmt.allocSz).map (fun x ↦ x.1) := by
    rw [vt_allocs]; exact List.mem_map.mpr ⟨v, hv, rfl⟩
  obtain ⟨x, hx, e⟩ := List.mem_map.mp this
  have := vt_alloc_vals (rd := rd) (w := w) hl x hx
  rw [e] at this
  exact this

/-- The offsets' bits buffers' allocations' positions. -/
def vtBitsPos : List ℕ := [2411, 2438, 2514, 2590, 2604, 2618, 2632, 2646, 2660, 2678, 2696, 2714, 2732, 2750, 2768, 2786, 2804, 2822, 2840, 2858, 2876, 2894, 2912, 2930, 2948, 2966, 2984, 3002, 3020, 3038, 3056, 3074, 3092, 3110, 3128, 3146, 3164, 3182, 3200, 3218, 3236, 3254, 3272, 3290, 3308, 3326, 3344, 3362, 3380, 3398, 3416, 3434, 3452, 3470, 4309, 4322, 4336, 4350, 4364, 4382, 4400, 4418, 4436, 4454, 4472, 4490, 4508, 4526, 4544, 4562, 4580, 4598, 4616, 4634, 4652, 4670, 4688, 4706, 4724, 4742, 4760, 4778, 4796, 4814, 4832, 4850, 4868, 4886, 4904, 4922, 4940, 4958, 4976, 4994, 5012, 5030, 5048, 5066, 5084]

set_option maxRecDepth 100000 in
theorem vt_bits_const : ∀ k < 99, tbStmtsEqb [.atom (.const (.n (vtAllocVars.getD (8 + k) 0 - 1))
    (word 17179869184 0 0))] ((vtPre.drop (vtBitsPos.getD k 0 - 1)).take 1) = true := by
  simp only [vtPre_drop]; decide +kernel

set_option maxRecDepth 100000 in
theorem vt_allocSz : (vtPre.filterMap LeanVM.Guest.Memory.Stmt.allocSz).map (fun x ↦ x.2) =
    [.inl 153, .inl 153, .inl 153, .inl 34, .inr (.n 9), .inl 1728, .inl 864, .inl 153] ++
      (List.range 99).map (fun k ↦ .inr (.n (vtAllocVars.getD (8 + k) 0 - 1))) ++
      [.inr (.n 5911), .inr (.n 5914), .inr (.n 5935)] := by decide +kernel

theorem word_g34 : word 17179869184 0 0 = gen ^ 34 := by
  rw [tb_word_eOfNat, gen_pow_eq_ofK]
  show ofK (K.ofBits 17179869184) = ofK (Parameters.gpow 34)
  rw [show K.ofBits 17179869184 = Parameters.gpow 34 by decide +kernel]

theorem logG_gen_pow {e : ℕ} (he : e < 2 ^ 64 - 1) : LeanVM.Guest.Memory.logG (gen ^ e) = e := by
  rw [gen_pow_eq_ofK]; exact LeanVM.Guest.Memory.logG_spec he

section
variable {H : VtHonest} {B : VtBases} {w : ℕ → E} {rd : Reader}

theorem vt_lin_reads (hm : MemLay rd (H.linL B ++ H.ownL B)) {q : ℕ × List E}
    (hq : q ∈ H.linL B) : TbReadsAt rd (ofK (gpow q.1)) q.2 :=
  hm q (List.mem_append_left _ hq)

theorem vt_own_reads (hm : MemLay rd (H.linL B ++ H.ownL B)) (hw : VtWOk H B w) {j : ℕ}
    (hj : j < 110) : TbReadsAt rd (w (vtAllocVars.getD j 0)) ((H.ownW B).getD j []) := by
  rw [hw.alloc j hj]
  have hb := ownB_length H B
  have ho := ownW_length H B
  have hmem : ((H.ownB B).getD j 0, (H.ownW B).getD j []) ∈ H.ownL B := by
    rw [VtHonest.ownL, List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    exact List.mem_iff_getElem.mpr ⟨j, by simp [hb, ho]; omega, by simp⟩
  exact hm _ (List.mem_append_right _ hmem)

end

/-- The buffers the loads read: the layout's. -/
noncomputable def VtHonest.bufs (H : VtHonest) (B : VtBases) : List (E × ℕ) :=
  (H.linL B ++ H.ownL B).map fun q ↦ (ofK (gpow q.1), q.2.length)

/-- The honest returns. -/
noncomputable def VtHonest.retsH (H : VtHonest) (B : VtBases) : List E :=
  H.s3.squeeze.2.cap ++ [ofK (gpow B.cur) * gen ^ 5 * gen ^ (3 * H.n) * gen ^ 157, gen ^ H.n, H.bv,
    H.rm]

set_option maxRecDepth 20000 in
/-- **`verify_tables` is complete at the `Rel` level.** -/
theorem vt_rel_complete {H : VtHonest} (h : H.Ok) (hs : VtShape H) (B : VtBases) {w : ℕ → E}
    (hw : VtWOk H B w) {rd : Reader} (hlow : LowDefB 8 rd)
    (hm : MemLay rd (H.linL B ++ H.ownL B)) :
    (∀ s ∈ vtPre, VSH (coreProgram.Rel rd) rd (vtσ rd w (H.args B)) s) ∧
      LoadsInBuf (vtσ rd w (H.args B)) (H.bufs B) vtPre ∧
      (vtPre.filterMap LeanVM.Guest.Memory.Stmt.allocSz).map
        (fun x ↦ x.2.elim id fun s ↦ LeanVM.Guest.Memory.logG (vtσ rd w (H.args B) s)) = H.sizes ∧
      ((vtPre.filterMap LeanVM.Guest.Memory.Stmt.allocSz).map Prod.fst).map (vtσ rd w (H.args B)) =
        (H.ownB B).map (fun b ↦ ofK (gpow b)) ∧
      vtRets.map (vtσ rd w (H.args B)) = H.retsH B := by
  obtain ⟨hlm, hlmμ, h19, hμ33, hr, hτ29, hτμ, hal, hf, hfcan, hfitP, hfitC, hbc⟩ := hs
  have hl : (H.args B).length = 22 := rfl
  have a5 : (H.args B).getD 5 0 = ofK (gpow B.cur) := rfl
  have a6 : (H.args B).getD 6 0 = (digestScalars H.pi).1 := rfl
  have a7 : (H.args B).getD 7 0 = (digestScalars H.pi).2 := rfl
  have a10 : (H.args B).getD 10 0 = ofK (gpow B.dims) := rfl
  have a11 : (H.args B).getD 11 0 = ofK (gpow B.rows) := rfl
  have a12 : (H.args B).getD 12 0 = ofK (gpow B.bk) := rfl
  have a13 : (H.args B).getD 13 0 = ofK (gpow B.sq) := rfl
  have a14 : (H.args B).getD 14 0 = ofK (gpow B.fpw) := rfl
  have a16 : (H.args B).getD 16 0 = ofK (gpow B.pool) := rfl
  have a17 : (H.args B).getD 17 0 = ofK (gpow B.cplen) := rfl
  have a18 : (H.args B).getD 18 0 = ofK (gpow B.chi) := rfl
  -- the caller's buffers
  have mCur : TbReadsAt rd (ofK (gpow B.cur)) H.curW := vt_lin_reads (q := (B.cur, H.curW)) hm (by simp [VtHonest.linL])
  have mZeta : TbReadsAt rd (ofK (gpow B.zeta)) H.point := vt_lin_reads (q := (B.zeta, H.point)) hm (by simp [VtHonest.linL])
  have mDims : TbReadsAt rd (ofK (gpow B.dims)) H.dimsW := vt_lin_reads (q := (B.dims, H.dimsW)) hm (by simp [VtHonest.linL])
  have mRows : TbReadsAt rd (ofK (gpow B.rows)) (H.rows.map eOfNat) :=
    vt_lin_reads (q := (B.rows, H.rows.map eOfNat)) hm (by simp [VtHonest.linL])
  have mBk : TbReadsAt rd (ofK (gpow B.bk)) H.bkW := vt_lin_reads (q := (B.bk, H.bkW)) hm (by simp [VtHonest.linL])
  have mSq : TbReadsAt rd (ofK (gpow B.sq)) gSquaresList := vt_lin_reads (q := (B.sq, gSquaresList)) hm (by simp [VtHonest.linL])
  have mFpw : TbReadsAt rd (ofK (gpow B.fpw)) (eqKernel H.alphas) :=
    vt_lin_reads (q := (B.fpw, eqKernel H.alphas)) hm (by simp [VtHonest.linL])
  have mPool : TbReadsAt rd (ofK (gpow B.pool)) H.poolW := vt_lin_reads (q := (B.pool, H.poolW)) hm (by simp [VtHonest.linL])
  have mCpl : TbReadsAt rd (ofK (gpow B.cplen)) H.cplenW := vt_lin_reads (q := (B.cplen, H.cplenW)) hm (by simp [VtHonest.linL])
  have mChi : TbReadsAt rd (ofK (gpow B.chi)) H.chiW := vt_lin_reads (q := (B.chi, H.chiW)) hm (by simp [VtHonest.linL])
  -- the own buffers
  have o0 : TbReadsAt rd (w 30) (vtSortW H.κ) := vt_own_reads hm hw (j := 0) (by norm_num)
  have o1 : TbReadsAt rd (w 31) vtSideW := vt_own_reads hm hw (j := 1) (by norm_num)
  have o2 : TbReadsAt rd (w 185) (vtOffW H.κ) := vt_own_reads hm hw (j := 2) (by norm_num)
  have o3 : TbReadsAt rd (w 2732) vtIdxcW := vt_own_reads hm hw (j := 3) (by norm_num)
  have o4 : TbReadsAt rd (w 2767) (H.point.map (1 + ·)) := vt_own_reads hm hw (j := 4) (by norm_num)
  have o5 : TbReadsAt rd (w 2769) (vtShEqW H.point H.τ) := vt_own_reads hm hw (j := 5) (by norm_num)
  have o6 : TbReadsAt rd (w 2770) (vtShGW H.point H.τ) := vt_own_reads hm hw (j := 6) (by norm_num)
  have o7 : TbReadsAt rd (w 2851) (vtIdxBufW H.point H.lm) :=
    vt_own_reads hm hw (j := 7) (by norm_num)
  have oF : ∀ b < 3, TbReadsAt rd (w (vtFwV.getD b 0 + 6)) (offBits (H.offP.getD b 0)) := by
    intro b hb
    have := vt_own_reads hm hw (j := 8 + b) (by omega)
    rwa [vtAllocVars_F b hb, ownW_getD_P H B (by omega)] at this
  have oP : ∀ i < 51, TbReadsAt rd (w ((vtPushSel.getD i default).2.2.1 + 6))
      (offBits (H.offP.getD (3 + i) 0)) := by
    intro i hi
    have := vt_own_reads hm hw (j := 11 + i) (by omega)
    rwa [vtAllocVars_P i hi, show 11 + i = 8 + (3 + i) by omega, ownW_getD_P H B (by omega)] at this
  have oC : ∀ i < 45, TbReadsAt rd (w ((vtCountSel.getD i default).2.2.1 + 6))
      (offBits (H.offC.getD i 0)) := by
    intro i hi
    have := vt_own_reads hm hw (j := 62 + i) (by omega)
    rwa [vtAllocVars_C i hi, show 62 + i = 8 + (54 + i) by omega, ownW_getD_C H B hi] at this
  -- the arguments' words
  have hdims : ∀ t < 6, LoadHolds rd ((H.args B).getD 10 0) (t + 1) (gen ^ H.τ t) := by
    intro t ht
    rw [a10]
    have := tb_load_of mDims (k := t + 1) (by simp [VtHonest.dimsW, vtTauList]; omega)
    simpa [VtHonest.dimsW, vtTauList, List.getD_eq_getElem?_getD, ht] using this
  have hrows : ∀ t < 6, LoadHolds rd ((H.args B).getD 11 0) t (eOfNat (vtRw H.rows t)) := by
    intro t ht
    rw [a11]
    have := tb_load_of mRows (k := t) (by simp [hr]; omega)
    rwa [List.getD_eq_getElem _ _ (by simp [hr]; omega), List.getElem_map,
      ← List.getD_eq_getElem _ 0 (by omega)] at this
  have hbk : ∀ b < 153, LoadHolds rd ((H.args B).getD 12 0) b (gen ^ H.κ b) := by
    intro b hb
    rw [a12]
    have := tb_load_of mBk (k := b) (by simp [VtHonest.bkW, blockKappaWords]; omega)
    rwa [VtHonest.bkW, vt_kappa_word _ _ hb] at this
  have hrun : ∀ t < 6, RunTables rd (w 2769 * gen ^ (288 * t)) (w 2770 * gen ^ (144 * t))
      (H.point.length - H.τ t) (H.point.drop (H.τ t)) ((H.point.map (1 + ·)).drop (H.τ t))
      ((gSquaresList.drop (H.τ t)).take (H.point.length - H.τ t)) :=
    fun t ht ↦ vt_runTables hμ33 o5 o6 ht
  -- statements `0 ..< 2404`
  obtain ⟨sV, s22, s27, s30, s31, s185, sPad, sSh, s2639, s2732, s2767, s2769, s2770⟩ :=
    vtS_complete (rd := rd) (w := w) (args := H.args B) hl hlow H.κ
      (fun b hb ↦ vtKap_lt hlm hτ29 hb) H.point hμ33 H.τ (vtRw H.rows) (fun t ht ↦ vtHt_eq hr ht)
      hτ29 hτμ mZeta rfl hdims hrows hbk mSq o0 o1 o2 o3 o4 hrun hw.pads hw.w2768

  -- statements `2404 ..< 5152`
  have hcurs := mCur
  rw [VtHonest.curW, tbReadsAt_append, tbReadsAt_append] at hcurs
  obtain ⟨⟨mX5, mXR⟩, mEv⟩ := hcurs
  have hx5 := h.hx5
  have hpool5 : ∀ i < 5, LoadHolds rd ((H.args B).getD 16 0) i (H.xs5.getD i 0) := by
    intro i hi
    rw [a16]
    have := tb_load_of mPool (k := i) (by simp [VtHonest.poolW, hx5]; omega)
    rwa [VtHonest.poolW, List.append_assoc, List.getD_append _ _ _ _ (by omega)] at this
  have hcpl5 : ∀ i < 5, LoadHolds rd ((H.args B).getD 17 0) i
      (gen ^ (if i < 4 then H.lm else 19)) := by
    intro i hi
    rw [a17]
    have := tb_load_of mCpl (k := i) (by simp [VtHonest.cplenW]; omega)
    interval_cases i <;> simpa [VtHonest.cplenW] using this
  have hcan5 : ∀ i < 5, IsCanonical128 ((H.args B).getD i 0) := by
    intro i hi; interval_cases i <;> exact hfcan _ (by norm_num)
  have HB : VtBHyp rd w (H.args B) ⟨H.point, H.lm, H.rows, H.alphas, H.xs5, H.bc⟩ :=
    { hl := hl, hlow := hlow, hml := hμ33, hlm := hlm, hlmμ := hlmμ, h19 := h19, hr := hr,
      hτ := hτ29, hτμ := hτμ, hmu := rfl, hz := mZeta, hdim := hdims, hbk := mBk, hal := hal,
      hW := mFpw, hxl := hx5, hcur := mX5, hpool := hpool5, hcpl := hcpl5, hcan := hcan5,
      e22 := s22, e185 := s185, eSh := sSh, e2732 := s2732, e2767 := s2767, e2769 := s2769,
      e2770 := s2770, hoff := o2, hidxc := o3, hz1 := o4, hrun := hrun, hidxB := o7,
      hfitP := hfitP, hfitC := hfitC, hbitsF := oF, hbitsP := oP, hbitsC := oC, hwF := hw.hwF,
      hwP := hw.hwP, hwC := hw.hwC, hwI := hw.hwI, hbc := hbc, hpw := sPad }
  obtain ⟨bV, bLd, bFresh, b4411, b4924, b5816, b2870, b2900, b2975, b2873, b2904, b2979, bP, bC⟩ :=
    vtB_complete HB
  have bF : vtFreshWords (vtσ rd w (H.args B)) = H.xs5 := bFresh

  -- values the bus fixes
  have p : ∀ i < 22, vtσ rd w (H.args B) (.n i) = (H.args B).getD i 0 := fun i hi ↦
    vt_param hl hi
  have e15 : vtσ rd w (H.args B) (.n 15) = H.beta := p 15 (by norm_num)
  have eMem : [vtσ rd w (H.args B) (.n 2914), vtσ rd w (H.args B) (.n 2927),
      vtσ rd w (H.args B) (.n 2940)] = H.xs5.take 3 := by rw [← bF]; rfl
  have e4444 : vtσ rd w (H.args B) (.n 4444) = H.xs5.getD 3 0 := by
    rw [← bF]; simp only [vtFreshWords, List.getD_cons_succ, List.getD_cons_zero]
  have e4502 : vtσ rd w (H.args B) (.n 4502) = H.xs5.getD 4 0 := by
    rw [← bF]; simp only [vtFreshWords, List.getD_cons_succ, List.getD_cons_zero]
  have e2639 : vtσ rd w (H.args B) (.n 2639) = H.bv := s2639.trans hw.w2639
  have e27 : vtσ rd w (H.args B) (.n 27) = H.values.getD 0 0 := s27 0 (by norm_num)
  have e28 : vtσ rd w (H.args B) (.n 28) = H.values.getD 1 0 := s27 1 (by norm_num)
  have e29 : vtσ rd w (H.args B) (.n 29) = H.values.getD 2 0 := s27 2 (by norm_num)
  rw [e15, eMem, e2639, e27] at b4411
  rw [e15, eMem, e4444, e4502, e2639, e27, e28] at b4924
  rw [e15, eMem, e4444, e4502, e2639, e27, e28, e29] at b5816
  -- the sponge after the framework words
  obtain ⟨fF, fR, fC⟩ := vt_fresh_good (rd := rd) (w := w) hl
  have hS1 : vtFreshFs (vtσ rd w (H.args B)) = H.s1 := by
    have hfl : [vtσ rd w (H.args B) (.n 0), vtσ rd w (H.args B) (.n 1),
        vtσ rd w (H.args B) (.n 2), vtσ rd w (H.args B) (.n 3), vtσ rd w (H.args B) (.n 4)] =
        H.f := by
      rw [p 0 (by norm_num), p 1 (by norm_num), p 2 (by norm_num), p 3 (by norm_num),
        p 4 (by norm_num)]
      show [H.f.getD 0 0, H.f.getD 1 0, H.f.getD 2 0, H.f.getD 3 0, H.f.getD 4 0] = H.f
      match H.f, hf with
      | [a, b, c, d, e], _ => rfl
    unfold vtFreshFs VtHonest.s1 VtHonest.s0
    rw [hfl, bF]
  have hzt : zTarget (vtσ rd w (H.args B)) H.s1.squeeze.1 = H.target := by
    unfold zTarget
    exact vt_target_eq H _ _ _ _ b4411 b4924 b5816 rfl
  -- statements `5152 ..< 5259`
  have hn := vt_n_ex (H := H) hr
  have hnμ : H.n ≤ H.point.length := by
    obtain ⟨t, ht, e⟩ := hn; rw [← e]; exact hτμ t ht
  have hlow64 : ∀ i < 64, (rd (Parameters.gpow i)).isSome := fun i hi ↦ hlow i (by norm_num; omega)
  have hdimσ : ∀ t < 6, LoadHolds rd (vtσ rd w (H.args B) (.n 10)) (t + 1) (gen ^ H.τ t) := by
    rw [p 10 (by norm_num)]; exact hdims
  have hxs : TbReadsAt rd (vtσ rd w (H.args B) (.n 5) * gen ^ 5) H.xsR := by
    rw [p 5 (by norm_num), a5, show (5 : ℕ) = H.xs5.length from hx5.symm]; exact mXR
  have oZ : ∀ k < 3, TbReadsAt rd (w ([5912, 5915, 5936].getD k 0))
      ([zcRoundsW H.cap0 H.target (ofK (gpow B.cur) * gen ^ 5) H.xsR H.n,
        zcCprodW H.cap0 H.target H.xsR H.n,
        (List.range (H.n + 1)).map (prefixProd 1 H.chiW ((H.point.map (1 + ·)).take H.n))].getD k
        []) := by
    intro k hk
    have := vt_own_reads hm hw (j := 107 + k) (by omega)
    rw [ownW_getD_Z H B hk] at this
    have e : vtAllocVars.getD (107 + k) 0 = [5912, 5915, 5936].getD k 0 := by
      interval_cases k <;> decide
    rwa [e] at this
  obtain ⟨zV, zOut⟩ := vtZ_complete (rd := rd) (w := w) hl (m := H.point.length) (n := H.n)
    (τ := H.τ) (fun t ht ↦ vt_n_ge hr ht) hn hnμ (by omega) (p 9 (by norm_num)) hdimσ hlow64
    hw.w5817 (S := H.s1) (by rw [← hS1, fF]; exact fR) (by rw [← hS1, fF]; rfl)
    (by rw [← hS1, fF, fR]; exact fC) h.hxR hxs
    (by rw [hzt, p 5 (by norm_num), a5]; exact oZ 0 (by norm_num))
    (by rw [hzt]; exact oZ 1 (by norm_num))
    (by rw [hzt, p 18 (by norm_num), a18]; exact mChi)
    (zs1 := H.point.map (1 + ·)) (by rw [s2767]; exact o4) (by simpa using hnμ)
    (by rw [hzt]; exact oZ 2 (by norm_num))

  obtain ⟨z5817, z5895, z5884, z5905, z5911, z5914, z5935, z5912, z5915, z5936, zCap, z5932,
    z5933⟩ := zOut
  rw [hzt] at zCap z5933
  change _ = (zcRec H.cap0 H.target H.xsR H.n).1 at zCap
  change _ = (zcRec H.cap0 H.target H.xsR H.n).2 at z5933
  -- statements `5259 ..< 10209`
  obtain ⟨hevT6, hevTw⟩ := vt_evsT_shape h hr
  have hev157 : H.evsT.flatten.length = 157 := by
    rw [List.length_flatten]
    match H.evsT, hevT6, hevTw with
    | [a, b, c, d, e, f], _, hw' =>
      have := hw' 0 (by norm_num); have := hw' 1 (by norm_num); have := hw' 2 (by norm_num)
      have := hw' 3 (by norm_num); have := hw' 4 (by norm_num); have := hw' 5 (by norm_num)
      simp_all [vtW6]
  have hevC : TbReadsAt rd (vtσ rd w (H.args B) (.n 5932)) H.evsT.flatten := by
    rw [z5932, p 5 (by norm_num), mul_assoc, ← pow_add]
    have : (H.xs5 ++ H.xsR).length = 5 + 3 * H.n := by simp [hx5, h.hxR]
    rw [← this]; exact mEv
  have hevs := vt_evs_good (rd := rd) (w := w) hl hevC hev157
  have hevsT : vtEvsT (vtσ rd w (H.args B)) = H.evsT := by
    apply lists_eq_of_flatten _ _ (by rw [vtEvsT_length, hevT6]) (fun i ↦ ?_)
      (by rw [vt_evsT_flatten, hevs])
    rcases Nat.lt_or_ge i 6 with hi | hi
    · rw [hevTw i hi]; simp [vtEvsT, vtEvT]; interval_cases i <;> rfl
    · rw [List.getD_eq_default _ _ (by simp [vtEvsT]; omega),
        List.getD_eq_default _ _ (by omega)]
  have hpts : H.pts.length = H.n := by simp [VtHonest.pts]
  have hcap0 : AllCanonical H.cap0 := by
    intro c hc
    simp only [VtHonest.cap0, Fs.squeeze, capOf, List.mem_cons, List.mem_nil_iff,
      or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> exact canon_cellsOfState _ _ _
  have hcapR := zcRec_canon (cl0 := H.target) (xs := H.xsR) hcap0 H.n
  have hfinσ := (vt_spec h).1
  obtain ⟨fV, fF, fEvs, fSp, f11197⟩ := vtF_complete (rd := rd) (w := w) hl H.bc hbc hr hdimσ bP bC
    (vt_pull_good hl) (by rw [s2767]; exact o4) (vt_xi_good hl) hal (by rw [p 14 (by norm_num)]; exact mFpw)
    z5817 (fun t ht ↦ vt_n_ge hr ht) hnμ hpts
    (by
      intro j hj
      rw [z5915]
      have := tb_load_of (oZ 1 (by norm_num)) (k := j) (by simp [zcCprodW]; omega)
      simp only [List.getD_cons_succ, List.getD_cons_zero] at this
      rw [zcCprodW, List.getD_eq_getElem _ _ (by simp; omega)] at this
      simpa [VtHonest.pts, ← List.map_take, List.take_range, min_eq_left hj] using this)
    (by
      refine ⟨H.chiW, (H.point.map (1 + ·)).take H.n, by simp [VtHonest.chiW, zcChis],
        by simp; omega, by rw [p 18 (by norm_num)]; exact mChi,
        by rw [s2767]; exact tbReadsAt_take o4 _, fun j hj ↦ ?_⟩
      rw [z5936]
      have := tb_load_of (oZ 2 (by norm_num)) (k := j) (by simp; omega)
      simpa [List.getD_eq_getElem?_getD, Nat.lt_succ_of_le hj] using this)
    (by
      intro i hi
      rw [p 18 (by norm_num), a18]
      have := tb_load_of mChi (k := H.n - 1 - i) (by simp [VtHonest.chiW, zcChis]; omega)
      simpa [VtHonest.chiW, zcChis, VtHonest.pts, List.getD_eq_getElem?_getD, List.getElem?_reverse,
        hi, show H.n - 1 - (H.n - 1 - i) = i by omega, show H.n - 1 - i < H.n by omega] using this)
    hev157 hevC
    (by
      intro k hk
      rw [p 16 (by norm_num)]
      have := tb_load_of mPool (k := 5 + k) (by simp [VtHonest.poolW, hx5, hev157, VtHonest.pcW]; omega)
      rwa [VtHonest.poolW, List.getD_append _ _ _ _ (by simp [hx5, hev157]; omega),
        List.getD_append_right _ _ _ _ (by omega), hx5, show 5 + k - 5 = k by omega] at this)
    (by
      intro k hk
      rw [p 17 (by norm_num), a17]
      have := tb_load_of mCpl (k := 5 + k) (by simp [VtHonest.cplenW]; omega)
      rwa [VtHonest.cplenW, List.getD_append_right _ _ _ _ (by simp),
        show 5 + k - [gen ^ H.lm, gen ^ H.lm, gen ^ H.lm, gen ^ H.lm, gen ^ (19 : ℕ)].length = k by
          simp,
        List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range] at this)
    (by
      intro i hi
      have hm : vtσ rd w (H.args B) (.n (5927 + i)) ∈ (zcRec H.cap0 H.target H.xsR H.n).1 := by
        rw [← zCap]; interval_cases i <;> simp
      exact hcapR _ hm)
    (by
      rw [z5933, hevsT, z5895, e15, eMem, e4444, e4502, e2639, e27, e28, e29]
      have hf := hfinσ
      unfold VtHonest.terms VtHonest.nC at hf
      rw [vt_nConstraints] at hf
      exact hf)

  -- statements `10209 ..< 10251`
  have hcv : vtCapV (vtσ rd w (H.args B)) 0 = (zcRec H.cap0 H.target H.xsR H.n).1 := by
    rw [← zCap]; simp [vtCapV, vtPermCap, List.range_succ]
  have hS3 : vtEvalFs (vtσ rd w (H.args B)) = H.s3 := by
    unfold VtHonest.s3 VtHonest.s2
    rw [vtEvalFs, hcv, fEvs]
  obtain ⟨-, eR, eC, eCan⟩ := vt_evalFs_good (rd := rd) (w := w) hl fSp
  rw [hS3] at eR eC eCan
  have hc6 : IsCanonical128 (vtσ rd w (H.args B) (.n 6)) := by
    rw [p 6 (by norm_num)]; exact (isCanonical128_ofLimbs_iff _ _ _).mpr rfl
  have hc7 : IsCanonical128 (vtσ rd w (H.args B) (.n 7)) := by
    rw [p 7 (by norm_num)]; exact (isCanonical128_ofLimbs_iff _ _ _).mpr rfl
  have hpc : ∀ i < 3, LoadHolds rd (ofK (gpow B.pool)) (162 + i) (H.pcW.getD i 0) := by
    intro i hi
    have := tb_load_of mPool (k := 162 + i) (by simp [VtHonest.poolW, VtHonest.pcW, hx5, hev157]; omega)
    rwa [VtHonest.poolW, List.getD_append_right _ _ _ _ (by simp [hx5, hev157]),
      show 162 + i - (H.xs5 ++ H.evsT.flatten).length = i by simp [hx5, hev157]] at this
  obtain ⟨tV, tOut⟩ := vtZt_complete (rd := rd) (w := w) hl (S2 := H.s3) eR eC eCan hc6 hc7
    (by rw [p 16 (by norm_num), p 6 (by norm_num), p 7 (by norm_num)]; exact hpc 0 (by norm_num))
    (by rw [p 16 (by norm_num), p 6 (by norm_num), p 7 (by norm_num)]; exact hpc 1 (by norm_num))
    (by
      rw [p 16 (by norm_num)]
      have := hpc 2 (by norm_num)
      simp only [VtHonest.pcW, List.map_cons, List.map_nil, List.getD_cons_succ,
        List.getD_cons_zero] at this
      convert this using 1
      rw [show ((digestScalars H.pi).1.limb 2) = 0 from rfl,
        show ((digestScalars H.pi).2.limb 2) = 0 from rfl, ofK_zero, multilinearEval_zero2])
  obtain ⟨t11217, tCap, t11242, t11243, t11244, t11245⟩ := tOut
  -- every statement
  refine ⟨forall_vtPre sV bV zV fV tV, ?_, ?_, ?_, ?_⟩
  rotate_left
  · -- the sizes
    have hm1 : (vtPre.filterMap LeanVM.Guest.Memory.Stmt.allocSz).map
        (fun x ↦ x.2.elim id fun s ↦ LeanVM.Guest.Memory.logG (vtσ rd w (H.args B) s)) =
        ((vtPre.filterMap LeanVM.Guest.Memory.Stmt.allocSz).map (fun x ↦ x.2)).map
          (fun y ↦ y.elim id fun s ↦ LeanVM.Guest.Memory.logG (vtσ rd w (H.args B) s)) := by
      rw [List.map_map]; rfl
    rw [hm1, vt_allocSz]
    have hb : ∀ k < 99, LeanVM.Guest.Memory.logG
        (vtσ rd w (H.args B) (.n (vtAllocVars.getD (8 + k) 0 - 1))) = 34 := by
      intro k hk
      have g := (vt_goodL (rd := rd) (w := w) hl _ _ (vt_bits_const k hk)).1
      simp only [GoodS, fixNe, Good] at g
      rw [g, word_g34, logG_gen_pow (by norm_num)]
    have hbits : ((List.range 99).map (fun k ↦ (Sum.inr (V.n (vtAllocVars.getD (8 + k) 0 - 1)) :
        ℕ ⊕ V))).map (fun y ↦ y.elim id fun s ↦ LeanVM.Guest.Memory.logG (vtσ rd w (H.args B) s)) =
        List.replicate 99 34 := by
      apply List.ext_getElem (by simp)
      intro k h1 h2
      simp only [List.getElem_map, List.getElem_range, Sum.elim_inr, List.getElem_replicate]
      exact hb k (by simpa using h1)
    simp only [List.map_append, hbits]
    simp only [List.map_cons, List.map_nil, Sum.elim_inl, Sum.elim_inr, id]
    rw [p 9 (by norm_num), z5911, z5914, z5935]
    simp only [VtHonest.args, List.getD_cons_succ, List.getD_cons_zero]
    rw [logG_gen_pow (e := H.μ) (by unfold VtHonest.μ; omega),
      logG_gen_pow (e := 7 * (H.n + 1)) (by omega), logG_gen_pow (e := H.n + 1) (by omega)]
    rfl
  · -- the allocations' pointers
    rw [show (vtPre.filterMap LeanVM.Guest.Memory.Stmt.allocSz).map Prod.fst =
      vtAllocVars.map V.n from vt_allocs, List.map_map]
    apply List.ext_getElem (by simp [vtAllocVars_length, ownB_length])
    intro j h1 h2
    have hj : j < 110 := by simpa [vtAllocVars_length] using h1
    simp only [List.getElem_map, Function.comp]
    rw [vt_alloc_var hl (List.getElem_mem _), ← List.getD_eq_getElem _ 0 (by
      simpa [vtAllocVars_length] using h1), hw.alloc j hj, List.getD_eq_getElem _ _ (by
      rw [ownB_length]; exact hj)]
  · -- the returns
    rw [VtHonest.retsH, ← tCap]
    simp only [vtRets, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [t11242, t11243, t11244, t11245, z5932, z5817, e2639, p 5 (by norm_num), a5]
    rfl
  · -- the loads
    have mem : ∀ q ∈ H.linL B ++ H.ownL B, (ofK (gpow q.1), q.2.length) ∈ H.bufs B :=
      fun q hq ↦ List.mem_map.mpr ⟨q, hq, rfl⟩
    have lin : ∀ q ∈ H.linL B, (ofK (gpow q.1), q.2.length) ∈ H.bufs B :=
      fun q hq ↦ mem q (List.mem_append_left _ hq)
    have own : ∀ j < 110, (w (vtAllocVars.getD j 0), ((H.ownW B).getD j []).length) ∈ H.bufs B := by
      intro j hj
      rw [hw.alloc j hj]
      refine mem ((H.ownB B).getD j 0, (H.ownW B).getD j []) (List.mem_append_right _ ?_)
      rw [VtHonest.ownL, List.getD_eq_getElem _ _ (by rw [ownB_length]; omega),
        List.getD_eq_getElem _ _ (by rw [ownW_length]; omega)]
      exact List.mem_iff_getElem.mpr ⟨j, by simp [ownB_length, ownW_length]; omega, by simp⟩
    have own' : ∀ j < 110, ∀ v, vtAllocVars.getD j 0 = v →
        (w v, ((H.ownW B).getD j []).length) ∈ H.bufs B := fun j hj v e ↦ e ▸ own j hj

    have conv : ∀ {blk : List Stmt}, LoadsInBuf (vtσ rd w (H.args B)) (H.bufs B) blk →
        ∀ s ∈ blk, ∀ d p' off, s = .atom (.load d p' off) →
          InBuf (vtσ rd w (H.args B)) (H.bufs B) p' off :=
      fun h s hs d p' off e ↦ h d p' off (e ▸ hs)
    have lens : H.dimsW.length = 7 ∧ (H.rows.map eOfNat).length = 6 ∧ H.bkW.length = 153 ∧
        (gSquaresList).length = 34 ∧ (eqKernel H.alphas).length = 16 ∧ H.poolW.length = 165 ∧
        H.cplenW.length = 162 ∧ H.curW.length = 5 + 3 * H.n + 157 := by
      refine ⟨by simp [VtHonest.dimsW, vtTauList], by simp [hr], by simp [VtHonest.bkW,
        blockKappaWords], by simp [gSquaresList], by rw [vt_length_eqKernel, hal]; rfl,
        by simp [VtHonest.poolW, VtHonest.pcW, hx5, hev157], by simp [VtHonest.cplenW],
        by rw [VtHonest.curW, List.length_append, List.length_append, hx5, h.hxR, hev157]⟩
    obtain ⟨lD, lR, lB, lS, lF, lP, lC, lCu⟩ := lens
    have mD := lin (B.dims, H.dimsW) (by simp [VtHonest.linL])
    have mR := lin (B.rows, H.rows.map eOfNat) (by simp [VtHonest.linL])
    have mB := lin (B.bk, H.bkW) (by simp [VtHonest.linL])
    have mS := lin (B.sq, gSquaresList) (by simp [VtHonest.linL])
    have mF := lin (B.fpw, eqKernel H.alphas) (by simp [VtHonest.linL])
    have mP := lin (B.pool, H.poolW) (by simp [VtHonest.linL])
    have mC := lin (B.cplen, H.cplenW) (by simp [VtHonest.linL])
    have mCu := lin (B.cur, H.curW) (by simp [VtHonest.linL])
    simp only [lD, lR, lB, lS, lF, lP, lC, lCu] at mD mR mB mS mF mP mC mCu
    have hsq' : ∀ j < 34, LoadHolds rd ((H.args B).getD 13 0) j (gen ^ 2 ^ j) := fun j hj ↦ by
      rw [a13]
      have := tb_load_of mSq (k := j) (by simp [gSquaresList]; exact hj)
      simpa [gSquaresList, List.getD_eq_getElem?_getD, hj] using this
    have LS := vtS_loads (rd := rd) (w := w) hl hlow H.κ (fun b hb ↦ vtKap_lt hlm hτ29 hb) hbk hsq'
      o0 o1 o2
    have LS' : LoadsInBuf (vtσ rd w (H.args B)) (H.bufs B) ((vtPre.drop 0).take 2404) := by
      refine loadsInBuf_mono (fun q hq ↦ ?_) LS
      simp only [vtBufsS, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, mD, rfl, le_rfl⟩
      · exact ⟨_, mR, rfl, le_rfl⟩
      · exact ⟨_, mB, rfl, le_rfl⟩
      · exact ⟨_, mS, rfl, le_rfl⟩
      · exact ⟨_, own 0 (by norm_num), rfl, by simp [VtHonest.ownW, vtSortW]⟩
      · exact ⟨_, own 1 (by norm_num), rfl, by simp [VtHonest.ownW, vtSideW]⟩
      · exact ⟨_, own 2 (by norm_num), rfl, by simp [VtHonest.ownW, vtOffW]⟩
      · exact ⟨_, own 3 (by norm_num), rfl, by simp [VtHonest.ownW, vtIdxcW]⟩
    have LB' : LoadsInBuf (vtσ rd w (H.args B)) (H.bufs B) ((vtPre.drop 2404).take 2748) := by
      refine loadsInBuf_mono (fun q hq ↦ ?_) bLd
      simp only [vtBufsB, vtBufsBIdx, List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff,
        or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · refine ⟨_, mCu, ?_, ?_⟩
        · simp only [p 5 (by norm_num), a5]
        · simp only; omega
      · refine ⟨_, mD, ?_, le_rfl⟩
        simp only [p 10 (by norm_num), a10]
      · refine ⟨_, mB, ?_, le_rfl⟩
        simp only [p 12 (by norm_num), a12]
      · refine ⟨_, mF, ?_, le_rfl⟩
        simp only [p 14 (by norm_num), a14]
      · refine ⟨_, mP, ?_, le_rfl⟩
        simp only [p 16 (by norm_num), a16]
      · refine ⟨_, mC, ?_, le_rfl⟩
        simp only [p 17 (by norm_num), a17]
      · refine ⟨_, own' 2 (by norm_num) 185 (by decide), ?_, by simp [VtHonest.ownW, vtOffW]⟩
        simp only [s185]
      · refine ⟨_, own' 7 (by norm_num) 2851 (by decide), ?_,
          by simp [VtHonest.ownW, vtIdxBufW]⟩
        simp only [vt_alloc_var hl (v := 2851) (by unfold vtAllocVars; simp)]
    have mR107 : (w 5912, 7 * (H.n + 1)) ∈ H.bufs B := by
      have := own 107 (by norm_num)
      have e : ((H.ownW B).getD 107 []).length = 7 * (H.n + 1) := by
        rw [show 107 = 107 + 0 from rfl, ownW_getD_Z H B (by norm_num)]
        exact zcRoundsW_len (cap0_length H) H.n
      rwa [e] at this
    have mR108 : (w 5915, H.n + 1) ∈ H.bufs B := by
      have := own 108 (by norm_num)
      have e : ((H.ownW B).getD 108 []).length = H.n + 1 := by
        rw [show 108 = 107 + 1 from rfl, ownW_getD_Z H B (by norm_num)]
        simp [zcCprodW]
      rwa [e] at this
    have mR109 : (w 5936, H.n + 1) ∈ H.bufs B := by
      have := own 109 (by norm_num)
      have e : ((H.ownW B).getD 109 []).length = H.n + 1 := by
        rw [show 109 = 107 + 2 from rfl, ownW_getD_Z H B (by norm_num)]
        simp
      rwa [e] at this
    have LZ := vtZ_inBuf (rd := rd) hl hw.w5817 (bufs := H.bufs B)
      (by rw [p 10 (by norm_num), a10]; exact mD) mR107 mR108
    have LF := vtF_loadsInBuf (rd := rd) (w := w) hl (bufs := H.bufs B)
      ⟨_, mF, 0, by rw [p 14 (by norm_num), a14]; simp, by omega⟩
      ⟨_, mCu, 5 + 3 * H.n, by rw [z5932, p 5 (by norm_num), a5, mul_assoc, ← pow_add], by omega⟩
      (BufWin.of_mem (by rw [p 10 (by norm_num), a10]; exact mD))
      ⟨_, mP, 0, by rw [p 16 (by norm_num), a16]; simp, by omega⟩
      ⟨_, mC, 0, by rw [p 17 (by norm_num), a17]; simp, by omega⟩
      hdimσ z5817 (fun t ht ↦ vt_n_ge hr ht)
      (BufWin.of_mem (by rw [z5915]; exact mR108)) (BufWin.of_mem (by rw [z5936]; exact mR109))
    have LT := vtZt_inBuf (rd := rd) (w := w) (args := H.args B) (bufs := H.bufs B)
      (by rw [p 16 (by norm_num), a16]; exact mP)
    intro d p' off hs
    exact forall_vtPre (P := fun s ↦ ∀ d p' off, s = .atom (.load d p' off) →
      InBuf (vtσ rd w (H.args B)) (H.bufs B) p' off) (conv LS') (conv LB') (conv LZ) (conv LF)
      (conv LT) _ hs d p' off rfl

/-- **`vt_rel_complete` with the explicit oracle** `vtW`. -/
theorem vt_rel_complete_vtW {H : VtHonest} (h : H.Ok) (hs : VtShape H) (B : VtBases)
    {rd : Reader} (hlow : LowDefB 8 rd) (hm : MemLay rd (H.linL B ++ H.ownL B)) :
    (∀ s ∈ vtPre, VSH (coreProgram.Rel rd) rd (vtσ rd (vtW H B) (H.args B)) s) ∧
      LoadsInBuf (vtσ rd (vtW H B) (H.args B)) (H.bufs B) vtPre ∧
      (vtPre.filterMap LeanVM.Guest.Memory.Stmt.allocSz).map (fun x ↦ x.2.elim id fun s ↦
        LeanVM.Guest.Memory.logG (vtσ rd (vtW H B) (H.args B) s)) = H.sizes ∧
      ((vtPre.filterMap LeanVM.Guest.Memory.Stmt.allocSz).map Prod.fst).map
        (vtσ rd (vtW H B) (H.args B)) = (H.ownB B).map (fun b ↦ ofK (gpow b)) ∧
      vtRets.map (vtσ rd (vtW H B) (H.args B)) = H.retsH B :=
  vt_rel_complete h hs B (vtW_ok H B) hlow hm

end
end LeanVM.Guest.B1.Tables
