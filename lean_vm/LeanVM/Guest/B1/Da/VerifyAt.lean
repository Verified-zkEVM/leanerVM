/-
  LeanVM.Guest.B1.Da.VerifyAt

  `da_verify` in the uniform placed form: its seven buffers after its frame, holding the words an
  honest run leaves, its callees after them; it reads `g_squares[L]` among its caller's words.
-/

module

public import LeanVM.Guest.B1.Da.ColumnAt
public import LeanVM.Guest.B1.Da.ColLoopAt
public import LeanVM.Guest.B1.Da.RowShapeAt
public import LeanVM.Guest.B1.Da.VerifyComplete

/-!
# `da_verify`, placed

At `fp`, `da_verify` allocates its buffers from `b0 = fp + fs "da_verify"` (`dvSizes`), holding
`dvConts` (`dvOwn`); its callees follow in call order: `da_row_shape` (`row_shape_completeAt`), the
loops over the rows (pure), the column loops (`colLoop_completeAt` over `col_completeAt`), the
column tree, the rows' digests, the padding rows and the row tree (pure). Its valuation is
`dv_core`'s at the allocator's buffers (`dvPtrsAt`), its walk takes the dispatch's arm `L`.
`da_verify_completeAt`: `da_verify` is `CompleteAtD`, reading `g^(2^L)` at `g^(s + L)` for
`g_squares = g^s`, returning the claim's cells.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd LeanVM.Guest.Value.Keccak
open LeanVM.Guest.B1 (CompleteAtD Returns Kid OutsOk CallsMatch RegionsOk outRegion DisjL Within
  disj_append disj_nil kidsFromIn_of_kidsD completeAt_of_rel_pureD regionsOk_of within_append
  bufL_within bufL_disj bufL_region)
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append)

@[expose] public section

/-! ## The path -/

/-- `da_verify`'s statements before the row tree's dispatch. -/
noncomputable def dvPre : List Stmt := (Fn.body Data.core25).take 51

/-- `da_verify`'s statements after the row tree's dispatch, but its `ret`. -/
noncomputable def dvPost : List Stmt := ((Fn.body Data.core25).drop 52).dropLast

set_option maxRecDepth 100000 in
theorem dv_split : Fn.body Data.core25 = dvPre ++ .dispatch (.n 2) dlNames [.n 41] [.n 48, .n 49] ::
    (dvPost ++ [.ret [.n 993, .n 994, .n 995, .n 996]]) := stmtsEqb_sound (by decide +kernel)

theorem dvP_eq : dvP = dvPre ++ .dispatch (.n 2) dlNames [.n 41] [.n 48, .n 49] :: dvPost := by
  rw [dvP, dv_split, show ∀ (A B : List Stmt) (d x : Stmt), A ++ d :: (B ++ [x]) = (A ++ d :: B) ++ [x]
    from fun A B d x => by simp, List.dropLast_concat]

set_option maxRecDepth 100000 in
theorem dvPre_straight : dvPre.all Main.Stmt.straight = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem dvPost_straight : dvPost.all Main.Stmt.straight = true := by decide +kernel

/-- `da_verify`'s statements before the dispatch: atoms, calls, and its guarded loops. -/
def dvPreKind : Stmt → Bool
  | .atom _ => true
  | .call .. => true
  | .callIf c _ _ => decide (c ∈ [V.n 15, .n 29, .n 35, .n 43, .n 46])
  | _ => false

set_option maxRecDepth 100000 in
theorem dvPre_kinds : dvPre.all dvPreKind = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem dvPost_atoms : dvPost.all (fun s => match s with | .atom _ => true | _ => false) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem dvPre_allocs : dvPre.filterMap Main.Stmt.allocSz = [(.n 12, .inr (.n 11)), (.n 13, .inr (.n 1)),
    (.n 17, .inl 256), (.n 26, .inr (.n 25)), (.n 27, .inr (.n 1)), (.n 31, .inl 512),
    (.n 41, .inr (.n 40))] := by decide +kernel

set_option maxRecDepth 100000 in
theorem dvPost_allocs : dvPost.filterMap Main.Stmt.allocSz = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem dvPre_addrs : dvPre.filterMap Main.Stmt.addrS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem dvPost_addrs : dvPost.filterMap Main.Stmt.addrS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem dvPre_calls : dvPre.filterMap Main.Stmt.callS =
    [(none, "da_row_shape", [.n 1, .n 2, .n 0], [.n 3, .n 4]),
      (some (.n 15), "__loop17", [.n 16, .n 1, .n 13, .n 12], []),
      (some (.n 29), "__loop18", [.n 30, .n 1, .n 26, .n 27], []),
      (none, "__loop19", [.n 32, .n 1, .n 3, .n 4, .n 2, .n 13, .n 31, .n 27, .n 17], []),
      (none, "__loop20", [.n 33, .n 1, .n 3, .n 4, .n 2, .n 13, .n 31, .n 27, .n 17], []),
      (some (.n 35), "__loop21", [.n 36, .n 1, .n 27], []),
      (none, "da_levels__L128_L7", [.n 31], [.n 37, .n 38]),
      (some (.n 43), "__loop22", [.n 44, .n 1, .n 13, .n 41], []),
      (some (.n 46), "__loop23", [.n 47, .n 4, .n 41, .n 1], [])] := by decide +kernel

set_option maxRecDepth 100000 in
theorem dvPost_calls : dvPost.filterMap Main.Stmt.callS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem dvPre_loads : dvPre.filterMap B1.Stmt.loadS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem dvPost_loads : dvPost.filterMap B1.Stmt.loadS = (List.range 256).map fun i => (.n 17, i) := by
  decide +kernel

theorem dv_loop : coreProgram.loop "da_verify" = false := by
  rw [Program.loop_of_find? find_da_verify]; decide +kernel

theorem one_add_gen_pow_ne' {a : ℕ} (ha : a < 2 ^ 64 - 1) : ((1 : E) + gen ^ a ≠ 0) ↔ a ≠ 0 := by
  rw [Ne, e_add_eq_zero_iff, eq_comm, gen_pow_eq_one_iff ha]

theorem find_l18 : coreProgram.find? "__loop17" = some (coreProgram.getD 356 default) :=
  find_of_idx (by have h := l18_ok; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2)
    (by rw [coreProgram_length]; omega)
theorem find_l19 : coreProgram.find? "__loop18" = some (coreProgram.getD 357 default) :=
  find_of_idx (by have h := l19_ok; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2)
    (by rw [coreProgram_length]; omega)
theorem find_l22 : coreProgram.find? "__loop21" = some (coreProgram.getD 360 default) :=
  find_of_idx (by have h := l22_ok; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2)
    (by rw [coreProgram_length]; omega)
theorem find_l23 : coreProgram.find? "__loop22" = some (coreProgram.getD 362 default) :=
  find_of_idx (by have h := l23_ok; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2)
    (by rw [coreProgram_length]; omega)
theorem find_l24 : coreProgram.find? "__loop23" = some (coreProgram.getD 363 default) :=
  find_of_idx (by have h := l24_ok; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2)
    (by rw [coreProgram_length]; omega)

theorem s23 : loopShapeF (coreProgram.getD 362 default) "__loop22" = true := by
  have h := l23_ok
  simp only [l23Ok, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.1.1.1.1.1

/-! ## The pure callees on `da_verify`'s buffers -/

section Kids

variable {rd : Reader} {r L : ℕ} {syms : ℕ → ℕ → List K} {ws : ℕ → List E} {P : DaPtrs}
  (hb : DvBufMem r L syms ws rd P)
include hb

theorem dvk_l18 (hr : r < 2 ^ 34) (hr1 : 1 ≤ r) :
    coreProgram.Rel rd "__loop17" [1, gen ^ r, P.pb, P.pd] [] :=
  (guard_complete find_l18 dvloops_shape.1.1 (rest := [P.pb, P.pd]) (m := r)
    fun i hi => l18_block (hb.pbase i hi)).2 ((one_add_gen_pow_ne' (by omega)).mpr (by omega))

theorem dvk_l19 (hr : r < 2 ^ 34) (hr1 : 1 ≤ r) :
    coreProgram.Rel rd "__loop18" [1, gen ^ r, P.acc, P.rb] [] :=
  (guard_complete find_l19 dvloops_shape.2.1.1 (rest := [P.acc, P.rb]) (m := r)
    fun i hi => l19_block (hb.rbase i hi) (by
      have := hb.acc i hi 0 (by simp); simpa [accSum] using this)).2
    ((one_add_gen_pow_ne' (by omega)).mpr (by omega))

theorem dvk_l22 (hr : r < 2 ^ 34) (hr1 : 1 ≤ r) (hdot : ∀ i < r, accSum syms ws i 128 = 0) :
    coreProgram.Rel rd "__loop21" [1, gen ^ r, P.rb] [] :=
  (guard_complete find_l22 dvloops_shape.2.2.1.1 (rest := [P.rb]) (m := r)
    fun i hi => l22_block (hb.rbase i hi) (by
      have := hb.acc i hi 128 (by simp); simp only [List.getElem_map, List.getElem_range] at this
      rwa [hdot i hi] at this)).2 ((one_add_gen_pow_ne' (by omega)).mpr (by omega))

theorem dvk_l7 : coreProgram.Rel rd "da_levels__L128_L7" [P.ct]
    [(cellRoot 7 (colLeaves r L syms)).1, (cellRoot 7 (colLeaves r L syms)).2] :=
  da_levels_complete 7 (by norm_num) rd P.ct (colLeaves r L syms)
    (by simp [colLeaves]) (fun _ => by rw [colLeaves]; exact canon_scalars_map _ _) hb.ct

theorem dvk_l23 (hrL : r ≤ 2 ^ L) (hr : r < 2 ^ 34) (hr1 : 1 ≤ r) :
    coreProgram.Rel rd "__loop22" [1, gen ^ r, P.pb, P.rt] [] := by
  refine (guard_complete find_l23 s23 (rest := [P.pb, P.rt]) (m := r) fun i hi => ?_).2
    ((one_add_gen_pow_ne' (by omega)).mpr (by omega))
  have hi2 : i < 2 ^ L := by omega
  obtain ⟨t0, t1⟩ := treeMem_leaf hb.rt (by simp [rowLeaves]) hi2
  have hrl : (rowLeaves r L syms).getD i 0 = digestScalars (rowD syms i) := by
    simp [rowLeaves, List.getD_eq_getElem?_getD, hi2, rowLeaf, hi]
  rw [hrl, rowD, ← prefixCells_bytes, ← gen_sq] at t0 t1
  exact l23_block (hb.pbase i hi) (hb.pcells i hi)
    (by rw [prefixCells, length_flatMap_range _ 2 _ (fun j => rfl)])
    (canon_digestCells_flat _ _) t0 t1

theorem dvk_l24 (hrL : r ≤ 2 ^ L) (hL : 2 ^ L < 2 ^ 34) (hg : 2 ^ L - r ≠ 0) :
    coreProgram.Rel rd "__loop23" [1, gen ^ (2 ^ L - r), P.rt, gen ^ r] [] := by
  refine (guard_complete find_l24 dvloops_shape.2.2.2.1 (rest := [P.rt, gen ^ r]) (m := 2 ^ L - r)
    fun d hd => ?_).2 ((one_add_gen_pow_ne' (by omega)).mpr hg)
  have hrd : r + d < 2 ^ L := by omega
  obtain ⟨t0, t1⟩ := treeMem_leaf hb.rt (by simp [rowLeaves]) hrd
  have hrl : (rowLeaves r L syms).getD (r + d) 0 = digestScalars daPadRowDigest := by
    simp [rowLeaves, List.getD_eq_getElem?_getD, hrd, rowLeaf]
  rw [hrl] at t0 t1
  have e : P.rt * (gen ^ r * gen ^ r) * (gen ^ d * gen ^ d) = P.rt * gen ^ (2 * (r + d)) := by
    rw [gen_sq, gen_sq, mul_assoc, ← pow_add]; congr 2; ring
  exact l24_block (by rw [e]; exact t0) (by rw [e]; exact t1)

theorem dvk_lev (hL : L ≤ 10) : coreProgram.Rel rd (dlNames[L]!) [P.rt]
    [(cellRoot L (rowLeaves r L syms)).1, (cellRoot L (rowLeaves r L syms)).2] := by
  rw [dlNames_get hL]
  exact da_levels_complete L hL rd P.rt (rowLeaves r L syms) (by simp [rowLeaves])
    (fun _ => by rw [rowLeaves]; exact canon_scalars_map _ _) hb.rt

end Kids

/-! ## `da_verify` -/

theorem mem_daPure_of {g : String} (h : g ∈ ["__loop17", "__loop18", "__loop21", "__loop22",
    "__loop23", "da_levels__L128_L7"]) : g ∈ daPureSet := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **`da_verify` is complete, placed**: on `r` rows of symbols `syms` orthogonal to the columns'
weights `ws`, reading `g^(2^L)` at `g^(s + L)` (`g_squares = g^s`), returning the claim's cells. -/
theorem da_verify_completeAt (fs : String → ℕ) (cert : String → V → ℕ)
    (hcv : cert "da_vector_cell" (.n 1) + 256 ≤ fs "da_vector_cell") {r L : ℕ}
    (hr1 : 1 ≤ r) (hr : r ≤ LeanDa.maxRows) (hL : 2 ^ L = LeanDa.nPad r)
    {syms : ℕ → ℕ → List K} {ws : ℕ → List E} (hsl : ∀ i j, (syms i j).length = 256)
    (hwl : ∀ j, (ws j).length = 256) (hdot : ∀ i < r, accSum syms ws i 128 = 0) (s : ℕ) :
    CompleteAtD fs cert 16 "da_verify" [(s + L, [gen ^ 2 ^ L])] [gen ^ s]
      (Returns (digestCells (daRoot r L syms) ++ digestCells (daVd ws))) := by
  -- the shape
  have hr' := hr
  unfold LeanDa.maxRows at hr'
  obtain ⟨hlo, hhi⟩ := nPad_bounds hr1
  have hrL : r ≤ 2 ^ L := hL ▸ hlo
  have hlt : 2 ^ L < 2 ^ 11 := by
    calc 2 ^ L < 2 * r := hL ▸ hhi
      _ ≤ 2 ^ 11 := by norm_num; omega
  have hL10 : L ≤ 10 := by
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt
    omega
  have hN : 2 ^ L ≤ 1024 := le_trans (Nat.pow_le_pow_right (by norm_num) hL10) (by norm_num)
  intro fp
  set b0 := fp + fs "da_verify" with hb0
  set P := dvPtrsAt r L b0 (fun _ => 0) (fun _ => 0) with hP
  set Lin : Layout := [(s + L, [gen ^ 2 ^ L])] with hLin
  set Own := dvOwn r L syms ws b0 with hOwn
  set cr := cellRoot 7 (colLeaves r L syms) with hcr
  set rr := cellRoot L (rowLeaves r L syms) with hrr
  have hfit := dvConts_fit (syms := syms) (ws := ws) (b0 := b0) hrL
  -- the column loops
  have hcol1 : ∀ k, 0 ≤ k → k < 64 → CompleteAtD fs cert 16 "da_verify_column__L1" Own
      [gen ^ k, gen ^ r, gen ^ 2 ^ L, gen ^ (2 ^ L - r), gen ^ L, P.pb, P.ct, P.rb, P.cd]
      (Returns []) := fun k _ hk =>
    col_completeAt fs cert hcv find_col1 core769_body col1_params (by
      rw [Program.loop_of_find? find_col1]; decide +kernel) find_l417 row417_shape.1 find_l418
      gap418_shape.1 (by decide) (by decide)
      (fun rd node lv hm => colm_rows1 hm hrL hsl hwl hk)
      (fun rd node lv hm => colm_gaps hm gap418_shape.1 gap418_shape.2 core896_body)
      hr1 hrL hL10 hwl (by omega)
  have hcol0 : ∀ k, 64 ≤ k → k < 128 → CompleteAtD fs cert 16 "da_verify_column__L0" Own
      [gen ^ k, gen ^ r, gen ^ 2 ^ L, gen ^ (2 ^ L - r), gen ^ L, P.pb, P.ct, P.rb, P.cd]
      (Returns []) := fun k _ hk =>
    col_completeAt fs cert hcv find_col0 core770_body col0_params (by
      rw [Program.loop_of_find? find_col0]; decide +kernel) find_l419 row419_shape.1 find_l420
      gap420_shape.1 (by decide) (by decide)
      (fun rd node lv hm => colm_rows0 hm hrL hsl hwl hk)
      (fun rd node lv hm => colm_gaps hm gap420_shape.1 gap420_shape.2 core898_body)
      hr1 hrL hL10 hwl hk
  have hl20 : CompleteAtD fs cert 16 "__loop19" Own
      [1, gen ^ r, gen ^ 2 ^ L, gen ^ (2 ^ L - r), gen ^ L, P.pb, P.ct, P.rb, P.cd] (Returns []) := by
    have := colLoop_completeAt fs cert (by rw [coreProgram_length]; omega) l20_ok word_g64
      (by norm_num) hcol1 0 le_rfl (by norm_num)
    rwa [pow_zero] at this
  have hl21 : CompleteAtD fs cert 16 "__loop20" Own
      [gen ^ 64, gen ^ r, gen ^ 2 ^ L, gen ^ (2 ^ L - r), gen ^ L, P.pb, P.ct, P.rb, P.cd]
      (Returns []) :=
    colLoop_completeAt fs cert (by rw [coreProgram_length]; omega) l21_ok word_g128
      (by norm_num) hcol0 64 le_rfl (by norm_num)
  -- the callees
  let ks : List Kid :=
    [⟨"da_row_shape", true, [gen ^ r, gen ^ L, gen ^ s], Lin, Returns [gen ^ 2 ^ L, gen ^ (2 ^ L - r)]⟩,
      ⟨"__loop17", true, [1, gen ^ r, P.pb, P.pd], Own, Returns []⟩,
      ⟨"__loop18", true, [1, gen ^ r, P.acc, P.rb], Own, Returns []⟩,
      ⟨"__loop19", true, [1, gen ^ r, gen ^ 2 ^ L, gen ^ (2 ^ L - r), gen ^ L, P.pb, P.ct, P.rb,
        P.cd], Own, Returns []⟩,
      ⟨"__loop20", true, [gen ^ 64, gen ^ r, gen ^ 2 ^ L, gen ^ (2 ^ L - r), gen ^ L, P.pb, P.ct,
        P.rb, P.cd], Own, Returns []⟩,
      ⟨"__loop21", true, [1, gen ^ r, P.rb], Own, Returns []⟩,
      ⟨"da_levels__L128_L7", true, [P.ct], Own, Returns [cr.1, cr.2]⟩,
      ⟨"__loop22", true, [1, gen ^ r, P.pb, P.rt], Own, Returns []⟩,
      ⟨"__loop23", decide (2 ^ L - r ≠ 0), [1, gen ^ (2 ^ L - r), P.rt, gen ^ r], Own, Returns []⟩,
      ⟨dlNames[L]!, true, [P.rt], Own, Returns [rr.1, rr.2]⟩]
  have hbm : ∀ rd, MemL rd Own → DvBufMem r L syms ws rd P := fun rd hm => dvBufMem_of_memL hm
  have hok : ∀ k ∈ ks, k.taken = true → CompleteAtD fs cert 16 k.f k.Lin k.args k.Out := by
    intro k hk ht
    simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact row_shape_completeAt fs cert hr1 hr hL
    · exact completeAt_of_rel_pureD daPure (mem_daPure_of (by simp))
        (fun rd hm => dvk_l18 (hbm rd hm) (by omega) hr1) 16
    · exact completeAt_of_rel_pureD daPure (mem_daPure_of (by simp))
        (fun rd hm => dvk_l19 (hbm rd hm) (by omega) hr1) 16
    · exact hl20
    · exact hl21
    · exact completeAt_of_rel_pureD daPure (mem_daPure_of (by simp))
        (fun rd hm => dvk_l22 (hbm rd hm) (by omega) hr1 hdot) 16
    · exact completeAt_of_rel_pureD daPure (mem_daPure_of (by simp))
        (fun rd hm => dvk_l7 (hbm rd hm)) 16
    · exact completeAt_of_rel_pureD daPure (mem_daPure_of (by simp))
        (fun rd hm => dvk_l23 (hbm rd hm) hrL (by omega) hr1) 16
    · simp only [decide_eq_true_eq] at ht
      exact completeAt_of_rel_pureD daPure (mem_daPure_of (by simp))
        (fun rd hm => dvk_l24 (hbm rd hm) hrL (by omega) ht) 16
    · exact completeAt_of_rel_pureD daPure (dlNames_mem_pure hL10)
        (fun rd hm => dvk_lev (hbm rd hm) hL10) 16
  obtain ⟨Nk, Lk, outs, hoo, hW, hD, -, hKids⟩ :=
    kidsFromIn_of_kidsD (fs := fs) (cert := cert) 16 ks hok (b0 + (dvSizes r L).sum)
  have hl0 : outs.length = 10 := hoo.length
  obtain ⟨o1, t1, rfl, hl1⟩ := exists_of_length_succ hl0
  obtain ⟨o2, t2, rfl, hl2⟩ := exists_of_length_succ hl1
  obtain ⟨o3, t3, rfl, hl3⟩ := exists_of_length_succ hl2
  obtain ⟨o4, t4, rfl, hl4⟩ := exists_of_length_succ hl3
  obtain ⟨o5, t5, rfl, hl5⟩ := exists_of_length_succ hl4
  obtain ⟨o6, t6, rfl, hl6⟩ := exists_of_length_succ hl5
  obtain ⟨o7, t7, rfl, hl7⟩ := exists_of_length_succ hl6
  obtain ⟨o8, t8, rfl, hl8⟩ := exists_of_length_succ hl7
  obtain ⟨o9, t9, rfl, hl9⟩ := exists_of_length_succ hl8
  obtain ⟨o10, t10, rfl, hl10⟩ := exists_of_length_succ hl9
  obtain rfl := List.eq_nil_of_length_eq_zero hl10
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -⟩ := hoo
  -- the layout
  have hWo : Within Own b0 (dvSizes r L).sum := bufL_within _ _ _ hfit
  refine ⟨fs "da_verify" + (dvSizes r L).sum + Nk, Own ++ Lk, _, [], ⟨rfl, rfl⟩, ?_,
    by rw [List.nil_append]; exact disj_append (bufL_disj _ _ _ hfit : DisjL Own) hD hWo hW le_rfl, fun rd hlow hm => ?_⟩
  · rw [List.nil_append, within_append]
    exact ⟨hWo.mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  simp only [List.nil_append] at hm
  obtain ⟨hm1, hLin'⟩ := memL_append.mp hm
  obtain ⟨hmO, hLk⟩ := memL_append.mp hm1
  have hb := hbm rd hmO
  -- the valuation and the path
  have hV := dv_core (rd := rd) (gsq := gen ^ s) (syms := syms) (r := r) (L := L) hb.cd
  set σ := dvσ rd (gen ^ s) r L P cr rr with hσ
  have hx : σ (.n 2) = ofK (gpow L) := by rw [hV.v2, gen_pow_eq_ofK]
  have hw := walk_dispatch σ dvPre dvPost dvPre_straight dvPost_straight (.n 2) dlNames [.n 41]
    [.n 48, .n 49] [.n 993, .n 994, .n 995, .n 996] (i := L) (by simp [dlNames]; omega)
    (by simp [dlNames]) hx
  rw [← dv_split] at hw
  set es := dvPre.flatMap (Main.slEvs σ) ++
    .call dlNames[L]! [.n 41] [.n 48, .n 49] :: dvPost.flatMap (Main.slEvs σ) with hes
  have hmemP : ∀ st, st ∈ dvPre ∨ st ∈ dvPost → st ∈ dvP := fun st h => by
    rw [dvP_eq]; rcases h with h | h <;> simp [h]
  have hev : ∀ e ∈ es, e.Holds rd σ := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · refine slEvs_holds (fun st hst => ?_) e he
      have hk := List.all_eq_true.mp dvPre_kinds st hst
      match st, hk with
      | .atom a, _ => exact hV.atoms a (mem_atomsIn (hmemP _ (Or.inl hst)))
      | .call .., _ => trivial
      | .ite .., hk => simp [dvPreKind] at hk
      | .match_ .., hk => simp [dvPreKind] at hk
      | .dispatch .., hk => simp [dvPreKind] at hk
      | .ret _, hk => simp [dvPreKind] at hk
      | .callIf c f args, hk =>
        simp only [dvPreKind, List.mem_cons, List.not_mem_nil, or_false, decide_eq_true_eq] at hk
        show IsInK (σ c)
        rcases hk with rfl | rfl | rfl | rfl | rfl
        · rw [hV.g15, ← pow_zero gen]; exact gen_pow_add_isInK _ _
        · rw [hV.g29, ← pow_zero gen]; exact gen_pow_add_isInK _ _
        · rw [hV.g35, ← pow_zero gen]; exact gen_pow_add_isInK _ _
        · rw [hV.g43, ← pow_zero gen]; exact gen_pow_add_isInK _ _
        · rw [hV.g46, ← pow_zero gen]; exact gen_pow_add_isInK _ _
    · rcases List.mem_cons.mp he with rfl | he
      · trivial
      · refine slEvs_holds (fun st hst => ?_) e he
        have hk := List.all_eq_true.mp dvPost_atoms st hst
        match st, hk with
        | .atom a, _ => exact hV.atoms a (mem_atomsIn (hmemP _ (Or.inr hst)))
        | .call .., hk => simp at hk
        | .callIf .., hk => simp at hk
        | .ite .., hk => simp at hk
        | .match_ .., hk => simp at hk
        | .dispatch .., hk => simp at hk
        | .ret _, hk => simp at hk
  obtain ⟨hpd, hpa, hpad, hpc⟩ := Main.straight_parts σ _ dvPre_straight
  obtain ⟨hqd, hqa, hqad, hqc⟩ := Main.straight_parts σ _ dvPost_straight
  have hal : allocs σ es = dvSizes r L := by
    rw [hes, allocs_append, show allocs σ (.call dlNames[L]! [.n 41] [.n 48, .n 49] ::
      dvPost.flatMap (Main.slEvs σ)) = allocs σ (dvPost.flatMap (Main.slEvs σ)) from rfl, hpa, hqa,
      dvPre_allocs, dvPost_allocs]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, Sum.elim_inl, id, List.append_nil,
      hV.v11, hV.v1, hV.v25, hV.v40, logG_gen_pow (show 128 * 2 ^ L < 2 ^ 64 - 1 by omega),
      logG_gen_pow (show r < 2 ^ 64 - 1 by omega), logG_gen_pow (show 129 * r < 2 ^ 64 - 1 by omega),
      logG_gen_pow (show 4 * 2 ^ L < 2 ^ 64 - 1 by omega)]
    rfl
  have h46 : decide (σ (.n 46) ≠ 0) = decide (2 ^ L - r ≠ 0) := by
    rw [hV.g46]; exact decide_eq_decide.mpr (one_add_gen_pow_ne' (by omega))
  have hT : ∀ {c : V} {x : ℕ}, σ c = 1 + gen ^ x → x ≠ 0 → x < 2 ^ 64 - 1 → decide (σ c ≠ 0) = true :=
    fun h hx hx' => by rw [h]; exact decide_eq_true ((one_add_gen_pow_ne' hx').mpr hx)
  have hcalls : calls es = [⟨"da_row_shape", [.n 1, .n 2, .n 0], [.n 3, .n 4], true⟩,
      ⟨"__loop17", [.n 16, .n 1, .n 13, .n 12], [], true⟩,
      ⟨"__loop18", [.n 30, .n 1, .n 26, .n 27], [], true⟩,
      ⟨"__loop19", [.n 32, .n 1, .n 3, .n 4, .n 2, .n 13, .n 31, .n 27, .n 17], [], true⟩,
      ⟨"__loop20", [.n 33, .n 1, .n 3, .n 4, .n 2, .n 13, .n 31, .n 27, .n 17], [], true⟩,
      ⟨"__loop21", [.n 36, .n 1, .n 27], [], true⟩,
      ⟨"da_levels__L128_L7", [.n 31], [.n 37, .n 38], true⟩,
      ⟨"__loop22", [.n 44, .n 1, .n 13, .n 41], [], true⟩,
      ⟨"__loop23", [.n 47, .n 4, .n 41, .n 1], [], decide (2 ^ L - r ≠ 0)⟩,
      ⟨dlNames[L]!, [.n 41], [.n 48, .n 49], true⟩] := by
    rw [hes, calls_append, show calls (.call dlNames[L]! [.n 41] [.n 48, .n 49] ::
      dvPost.flatMap (Main.slEvs σ)) = ⟨dlNames[L]!, [.n 41], [.n 48, .n 49], true⟩ ::
        calls (dvPost.flatMap (Main.slEvs σ)) from rfl, hpc, hqc, dvPre_calls, dvPost_calls]
    simp only [List.map_cons, List.map_nil, Main.mkCall, h46,
      hT hV.g15 (by omega) (by omega), hT hV.g29 (by omega) (by omega),
      hT hV.g35 (by omega) (by omega), hT hV.g43 (by omega) (by omega),
      List.nil_append, List.cons_append]
  -- the walk
  have hown : ∀ i, RegionL Own i → ownData cert fp b0 "da_verify" (dvSizes r L) es i :=
    fun i hi => Or.inl (bufL_region _ _ _ hfit i hi)
  have hcdO : ∀ k < 256, RegionL Own (dxC r L b0 + k) := fun k hk =>
    regionL_of_mem (L := Own) (xs := cdCells ws) (by
      rw [hOwn, dvOwn_eq]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      (by rw [cdCells_length]; exact hk)
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    (R := RegionL Lin) (D := RegionL []) (fp := fp) (N := Nk)
    (args := [gen ^ s]) (rets := digestCells (daRoot r L syms) ++ digestCells (daVd ws))
    (Dk := fun i => (fun _ => False) i ∨ outRegion ks [o1, o2, o3, o4, o5, o6, o7, o8, o9, o10] i)
    coreProgram_wf find_da_verify (Or.inl dv_loop) (by
      show [σ (.n 0)] = _; rw [hV.v0]) hw hV.rets hev
    (by
      rw [hal, hes, allocDsts_append, show allocDsts (.call dlNames[L]! [.n 41] [.n 48, .n 49] ::
        dvPost.flatMap (Main.slEvs σ)) = allocDsts (dvPost.flatMap (Main.slEvs σ)) from rfl, hpd,
        hqd, dvPre_allocs, dvPost_allocs]
      simp only [List.map_cons, List.map_nil, List.append_nil, hV.v12, hV.v13, hV.v17, hV.v26,
        hV.v27, hV.v31, hV.v41, hP, dvPtrsAt, gen_pow_eq_ofK]
      rfl)
    (fun q hq => by
      rw [hes, addrs_append, show addrs (.call dlNames[L]! [.n 41] [.n 48, .n 49] ::
        dvPost.flatMap (Main.slEvs σ)) = addrs (dvPost.flatMap (Main.slEvs σ)) from rfl, hpad, hqad,
        dvPre_addrs, dvPost_addrs] at hq
      simp at hq)
    ?_ ?_ (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
  · rw [hal] at h
    exact h
  · rw [hcalls, hal]
    refine hKids rd σ _ _ _ ?_ hlow hLk ?_ (regionsOk_of fun k hk _ i hi => ?_)
    · refine ⟨rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl,
        fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl,
        fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl,
        fun ht => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩, trivial⟩
      · show [σ (.n 1), σ (.n 2), σ (.n 0)] = _; rw [hV.v1, hV.v2, hV.v0]
      · rw [(h1 rfl).1]; show [σ (.n 3), σ (.n 4)] = _; rw [hV.v3, hV.v4]
      · show [σ (.n 16), σ (.n 1), σ (.n 13), σ (.n 12)] = _; rw [hV.g16, hV.v1, hV.v13, hV.v12]
      · rw [(h2 rfl).1]; rfl
      · show [σ (.n 30), σ (.n 1), σ (.n 26), σ (.n 27)] = _; rw [hV.g30, hV.v1, hV.v26, hV.v27]
      · rw [(h3 rfl).1]; rfl
      · show [σ (.n 32), σ (.n 1), σ (.n 3), σ (.n 4), σ (.n 2), σ (.n 13), σ (.n 31), σ (.n 27),
          σ (.n 17)] = _
        rw [hV.v32, hV.v1, hV.v3, hV.v4, hV.v2, hV.v13, hV.v31, hV.v27, hV.v17]
      · rw [(h4 rfl).1]; rfl
      · show [σ (.n 33), σ (.n 1), σ (.n 3), σ (.n 4), σ (.n 2), σ (.n 13), σ (.n 31), σ (.n 27),
          σ (.n 17)] = _
        rw [hV.v33, hV.v1, hV.v3, hV.v4, hV.v2, hV.v13, hV.v31, hV.v27, hV.v17]
      · rw [(h5 rfl).1]; rfl
      · show [σ (.n 36), σ (.n 1), σ (.n 27)] = _; rw [hV.g36, hV.v1, hV.v27]
      · rw [(h6 rfl).1]; rfl
      · show [σ (.n 31)] = _; rw [hV.v31]
      · rw [(h7 rfl).1]; show [σ (.n 37), σ (.n 38)] = _; rw [hV.v37, hV.v38]
      · show [σ (.n 44), σ (.n 1), σ (.n 13), σ (.n 41)] = _; rw [hV.g44, hV.v1, hV.v13, hV.v41]
      · rw [(h8 rfl).1]; rfl
      · show [σ (.n 47), σ (.n 4), σ (.n 41), σ (.n 1)] = _; rw [hV.g47, hV.v4, hV.v41, hV.v1]
      · rw [(h9 ht).1]; rfl
      · show [σ (.n 41)] = _; rw [hV.v41]
      · rw [(h10 rfl).1]; show [σ (.n 48), σ (.n 49)] = _; rw [hV.v48, hV.v49]
    · intro q hq
      simp only [B1.Kid.lins, ks, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_append] at hq
      rcases hq with hq | hq | hq | hq | hq | hq | hq | hq | hq | hq
      · exact hLin' q hq
      all_goals exact hmO q hq
    · simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (Or.inl hi)
      all_goals exact Or.inl (Or.inr (hown i hi))
  · intro A hA
    rw [hes, loadAddrs_append, show loadAddrs σ (.call dlNames[L]! [.n 41] [.n 48, .n 49] ::
      dvPost.flatMap (Main.slEvs σ)) = loadAddrs σ (dvPost.flatMap (Main.slEvs σ)) from rfl,
      B1.loadAddrs_straight σ _ dvPre_straight, B1.loadAddrs_straight σ _ dvPost_straight,
      dvPre_loads, dvPost_loads] at hA
    simp only [List.map_nil, List.nil_append, List.map_map, List.mem_map, List.mem_range,
      Function.comp] at hA
    obtain ⟨i, hi, rfl⟩ := hA
    refine ⟨dxC r L b0 + i, ?_, Or.inl (by rw [hal]; exact hown _ (hcdO i hi))⟩
    rw [hV.v17]
    exact limb0_gen_pow_mul _ _

end
end LeanVM.Guest.B1.Da
