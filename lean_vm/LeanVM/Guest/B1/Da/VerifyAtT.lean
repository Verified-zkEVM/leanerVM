/-
  LeanVM.Guest.B1.Da.VerifyAtT

  `da_verify` placed, by a tree of its honest shape (`Budget.NodeHonest`): its node at a valuation
  holding the DA shape (`v1 = g^r`, the row tree's dispatch `v2 = g^L`, `da_row_shape`'s returns
  `v3`, `v4`) and its buffers' sizes, its calls, its buffers, and its column loops' trees of their
  honest shapes, their columns' too.

  `da_verify` checks Benedikt Wagner's LeanDA witnesses (`Da.Witness.Opens`), as ported here.
-/

module

public import LeanVM.Guest.B1.Da.VerifyAt
public import LeanVM.Guest.B1.Da.ColumnAtT
public import LeanVM.Guest.B1.Da.ColLoopAtT

/-!
# `da_verify`, its honest shape

`dvQ r L`: `v1 = g^r` (the end of the row loops `__loop17`, `__loop18`, `__loop21`, `__loop22`),
`v2 = g^L`, `v3 = g^(2^L)`, `v4 = g^(2^L - r)` (`da_row_shape`'s returns; the end of `__loop23`),
the buffers' sizes' operands `v11 = g^(128·2^L)`, `v25 = g^(129·r)`, `v40 = g^(4·2^L)`, and the
row loops' starts `v16 = v30 = v36 = v44 = v47 = 1` (read by the budget's counts).
`dvCallList r L`: its ten calls. `dvTs r L`: `__loop19`'s tree `l20NH r L` (64 iterations from
counter `0`, each column `da_verify_column__L1` of `colNH`), `__loop20`'s `l21NH r L` (64 from
`64`, `da_verify_column__L0`), no predicate on the others. `dvNH r L`: `da_verify`'s honest shape,
its `HeapBuf`s `dvSizes r L`. `dvT_completeAt`: `da_verify_completeAt` (same proof) by such
a tree.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd LeanVM.Guest.Value.Keccak
open LeanVM.Guest.Budget (NodeHonest)
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDT Returns Kid OutsOk CallsMatch RegionsOk outRegion DisjL
  Within disj_append disj_nil kidsFromIn_of_kidsD completeAt_of_rel_pureD regionsOk_of within_append
  bufL_within bufL_disj bufL_region)
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append)

@[expose] public section

/-- The words `da_verify`'s loops start and end at and its buffers' sizes are read from. -/
def dvQ (r L : ℕ) (σ : Val) : Prop :=
  σ (.n 1) = gen ^ r ∧ σ (.n 2) = gen ^ L ∧ σ (.n 3) = gen ^ 2 ^ L ∧ σ (.n 4) = gen ^ (2 ^ L - r) ∧
    σ (.n 11) = gen ^ (128 * 2 ^ L) ∧ σ (.n 25) = gen ^ (129 * r) ∧ σ (.n 40) = gen ^ (4 * 2 ^ L) ∧
    σ (.n 16) = 1 ∧ σ (.n 30) = 1 ∧ σ (.n 36) = 1 ∧ σ (.n 44) = 1 ∧ σ (.n 47) = 1

/-- `da_verify`'s calls. -/
def dvCallList (r L : ℕ) : List Call :=
  [⟨"da_row_shape", [.n 1, .n 2, .n 0], [.n 3, .n 4], true⟩,
    ⟨"__loop17", [.n 16, .n 1, .n 13, .n 12], [], true⟩,
    ⟨"__loop18", [.n 30, .n 1, .n 26, .n 27], [], true⟩,
    ⟨"__loop19", [.n 32, .n 1, .n 3, .n 4, .n 2, .n 13, .n 31, .n 27, .n 17], [], true⟩,
    ⟨"__loop20", [.n 33, .n 1, .n 3, .n 4, .n 2, .n 13, .n 31, .n 27, .n 17], [], true⟩,
    ⟨"__loop21", [.n 36, .n 1, .n 27], [], true⟩,
    ⟨"da_levels__L128_L7", [.n 31], [.n 37, .n 38], true⟩,
    ⟨"__loop22", [.n 44, .n 1, .n 13, .n 41], [], true⟩,
    ⟨"__loop23", [.n 47, .n 4, .n 41, .n 1], [], decide (2 ^ L - r ≠ 0)⟩,
    ⟨dlNames[L]!, [.n 41], [.n 48, .n 49], true⟩]

/-- `__loop19`'s honest tree: columns `0 … 63`, each `da_verify_column__L1`. -/
def l20NH (r L : ℕ) : Tree → Prop :=
  colFrom "__loop19" "da_verify_column__L1" 64
    (colNH "da_verify_column__L1" "__loop415" "__loop416" r L) 64 0

/-- `__loop20`'s honest tree: columns `64 … 127`, each `da_verify_column__L0`. -/
def l21NH (r L : ℕ) : Tree → Prop :=
  colFrom "__loop20" "da_verify_column__L0" 128
    (colNH "da_verify_column__L0" "__loop417" "__loop418" r L) 64 64

/-- The predicates on `da_verify`'s callees' trees. -/
def dvTs (r L : ℕ) : List (Tree → Prop) :=
  [fun _ => True, fun _ => True, fun _ => True, l20NH r L, l21NH r L, fun _ => True, fun _ => True,
    fun _ => True, fun _ => True, fun _ => True]

/-- **`da_verify`'s honest shape** on `r` rows of `2^L` padded. -/
def dvNH (r L : ℕ) : Tree → Prop :=
  NodeHonest coreProgram "da_verify" (dvQ r L) (fun _ => dvCallList r L) (fun _ => dvSizes r L) (dvTs r L)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **`da_verify` is complete, placed, by a tree of its honest shape** (`dvNH r L`). -/
theorem dvT_completeAt (fs : String → ℕ) (cert : String → V → ℕ)
    (hcv : cert "da_vector_cell" (.n 1) + 256 ≤ fs "da_vector_cell") {r L : ℕ}
    (hr1 : 1 ≤ r) (hr : r ≤ LeanDa.maxRows) (hL : 2 ^ L = LeanDa.nPad r)
    {syms : ℕ → ℕ → List K} {ws : ℕ → List E} (hsl : ∀ i j, (syms i j).length = 256)
    (hwl : ∀ j, (ws j).length = 256) (hdot : ∀ i < r, accSum syms ws i 128 = 0) (s : ℕ) :
    CompleteAtDT fs cert 16 "da_verify" [(s + L, [gen ^ 2 ^ L])] [gen ^ s]
      (Returns (digestCells (daRoot r L syms) ++ digestCells (daVd ws))) (dvNH r L) := by
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
  have hcol1 : ∀ k, 0 ≤ k → k < 64 → CompleteAtDT fs cert 16 "da_verify_column__L1" Own
      [gen ^ k, gen ^ r, gen ^ 2 ^ L, gen ^ (2 ^ L - r), gen ^ L, P.pb, P.ct, P.rb, P.cd]
      (Returns []) (colNH "da_verify_column__L1" "__loop415" "__loop416" r L) := fun k _ hk =>
    col_completeAtT fs cert hcv find_col1 core769_body col1_params (by
      rw [Program.loop_of_find? find_col1]; decide +kernel) find_l417 row417_shape.1 find_l418
      gap418_shape.1 (by decide) (by decide)
      (fun rd node lv hm => colm_rows1 hm hrL hsl hwl hk)
      (fun rd node lv hm => colm_gaps hm gap418_shape.1 gap418_shape.2 core896_body)
      hr1 hrL hL10 hwl (by omega)
  have hcol0 : ∀ k, 64 ≤ k → k < 128 → CompleteAtDT fs cert 16 "da_verify_column__L0" Own
      [gen ^ k, gen ^ r, gen ^ 2 ^ L, gen ^ (2 ^ L - r), gen ^ L, P.pb, P.ct, P.rb, P.cd]
      (Returns []) (colNH "da_verify_column__L0" "__loop417" "__loop418" r L) := fun k _ hk =>
    col_completeAtT fs cert hcv find_col0 core770_body col0_params (by
      rw [Program.loop_of_find? find_col0]; decide +kernel) find_l419 row419_shape.1 find_l420
      gap420_shape.1 (by decide) (by decide)
      (fun rd node lv hm => colm_rows0 hm hrL hsl hwl hk)
      (fun rd node lv hm => colm_gaps hm gap420_shape.1 gap420_shape.2 core898_body)
      hr1 hrL hL10 hwl hk
  have hl20 : CompleteAtDT fs cert 16 "__loop19" Own
      [1, gen ^ r, gen ^ 2 ^ L, gen ^ (2 ^ L - r), gen ^ L, P.pb, P.ct, P.rb, P.cd] (Returns [])
      (l20NH r L) := by
    have := colLoop_completeAtT fs cert (by rw [coreProgram_length]; omega) l20_ok word_g64
      (by norm_num) hcol1 0 le_rfl (by norm_num)
    rwa [pow_zero] at this
  have hl21 : CompleteAtDT fs cert 16 "__loop20" Own
      [gen ^ 64, gen ^ r, gen ^ 2 ^ L, gen ^ (2 ^ L - r), gen ^ L, P.pb, P.ct, P.rb, P.cd]
      (Returns []) (l21NH r L) :=
    colLoop_completeAtT fs cert (by rw [coreProgram_length]; omega) l21_ok word_g128
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
  have hokT : B1.KidsDT fs cert 16 ks (dvTs r L) :=
    ⟨fun _ => (row_shape_completeAt fs cert hr1 hr hL).toT,
      fun _ => (completeAt_of_rel_pureD daPure (mem_daPure_of (by simp))
        (fun rd hm => dvk_l18 (hbm rd hm) (by omega) hr1) 16).toT,
      fun _ => (completeAt_of_rel_pureD daPure (mem_daPure_of (by simp))
        (fun rd hm => dvk_l19 (hbm rd hm) (by omega) hr1) 16).toT,
      fun _ => hl20, fun _ => hl21,
      fun _ => (completeAt_of_rel_pureD daPure (mem_daPure_of (by simp))
        (fun rd hm => dvk_l22 (hbm rd hm) (by omega) hr1 hdot) 16).toT,
      fun _ => (completeAt_of_rel_pureD daPure (mem_daPure_of (by simp))
        (fun rd hm => dvk_l7 (hbm rd hm)) 16).toT,
      fun _ => (completeAt_of_rel_pureD daPure (mem_daPure_of (by simp))
        (fun rd hm => dvk_l23 (hbm rd hm) hrL (by omega) hr1) 16).toT,
      fun ht => (completeAt_of_rel_pureD daPure (mem_daPure_of (by simp))
        (fun rd hm => dvk_l24 (hbm rd hm) hrL (by omega) (of_decide_eq_true ht)) 16).toT,
      fun _ => (completeAt_of_rel_pureD daPure (dlNames_mem_pure hL10)
        (fun rd hm => dvk_lev (hbm rd hm) hL10) 16).toT, trivial⟩
  obtain ⟨Nk, Lk, outs, hoo, hW, hD, -, hKids⟩ :=
    B1.kidsFromInT_of_kidsDT (fs := fs) (cert := cert) 16 ks (dvTs r L) hokT (b0 + (dvSizes r L).sum)
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
  have h := relAtInWT_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
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
    (dvTs r L) ?_ ?_ (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
  · have h' := relAtInT_nodeHonest (Q := dvQ r L) (cs := fun _ => dvCallList r L)
      (bs := fun _ => dvSizes r L) (Ts := dvTs r L) h find_da_verify hw
      ⟨hV.v1, hV.v2, hV.v3, hV.v4, hV.v11, hV.v25, hV.v40, hV.g16, hV.g30, hV.g36, hV.g44,
        hV.g47⟩ hcalls hal (by simp [dvCallList, dvTs])
    rw [hal] at h'
    exact h'
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
