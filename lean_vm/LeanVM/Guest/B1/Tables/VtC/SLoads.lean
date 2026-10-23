/-
  LeanVM.Guest.B1.Tables.VtC.SLoads

  Where `verify_tables`' loads of statements `0 ..< 2404` read: in `dims_g`, `table_rows`,
  `block_kappa`, `g_squares`, `sort_order`, `block_side_tab`, `block_off_g` and `idxc_tab`.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.SAll
public import LeanVM.Guest.B1.Tables.VtC.InBuf

/-!
# The loads of statements `0 ..< 2404`

`vtBufsS`: the buffers they read and write, (pointer, length). `loadsDirect`: every load of a
block goes through a buffer's own pointer variable at an offset below its length (a kernel check).
`rank0_loads`, `rank_loads`: a rank's lookups land at its block `e < 153` of `block_side_tab`,
`block_kappa`, `block_off_g`, and at `κ < 34` of `g_squares`. `vtS_loads`: under `vtS_complete`'s
hypotheses, every load lands in one of the buffers.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The buffers statements `0 ..< 2404` load from and store into. -/
def vtBufsS (args : List E) (w : ℕ → E) : List (E × ℕ) :=
  [(args.getD 10 0, 7), (args.getD 11 0, 6), (args.getD 12 0, 153), (args.getD 13 0, 34),
    (w 30, 153), (w 31, 153), (w 185, 153), (w 2732, 34)]

/-- Every load of the block is through `.n p` at an offset below `len`, `(p, len) ∈ ps`. -/
def loadsDirect (ps : List (ℕ × ℕ)) (blk : List Stmt) : Bool :=
  blk.all fun s ↦ match s with
    | .atom (.load _ p off) => ps.any fun q ↦ decide (p = .n q.1) && decide (off < q.2)
    | _ => true

/-- A statement's loads land in the buffers. -/
def LoadIn (σ : Val) (bufs : List (E × ℕ)) (s : Stmt) : Prop :=
  ∀ d p off, s = .atom (.load d p off) → InBuf σ bufs p off

theorem loadsDirect_ok {σ : Val} {bufs : List (E × ℕ)} {ps : List (ℕ × ℕ)} {blk : List Stmt}
    (h : loadsDirect ps blk = true) (hb : ∀ q ∈ ps, (σ (.n q.1), q.2) ∈ bufs) :
    ∀ s ∈ blk, LoadIn σ bufs s := by
  intro s hs d p off rfl
  have := List.all_eq_true.mp h _ hs
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
  obtain ⟨q, hq, rfl, hoff⟩ := this
  exact vt_inBuf_direct (hb q hq) hoff

theorem loadsInBuf_of {σ : Val} {bufs : List (E × ℕ)} {blk : List Stmt}
    (h : ∀ s ∈ blk, LoadIn σ bufs s) : LoadsInBuf σ bufs blk :=
  fun d p off hs ↦ h _ hs d p off rfl

theorem inBuf_mul {σ : Val} {bufs : List (E × ℕ)} {p : V} {b : E} {len j : ℕ}
    (hq : (b, len) ∈ bufs) (hp : σ p = b * gen ^ j) (hj : j < len) : InBuf σ bufs p 0 :=
  ⟨_, hq, j, hp, by simpa using hj⟩

variable {rd : Reader} {w : ℕ → E} {σ : Val} {bufs : List (E × ℕ)}

theorem rank0_loads {v R s e κ : ℕ} (hv : 186 ≤ v) (hg : GoodL rd w σ (vtRank0T v R s))
    (ev : σ (.n v) = gen ^ e) (e9 : σ (.n (v + 9)) = gen ^ κ) (he : e < 153) (hκ : κ < 34)
    (hR : R < 153) (b30 : (σ (.n 30), 153) ∈ bufs) (b31 : (σ (.n 31), 153) ∈ bufs)
    (b12 : (σ (.n 12), 153) ∈ bufs) (b185 : (σ (.n 185), 153) ∈ bufs)
    (b13 : (σ (.n 13), 34) ∈ bufs) : ∀ st ∈ vtRank0T v R s, LoadIn σ bufs st := by
  simp only [vtRank0T, GoodL, GoodS, fixNe, Good, and_true] at hg
  obtain ⟨-, -, -, g3, -, -, -, g7, -, -, g10, -, g12, -⟩ := hg
  simp only [show (31 : ℕ) < v + 5 ∧ v < v + 5 from ⟨by omega, by omega⟩,
    show (12 : ℕ) < v + 8 ∧ v < v + 8 from ⟨by omega, by omega⟩,
    show (185 : ℕ) < v + 11 ∧ v < v + 11 from ⟨by omega, by omega⟩,
    show (13 : ℕ) < v + 12 ∧ v + 9 < v + 12 from ⟨by omega, by omega⟩] at g3 g7 g10 g12
  intro st hst d p off rfl
  simp only [vtRank0T, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq,
    Atom.load.injEq, reduceCtorEq, false_or, or_false] at hst
  rcases hst with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
  · exact vt_inBuf_direct b30 hR
  · exact inBuf_mul b31 (by rw [g3, ev]) he
  · exact inBuf_mul b12 (by rw [g7, ev]) he
  · exact inBuf_mul b185 (by rw [g10, ev]) he
  · exact inBuf_mul b13 (by rw [g12, e9]) hκ

theorem rank_loads {v R s pk pc gin e κ : ℕ} (hv : 186 ≤ v)
    (hg : GoodL rd w σ (vtRankT v R s pk pc gin))
    (ev : σ (.n v) = gen ^ e) (e9 : σ (.n (v + 9)) = gen ^ κ) (he : e < 153) (hκ : κ < 34)
    (hR : R < 153) (b30 : (σ (.n 30), 153) ∈ bufs) (b31 : (σ (.n 31), 153) ∈ bufs)
    (b12 : (σ (.n 12), 153) ∈ bufs) (b185 : (σ (.n 185), 153) ∈ bufs)
    (b13 : (σ (.n 13), 34) ∈ bufs) : ∀ st ∈ vtRankT v R s pk pc gin, LoadIn σ bufs st := by
  simp only [vtRankT, GoodL, GoodS, fixNe, Good, and_true] at hg
  obtain ⟨-, -, -, g3, -, -, -, g7, -, -, -, -, -, -, g14, -, g16, -, -⟩ := hg
  simp only [show (31 : ℕ) < v + 5 ∧ v < v + 5 from ⟨by omega, by omega⟩,
    show (12 : ℕ) < v + 8 ∧ v < v + 8 from ⟨by omega, by omega⟩,
    show (185 : ℕ) < v + 21 ∧ v < v + 21 from ⟨by omega, by omega⟩,
    show (13 : ℕ) < v + 22 ∧ v + 9 < v + 22 from ⟨by omega, by omega⟩] at g3 g7 g14 g16
  intro st hst d p off rfl
  simp only [vtRankT, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq,
    Atom.load.injEq, reduceCtorEq, false_or, or_false] at hst
  rcases hst with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
  · exact vt_inBuf_direct b30 hR
  · exact inBuf_mul b31 (by rw [g3, ev]) he
  · exact inBuf_mul b12 (by rw [g7, ev]) he
  · exact inBuf_mul b185 (by rw [g14, ev]) he
  · exact inBuf_mul b13 (by rw [g16, e9]) hκ

theorem vtS_loads_checks :
    loadsDirect [(31, 153)] ((vtPre.drop 0).take 318) = true ∧
    loadsDirect [(10, 7), (11, 6), (2732, 34)] ((vtPre.drop 2189).take 215) = true := by
  decide +kernel

section
variable {args : List E}

set_option maxHeartbeats 2000000 in
/-- **Where statements `0 ..< 2404` load**: in `vtBufsS`, under `vtS_complete`'s hypotheses. -/
theorem vtS_loads (hl : args.length = 22) (hlow : LowDefB 8 rd) (κ : ℕ → ℕ)
    (hκ : ∀ b < 153, κ b < 34)
    (hbk : ∀ b < 153, LoadHolds rd (args.getD 12 0) b (gen ^ κ b))
    (hsq : ∀ j < 34, LoadHolds rd (args.getD 13 0) j (gen ^ 2 ^ j))
    (hso : TbReadsAt rd (w 30) (vtSortW κ)) (hst : TbReadsAt rd (w 31) vtSideW)
    (hoff : TbReadsAt rd (w 185) (vtOffW κ)) :
    LoadsInBuf (vtσ rd w args) (vtBufsS args w) ((vtPre.drop 0).take 2404) := by
  obtain ⟨c1, c2⟩ := vtS_loads_checks
  obtain ⟨HP, HC⟩ := vtS_sides hl hlow κ hκ hbk hsq hso hst hoff
  have hlP : (vtKsP κ).length = 54 := by simp [vtKsP]
  have hlC : (vtKsC κ).length = 45 := by simp [vtKsC]
  have e10 : vtσ rd w args (.n 10) = args.getD 10 0 := vt_param hl (by norm_num)
  have e11 : vtσ rd w args (.n 11) = args.getD 11 0 := vt_param hl (by norm_num)
  have e12 : vtσ rd w args (.n 12) = args.getD 12 0 := vt_param hl (by norm_num)
  have e13 : vtσ rd w args (.n 13) = args.getD 13 0 := vt_param hl (by norm_num)
  have e30 : vtσ rd w args (.n 30) = w 30 := vt_alloc hl 8 (sz := 153) (by decide +kernel)
  have e31 : vtσ rd w args (.n 31) = w 31 := vt_alloc hl 10 (sz := 153) (by decide +kernel)
  have e185 : vtσ rd w args (.n 185) = w 185 := vt_alloc hl 317 (sz := 153) vtSort_alloc185
  have e2732 : vtσ rd w args (.n 2732) = w 2732 :=
    vt_alloc hl 2257 (sz := 34) (by decide +kernel)
  have b30 : (vtσ rd w args (.n 30), 153) ∈ vtBufsS args w := by rw [e30]; simp [vtBufsS]
  have b31 : (vtσ rd w args (.n 31), 153) ∈ vtBufsS args w := by rw [e31]; simp [vtBufsS]
  have b12 : (vtσ rd w args (.n 12), 153) ∈ vtBufsS args w := by rw [e12]; simp [vtBufsS]
  have b185 : (vtσ rd w args (.n 185), 153) ∈ vtBufsS args w := by rw [e185]; simp [vtBufsS]
  have b13 : (vtσ rd w args (.n 13), 34) ∈ vtBufsS args w := by rw [e13]; simp [vtBufsS]
  have hoP := fun r (hr : r < 54) => ord_lt (vtKsP κ) (r := r) (by rw [hlP]; exact hr)
  have hoC := fun r (hr : r < 45) => ord_lt (vtKsC κ) (r := r) (by rw [hlC]; exact hr)
  rw [hlP] at hoP
  rw [hlC] at hoC
  have hkP : ∀ c < 54, (vtKsP κ).getD c 0 < 34 := fun c hc => by
    simp [vtKsP, hc]; exact hκ c (by omega)
  have hkC : ∀ c < 45, (vtKsC κ).getD c 0 < 34 := fun c hc => by
    simp [vtKsC, hc]; exact hκ _ (by omega)
  refine loadsInBuf_of (forall_slice_split 0 318 2086
    (loadsDirect_ok c1 (by simp [b31])) (forall_slice_split 318 1021 1065 ?_
      (forall_slice_split 1339 850 215 ?_ (loadsDirect_ok c2 ?_))))
  · rw [← vtPushBlk_length]
    refine forall_slice_of vtPushBlk_check ?_
    intro st hst'
    simp only [vtSideBlk, List.mem_append, List.mem_flatten, List.mem_map, List.mem_range] at hst'
    rcases hst' with h0 | ⟨_, ⟨r, hr, rfl⟩, hm⟩
    · obtain ⟨-, ev, e9, -⟩ := HP 0 (by rw [hlP]; norm_num)
      simp only [vtRv, ↓reduceIte, Nat.zero_add, Nat.sub_zero] at ev e9
      exact rank0_loads (by norm_num) (vt_goodL hl _ _ vtPush0_check) ev e9 (by
        have := hoP 0 (by norm_num); omega) (hkP _ (hoP 0 (by norm_num))) (by norm_num)
        b30 b31 b12 b185 b13 st h0
    · obtain ⟨-, ev, e9, -⟩ := HP (r + 1) (by rw [hlP]; omega)
      simp only [Nat.zero_add, Nat.sub_zero] at ev e9
      have hr1 := hoP (r + 1) (by omega)
      have hv := vtRv_ge 186 (r + 1)
      have hg := vt_goodL (rd := rd) (w := w) hl _ _ (vtPush_check (r + 1) (by omega) (by omega))
      simp only [vtRankAt] at hg hm
      exact rank_loads (by omega) hg ev e9 (by omega) (hkP _ hr1) (by omega) b30 b31 b12 b185
        b13 st hm
  · rw [← vtCountBlk_length]
    refine forall_slice_of vtCountBlk_check ?_
    intro st hst'
    simp only [vtSideBlk, List.mem_append, List.mem_flatten, List.mem_map, List.mem_range] at hst'
    rcases hst' with h0 | ⟨_, ⟨r, hr, rfl⟩, hm⟩
    · obtain ⟨-, ev, e9, -⟩ := HC 0 (by rw [hlC]; norm_num)
      simp only [vtRv, ↓reduceIte, Nat.add_sub_cancel_left] at ev e9
      exact rank0_loads (by norm_num) (vt_goodL hl _ _ vtCount0_check) ev e9 (by
        have := hoC 0 (by norm_num); omega) (hkC _ (hoC 0 (by norm_num))) (by norm_num)
        b30 b31 b12 b185 b13 st h0
    · obtain ⟨-, ev, e9, -⟩ := HC (r + 1) (by rw [hlC]; omega)
      simp only [Nat.add_sub_cancel_left] at ev e9
      have hr1 := hoC (r + 1) (by omega)
      have hv := vtRv_ge 1525 (r + 1)
      have hg := vt_goodL (rd := rd) (w := w) hl _ _ (vtCount_check (r + 1) (by omega) (by omega))
      simp only [vtRankAt] at hg hm
      exact rank_loads (by omega) hg ev e9 (by omega) (hkC _ hr1) (by omega) b30 b31 b12 b185
        b13 st hm
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · rw [e10]; simp [vtBufsS]
    · rw [e11]; simp [vtBufsS]
    · rw [e2732]; simp [vtBufsS]

end

end
end LeanVM.Guest.B1.Tables
