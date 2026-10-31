/-
  LeanVM.Guest.B1.Tables.VtC.SSort

  `verify_tables`' statements `0 ..< 2189` hold on the honest valuation: the capacity and claims
  copied, `sort_order` hinted, `block_side_tab` written, the push and count sides' block orders
  certified into `block_off_g`.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.SSide

/-!
# The block certification (G:1948-1986)

The honest buffers, for the blocks' log-sizes `κ`: `vtSortW κ` (`sort_order`: each side's
`stack_offsets` order, push from `0`, count from `108`; pull's slots `1`), `vtSideW`
(`block_side_tab`: the blocks' sides), `vtOffW κ` (`block_off_g`: the push and count blocks'
`g^offset`, pull's `1`). `vtS_sort`: on a memory holding `block_kappa`'s `g^κ`, the squares and the
three buffers, defined below `2^8`, statements `0 ..< 2189` hold.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-! ## The honest buffers -/

/-- The push side's log-sizes. -/
def vtKsP (κ : ℕ → ℕ) : List ℕ := (List.range 54).map κ

/-- The count side's log-sizes. -/
def vtKsC (κ : ℕ → ℕ) : List ℕ := (List.range 45).map fun c ↦ κ (108 + c)

/-- `sort_order`'s honest words. -/
def vtSortW (κ : ℕ → ℕ) : List E := (List.range 153).map fun i ↦
  if i < 54 then gen ^ (tbStackOrder (vtKsP κ)).getD i 0
  else if i < 108 then 1 else gen ^ (108 + (tbStackOrder (vtKsC κ)).getD (i - 108) 0)

/-- `block_side_tab`'s words. -/
def vtSideW : List E := (List.range 153).map fun b ↦ word (vtBlockSide b) 0 0

/-- `block_off_g`'s honest words. -/
def vtOffW (κ : ℕ → ℕ) : List E := (List.range 153).map fun b ↦
  if b < 54 then gen ^ (stackOffsets (vtKsP κ)).1.getD b 0
  else if b < 108 then 1 else gen ^ (stackOffsets (vtKsC κ)).1.getD (b - 108) 0

/-! ## Slices -/

theorem forall_slice_split {P : Stmt → Prop} (a m n : ℕ) (h1 : ∀ s ∈ (vtPre.drop a).take m, P s)
    (h2 : ∀ s ∈ (vtPre.drop (a + m)).take n, P s) : ∀ s ∈ (vtPre.drop a).take (m + n), P s := by
  intro s hs
  rw [List.take_add, List.mem_append, List.drop_drop] at hs
  rcases hs with hs | hs
  · exact h1 s hs
  · exact h2 s hs

theorem forall_slice_of {P : Stmt → Prop} {a : ℕ} {blk : List Stmt}
    (heq : tbStmtsEqb blk ((vtPre.drop a).take blk.length) = true) (h : ∀ s ∈ blk, P s) :
    ∀ s ∈ (vtPre.drop a).take blk.length, P s := by
  rw [← tbStmtsEqb_sound heq]; exact h

/-- A side's statements: its first rank, then the others. -/
def vtSideBlk (v0 R0 s n : ℕ) : List Stmt :=
  vtRank0T v0 R0 s ++ ((List.range (n - 1)).map fun r ↦ vtRankAt v0 R0 s (r + 1)).flatten

theorem vtPushBlk_check :
    tbStmtsEqb (vtSideBlk 186 0 0 54) ((vtPre.drop 318).take (vtSideBlk 186 0 0 54).length) =
      true := by simp only [vtPre_drop]; decide +kernel

theorem vtCountBlk_check :
    tbStmtsEqb (vtSideBlk 1525 108 2 45) ((vtPre.drop 1339).take (vtSideBlk 1525 108 2 45).length) =
      true := by simp only [vtPre_drop]; decide +kernel

theorem vtPushBlk_length : (vtSideBlk 186 0 0 54).length = 1021 := by decide +kernel

theorem vtCountBlk_length : (vtSideBlk 1525 108 2 45).length = 850 := by decide +kernel

theorem vtPush_reads0 : ∀ a ∈ vtRankReads 186 0 ++ [.load (.n (186 + 13)) (.n (186 + 12)) 0],
    a ∉ vtSL := by decide +kernel

theorem vtCount_reads0 : ∀ a ∈ vtRankReads 1525 108 ++ [.load (.n (1525 + 13)) (.n (1525 + 12)) 0],
    a ∉ vtSL := by decide +kernel

theorem vtPush_reads : ∀ r < 54, 1 ≤ r → ∀ a ∈ vtRankReads (vtRv 186 r) (0 + r) ++
    [.load (.n (vtRv 186 r + 23)) (.n (vtRv 186 r + 22)) 0], a ∉ vtSL := by decide +kernel

theorem vtCount_reads : ∀ r < 45, 1 ≤ r → ∀ a ∈ vtRankReads (vtRv 1525 r) (108 + r) ++
    [.load (.n (vtRv 1525 r + 23)) (.n (vtRv 1525 r + 22)) 0], a ∉ vtSL := by decide +kernel

theorem vtSort_prelude_check : tbStmtsEqb [.atom (.copy (.n 22) (.n 0)), .atom (.copy (.n 23) (.n 1)),
    .atom (.copy (.n 24) (.n 2)), .atom (.copy (.n 25) (.n 3)), .atom (.copy (.n 26) (.n 4)),
    .atom (.copy (.n 27) (.n 19)), .atom (.copy (.n 28) (.n 20)), .atom (.copy (.n 29) (.n 21)),
    .atom (.hint (.alloc (.n 30) 153)), .atom (.hint (.witness "sort_order" (.heap (.n 30) 0 153))),
    .atom (.hint (.alloc (.n 31) 153))] ((vtPre.drop 0).take 11) = true := by
      simp only [vtPre_drop]; decide +kernel

theorem vtSort_alloc185 : tbStmtsEqb [.atom (.hint (.alloc (.n 185) 153))]
    ((vtPre.drop 317).take 1) = true := by simp only [vtPre_drop]; decide +kernel

theorem vtSideT_length : vtSideT.length = 306 := by decide +kernel

/-! ## The statements -/

section
variable {rd : Reader} {w : ℕ → E} {args : List E}

theorem vt_alloc (hl : args.length = 22) (n : ℕ) {d : ℕ} {sz : ℕ}
    (heq : tbStmtsEqb [.atom (.hint (.alloc (.n d) sz))] ((vtPre.drop n).take 1) = true) :
    vtσ rd w args (.n d) = w d := by
  have h := vt_goodL (rd := rd) (w := w) hl n _ heq
  simpa [GoodL, GoodS, fixNe, Good] using h

/-- Side-tab entries. -/
theorem vtSideW_get {rd : Reader} {p : E} (h : TbReadsAt rd p vtSideW) {b : ℕ} (hb : b < 153) :
    LoadHolds rd p b (word (vtBlockSide b) 0 0) := by
  have := h b (by simp [vtSideW]; exact hb)
  simpa [vtSideW] using this

/-- **The two sides' ranks**, rank by rank. -/
theorem vtS_sides (hl : args.length = 22) (hlow : LowDefB 8 rd) (κ : ℕ → ℕ)
    (hκ : ∀ b < 153, κ b < 34)
    (hbk : ∀ b < 153, LoadHolds rd (args.getD 12 0) b (gen ^ κ b))
    (hsq : ∀ j < 34, LoadHolds rd (args.getD 13 0) j (gen ^ 2 ^ j))
    (hso : TbReadsAt rd (w 30) (vtSortW κ)) (hst : TbReadsAt rd (w 31) vtSideW)
    (hoff : TbReadsAt rd (w 185) (vtOffW κ)) :
    (∀ r < (vtKsP κ).length,
        (if r = 0 then ∀ st ∈ vtRank0T 186 0 0, VSH (coreProgram.Rel rd) rd (vtσ rd w args) st
          else ∀ st ∈ vtRankAt 186 0 0 r, VSH (coreProgram.Rel rd) rd (vtσ rd w args) st) ∧
        RankOut (vtσ rd w args) 186 (fun r => 0 + (tbStackOrder (vtKsP κ)).getD r 0)
          (fun b => (vtKsP κ).getD (b - 0) 0) (ordPre (vtKsP κ)) r) ∧
      (∀ r < (vtKsC κ).length,
        (if r = 0 then ∀ st ∈ vtRank0T 1525 108 2, VSH (coreProgram.Rel rd) rd (vtσ rd w args) st
          else ∀ st ∈ vtRankAt 1525 108 2 r, VSH (coreProgram.Rel rd) rd (vtσ rd w args) st) ∧
        RankOut (vtσ rd w args) 1525 (fun r => 108 + (tbStackOrder (vtKsC κ)).getD r 0)
          (fun b => (vtKsC κ).getD (b - 108) 0) (ordPre (vtKsC κ)) r) := by
  have e12 : vtσ rd w args (.n 12) = args.getD 12 0 := vt_param hl (by norm_num)
  have e13 : vtσ rd w args (.n 13) = args.getD 13 0 := vt_param hl (by norm_num)
  have e30 : vtσ rd w args (.n 30) = w 30 :=
    vt_alloc hl 8 (sz := 153) (by decide +kernel)
  have e31 : vtσ rd w args (.n 31) = w 31 :=
    vt_alloc hl 10 (sz := 153) (by decide +kernel)
  have e185 : vtσ rd w args (.n 185) = w 185 := vt_alloc hl 317 (sz := 153) vtSort_alloc185
  have hsq' : ∀ j < 34, LoadHolds rd (vtσ rd w args (.n 13)) j (gen ^ 2 ^ j) := by
    rw [e13]; exact hsq
  have hkl : ∀ b < 153, LoadHolds rd (vtσ rd w args (.n 12)) b (gen ^ κ b) := by
    rw [e12]; exact hbk
  have hlP : (vtKsP κ).length = 54 := by simp [vtKsP]
  have hlC : (vtKsC κ).length = 45 := by simp [vtKsC]
  have H1 := side_ranks (rd := rd) (w := w) hl hlow (v0 := 186) (p0 := 318) (R0 := 0) (s := 0)
    (base := 0) (vtKsP κ) (by norm_num)
    vtPush0_check (by rw [hlP]; exact vtPush_check)
    vtPush_reads0 (by rw [hlP]; exact vtPush_reads) (fun c hc => by
      rw [hlP] at hc; simp [vtKsP, hc]; exact hκ c (by omega)) (by simp [hlP])
    (fun r hr => by
      rw [hlP] at hr; rw [e30]
      have := hso r (by simp [vtSortW]; omega)
      simpa [vtSortW, hr] using this)
    (fun c hc => by
      rw [hlP] at hc; rw [e31]
      have := vtSideW_get hst (b := 0 + c) (by omega)
      rwa [show vtBlockSide (0 + c) = 0 by simp [vtBlockSide]; omega] at this)
    (fun c hc => by
      rw [hlP] at hc
      have := hkl (0 + c) (by omega)
      simpa [vtKsP, hc] using this)
    (fun c hc => by
      rw [hlP] at hc; rw [e185]
      have := hoff c (by simp [vtOffW]; omega)
      simpa [vtOffW, hc] using this)
    hsq'
  have H2 := side_ranks (rd := rd) (w := w) hl hlow (v0 := 1525) (p0 := 1339) (R0 := 108)
    (s := 2) (base := 108) (vtKsC κ) (by norm_num)
    vtCount0_check (by rw [hlC]; exact vtCount_check)
    vtCount_reads0 (by rw [hlC]; exact vtCount_reads) (fun c hc => by
      rw [hlC] at hc; simp [vtKsC, hc]; exact hκ _ (by omega)) (by simp [hlC])
    (fun r hr => by
      rw [hlC] at hr; rw [e30]
      have := hso (108 + r) (by simp [vtSortW]; omega)
      simpa [vtSortW, hr, show ¬ (108 + r < 54) by omega, show ¬ (108 + r < 108) by omega]
        using this)
    (fun c hc => by
      rw [hlC] at hc; rw [e31]
      have := vtSideW_get hst (b := 108 + c) (by omega)
      rwa [show vtBlockSide (108 + c) = 2 by simp [vtBlockSide]; omega] at this)
    (fun c hc => by
      rw [hlC] at hc
      have := hkl (108 + c) (by omega)
      simpa [vtKsC, hc] using this)
    (fun c hc => by
      rw [hlC] at hc; rw [e185]
      have := hoff (108 + c) (by simp [vtOffW]; omega)
      simpa [vtOffW, hc, show ¬ (108 + c < 54) by omega, show ¬ (108 + c < 108) by omega]
        using this)
    hsq'
  exact ⟨H1, H2⟩

/-- **Statements `0 ..< 2189`.** -/
theorem vtS_sort (hl : args.length = 22) (hlow : LowDefB 8 rd) (κ : ℕ → ℕ)
    (hκ : ∀ b < 153, κ b < 34)
    (hbk : ∀ b < 153, LoadHolds rd (args.getD 12 0) b (gen ^ κ b))
    (hsq : ∀ j < 34, LoadHolds rd (args.getD 13 0) j (gen ^ 2 ^ j))
    (hso : TbReadsAt rd (w 30) (vtSortW κ)) (hst : TbReadsAt rd (w 31) vtSideW)
    (hoff : TbReadsAt rd (w 185) (vtOffW κ)) :
    ∀ s ∈ (vtPre.drop 0).take 2189, VSH (coreProgram.Rel rd) rd (vtσ rd w args) s := by
  have e12 : vtσ rd w args (.n 12) = args.getD 12 0 := vt_param hl (by norm_num)
  have e13 : vtσ rd w args (.n 13) = args.getD 13 0 := vt_param hl (by norm_num)
  have e30 : vtσ rd w args (.n 30) = w 30 :=
    vt_alloc hl 8 (sz := 153) (by decide +kernel)
  have e31 : vtσ rd w args (.n 31) = w 31 :=
    vt_alloc hl 10 (sz := 153) (by decide +kernel)
  have e185 : vtσ rd w args (.n 185) = w 185 := vt_alloc hl 317 (sz := 153) vtSort_alloc185
  have hsq' : ∀ j < 34, LoadHolds rd (vtσ rd w args (.n 13)) j (gen ^ 2 ^ j) := by
    rw [e13]; exact hsq
  have hkl : ∀ b < 153, LoadHolds rd (vtσ rd w args (.n 12)) b (gen ^ κ b) := by
    rw [e12]; exact hbk
  have hlP : (vtKsP κ).length = 54 := by simp [vtKsP]
  have hlC : (vtKsC κ).length = 45 := by simp [vtKsC]
  have hsides := vtS_sides hl hlow κ hκ hbk hsq hso hst hoff
  -- the prelude, the side tab, the push and count sides
  refine forall_slice_split 0 11 2178 ?_ (forall_slice_split 11 306 1872 ?_
    (forall_slice_split 317 1 1871 ?_ (forall_slice_split 318 1021 850 ?_ ?_)))
  · rw [← show [Stmt.atom (.copy (.n 22) (.n 0)), .atom (.copy (.n 23) (.n 1)),
      .atom (.copy (.n 24) (.n 2)), .atom (.copy (.n 25) (.n 3)), .atom (.copy (.n 26) (.n 4)),
      .atom (.copy (.n 27) (.n 19)), .atom (.copy (.n 28) (.n 20)),
      .atom (.copy (.n 29) (.n 21)), .atom (.hint (.alloc (.n 30) 153)),
      .atom (.hint (.witness "sort_order" (.heap (.n 30) 0 153))),
      .atom (.hint (.alloc (.n 31) 153))].length = 11 from rfl]
    refine forall_slice_of vtSort_prelude_check ?_
    exact vt_block hl 0 _ vtSort_prelude_check [] (by decide +kernel) (by simp)
  · rw [← vtSideT_length]
    refine forall_slice_of vtSideT_check ?_
    intro st hst'
    simp only [vtSideT, List.mem_flatten, List.mem_map, List.mem_range] at hst'
    obtain ⟨_, ⟨b, hb, rfl⟩, hm⟩ := hst'
    have hc : vtσ rd w args (.n (32 + b)) = word (vtBlockSide b) 0 0 := by
      have := vt_goodS (rd := rd) (w := w) hl (vt_mem_slice vtSideT_check
        (show Stmt.atom (.const (.n (32 + b)) (word (vtBlockSide b) 0 0)) ∈ vtSideT by
          simp only [vtSideT, List.mem_flatten, List.mem_map, List.mem_range]
          exact ⟨_, ⟨b, hb, rfl⟩, List.mem_cons_self⟩))
      simpa [fixNe, GoodS, Good] using this
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact hc
    · show LoadHolds rd _ _ _
      rw [e31, hc]; exact vtSideW_get hst hb
  · rw [show (1 : ℕ) = [Stmt.atom (.hint (.alloc (.n 185) 153))].length from rfl]
    refine forall_slice_of vtSort_alloc185 ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    trivial
  · -- the push side
    rw [← vtPushBlk_length]
    refine forall_slice_of vtPushBlk_check ?_
    have H := hsides.1
    intro st hst'
    simp only [vtSideBlk, List.mem_append, List.mem_flatten, List.mem_map, List.mem_range] at hst'
    rcases hst' with h0 | ⟨_, ⟨r, hr, rfl⟩, hm⟩
    · simpa using (H 0 (by rw [hlP]; norm_num)).1 st h0
    · have := (H (r + 1) (by rw [hlP]; omega)).1
      simp only [Nat.add_one_ne_zero, ↓reduceIte] at this
      exact this st hm
  · -- the count side
    rw [← vtCountBlk_length]
    refine forall_slice_of vtCountBlk_check ?_
    have H := hsides.2
    intro st hst'
    simp only [vtSideBlk, List.mem_append, List.mem_flatten, List.mem_map, List.mem_range] at hst'
    rcases hst' with h0 | ⟨_, ⟨r, hr, rfl⟩, hm⟩
    · simpa using (H 0 (by rw [hlC]; norm_num)).1 st h0
    · have := (H (r + 1) (by rw [hlC]; omega)).1
      simp only [Nat.add_one_ne_zero, ↓reduceIte] at this
      exact this st hm

end

end
end LeanVM.Guest.B1.Tables
