/-
  LeanVM.Guest.B1.Tables.VtC.BMain

  **`verify_tables`' bus sides complete** (statements `2404 ..< 5152`, fork B of B1-c).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.BAll

/-!
# The bus sides, complete

`vtB_complete`: under `VtBHyp`, every statement of `2404 ..< 5152` holds on the honest valuation,
every load reads inside `vtBufsB`, the framework words are the cursor's, the selectors are the
blocks' `blockSel`, and the three bus totals are `vtAcc0/1/2`'s (as `vt_asm_totals`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Fwd LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
open LeanVM.Protocol.EndToEnd.Complete (blockSel)

@[expose] public section

theorem vtB_flatP : tbStmtsEqb ((List.range 51).flatMap fun i ↦ vtSelT
    (vtPushSel.getD i default).2.2.1 (vtPushSel.getD i default).1
    (vtPushSel.getD i default).2.2.2.1 (vtPushSel.getD i default).2.2.2.2)
    ((vtPre.drop 2586).take 898) = true := by simp only [vtPre_drop]; decide +kernel

theorem vtB_flatC : tbStmtsEqb ((List.range 45).flatMap fun i ↦ vtSelT
    (vtCountSel.getD i default).2.2.1 (vtCountSel.getD i default).1
    (vtCountSel.getD i default).2.2.2.1 (vtCountSel.getD i default).2.2.2.2)
    ((vtPre.drop 4305).take 793) = true := by simp only [vtPre_drop]; decide +kernel

theorem vtB_fs_checks :
    tbStmtsEqb (fsNextT (.n 5) 0 2914) ((vtPre.drop 2462).take 9) = true ∧
    tbStmtsEqb (fsNextT (.n 5) 1 2927) ((vtPre.drop 2476).take 9) = true ∧
    tbStmtsEqb (fsNextT (.n 5) 2 2940) ((vtPre.drop 2490).take 9) = true ∧
    tbStmtsEqb (fsNextT (.n 5) 3 4444) ((vtPre.drop 3938).take 9) = true ∧
    tbStmtsEqb (fsNextT (.n 5) 4 4502) ((vtPre.drop 3983).take 9) = true := by
      simp only [vtPre_drop]; decide +kernel

theorem vtB_fs_reads : Atom.load (.n 2914) (.n 5) 0 ∉ vtSL ∧ Atom.load (.n 2927) (.n 5) 1 ∉ vtSL ∧
    Atom.load (.n 2940) (.n 5) 2 ∉ vtSL ∧ Atom.load (.n 4444) (.n 5) 3 ∉ vtSL ∧
    Atom.load (.n 4502) (.n 5) 4 ∉ vtSL := by decide +kernel

theorem vtB_index_stmts :
    tbStmtsEqb [.dispatch (.n 2884) vtImNames [.n 8] [.n 2908]] ((vtPre.drop 2455).take 1) = true ∧
    tbStmtsEqb [.dispatch (.n 2959) vtImNames [.n 8] [.n 2983]] ((vtPre.drop 2531).take 1) = true :=
  by simp only [vtPre_drop]; decide +kernel

theorem vtB_list5 (l : List E) (h : l.length = 5) :
    [l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0, l.getD 4 0] = l := by
  match l, h with
  | [_, _, _, _, _], _ => rfl

/-- A slice is a checked block's statements. -/
theorem vtB_tmpl {P : Stmt → Prop} {blk : List Stmt} {pos : ℕ}
    (hc : tbStmtsEqb blk ((vtPre.drop pos).take blk.length) = true) (h : ∀ s ∈ blk, P s) :
    ∀ s ∈ (vtPre.drop pos).take blk.length, P s := by
  rw [← tbStmtsEqb_sound hc]; exact h

/-- Slices in a row. -/
theorem vtB_cover {P : Stmt → Prop} : ∀ (cuts : List ℕ) (a : ℕ),
    (∀ i < cuts.length, ∀ s ∈ (vtPre.drop (a + (cuts.take i).sum)).take (cuts.getD i 0), P s) →
      ∀ s ∈ (vtPre.drop a).take cuts.sum, P s
  | [], _, _ => by simp
  | c :: cuts, a, h => by
    rw [List.sum_cons]
    refine forall_slice_split a c cuts.sum (by simpa using h 0 (by simp)) ?_
    refine vtB_cover cuts (a + c) fun i hi ↦ ?_
    have := h (i + 1) (by simp; omega)
    simpa [List.take_succ_cons, Nat.add_assoc] using this

section
variable {rd : Reader} {wo : ℕ → E} {args : List E}

/-- An allocation's pointer: the oracle's. -/
theorem vtB_allocDyn (hl : args.length = 22) {d s : V}
    (hm : Stmt.atom (.hint (.allocDyn d s)) ∈ vtPre) : vtσ rd wo args d = wo d.idx :=
  vt_goodS (rd := rd) (w := wo) hl hm

/-- **`index_mle`'s arm, complete.** -/
theorem vtB_indexArm (hl : args.length = 22) {x r : V} {point : List E} {κ : ℕ}
    (hm : Stmt.dispatch x vtImNames [.n 8] [r] ∈ vtPre) (hx : vtσ rd wo args x = gen ^ κ)
    (hκ : κ < 34) (hκμ : κ ≤ point.length) (hz : TbReadsAt rd (vtσ rd wo args (.n 8)) point)
    (hr : wo r.idx = indexMle (point.take κ)) :
    VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.dispatch x vtImNames [.n 8] [r]) ∧
      vtσ rd wo args r = indexMle (point.take κ) := by
  have er : vtσ rd wo args r = indexMle (point.take κ) := by
    rw [vtB_retsM (rd := rd) (w := wo) hl hm r (by simp), hr]
  refine ⟨vshB_dispatch (j := κ) (by simp [vtImNames]; omega) hx ?_, er⟩
  simp only [vtImNames, List.getElem_map, List.getElem_range, List.map_cons, List.map_nil]
  rw [er]
  exact index_mle_complete_holds κ hκ rd _ _
    ⟨point.take κ, by simp; omega, tbReadsAt_take hz κ, rfl⟩

theorem vtB_kap_vals (lm : ℕ) (τ : ℕ → ℕ) : vtKap lm τ 1 = lm ∧ vtKap lm τ 2 = 19 ∧
    vtKap lm τ 55 = lm ∧ vtKap lm τ 56 = 19 := by
  simp [vtKap, blockKappaSrc, blockKappaAdj]

theorem vtB_ksP (lm : ℕ) (τ : ℕ → ℕ) : vtKsP (vtKap lm τ) = vtSizesP lm τ := by
  apply List.ext_getElem (by simp [vtKsP, vtSizesP_length])
  intro i h1 h2
  have hi : i < 54 := by simpa [vtKsP] using h1
  simp only [vtKsP, List.getElem_map, List.getElem_range]
  rw [vt_kapP lm τ hi, List.getD_eq_getElem _ _ h2]

theorem vtB_ksC (lm : ℕ) (τ : ℕ → ℕ) : vtKsC (vtKap lm τ) = vtSizesC τ := by
  apply List.ext_getElem (by simp [vtKsC, vtSizesC_length])
  intro i h1 h2
  have hi : i < 45 := by simpa [vtKsC] using h1
  simp only [vtKsC, List.getElem_map, List.getElem_range]
  rw [vt_kapC lm τ hi, List.getD_eq_getElem _ _ h2]


set_option maxRecDepth 100000 in
/-- **`verify_tables`' bus sides complete** (statements `2404 ..< 5152`). -/
theorem vtB_complete {D : VtBIn} (H : VtBHyp rd wo args D) :
    (∀ s ∈ (vtPre.drop 2404).take 2748, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s) ∧
      LoadsInBuf (vtσ rd wo args) (vtBufsB (vtσ rd wo args)) ((vtPre.drop 2404).take 2748) ∧
      vtFreshWords (vtσ rd wo args) = D.xs ∧
      vtσ rd wo args (.n 4411) = (vtAcc0 (layoutOf D.bc D.lm D.rows) D.alphas
        (vtσ rd wo args (.n 15)) D.point
        [vtσ rd wo args (.n 2914), vtσ rd wo args (.n 2927), vtσ rd wo args (.n 2940)]
        (vtσ rd wo args (.n 2639)) (vtσ rd wo args (.n 27))).2 ∧
      vtσ rd wo args (.n 4924) = (vtAcc1 (layoutOf D.bc D.lm D.rows) D.alphas
        (vtσ rd wo args (.n 15)) D.point
        [vtσ rd wo args (.n 2914), vtσ rd wo args (.n 2927), vtσ rd wo args (.n 2940)]
        (vtσ rd wo args (.n 4444)) (vtσ rd wo args (.n 4502)) (vtσ rd wo args (.n 2639))
        (vtσ rd wo args (.n 27)) (vtσ rd wo args (.n 28))).2 ∧
      vtσ rd wo args (.n 5816) = (vtAcc2 (layoutOf D.bc D.lm D.rows) D.alphas
        (vtσ rd wo args (.n 15)) D.point
        [vtσ rd wo args (.n 2914), vtσ rd wo args (.n 2927), vtσ rd wo args (.n 2940)]
        (vtσ rd wo args (.n 4444)) (vtσ rd wo args (.n 4502)) (vtσ rd wo args (.n 2639))
        (vtσ rd wo args (.n 27)) (vtσ rd wo args (.n 28)) (vtσ rd wo args (.n 29))).2 ∧
      vtσ rd wo args (.n 2870) = blockSel (vtSizesP D.lm (vtHt D.rows)) D.point.length 0 D.point ∧
      vtσ rd wo args (.n 2900) = blockSel (vtSizesP D.lm (vtHt D.rows)) D.point.length 1 D.point ∧
      vtσ rd wo args (.n 2975) = blockSel (vtSizesP D.lm (vtHt D.rows)) D.point.length 2 D.point ∧
      vtσ rd wo args (.n 2873) = vtσ rd wo args (.n 2870) ∧
      vtσ rd wo args (.n 2904) = vtσ rd wo args (.n 2900) ∧
      vtσ rd wo args (.n 2979) = vtσ rd wo args (.n 2975) ∧
      (∀ i < 51, vtσ rd wo args (.n (vtPushPadData.getD i default).2.2.1) =
        blockSel (vtSizesP D.lm (vtHt D.rows)) D.point.length (3 + i) D.point) ∧
      (∀ i < 45, vtσ rd wo args (.n (vtCountPadData.getD i default).2.2.1) =
        blockSel (vtSizesC (vtHt D.rows)) D.point.length i D.point) := by
  obtain ⟨hl, hlow, hml, hlm, hlmμ, h19, hr, hτ, hτμ, hmu, hz, hdim, hbk, hal, hW, hxl, hcur,
    hpool, hcpl, hcan, e22, e185, eSh, e2732, e2767, e2769, e2770, hoff, hidxc, hz1, hrun, hidxB,
    hfitP, hfitC, hbitsF, hbitsP, hbitsC, hwF, hwP, hwC, hwI, hbc, hpw⟩ := H
  have p : ∀ i < 22, vtσ rd wo args (.n i) = args.getD i 0 := fun i hi ↦ vt_param hl hi
  have hlow34 : ∀ i < 34, (rd (Parameters.gpow i)).isSome := fun i hi ↦ hlow i (by norm_num; omega)
  -- the weights
  have hWl : (eqKernel D.alphas).length = 16 := by rw [vt_length_eqKernel, hal]; rfl
  set W : ℕ → E := fun i ↦ (eqKernel D.alphas).getD i 0 with hWd
  have hw : ∀ i < 16, LoadHolds rd (vtσ rd wo args (.n 14)) i (W i) := fun i hi ↦ by
    rw [p 14 (by norm_num)]
    have := hW i (by omega)
    rwa [← List.getD_eq_getElem _ 0] at this
  have hWσ : TbReadsAt rd (vtσ rd wo args (.n 14)) (eqKernel D.alphas) := by
    rw [p 14 (by norm_num)]; exact hW
  have hP := vtP_honest hl (by omega) hWσ
  -- the block sizes
  have hbkc : ∀ b < 153, LoadHolds rd (vtσ rd wo args (.n 12)) b
      (gen ^ vtKap D.lm (vtHt D.rows) b) := fun b hb ↦ by
    have hl' : b < (blockKappaWords (gen ^ D.lm)
        ((vtTauList (vtHt D.rows)).map (gen ^ ·))).length := by simp [blockKappaWords]; exact hb
    have := hbk b hl'
    rw [← List.getD_eq_getElem _ 0 hl', vt_kappa_word D.lm (vtHt D.rows) hb] at this
    rw [p 12 (by norm_num)]; exact this
  have hκ : ∀ b < 153, vtKap D.lm (vtHt D.rows) b < 34 := fun b hb ↦ vt_kap_lt _ _ hlm hτ hb
  obtain ⟨k1, k2, k55, k56⟩ := vtB_kap_vals D.lm (vtHt D.rows)
  -- the offsets
  have hoffP : ∀ b < 54, LoadHolds rd (vtσ rd wo args (.n 185)) b
      (gen ^ (stackOffsets (vtSizesP D.lm (vtHt D.rows))).1.getD b 0) := fun b hb ↦ by
    rw [e185]
    have := hoff b (by simp [vtOffW]; omega)
    simpa [vtOffW, hb, vtB_ksP] using this
  have hoffC : ∀ c < 45, LoadHolds rd (vtσ rd wo args (.n 185)) (108 + c)
      (gen ^ (stackOffsets (vtSizesC (vtHt D.rows))).1.getD c 0) := fun c hc ↦ by
    rw [e185]
    have := hoff (108 + c) (by simp [vtOffW]; omega)
    simpa [vtOffW, show ¬ 108 + c < 54 by omega, show ¬ 108 + c < 108 by omega, vtB_ksC] using this
  have halP : ∀ b < 54, 2 ^ (vtSizesP D.lm (vtHt D.rows)).getD b 0 ∣
      (stackOffsets (vtSizesP D.lm (vtHt D.rows))).1.getD b 0 ∧
      (stackOffsets (vtSizesP D.lm (vtHt D.rows))).1.getD b 0 < 2 ^ D.point.length :=
    fun b hb ↦ ⟨vtB_stack_aligned _ (by rw [vtSizesP_length]; exact hb),
      vtB_stack_lt _ (by rw [vtSizesP_length]; exact hb) hfitP⟩
  have halC : ∀ c < 45, 2 ^ (vtSizesC (vtHt D.rows)).getD c 0 ∣
      (stackOffsets (vtSizesC (vtHt D.rows))).1.getD c 0 ∧
      (stackOffsets (vtSizesC (vtHt D.rows))).1.getD c 0 < 2 ^ D.point.length :=
    fun c hc ↦ ⟨vtB_stack_aligned _ (by rw [vtSizesC_length]; exact hc),
      vtB_stack_lt _ (by rw [vtSizesC_length]; exact hc) hfitC⟩
  -- the selectors
  have hsh : ∀ t < 6, ∃ d, vtσ rd wo args (.n (vtShLen t)) = gen ^ d ∧
      D.point.length = d + vtHt D.rows t ∧
      RunTables rd (vtσ rd wo args (.n 2769) * gen ^ (288 * t))
        (vtσ rd wo args (.n 2770) * gen ^ (144 * t)) d
        (D.point.drop (vtHt D.rows t)) ((D.point.map (1 + ·)).drop (vtHt D.rows t))
        ((gSquaresList.drop (vtHt D.rows t)).take d) := fun t ht ↦
    ⟨D.point.length - vtHt D.rows t, eSh t ht, by have := hτμ t ht; omega,
      by rw [e2769, e2770]; exact hrun t ht⟩
  have hbF : ∀ b < 3, TbReadsAt rd (vtσ rd wo args (.n (vtFwV.getD b 0 + 6)))
      (offBits ((stackOffsets (vtSizesP D.lm (vtHt D.rows))).1.getD b 0)) := fun b hb ↦ by
    rw [vtB_allocDyn hl (vt_mem_slice (vtFw_check b hb)
      (by simp [vtFwSelT] : Stmt.atom (.hint (.allocDyn (.n (vtFwV.getD b 0 + 6))
        (.n (vtFwV.getD b 0 + 5)))) ∈ _))]
    exact hbitsF b hb
  have hbP : ∀ i < 51, TbReadsAt rd (vtσ rd wo args (.n ((vtPushSel.getD i default).2.2.1 + 6)))
      (offBits ((stackOffsets (vtSizesP D.lm (vtHt D.rows))).1.getD (3 + i) 0)) := fun i hi ↦ by
    rw [vtB_allocDyn hl (vt_mem_slice (vtPushSel_check i (by rw [show vtPushSel.length = 51 from rfl]; exact hi))
      (by simp [vtSelT] : Stmt.atom (.hint (.allocDyn (.n ((vtPushSel.getD i default).2.2.1 + 6))
        (.n ((vtPushSel.getD i default).2.2.1 + 5)))) ∈ _))]
    exact hbitsP i hi
  have hbC : ∀ i < 45, TbReadsAt rd (vtσ rd wo args (.n ((vtCountSel.getD i default).2.2.1 + 6)))
      (offBits ((stackOffsets (vtSizesC (vtHt D.rows))).1.getD i 0)) := fun i hi ↦ by
    rw [vtB_allocDyn hl (vt_mem_slice (vtCountSel_check i (by rw [show vtCountSel.length = 45 from rfl]; exact hi))
      (by simp [vtSelT] : Stmt.atom (.hint (.allocDyn (.n ((vtCountSel.getD i default).2.2.1 + 6))
        (.n ((vtCountSel.getD i default).2.2.1 + 5)))) ∈ _))]
    exact hbitsC i hi
  obtain ⟨⟨vF, vP, vC⟩, s0, s1, s2, c0, c1, c2, hS, hsum, hSC, hsumC⟩ :=
    vtc_sels hl (by rw [p 9 (by norm_num)]; exact hmu) hml hlmμ h19 hτ
      (fun t ht ↦ by rw [p 10 (by norm_num)]; exact hdim t ht) (by rw [p 12 (by norm_num)]; exact hbk)
      (by rw [e2767]; exact hz1) (by rw [e2732]; exact hidxc) hsh hoffP hoffC halP halC hbF hbP hbC
      hwF hwP hwC hlow34
  -- the stream reads
  have hx : ∀ i < 5, LoadHolds rd (vtσ rd wo args (.n 5)) i (D.xs.getD i 0) := fun i hi ↦ by
    rw [p 5 (by norm_num), List.getD_eq_getElem D.xs 0 (by omega : i < D.xs.length)]
    exact hcur i (by omega)
  obtain ⟨cF0, cF1, cF2, cF3, cF4⟩ := vtB_fs_checks
  obtain ⟨rF0, rF1, rF2, rF3, rF4⟩ := vtB_fs_reads
  obtain ⟨f0, x0, v0⟩ := vtc_fsNext hl cF0 rF0 (hx 0 (by norm_num))
  obtain ⟨f1, x1, v1⟩ := vtc_fsNext hl cF1 rF1 (hx 1 (by norm_num))
  obtain ⟨f2, x2, v2⟩ := vtc_fsNext hl cF2 rF2 (hx 2 (by norm_num))
  obtain ⟨f3, x3, v3⟩ := vtc_fsNext hl cF3 rF3 (hx 3 (by norm_num))
  obtain ⟨f4, x4, v4⟩ := vtc_fsNext hl cF4 rF4 (hx 4 (by norm_num))
  -- the reads the specials need
  have rd2884 := vtB_readM hl (vtB_memAt 2434 (.atom (.load (.n 2884) (.n 12) 1)) (by decide +kernel)) (by decide +kernel)
    (hbkc 1 (by norm_num))
  have rd2959 := vtB_readM hl (vtB_memAt 2510 (.atom (.load (.n 2959) (.n 12) 2)) (by decide +kernel)) (by decide +kernel)
    (hbkc 2 (by norm_num))
  have rd4430 := vtB_readM hl (vtB_memAt 3926 (.atom (.load (.n 4430) (.n 12) 55)) (by decide +kernel)) (by decide +kernel)
    (hbkc 55 (by norm_num))
  have rd4475 := vtB_readM hl (vtB_memAt 3970 (.atom (.load (.n 4475) (.n 12) 56)) (by decide +kernel)) (by decide +kernel)
    (hbkc 56 (by norm_num))
  rw [k1] at rd2884
  rw [k2] at rd2959
  rw [k55] at rd4430
  rw [k56] at rd4475
  have hz8 : TbReadsAt rd (vtσ rd wo args (.n 8)) D.point := by rw [p 8 (by norm_num)]; exact hz
  obtain ⟨I1, i1⟩ := vtB_indexArm hl (vtB_memAt 2455 _ (vtAt_eqb vtB_index_stmts.1)) rd2884.1 (by omega) hlmμ hz8
    hwI.1
  obtain ⟨I2, i2⟩ := vtB_indexArm hl (vtB_memAt 2531 _ (vtAt_eqb vtB_index_stmts.2)) rd2959.1 (by norm_num) h19
    hz8 hwI.2
  -- the buffers
  have e2851 : vtσ rd wo args (.n 2851) = wo 2851 := vt_alloc hl 2404 (sz := 153) (by decide +kernel)
  have hidxσ : ∀ i < 3, LoadHolds rd (vtσ rd wo args (.n 2851)) i
      ((vtIdxBufW D.point D.lm).getD i 0) := fun i hi ↦ by
    rw [e2851, List.getD_eq_getElem _ _ (by simp [vtIdxBufW]; omega)]
    exact hidxB i (by simp [vtIdxBufW]; omega)
  have hpoolσ : ∀ i < 5, LoadHolds rd (vtσ rd wo args (.n 16)) i (D.xs.getD i 0) := fun i hi ↦ by
    rw [p 16 (by norm_num)]; exact hpool i hi
  have hcplσ : ∀ i < 5, LoadHolds rd (vtσ rd wo args (.n 17)) i
      (gen ^ (if i < 4 then D.lm else 19)) := fun i hi ↦ by
    rw [p 17 (by norm_num)]; exact hcpl i hi
  have q1 : (vtIdxBufW D.point D.lm).getD 1 0 = indexMle (D.point.take D.lm) := by
    simp [vtIdxBufW]
  have q2 : (vtIdxBufW D.point D.lm).getD 2 0 = indexMle (D.point.take 19) := by
    simp [vtIdxBufW]
  -- the stores
  have h2456 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 2908) (.n 2851) 1)) :=
    vsh_store (hidxσ 1 (by norm_num)) (by rw [i1, q1])
  have h2532 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 2983) (.n 2851) 2)) :=
    vsh_store (hidxσ 2 (by norm_num)) (by rw [i2, q2])
  have hpS : ∀ (i b : ℕ), i < 5 → vtσ rd wo args (.n b) = D.xs.getD i 0 →
      VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n b) (.n 16) i)) :=
    fun i b hi he ↦ vsh_store (hpoolσ i hi) he
  have hcS : ∀ (i b : ℕ), i < 4 → vtσ rd wo args (.n b) = gen ^ D.lm →
      VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n b) (.n 17) i)) :=
    fun i b hi he ↦ vsh_store (hcplσ i (by omega)) (by rw [he]; simp [hi])
  have hcS4 : ∀ b : ℕ, vtσ rd wo args (.n b) = gen ^ 19 →
      VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n b) (.n 17) 4)) :=
    fun b he ↦ vsh_store (hcplσ 4 (by norm_num)) (by rw [he]; simp)
  -- the permutation
  have h3982 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.keccak [.n 2921, .n 2923,
      .n 2934, .n 2936, .n 2947, .n 2949, .n 4451, .n 4453, .n 22, .n 23, .n 24, .n 25, .n 26]
      (lyOuts 4489) false false)) := by
    have hg := vt_goodS (rd := rd) (w := wo) hl (vtB_memAt 3982 (.atom (.keccak [.n 2921, .n 2923, .n 2934, .n 2936, .n 2947, .n 2949, .n 4451, .n 4453, .n 22, .n 23, .n 24, .n 25, .n 26] (lyOuts 4489) false false)) (by decide +kernel))
    rw [fixNe_atom] at hg
    refine holds_of_good (rd := rd) (σ := vtσ rd wo args) (S := vtSL) (w := wo)
      (a := .keccak [.n 2921, .n 2923, .n 2934, .n 2936, .n 2947, .n 2949, .n 4451, .n 4453, .n 22,
        .n 23, .n 24, .n 25, .n 26] (lyOuts 4489) false false) hg ?_
    show ∀ c : Fin 13, _
    intro c
    have k0 := fsPackVals_canonical (D.xs.getD 0 0) dsObserve
    have k1' := fsPackVals_canonical (D.xs.getD 1 0) dsObserve
    have k2' := fsPackVals_canonical (D.xs.getD 2 0) dsObserve
    have k3 := fsPackVals_canonical (D.xs.getD 3 0) dsObserve
    fin_cases c <;> simp [cells13]
    · rw [show 2921 = 2914 + 1 + 6 by rfl, v0 6 (by norm_num)]; exact k0.1
    · rw [show 2923 = 2914 + 1 + 8 by rfl, v0 8 (by norm_num)]; exact k0.2
    · rw [show 2934 = 2927 + 1 + 6 by rfl, v1 6 (by norm_num)]; exact k1'.1
    · rw [show 2936 = 2927 + 1 + 8 by rfl, v1 8 (by norm_num)]; exact k1'.2
    · rw [show 2947 = 2940 + 1 + 6 by rfl, v2 6 (by norm_num)]; exact k2'.1
    · rw [show 2949 = 2940 + 1 + 8 by rfl, v2 8 (by norm_num)]; exact k2'.2
    · rw [show 4451 = 4444 + 1 + 6 by rfl, v3 6 (by norm_num)]; exact k3.1
    · rw [show 4453 = 4444 + 1 + 8 by rfl, v3 8 (by norm_num)]; exact k3.2
    · rw [show 22 = 22 + 0 by rfl, e22 0 (by norm_num)]; exact hcan 0 (by norm_num)
    · rw [show 23 = 22 + 1 by rfl, e22 1 (by norm_num)]; exact hcan 1 (by norm_num)
    · rw [show 24 = 22 + 2 by rfl, e22 2 (by norm_num)]; exact hcan 2 (by norm_num)
    · rw [show 25 = 22 + 3 by rfl, e22 3 (by norm_num)]; exact hcan 3 (by norm_num)
    · rw [show 26 = 22 + 4 by rfl, e22 4 (by norm_num)]; exact hcan 4 (by norm_num)
  -- the glue
  have g2404 := vtB_glue_2404 (rd := rd) (wo := wo) hl
  have g2424 := vtB_glue_2424 hl hw
  have g2452 := vtB_glue_2452 hl hw I1 h2456
  have g2471 := vtB_glue_2471 hl hw (hpS 0 2914 (by norm_num) x0)
    (hcS 0 2884 (by norm_num) rd2884.1)
  have g2485 := vtB_glue_2485 hl hw (hpS 1 2927 (by norm_num) x1)
    (hcS 1 2884 (by norm_num) rd2884.1)
  have g2499 := vtB_glue_2499 hl hw (hpS 2 2940 (by norm_num) x2)
    (hcS 2 2884 (by norm_num) rd2884.1)
  have g2528 := vtB_glue_2528 hl hw I2 h2532
  have g3484 := vtB_glue_3484 hl hw
  have g3910 := vtB_glue_3910 hl hw hbkc hκ hidxσ hlow34
  have g3947 := vtB_glue_3947 hl hw hbkc hκ hpoolσ hidxσ hlow34 (hpS 3 4444 (by norm_num) x3)
    (hcS 3 4430 (by norm_num) rd4430.1) h3982
  have g3992 := vtB_glue_3992 hl hw hbkc hκ hlow34 (hpS 4 4502 (by norm_num) x4)
    (hcS4 4475 rd4475.1)
  have g5098 := vtB_glue_5098 (rd := rd) (wo := wo) hl
  -- every statement
  have hall : ∀ s ∈ (vtPre.drop 2404).take 2748, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
    refine vtB_cover [3, 17, 10, 18, 10, 9, 5, 9, 5, 9, 11, 18, 58, 898, 426, 28, 9, 36, 9, 313,
      793, 54] 2404 fun i hi ↦ ?_
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i
    · exact g2404
    · exact vtB_tmpl (vtFw_check 0 (by norm_num)) (vF 0 (by norm_num))
    · exact g2424
    · exact vtB_tmpl (vtFw_check 1 (by norm_num)) (vF 1 (by norm_num))
    · exact g2452
    · exact vtB_tmpl cF0 f0
    · exact g2471
    · exact vtB_tmpl cF1 f1
    · exact g2485
    · exact vtB_tmpl cF2 f2
    · exact g2499
    · exact vtB_tmpl (vtFw_check 2 (by norm_num)) (vF 2 (by norm_num))
    · exact g2528
    · intro s hs
      change s ∈ (vtPre.drop 2586).take 898 at hs
      rw [← tbStmtsEqb_sound vtB_flatP] at hs
      obtain ⟨j, hj, hs⟩ := List.mem_flatMap.mp hs
      exact vP j (List.mem_range.mp hj) s hs
    · exact g3484
    · exact g3910
    · exact vtB_tmpl cF3 f3
    · exact g3947
    · exact vtB_tmpl cF4 f4
    · exact g3992
    · intro s hs
      change s ∈ (vtPre.drop 4305).take 793 at hs
      rw [← tbStmtsEqb_sound vtB_flatC] at hs
      obtain ⟨j, hj, hs⟩ := List.mem_flatMap.mp hs
      exact vC j (List.mem_range.mp hj) s hs
    · exact g5098
  -- the totals
  have i1' : vtσ rd wo args (.n 4440) = vtσ rd wo args (.n 2908) := by
    rw [(vtB_readM hl (vtB_memAt 3934 (.atom (.load (.n 4440) (.n 2851) 1)) (by decide +kernel)) (by decide +kernel)
      (hidxσ 1 (by norm_num))).1, q1, i1]
  have i2' : vtσ rd wo args (.n 4485) = vtσ rd wo args (.n 2983) := by
    rw [(vtB_readM hl (vtB_memAt 3978 (.atom (.load (.n 4485) (.n 2851) 2)) (by decide +kernel)) (by decide +kernel)
      (hidxσ 2 (by norm_num))).1, q2, i2]
  have m0 : vtσ rd wo args (.n 4457) = vtσ rd wo args (.n 2914) := by
    rw [(vtB_readM hl (vtB_memAt 3952 (.atom (.load (.n 4457) (.n 16) 0)) (by decide +kernel)) (by decide +kernel)
      (hpoolσ 0 (by norm_num))).1, x0]
  have m1 : vtσ rd wo args (.n 4461) = vtσ rd wo args (.n 2927) := by
    rw [(vtB_readM hl (vtB_memAt 3956 (.atom (.load (.n 4461) (.n 16) 1)) (by decide +kernel)) (by decide +kernel)
      (hpoolσ 1 (by norm_num))).1, x1]
  have m2 : vtσ rd wo args (.n 4465) = vtσ rd wo args (.n 2940) := by
    rw [(vtB_readM hl (vtB_memAt 3960 (.atom (.load (.n 4465) (.n 16) 2)) (by decide +kernel)) (by decide +kernel)
      (hpoolσ 2 (by norm_num))).1, x2]
  have hb1 : vtσ rd wo args (.n 2853) = vtσ rd wo args (.n 15) + 1 := by
    have g := vt_goodL (rd := rd) (w := wo) hl 2405 [.atom (.const (.n 2852) (word 1 0 0)),
      .atom (.add (.n 2853) (.n 15) (.n 2852))] (by decide +kernel)
    simp only [GoodL, GoodS, fixNe, Good, and_true] at g
    rw [g.2, g.1, tb_word_one]
  have hpv : vtσ rd wo args (.n 4411) = vtσ rd wo args (.n 3036) + vtσ rd wo args (.n 4406) +
      (1 + vtσ rd wo args (.n 3984)) + vtσ rd wo args (.n 27) := by
    have g := vt_goodL (rd := rd) (w := wo) hl 3905 [.atom (.add (.n 4407) (.n 3036) (.n 4406)),
      .atom (.const (.n 4408) (word 1 0 0)), .atom (.add (.n 4409) (.n 4408) (.n 3984)),
      .atom (.add (.n 4410) (.n 4407) (.n 4409)), .atom (.add (.n 4411) (.n 4410) (.n 27))]
      (by decide +kernel)
    simp only [GoodL, GoodS, fixNe, Good, and_true] at g
    obtain ⟨a1, a2, a3, a4, a5⟩ := g
    rw [a5, a4, a3, a2, a1, tb_word_one]
  have hpw' : ∀ t < 6, paddingWeight (D.point.take (vtHt D.rows t)) (vtRw D.rows t) =
      vtσ rd wo args (.n (vtPadV t)) := fun t ht ↦ (hpw t ht).symm
  have e0 := vt_total0 hbc D.alphas (vtσ rd wo args (.n 15)) D.point
    [vtσ rd wo args (.n 2914), vtσ rd wo args (.n 2927), vtσ rd wo args (.n 2940)]
    (vtσ rd wo args (.n 2639)) (vtσ rd wo args (.n 27)) _ _ _ (fun c ↦ vtσ rd wo args (.n c))
    (fun t ↦ vtσ rd wo args (.n (vtPadV t))) s0.symm s1.symm s2.symm (fun i hi ↦ hS i hi) hpw' hr
  have e1 := vt_total1 hbc D.alphas (vtσ rd wo args (.n 15)) D.point
    [vtσ rd wo args (.n 2914), vtσ rd wo args (.n 2927), vtσ rd wo args (.n 2940)]
    (vtσ rd wo args (.n 4444)) (vtσ rd wo args (.n 4502)) (vtσ rd wo args (.n 2639))
    (vtσ rd wo args (.n 27)) (vtσ rd wo args (.n 28)) _ _ _ (fun c ↦ vtσ rd wo args (.n c))
    (fun t ↦ vtσ rd wo args (.n (vtPadV t))) s0.symm s1.symm s2.symm (fun i hi ↦ hS i hi) hpw' hr
  have e2 := vt_total2 (bc := D.bc) (lm := D.lm) D.alphas (vtσ rd wo args (.n 15)) D.point
    [vtσ rd wo args (.n 2914), vtσ rd wo args (.n 2927), vtσ rd wo args (.n 2940)]
    (vtσ rd wo args (.n 4444)) (vtσ rd wo args (.n 4502)) (vtσ rd wo args (.n 2639))
    (vtσ rd wo args (.n 27)) (vtσ rd wo args (.n 28)) (vtσ rd wo args (.n 29))
    (fun c ↦ vtσ rd wo args (.n c)) (fun t ↦ vtσ rd wo args (.n (vtPadV t))) W
    (fun i hi ↦ hSC i hi) hpw' hr
  have hpush := vtP_push_total hP hw
  have hfw := vtP_push_fw hP hw
  rw [hb1] at hpush
  have hpad : vtσ rd wo args (.n 4406) = vtPadSum (fun c ↦ vtσ rd wo args (.n c))
      (fun t ↦ vtσ rd wo args (.n (vtPadV t))) W (vtσ rd wo args (.n 15) + 1) vtPushPadData := by
    have := hpv.symm.trans hpush
    linear_combination this
  have hfp : ∀ (L : Layout), L.logMemory = D.lm → L.logBytecode = 19 →
      vtFpPush L D.alphas D.point
        [vtσ rd wo args (.n 2914), vtσ rd wo args (.n 2927), vtσ rd wo args (.n 2940)]
        (vtσ rd wo args (.n 2639)) =
        [W 0 + W 1 + W 2, W 0 * gen + W 1 * vtσ rd wo args (.n 2908) + W 2 +
          W 3 * vtσ rd wo args (.n 2914) + W 4 * vtσ rd wo args (.n 2927) +
          W 5 * vtσ rd wo args (.n 2940), W 0 * gen ^ 2 + W 1 * vtσ rd wo args (.n 2983) + W 2 +
          vtσ rd wo args (.n 2639)] ∧
      vtFpPull L D.alphas D.point
          [vtσ rd wo args (.n 2914), vtσ rd wo args (.n 2927), vtσ rd wo args (.n 2940)]
          (vtσ rd wo args (.n 4444)) (vtσ rd wo args (.n 4502)) (vtσ rd wo args (.n 2639)) =
        [W 0 + W 1 * vtWFinalPc + W 2, W 0 * gen + W 1 * vtσ rd wo args (.n 2908) +
          W 2 * vtσ rd wo args (.n 4444) + W 3 * vtσ rd wo args (.n 2914) +
          W 4 * vtσ rd wo args (.n 2927) + W 5 * vtσ rd wo args (.n 2940),
          W 0 * gen ^ 2 + W 1 * vtσ rd wo args (.n 2983) + W 2 * vtσ rd wo args (.n 4502) +
            vtσ rd wo args (.n 2639)] := by
    intro L hL1 hL2
    simp only [vtFpPush, vtFpPull, fingerprints, hL1, hL2, vt_take3 (eqKernel D.alphas) (by omega),
      vt_take6 (eqKernel D.alphas) (by omega), ← i1, ← i2, vtWFinalPc_eq, dot,
      List.zipWith_cons_cons, List.zipWith_nil_left, List.foldl_cons, List.foldl_nil,
      List.cons_append, List.nil_append, sepState, sepMem, sepBytecode, Verifier.gpow, pow_zero]
    refine ⟨?_, ?_⟩ <;> simp only [List.cons.injEq, and_true] <;> refine ⟨?_, ?_, ?_⟩ <;> ring
  obtain ⟨fP, fQ⟩ := hfp (layoutOf D.bc D.lm D.rows) (vt_layout_logMemory D.bc D.lm D.rows)
    (vt_layout_logBytecode D.bc D.lm D.rows hbc)
  have hfresh : vtFreshWords (vtσ rd wo args) = D.xs := by
    show [vtσ rd wo args (.n 2914), vtσ rd wo args (.n 2927), vtσ rd wo args (.n 2940),
      vtσ rd wo args (.n 4444), vtσ rd wo args (.n 4502)] = D.xs
    rw [x0, x1, x2, x3, x4]
    exact vtB_list5 D.xs hxl
  refine ⟨hall, vtB_loadsInBuf _, hfresh, ?_, ?_, ?_, s0, s1, s2, c0, c1, c2, hS, hSC⟩
  · rw [e0, fP, hpush, hfw, hsum]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    ring
  · rw [e1, fQ, vtP_pull_total hP hw, hpad, c0, c1, c2, i1', i2', m0, m1, m2]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    ring
  · rw [e2, vtP_count_total hP W, hsumC]
    ring

end

end
end LeanVM.Guest.B1.Tables
