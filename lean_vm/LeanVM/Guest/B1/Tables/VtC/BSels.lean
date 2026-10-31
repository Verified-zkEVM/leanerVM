/-
  LeanVM.Guest.B1.Tables.VtC.BSels

  All of `verify_tables`' block selectors complete: the push side's three framework blocks and
  `51` table blocks, the count side's `45` table blocks, at the certified stack offsets.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.BSel
public import LeanVM.Guest.B1.Tables.Vt.SelsAll

/-!
# The block selectors, complete

`vtc_sels`: on the bus point at `zeta` (`μ` coordinates, `log_mem ≤ μ`, `19 ≤ μ`), `block_kappa`
the blocks' log-sizes, `dims_g` the tables' heights `τ`, `block_off_g` each push and count block's
offset in its side's stack (`stackOffsets`, aligned, below `2^μ`), each block's offset bits at its
hinted buffer, `zeta1`, `idxc_tab` and the shared tables, and the callees returning each block's
`blockSel` and `g^offset`: every selector statement holds, and the selectors, their copies and the
two running sums are `vt_sels`'.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Fwd LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (blockSel)
open Finset

@[expose] public section

/-- The framework blocks' first values and running-sum links. -/
def vtFwV : List ℕ := [2854, 2884, 2959]
def vtFwPrev : List (Option ℕ) := [none, some 2870, some 2903]
def vtFwPos : List ℕ := [2407, 2434, 2510]

theorem vtFw_check : ∀ b < 3, tbStmtsEqb (vtFwSelT (vtFwV.getD b 0) b (vtFwPrev.getD b none))
    ((vtPre.drop (vtFwPos.getD b 0)).take
      (vtFwSelT (vtFwV.getD b 0) b (vtFwPrev.getD b none)).length) = true := by
        simp only [vtPre_drop]; decide +kernel

theorem vtFw_reads : ∀ b < 3, Atom.load (.n (vtFwV.getD b 0)) (.n 12) b ∉ vtSL ∧
    Atom.load (.n (vtFwV.getD b 0 + 7)) (.n 185) b ∉ vtSL ∧
    Atom.load (.n (vtFwV.getD b 0 + 18)) (.n 185) b ∉ vtSL := by decide +kernel

theorem vtPushSel_reads : ∀ i < 51,
    Atom.load (.n (vtPushSel.getD i default).2.2.1) (.n 12) (vtPushSel.getD i default).1 ∉ vtSL ∧
    Atom.load (.n ((vtPushSel.getD i default).2.2.1 + 7)) (.n 185) (vtPushSel.getD i default).1 ∉ vtSL ∧
    Atom.load (.n ((vtPushSel.getD i default).2.2.1 + 8)) (.n 10)
      ((vtPushSel.getD i default).2.2.2.1 + 1) ∉ vtSL ∧
    Atom.load (.n (vtSelE (vtPushSel.getD i default).2.2.1 (vtPushSel.getD i default).2.2.2.1 + 2))
      (.n 185) (vtPushSel.getD i default).1 ∉ vtSL := by decide +kernel

theorem vtCountSel_reads : ∀ i < 45,
    Atom.load (.n (vtCountSel.getD i default).2.2.1) (.n 12) (vtCountSel.getD i default).1 ∉ vtSL ∧
    Atom.load (.n ((vtCountSel.getD i default).2.2.1 + 7)) (.n 185) (vtCountSel.getD i default).1 ∉ vtSL ∧
    Atom.load (.n ((vtCountSel.getD i default).2.2.1 + 8)) (.n 10)
      ((vtCountSel.getD i default).2.2.2.1 + 1) ∉ vtSL ∧
    Atom.load (.n (vtSelE (vtCountSel.getD i default).2.2.1 (vtCountSel.getD i default).2.2.2.1 + 2))
      (.n 185) (vtCountSel.getD i default).1 ∉ vtSL := by decide +kernel

theorem vtSel_v : (∀ i < 51, 2770 < (vtPushSel.getD i default).2.2.1) ∧
    (∀ i < 45, 2770 < (vtCountSel.getD i default).2.2.1) := by decide

section
variable {rd : Reader} {wo : ℕ → E} {args : List E}

/-- **All the block selectors, complete.** -/
theorem vtc_sels (hl : args.length = 22) {point : List E}
    (hmu : vtσ rd wo args (.n 9) = gen ^ point.length) (hml : point.length < 33) {lm : ℕ}
    (hlmμ : lm ≤ point.length) (h19 : 19 ≤ point.length) {τ : ℕ → ℕ}
    (hτ : ∀ t < 6, τ t < 29)
    (hdim : ∀ t < 6, LoadHolds rd (vtσ rd wo args (.n 10)) (t + 1) (gen ^ τ t))
    (hbk : TbReadsAt rd (vtσ rd wo args (.n 12))
      (blockKappaWords (gen ^ lm) ((vtTauList τ).map (gen ^ ·))))
    (hz1 : TbReadsAt rd (vtσ rd wo args (.n 2767)) (point.map (1 + ·)))
    (hidxc : TbReadsAt rd (vtσ rd wo args (.n 2732)) vtIdxcList)
    (hsh : ∀ t < 6, ∃ d, vtσ rd wo args (.n (vtShLen t)) = gen ^ d ∧ point.length = d + τ t ∧
      RunTables rd (vtσ rd wo args (.n 2769) * gen ^ (288 * t))
        (vtσ rd wo args (.n 2770) * gen ^ (144 * t)) d
        (point.drop (τ t)) ((point.map (1 + ·)).drop (τ t)) ((gSquaresList.drop (τ t)).take d))
    (hoffP : ∀ b < 54, LoadHolds rd (vtσ rd wo args (.n 185)) b
      (gen ^ (stackOffsets (vtSizesP lm τ)).1.getD b 0))
    (hoffC : ∀ c < 45, LoadHolds rd (vtσ rd wo args (.n 185)) (108 + c)
      (gen ^ (stackOffsets (vtSizesC τ)).1.getD c 0))
    (halP : ∀ b < 54, 2 ^ (vtSizesP lm τ).getD b 0 ∣ (stackOffsets (vtSizesP lm τ)).1.getD b 0 ∧
      (stackOffsets (vtSizesP lm τ)).1.getD b 0 < 2 ^ point.length)
    (halC : ∀ c < 45, 2 ^ (vtSizesC τ).getD c 0 ∣ (stackOffsets (vtSizesC τ)).1.getD c 0 ∧
      (stackOffsets (vtSizesC τ)).1.getD c 0 < 2 ^ point.length)
    (hbitsF : ∀ b < 3, TbReadsAt rd (vtσ rd wo args (.n (vtFwV.getD b 0 + 6)))
      (offBits ((stackOffsets (vtSizesP lm τ)).1.getD b 0)))
    (hbitsP : ∀ i < 51, TbReadsAt rd (vtσ rd wo args (.n ((vtPushSel.getD i default).2.2.1 + 6)))
      (offBits ((stackOffsets (vtSizesP lm τ)).1.getD (3 + i) 0)))
    (hbitsC : ∀ i < 45, TbReadsAt rd (vtσ rd wo args (.n ((vtCountSel.getD i default).2.2.1 + 6)))
      (offBits ((stackOffsets (vtSizesC τ)).1.getD i 0)))
    (hwF : ∀ b < 3, wo (vtFwV.getD b 0 + 16) = blockSel (vtSizesP lm τ) point.length b point ∧
      wo (vtFwV.getD b 0 + 17) = gen ^ (stackOffsets (vtSizesP lm τ)).1.getD b 0)
    (hwP : ∀ i < 51, wo (vtSelE (vtPushSel.getD i default).2.2.1 (vtPushSel.getD i default).2.2.2.1) =
        blockSel (vtSizesP lm τ) point.length (3 + i) point ∧
      wo (vtSelE (vtPushSel.getD i default).2.2.1 (vtPushSel.getD i default).2.2.2.1 + 1) =
        gen ^ (stackOffsets (vtSizesP lm τ)).1.getD (3 + i) 0)
    (hwC : ∀ i < 45, wo (vtSelE (vtCountSel.getD i default).2.2.1
        (vtCountSel.getD i default).2.2.2.1) = blockSel (vtSizesC τ) point.length i point ∧
      wo (vtSelE (vtCountSel.getD i default).2.2.1 (vtCountSel.getD i default).2.2.2.1 + 1) =
        gen ^ (stackOffsets (vtSizesC τ)).1.getD i 0)
    (hlow : ∀ i < 34, (rd (Parameters.gpow i)).isSome) :
    ((∀ b < 3, ∀ s ∈ vtFwSelT (vtFwV.getD b 0) b (vtFwPrev.getD b none),
        VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s) ∧
      (∀ i < 51, ∀ s ∈ vtSelT (vtPushSel.getD i default).2.2.1 (vtPushSel.getD i default).1
          (vtPushSel.getD i default).2.2.2.1 (vtPushSel.getD i default).2.2.2.2,
        VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s) ∧
      (∀ i < 45, ∀ s ∈ vtSelT (vtCountSel.getD i default).2.2.1 (vtCountSel.getD i default).1
          (vtCountSel.getD i default).2.2.2.1 (vtCountSel.getD i default).2.2.2.2,
        VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s)) ∧
      vtσ rd wo args (.n 2870) = blockSel (vtSizesP lm τ) point.length 0 point ∧
      vtσ rd wo args (.n 2900) = blockSel (vtSizesP lm τ) point.length 1 point ∧
      vtσ rd wo args (.n 2975) = blockSel (vtSizesP lm τ) point.length 2 point ∧
      vtσ rd wo args (.n 2873) = vtσ rd wo args (.n 2870) ∧
      vtσ rd wo args (.n 2904) = vtσ rd wo args (.n 2900) ∧
      vtσ rd wo args (.n 2979) = vtσ rd wo args (.n 2975) ∧
      (∀ i < 51, vtσ rd wo args (.n (vtPushPadData.getD i default).2.2.1) =
        blockSel (vtSizesP lm τ) point.length (3 + i) point) ∧
      vtσ rd wo args (.n 3984) = vtσ rd wo args (.n 2870) + vtσ rd wo args (.n 2900) +
        vtσ rd wo args (.n 2975) +
        (vtPushPadData.map fun x ↦ vtσ rd wo args (.n x.2.2.1)).sum ∧
      (∀ i < 45, vtσ rd wo args (.n (vtCountPadData.getD i default).2.2.1) =
        blockSel (vtSizesC τ) point.length i point) ∧
      vtσ rd wo args (.n 5761) = (vtCountPadData.map fun x ↦ vtσ rd wo args (.n x.2.2.1)).sum := by
  -- the block sizes
  have hbkc : ∀ b < 153, LoadHolds rd (vtσ rd wo args (.n 12)) b (gen ^ vtKap lm τ b) :=
    fun b hb ↦ by
      have hl' : b < (blockKappaWords (gen ^ lm) ((vtTauList τ).map (gen ^ ·))).length := by
        simp [blockKappaWords]; exact hb
      have := hbk b hl'
      rwa [← List.getD_eq_getElem _ 0 hl', vt_kappa_word lm τ hb] at this
  have hkP : ∀ b < 54, LoadHolds rd (vtσ rd wo args (.n 12)) b
      (gen ^ (vtSizesP lm τ).getD b 0) :=
    fun b hb ↦ by rw [← vt_kapP lm τ hb]; exact hbkc b (by omega)
  -- the framework blocks
  have hfw : ∀ b < 3, (∀ s ∈ vtFwSelT (vtFwV.getD b 0) b (vtFwPrev.getD b none),
        VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s) ∧
      vtσ rd wo args (.n (vtFwV.getD b 0 + 16)) = blockSel (vtSizesP lm τ) point.length b point ∧
      vtσ rd wo args (.n (if (vtFwPrev.getD b none).isNone then vtFwV.getD b 0 + 19
        else vtFwV.getD b 0 + 20)) = vtσ rd wo args (.n (vtFwV.getD b 0 + 16)) ∧
      vtσ rd wo args (.n (if (vtFwPrev.getD b none).isNone then vtFwV.getD b 0 + 16
        else vtFwV.getD b 0 + 19)) =
        (match vtFwPrev.getD b none with | none => 0 | some p => vtσ rd wo args (.n p)) +
          vtσ rd wo args (.n (vtFwV.getD b 0 + 16)) := by
    intro b hb
    have hκμ : (vtSizesP lm τ).getD b 0 ≤ point.length := by
      interval_cases b <;> simp [vtSizesP] <;> omega
    obtain ⟨a1, a2⟩ := halP b (by omega)
    obtain ⟨w1, w2⟩ := hwF b hb
    rw [← vt_eqAbove_blockSel] at w1 ⊢
    exact vtc_fwblock hl (vtFw_check b hb) (by interval_cases b <;> decide) (vtFw_reads b hb) hmu
      hml hz1 hidxc (hkP b (by omega)) hκμ (hoffP b (by omega)) a1 a2 (hbitsF b hb) w1 w2 hlow
  obtain ⟨f0, s0, c0, -⟩ := hfw 0 (by norm_num)
  obtain ⟨f1, s1, c1, u1⟩ := hfw 1 (by norm_num)
  obtain ⟨f2, s2, c2, u2⟩ := hfw 2 (by norm_num)
  simp only [vtFwV, vtFwPrev, List.getD_cons_zero, List.getD_cons_succ, Option.isNone_none,
    Option.isNone_some, ↓reduceIte, Bool.false_eq_true, Nat.reduceAdd] at s0 c0 s1 c1 u1 s2 c2 u2
  -- a table block's selector
  have hblk : ∀ {sizes : List ℕ} {b c v t : ℕ} {prev : Option ℕ} {pos : ℕ},
      tbStmtsEqb (vtSelT v b t prev) ((vtPre.drop pos).take (vtSelT v b t prev).length) = true →
      2770 < v → t < 6 → sizes.getD c 0 = τ t →
      (Atom.load (.n v) (.n 12) b ∉ vtSL ∧ Atom.load (.n (v + 7)) (.n 185) b ∉ vtSL ∧
        Atom.load (.n (v + 8)) (.n 10) (t + 1) ∉ vtSL ∧
        Atom.load (.n (vtSelE v t + 2)) (.n 185) b ∉ vtSL) →
      LoadHolds rd (vtσ rd wo args (.n 12)) b (gen ^ τ t) →
      LoadHolds rd (vtσ rd wo args (.n 185)) b (gen ^ (stackOffsets sizes).1.getD c 0) →
      2 ^ τ t ∣ (stackOffsets sizes).1.getD c 0 →
      (stackOffsets sizes).1.getD c 0 < 2 ^ point.length →
      TbReadsAt rd (vtσ rd wo args (.n (v + 6))) (offBits ((stackOffsets sizes).1.getD c 0)) →
      wo (vtSelE v t) = blockSel sizes point.length c point →
      wo (vtSelE v t + 1) = gen ^ (stackOffsets sizes).1.getD c 0 →
      (∀ s ∈ vtSelT v b t prev, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s) ∧
        vtσ rd wo args (.n (vtSelE v t)) = blockSel sizes point.length c point ∧
        vtσ rd wo args (.n (vtSelCopy v t prev)) = vtσ rd wo args (.n (vtSelE v t)) ∧
        vtσ rd wo args (.n (vtSelSum v t prev)) =
          (match prev with | none => 0 | some p => vtσ rd wo args (.n p)) +
            vtσ rd wo args (.n (vtSelE v t)) := by
    intro sizes b c v t prev pos hc hv ht hsz hS hk hoff hal hob hbits hw0 hw1
    obtain ⟨d, hdv, hpl, hrun⟩ := hsh t ht
    rw [← vt_eqAbove_blockSel, hsz] at hw0
    obtain ⟨e0, e1, e2, e3⟩ := vtc_selblock hl hc ht hv hS hpl hml (hτ t ht) hdv hrun hk (hdim t ht)
      hoff hal hob hbits hw0 hw1 hlow
    rw [← hsz, vt_eqAbove_blockSel] at e1
    exact ⟨e0, e1, e2, e3⟩
  -- the push table blocks
  have hP : ∀ i < 51,
      (∀ s ∈ vtSelT (vtPushSel.getD i default).2.2.1 (vtPushSel.getD i default).1
          (vtPushSel.getD i default).2.2.2.1 (vtPushSel.getD i default).2.2.2.2,
        VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s) ∧
      vtσ rd wo args (.n (vtSelE (vtPushSel.getD i default).2.2.1
        (vtPushSel.getD i default).2.2.2.1)) = blockSel (vtSizesP lm τ) point.length (3 + i) point ∧
      vtσ rd wo args (.n (vtPushPadData.getD i default).2.2.1) =
        vtσ rd wo args (.n (vtSelE (vtPushSel.getD i default).2.2.1
          (vtPushSel.getD i default).2.2.2.1)) ∧
      vtσ rd wo args (.n (vtSelSum (vtPushSel.getD i default).2.2.1
        (vtPushSel.getD i default).2.2.2.1 (vtPushSel.getD i default).2.2.2.2)) =
        vtσ rd wo args (.n (if i = 0 then 2978 else vtSelSum (vtPushSel.getD (i - 1) default).2.2.1
          (vtPushSel.getD (i - 1) default).2.2.2.1 (vtPushSel.getD (i - 1) default).2.2.2.2)) +
        vtσ rd wo args (.n (vtSelE (vtPushSel.getD i default).2.2.1
          (vtPushSel.getD i default).2.2.2.1)) := by
    intro i hi
    obtain ⟨d1, d2, d3, d4, d5⟩ := vt_pushSel_data i hi
    have hsz : (vtSizesP lm τ).getD (vtPushSel.getD i default).1 0 =
        τ (vtPushSel.getD i default).2.2.2.1 := by
      rw [d1, d2, ← vt_kapP lm τ (by omega)]
      obtain ⟨e1, e2, e3⟩ := vt_srcP i hi
      rw [vtKap, e1, e2, vt_tau_getD lm τ e3, Nat.add_zero]
    have hk : LoadHolds rd (vtσ rd wo args (.n 12)) (vtPushSel.getD i default).1
        (gen ^ τ (vtPushSel.getD i default).2.2.2.1) := by
      rw [← hsz]; exact hkP _ (by rw [d1]; omega)
    obtain ⟨a1, a2⟩ := halP (3 + i) (by omega)
    have hsz' : (vtSizesP lm τ).getD (3 + i) 0 = τ (vtPushSel.getD i default).2.2.2.1 := by
      rw [← d1]; exact hsz
    rw [hsz'] at a1
    obtain ⟨w0, w1⟩ := hwP i hi
    obtain ⟨e0, e1, e2, e3⟩ := hblk (c := 3 + i)
      (vtPushSel_check i (by rw [show vtPushSel.length = 51 from rfl]; exact hi))
      (vtSel_v.1 i hi) (by rw [d2]; exact d3) hsz'
      (vtPushSel_reads i hi) hk (by rw [d1]; exact hoffP _ (by omega))
      a1 a2 (hbitsP i hi) w0 w1
    rw [d4] at e2
    refine ⟨e0, e1, e2, ?_⟩
    rw [e3, d5]
  -- the count blocks
  have hC : ∀ i < 45,
      (∀ s ∈ vtSelT (vtCountSel.getD i default).2.2.1 (vtCountSel.getD i default).1
          (vtCountSel.getD i default).2.2.2.1 (vtCountSel.getD i default).2.2.2.2,
        VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s) ∧
      vtσ rd wo args (.n (vtSelE (vtCountSel.getD i default).2.2.1
        (vtCountSel.getD i default).2.2.2.1)) = blockSel (vtSizesC τ) point.length i point ∧
      vtσ rd wo args (.n (vtCountPadData.getD i default).2.2.1) =
        vtσ rd wo args (.n (vtSelE (vtCountSel.getD i default).2.2.1
          (vtCountSel.getD i default).2.2.2.1)) ∧
      vtσ rd wo args (.n (vtSelSum (vtCountSel.getD i default).2.2.1
        (vtCountSel.getD i default).2.2.2.1 (vtCountSel.getD i default).2.2.2.2)) =
        (if i = 0 then 0 else vtσ rd wo args (.n (vtSelSum (vtCountSel.getD (i - 1) default).2.2.1
          (vtCountSel.getD (i - 1) default).2.2.2.1 (vtCountSel.getD (i - 1) default).2.2.2.2))) +
        vtσ rd wo args (.n (vtSelE (vtCountSel.getD i default).2.2.1
          (vtCountSel.getD i default).2.2.2.1)) := by
    intro i hi
    obtain ⟨d1, d2, d3, d4, d5⟩ := vt_countSel_data i hi
    have hsz : (vtSizesC τ).getD i 0 = τ (vtCountSel.getD i default).2.2.2.1 := by
      rw [d2, ← vt_kapC lm τ hi]
      obtain ⟨e1, e2, e3⟩ := vt_srcC i hi
      rw [vtKap, e1, e2, vt_tau_getD lm τ e3, Nat.add_zero]
    have hk : LoadHolds rd (vtσ rd wo args (.n 12)) (vtCountSel.getD i default).1
        (gen ^ τ (vtCountSel.getD i default).2.2.2.1) := by
      rw [← hsz, d1, ← vt_kapC lm τ hi]; exact hbkc _ (by omega)
    obtain ⟨a1, a2⟩ := halC i hi
    rw [hsz] at a1
    obtain ⟨w0, w1⟩ := hwC i hi
    obtain ⟨e0, e1, e2, e3⟩ := hblk (c := i)
      (vtCountSel_check i (by rw [show vtCountSel.length = 45 from rfl]; exact hi))
      (vtSel_v.2 i hi) (by rw [d2]; exact d3) hsz (vtCountSel_reads i hi) hk
      (by rw [d1]; exact hoffC i hi) a1 a2 (hbitsC i hi) w0 w1
    rw [d4] at e2
    refine ⟨e0, e1, e2, ?_⟩
    rw [e3, d5]
    split_ifs <;> rfl
  -- the sums
  have hsumP := vt_running_sum (fun i ↦ vtσ rd wo args (.n (vtSelSum (vtPushSel.getD i default).2.2.1
      (vtPushSel.getD i default).2.2.2.1 (vtPushSel.getD i default).2.2.2.2)))
    (fun i ↦ vtσ rd wo args (.n (if i = 0 then 2978 else vtSelSum
      (vtPushSel.getD (i - 1) default).2.2.1
      (vtPushSel.getD (i - 1) default).2.2.2.1 (vtPushSel.getD (i - 1) default).2.2.2.2)))
    (fun i ↦ vtσ rd wo args (.n (vtPushPadData.getD i default).2.2.1)) (vtσ rd wo args (.n 2978)) 51
    (fun i hi ↦ by rw [(hP i hi).2.2.2, (hP i hi).2.2.1]) (by simp)
    (fun i h0 _ ↦ by simp [show i ≠ 0 by omega]) 50 (by norm_num)
  have hsumC := vt_running_sum (fun i ↦ vtσ rd wo args (.n (vtSelSum
      (vtCountSel.getD i default).2.2.1
      (vtCountSel.getD i default).2.2.2.1 (vtCountSel.getD i default).2.2.2.2)))
    (fun i ↦ if i = 0 then 0 else vtσ rd wo args (.n (vtSelSum
      (vtCountSel.getD (i - 1) default).2.2.1
      (vtCountSel.getD (i - 1) default).2.2.2.1 (vtCountSel.getD (i - 1) default).2.2.2.2)))
    (fun i ↦ vtσ rd wo args (.n (vtCountPadData.getD i default).2.2.1)) 0 45
    (fun i hi ↦ by rw [(hC i hi).2.2.2, (hC i hi).2.2.1]) (by simp)
    (fun i h0 _ ↦ by simp [show i ≠ 0 by omega]) 44 (by norm_num)
  simp only [vt_pushSel_last] at hsumP
  simp only [vt_countSel_last] at hsumC
  refine ⟨⟨fun b hb ↦ (hfw b hb).1, fun i hi ↦ (hP i hi).1, fun i hi ↦ (hC i hi).1⟩,
    s0, s1, s2, c0, c1, c2, fun i hi ↦ (hP i hi).2.2.1.trans (hP i hi).2.1, ?_,
    fun i hi ↦ (hC i hi).2.2.1.trans (hC i hi).2.1, ?_⟩
  · rw [hsumP, u2, u1, vt_sum_map_range, vtPushPadData_length]
  · rw [hsumC, vt_sum_map_range, vtCountPadData_length, zero_add]

end

end
end LeanVM.Guest.B1.Tables
