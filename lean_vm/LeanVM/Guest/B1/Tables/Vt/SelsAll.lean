/-
  LeanVM.Guest.B1.Tables.Vt.SelsAll

  `verify_tables`' block selectors, all of them: the push side's framework and table blocks and
  the count side's blocks, each the specification's `blockSel` of its side's log-sizes, and the
  sides' selector sums.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Sels
public import LeanVM.Guest.B1.Tables.Vt.SelFw

/-!
# All the block selectors (G:1988-2075, 2116-2126, 2311-2385)

`vt_sels`: when `block_kappa` holds `blockKappaWords` of `log_mem` and the tables' heights `τ`,
the point fits the memory and bytecode blocks, the push side's three framework selectors and
`51` table block selectors are `blockSel (vtSizesP log_mem τ)`, the count side's `45` are
`blockSel (vtSizesC τ)`, and `selector_sum` is each side's sum.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (blockSel)
open Finset

@[expose] public section

/-- A list's sum through its indices. -/
theorem vt_sum_map_range {α : Type} [Inhabited α] (g : α → E) :
    ∀ l : List α, (l.map g).sum = ∑ i ∈ range l.length, g (l.getD i default)
  | [] => by simp
  | a :: l => by
    rw [List.map_cons, List.sum_cons, vt_sum_map_range g l, List.length_cons,
      sum_range_succ']
    simp [add_comm]

theorem vt_kap_lt (lm : ℕ) (τ : ℕ → ℕ) (hlm : lm ≤ 32) (hτ : ∀ t < 6, τ t < 29) {b : ℕ}
    (hb : b < 153) : vtKap lm τ b < 34 := by
  have hadj : ∀ b < 153, blockKappaAdj b = 0 ∨
      (blockKappaAdj b = 19 ∧ blockKappaSrc.getD b 0 = 0) := by decide
  have hle : ∀ s < 8, ([0, lm] ++ vtTauList τ).getD s 0 ≤ 32 := by
    intro s hs
    match s, hs with
    | 0, _ => simp
    | 1, _ => simpa using hlm
    | s + 2, hs => rw [vt_tau_getD lm τ (by omega)]; have := hτ s (by omega); omega
  rcases hadj b hb with h0 | ⟨h19, hs0⟩
  · rw [vtKap, h0]; have := hle _ (vt_src_lt b hb); omega
  · rw [vtKap, h19, hs0]; simp

theorem vtSizesP_length (lm : ℕ) (τ : ℕ → ℕ) : (vtSizesP lm τ).length = 54 := by
  simp [vtSizesP, vtPushPadData_length]

theorem vtSizesC_length (τ : ℕ → ℕ) : (vtSizesC τ).length = 45 := by
  simp [vtSizesC, vtCountPadData_length]

theorem vtSizesP_le (lm : ℕ) (τ : ℕ → ℕ) (hlm : lm ≤ 32) (hτ : ∀ t < 6, τ t < 29) (b : ℕ) :
    (vtSizesP lm τ).getD b 0 ≤ 34 := by
  rcases Nat.lt_or_ge b 54 with hb | hb
  · rw [← vt_kapP lm τ hb]; have := vt_kap_lt lm τ hlm hτ (b := b) (by omega); omega
  · rw [List.getD_eq_default _ _ (by rw [vtSizesP_length]; exact hb)]; omega

theorem vtSizesC_le (lm : ℕ) (τ : ℕ → ℕ) (hlm : lm ≤ 32) (hτ : ∀ t < 6, τ t < 29) (b : ℕ) :
    (vtSizesC τ).getD b 0 ≤ 34 := by
  rcases Nat.lt_or_ge b 45 with hb | hb
  · rw [← vt_kapC lm τ hb]; have := vt_kap_lt lm τ hlm hτ (b := 108 + b) (by omega); omega
  · rw [List.getD_eq_default _ _ (by rw [vtSizesC_length]; exact hb)]; omega

/-- The push table blocks' data: block `3 + i`, its table, its copy, the running sum's chain. -/
theorem vt_pushSel_data : ∀ i < 51,
    (vtPushSel.getD i default).1 = 3 + i ∧
    (vtPushSel.getD i default).2.2.2.1 = (vtPushPadData.getD i default).2.1 ∧
    (vtPushPadData.getD i default).2.1 < 6 ∧
    vtSelCopy (vtPushSel.getD i default).2.2.1 (vtPushSel.getD i default).2.2.2.1
      (vtPushSel.getD i default).2.2.2.2 = (vtPushPadData.getD i default).2.2.1 ∧
    (vtPushSel.getD i default).2.2.2.2 = some (if i = 0 then 2978 else
      vtSelSum (vtPushSel.getD (i - 1) default).2.2.1 (vtPushSel.getD (i - 1) default).2.2.2.1
        (vtPushSel.getD (i - 1) default).2.2.2.2) := by decide

/-- The count blocks' data. -/
theorem vt_countSel_data : ∀ i < 45,
    (vtCountSel.getD i default).1 = 108 + i ∧
    (vtCountSel.getD i default).2.2.2.1 = (vtCountPadData.getD i default).2.1 ∧
    (vtCountPadData.getD i default).2.1 < 6 ∧
    vtSelCopy (vtCountSel.getD i default).2.2.1 (vtCountSel.getD i default).2.2.2.1
      (vtCountSel.getD i default).2.2.2.2 = (vtCountPadData.getD i default).2.2.1 ∧
    (vtCountSel.getD i default).2.2.2.2 = (if i = 0 then none else
      some (vtSelSum (vtCountSel.getD (i - 1) default).2.2.1
        (vtCountSel.getD (i - 1) default).2.2.2.1 (vtCountSel.getD (i - 1) default).2.2.2.2)) := by
  decide

theorem vt_pushSel_last : vtSelSum (vtPushSel.getD 50 default).2.2.1
    (vtPushSel.getD 50 default).2.2.2.1 (vtPushSel.getD 50 default).2.2.2.2 = 3984 := by decide

theorem vt_countSel_last : vtSelSum (vtCountSel.getD 44 default).2.2.1
    (vtCountSel.getD 44 default).2.2.2.1 (vtCountSel.getD 44 default).2.2.2.2 = 5761 := by decide

theorem vt_countSel_first : vtSelSum (vtCountSel.getD 0 default).2.2.1
    (vtCountSel.getD 0 default).2.2.2.1 (vtCountSel.getD 0 default).2.2.2.2 =
    vtSelE (vtCountSel.getD 0 default).2.2.1 (vtCountSel.getD 0 default).2.2.2.1 := by decide

/-- A running sum: each step adds its term to the previous step's sum. -/
theorem vt_running_sum (S : ℕ → E) (prev : ℕ → E) (x : ℕ → E) (s0 : E) (n : ℕ)
    (hstep : ∀ i < n, S i = prev i + x i) (h0 : prev 0 = s0)
    (hchain : ∀ i, 0 < i → i < n → prev i = S (i - 1)) :
    ∀ k < n, S k = s0 + ∑ i ∈ range (k + 1), x i := by
  intro k hk
  induction k with
  | zero => rw [hstep 0 hk, h0]; simp
  | succ k ih =>
    rw [hstep (k + 1) hk, hchain (k + 1) (by omega) hk, Nat.add_sub_cancel, ih (by omega),
      sum_range_succ _ (k + 1)]
    ring

section
variable {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemImage μ)
include hμ

set_option maxHeartbeats 1000000 in
/-- **All the block selectors.** -/
theorem vt_sels {σ : Val} (h : VtH Lm.read σ) {point : List E}
    (hz : TbReadsAt Lm.read (σ (.n 8)) point) (hmu : σ (.n 9) = gen ^ point.length)
    (hml : point.length < 33) (hsq : TbReadsAt Lm.read (σ (.n 13)) gSquaresList) {lm : ℕ}
    (hlm : lm ≤ 32) {τ : ℕ → ℕ} (hτ : ∀ t < 6, τ t < 29)
    (hdim : ∀ t < 6, LoadHolds Lm.read (σ (.n 10)) (t + 1) (gen ^ τ t))
    (hbk : TbReadsAt Lm.read (σ (.n 12)) (blockKappaWords (gen ^ lm) ((vtTauList τ).map (gen ^ ·)))) :
    lm ≤ point.length ∧ 19 ≤ point.length ∧
      LoadHolds Lm.read (σ (.n 12)) 1 (gen ^ lm) ∧ LoadHolds Lm.read (σ (.n 12)) 2 (gen ^ 19) ∧
      σ (.n 2870) = blockSel (vtSizesP lm τ) point.length 0 point ∧
      σ (.n 2900) = blockSel (vtSizesP lm τ) point.length 1 point ∧
      σ (.n 2975) = blockSel (vtSizesP lm τ) point.length 2 point ∧
      σ (.n 2873) = σ (.n 2870) ∧ σ (.n 2904) = σ (.n 2900) ∧ σ (.n 2979) = σ (.n 2975) ∧
      (∀ i < 51, σ (.n (vtPushPadData.getD i default).2.2.1) =
        blockSel (vtSizesP lm τ) point.length (3 + i) point) ∧
      σ (.n 3984) = σ (.n 2870) + σ (.n 2900) + σ (.n 2975) +
        (vtPushPadData.map fun x ↦ σ (.n x.2.2.1)).sum ∧
      (∀ i < 45, σ (.n (vtCountPadData.getD i default).2.2.1) =
        blockSel (vtSizesC τ) point.length i point) ∧
      σ (.n 5761) = (vtCountPadData.map fun x ↦ σ (.n x.2.2.1)).sum := by
  -- the block sizes
  have hbkc : ∀ b < 153, LoadHolds Lm.read (σ (.n 12)) b (gen ^ vtKap lm τ b) := fun b hb => by
    have hl : b < (blockKappaWords (gen ^ lm) ((vtTauList τ).map (gen ^ ·))).length := by
      simp [blockKappaWords]; exact hb
    have := hbk b hl
    rwa [← List.getD_eq_getElem _ 0 hl, vt_kappa_word lm τ hb] at this
  have hsq' : ∀ j < 34, LoadHolds Lm.read (σ (.n 13)) j (gen ^ 2 ^ j) := fun j hj => by
    have := hsq j (by simp [gSquaresList]; exact hj)
    simpa [gSquaresList] using this
  obtain ⟨⟨κP, hκPl, hκP12, hκP185, hκPlt⟩, ⟨κC, hκCl, hκC12, hκC185, hκClt⟩⟩ :=
    vt_sort hμ Lm h (fun b hb => ⟨_, vt_kap_lt lm τ hlm hτ hb, hbkc b hb⟩) hsq'
  have eP : κP = vtSizesP lm τ := by
    apply List.ext_getElem (by rw [hκPl, vtSizesP_length])
    intro c h1 h2
    have hc : c < 54 := by omega
    have e1 := tb_loadHolds_unique (hκP12 c hc) (by rw [Nat.zero_add]; exact hbkc c (by omega))
    have e2 := gen_pow_inj (by have := hκPlt c hc; omega)
      (by have := vt_kap_lt lm τ hlm hτ (b := c) (by omega); omega) e1
    rw [← List.getD_eq_getElem κP 0 h1, ← List.getD_eq_getElem _ 0 h2, e2, vt_kapP lm τ hc]
  have eC : κC = vtSizesC τ := by
    apply List.ext_getElem (by rw [hκCl, vtSizesC_length])
    intro c h1 h2
    have hc : c < 45 := by omega
    have e1 := tb_loadHolds_unique (hκC12 c hc) (hbkc (108 + c) (by omega))
    have e2 := gen_pow_inj (by have := hκClt c hc; omega)
      (by have := vt_kap_lt lm τ hlm hτ (b := 108 + c) (by omega); omega) e1
    rw [← List.getD_eq_getElem κC 0 h1, ← List.getD_eq_getElem _ 0 h2, e2, vt_kapC lm τ hc]
  subst eP eC
  have hobP : ∀ b, (stackOffsets (vtSizesP lm τ)).1.getD b 0 < 2 ^ 62 :=
    vt_stackOffsets_lt _ (by rw [vtSizesP_length]; norm_num) (vtSizesP_le lm τ hlm hτ)
  have hobC : ∀ b, (stackOffsets (vtSizesC τ)).1.getD b 0 < 2 ^ 62 :=
    vt_stackOffsets_lt _ (by rw [vtSizesC_length]; norm_num) (vtSizesC_le lm τ hlm hτ)
  have hz1 := vt_zeta1 h hz hmu (by omega)
  have hidxc := vt_idxc h
  have hkP : ∀ b < 54, LoadHolds Lm.read (σ (.n 12)) b (gen ^ (vtSizesP lm τ).getD b 0) :=
    fun b hb => by rw [← vt_kapP lm τ hb]; exact hbkc b (by omega)
  have hoffP : ∀ b < 54, LoadHolds Lm.read (σ (.n 185)) b
      (gen ^ (stackOffsets (vtSizesP lm τ)).1.getD b 0) :=
    fun b hb => by have := hκP185 b hb; rwa [Nat.zero_add] at this
  -- the framework blocks
  have f0 := vt_fwblock hμ Lm h vtFw0_check hmu hml hz1 hidxc (hkP 0 (by norm_num))
    (by have := vtSizesP_le lm τ hlm hτ 0; simp [vtSizesP]) (hoffP 0 (by norm_num)) (hobP 0)
  have f1 := vt_fwblock hμ Lm h vtFw1_check hmu hml hz1 hidxc (hkP 1 (by norm_num))
    (by simp [vtSizesP]; omega) (hoffP 1 (by norm_num)) (hobP 1)
  have f2 := vt_fwblock hμ Lm h vtFw2_check hmu hml hz1 hidxc (hkP 2 (by norm_num))
    (by simp [vtSizesP]) (hoffP 2 (by norm_num)) (hobP 2)
  simp only [Option.isNone_none, Option.isNone_some, ↓reduceIte, Bool.false_eq_true,
    Nat.reduceAdd, zero_add, vt_eqAbove_blockSel] at f0 f1 f2
  obtain ⟨-, s0, c0, -⟩ := f0
  obtain ⟨l1, s1, c1, u1⟩ := f1
  obtain ⟨l2, s2, c2, u2⟩ := f2
  simp only [vtSizesP, List.cons_append, List.getD_cons_succ, List.getD_cons_zero] at l1 l2
  -- the shared tables
  have hsh : ∀ t < 6, ∃ d, σ (.n (vtShLen t)) = gen ^ d ∧ point.length = d + τ t ∧
      RunTables Lm.read (σ (.n 2769) * gen ^ (288 * t)) (σ (.n 2770) * gen ^ (144 * t)) d
        (point.drop (τ t)) ((point.map (1 + ·)).drop (τ t)) ((gSquaresList.drop (τ t)).take d) :=
    fun t ht => vt_shared hμ Lm h hz hmu hml hz1 hsq ht (hτ t ht) (hdim t ht)
  -- a table block's selector
  have hblk : ∀ {sizes : List ℕ} {b c w t : ℕ} {prev : Option ℕ} {pos : ℕ},
      tbStmtsEqb (vtSelT w b t prev) ((vtPre.drop pos).take (vtSelT w b t prev).length) = true →
      t < 6 → sizes.getD c 0 = τ t → (∀ b, (stackOffsets sizes).1.getD b 0 < 2 ^ 62) →
      LoadHolds Lm.read (σ (.n 185)) b (gen ^ (stackOffsets sizes).1.getD c 0) →
      σ (.n (vtSelE w t)) = blockSel sizes point.length c point ∧
        σ (.n (vtSelCopy w t prev)) = σ (.n (vtSelE w t)) ∧
        σ (.n (vtSelSum w t prev)) = (match prev with | none => 0 | some p => σ (.n p)) +
          σ (.n (vtSelE w t)) := by
    intro sizes b c w t prev pos hc ht hsz hob hoff
    obtain ⟨d, hdv, hpl, hrun⟩ := hsh t ht
    obtain ⟨e1, e2, e3⟩ := vt_selblock h hc ht hpl (by have := hτ t ht; omega) hdv hrun hoff
      (hob c)
    rw [← hsz, vt_eqAbove_blockSel] at e1
    exact ⟨e1, e2, e3⟩
  -- the push table blocks
  have hP : ∀ i < 51,
      σ (.n (vtSelE (vtPushSel.getD i default).2.2.1 (vtPushSel.getD i default).2.2.2.1)) =
        blockSel (vtSizesP lm τ) point.length (3 + i) point ∧
      σ (.n (vtPushPadData.getD i default).2.2.1) = σ (.n (vtSelE (vtPushSel.getD i default).2.2.1
        (vtPushSel.getD i default).2.2.2.1)) ∧
      σ (.n (vtSelSum (vtPushSel.getD i default).2.2.1 (vtPushSel.getD i default).2.2.2.1
        (vtPushSel.getD i default).2.2.2.2)) =
        σ (.n (if i = 0 then 2978 else vtSelSum (vtPushSel.getD (i - 1) default).2.2.1
          (vtPushSel.getD (i - 1) default).2.2.2.1 (vtPushSel.getD (i - 1) default).2.2.2.2)) +
        σ (.n (vtSelE (vtPushSel.getD i default).2.2.1 (vtPushSel.getD i default).2.2.2.1)) := by
    intro i hi
    obtain ⟨d1, d2, d3, d4, d5⟩ := vt_pushSel_data i hi
    have hsz : (vtSizesP lm τ).getD (vtPushSel.getD i default).1 0 =
        τ (vtPushSel.getD i default).2.2.2.1 := by
      rw [d1, d2, ← vt_kapP lm τ (by omega)]
      obtain ⟨e1, e2, e3⟩ := vt_srcP i hi
      rw [vtKap, e1, e2, vt_tau_getD lm τ e3, Nat.add_zero]
    obtain ⟨e1, e2, e3⟩ := hblk (c := (vtPushSel.getD i default).1)
      (vtPushSel_check i (by rw [show vtPushSel.length = 51 from rfl]; exact hi))
      (by rw [d2]; exact d3) hsz hobP (hoffP _ (by rw [d1]; omega))
    rw [d1] at e1
    rw [d4] at e2
    refine ⟨e1, e2, ?_⟩
    rw [e3, d5]
  -- the count blocks
  have hoffC : ∀ c < 45, LoadHolds Lm.read (σ (.n 185)) (108 + c)
      (gen ^ (stackOffsets (vtSizesC τ)).1.getD c 0) := hκC185
  have hC : ∀ i < 45,
      σ (.n (vtSelE (vtCountSel.getD i default).2.2.1 (vtCountSel.getD i default).2.2.2.1)) =
        blockSel (vtSizesC τ) point.length i point ∧
      σ (.n (vtCountPadData.getD i default).2.2.1) = σ (.n (vtSelE (vtCountSel.getD i default).2.2.1
        (vtCountSel.getD i default).2.2.2.1)) ∧
      σ (.n (vtSelSum (vtCountSel.getD i default).2.2.1 (vtCountSel.getD i default).2.2.2.1
        (vtCountSel.getD i default).2.2.2.2)) =
        (if i = 0 then 0 else σ (.n (vtSelSum (vtCountSel.getD (i - 1) default).2.2.1
          (vtCountSel.getD (i - 1) default).2.2.2.1 (vtCountSel.getD (i - 1) default).2.2.2.2))) +
        σ (.n (vtSelE (vtCountSel.getD i default).2.2.1 (vtCountSel.getD i default).2.2.2.1)) := by
    intro i hi
    obtain ⟨d1, d2, d3, d4, d5⟩ := vt_countSel_data i hi
    have hsz : (vtSizesC τ).getD i 0 = τ (vtCountSel.getD i default).2.2.2.1 := by
      rw [d2, ← vt_kapC lm τ hi]
      obtain ⟨e1, e2, e3⟩ := vt_srcC i hi
      rw [vtKap, e1, e2, vt_tau_getD lm τ e3, Nat.add_zero]
    obtain ⟨e1, e2, e3⟩ := hblk (c := i)
      (vtCountSel_check i (by rw [show vtCountSel.length = 45 from rfl]; exact hi))
      (by rw [d2]; exact d3) hsz hobC (by rw [d1]; exact hoffC i hi)
    rw [d4] at e2
    refine ⟨e1, e2, ?_⟩
    rw [e3, d5]
    split_ifs <;> rfl
  -- the sums
  have hsumP := vt_running_sum (fun i ↦ σ (.n (vtSelSum (vtPushSel.getD i default).2.2.1
      (vtPushSel.getD i default).2.2.2.1 (vtPushSel.getD i default).2.2.2.2)))
    (fun i ↦ σ (.n (if i = 0 then 2978 else vtSelSum (vtPushSel.getD (i - 1) default).2.2.1
      (vtPushSel.getD (i - 1) default).2.2.2.1 (vtPushSel.getD (i - 1) default).2.2.2.2)))
    (fun i ↦ σ (.n (vtPushPadData.getD i default).2.2.1)) (σ (.n 2978)) 51
    (fun i hi ↦ by rw [(hP i hi).2.2, (hP i hi).2.1]) (by simp)
    (fun i h0 _ ↦ by simp [show i ≠ 0 by omega]) 50 (by norm_num)
  have hsumC := vt_running_sum (fun i ↦ σ (.n (vtSelSum (vtCountSel.getD i default).2.2.1
      (vtCountSel.getD i default).2.2.2.1 (vtCountSel.getD i default).2.2.2.2)))
    (fun i ↦ if i = 0 then 0 else σ (.n (vtSelSum (vtCountSel.getD (i - 1) default).2.2.1
      (vtCountSel.getD (i - 1) default).2.2.2.1 (vtCountSel.getD (i - 1) default).2.2.2.2)))
    (fun i ↦ σ (.n (vtCountPadData.getD i default).2.2.1)) 0 45
    (fun i hi ↦ by rw [(hC i hi).2.2, (hC i hi).2.1]) (by simp)
    (fun i h0 _ ↦ by simp [show i ≠ 0 by omega]) 44 (by norm_num)
  simp only [vt_pushSel_last] at hsumP
  simp only [vt_countSel_last] at hsumC
  refine ⟨l1, l2, by simpa [vtSizesP] using hkP 1 (by norm_num),
    by simpa [vtSizesP] using hkP 2 (by norm_num), s0, s1, s2, c0, c1, c2,
    fun i hi ↦ (hP i hi).2.1.trans (hP i hi).1, ?_, fun i hi ↦ (hC i hi).2.1.trans (hC i hi).1, ?_⟩
  · rw [hsumP, u2, u1, vt_sum_map_range, vtPushPadData_length]
  · rw [hsumC, vt_sum_map_range, vtCountPadData_length, zero_add]

end

end
end LeanVM.Guest.B1.Tables
