/-
  LeanVM.Guest.B1.Tables.VtC.SSide

  A side's certified block order on the honest valuation: `sort_order` holding `stack_offsets`'
  order of the side's log-sizes, every rank holds and writes its block's offset.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.SRank

/-!
# A side (G:1965-1991)

`tbStackOrder κs`: `stack_offsets`' order of the side's log-sizes (`stackLe`, the stable sort,
larger first): a permutation (`ord_perm`), adjacent ranks non-increasing in size, ties ascending
(`ord_adj`). `side_ok`: on a memory holding the side's order in `sort_order` (from `R0`), the
blocks' sides, their `g^κ`, their `stackOffsets` offsets in `block_off_g` (from `base`) and the
squares, every statement of the side's ranks holds.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-! ## The honest order -/

section
variable (κs : List ℕ)

theorem ord_perm : (tbStackOrder κs).Perm (List.range κs.length) := List.mergeSort_perm _ _

theorem ord_length : (tbStackOrder κs).length = κs.length := by
  rw [(ord_perm κs).length_eq, List.length_range]

theorem ord_nodup : (tbStackOrder κs).Nodup := (ord_perm κs).nodup_iff.mpr List.nodup_range

theorem ord_lt {r : ℕ} (hr : r < κs.length) : (tbStackOrder κs).getD r 0 < κs.length := by
  have hm : (tbStackOrder κs).getD r 0 ∈ tbStackOrder κs := by
    rw [List.getD_eq_getElem _ _ (by rw [ord_length]; exact hr)]; exact List.getElem_mem _
  exact List.mem_range.mp ((ord_perm κs).subset hm)

theorem ord_sorted : (tbStackOrder κs).Pairwise fun a b => stackLe (κs.getD · 0) a b = true := by
  rw [tbStackOrder]
  apply List.pairwise_mergeSort
  · intro a b c; simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega
  · intro a b; simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega

/-- Adjacent ranks: sizes do not increase, ties ascend. -/
theorem ord_adj {r : ℕ} (hr : r + 1 < κs.length) :
    κs.getD ((tbStackOrder κs).getD (r + 1) 0) 0 ≤ κs.getD ((tbStackOrder κs).getD r 0) 0 ∧
      (κs.getD ((tbStackOrder κs).getD (r + 1) 0) 0 = κs.getD ((tbStackOrder κs).getD r 0) 0 →
        (tbStackOrder κs).getD r 0 < (tbStackOrder κs).getD (r + 1) 0) := by
  have hlen := ord_length κs
  have hp := List.pairwise_iff_getElem.mp (ord_sorted κs) r (r + 1) (by omega) (by omega)
    (by omega)
  have hne : (tbStackOrder κs)[r]'(by omega) ≠ (tbStackOrder κs)[r + 1]'(by omega) := fun he =>
    absurd ((List.Nodup.getElem_inj_iff (ord_nodup κs)).mp he) (by omega)
  simp only [List.getD_eq_getElem _ _ (show r < (tbStackOrder κs).length by omega),
    List.getD_eq_getElem _ _ (show r + 1 < (tbStackOrder κs).length by omega)]
  simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hp
  omega

/-- The prefix sizes along the order. -/
def ordPre (r : ℕ) : ℕ := tbPrefixSize (κs.getD · 0) (tbStackOrder κs) r

theorem ordPre_zero : ordPre κs 0 = 0 := by simp [ordPre, tbPrefixSize]

theorem ordPre_succ {r : ℕ} (hr : r < κs.length) :
    ordPre κs (r + 1) = ordPre κs r + 2 ^ κs.getD ((tbStackOrder κs).getD r 0) 0 := by
  rw [ordPre, tb_prefixSize_succ _ _ _ (by rw [ord_length]; exact hr)]; rfl

theorem ordOff {r : ℕ} (hr : r < κs.length) :
    (stackOffsets κs).1.getD ((tbStackOrder κs).getD r 0) 0 = ordPre κs r :=
  tb_stackOffsets_fst κs r hr

end

/-! ## Branches -/

theorem vt_goodIte' {rd : Reader} {w : ℕ → E} {args : List E} (hl : args.length = 22) {c : V}
    {z nb : List Stmt} (hm : Stmt.ite c z nb ∈ vtPre) : GoodL rd w (vtσ rd w args) (z ++ nb) := by
  have h : ∀ t ∈ z ++ nb, GoodS rd vtSL w (vtσ rd w args) (fixNe t) :=
    fun t ht ↦ vt_good hl _ (vtEvL_mem_ite hm ht)
  clear hm
  generalize z ++ nb = l at h
  induction l with
  | nil => trivial
  | cons s ss ih =>
    exact ⟨h s List.mem_cons_self, ih fun t ht ↦ h t (List.mem_cons_of_mem _ ht)⟩

theorem vtRankAt_ite (v0 R0 s r : ℕ) : Stmt.ite (.n (vtRv v0 r + 15))
    (vtTieB (vtRv v0 r) (vtRv v0 (r - 1))) [] ∈ vtRankAt v0 R0 s r := by
  simp [vtRankAt, vtRankT, vtTieB]

/-! ## A side -/

theorem vtRv_ge (v0 r : ℕ) : v0 ≤ vtRv v0 r := by
  unfold vtRv; split_ifs
  · exact le_rfl
  · exact Nat.le_add_right_of_le (Nat.le_add_right _ _)

theorem vtRv_step (v0 r : ℕ) : vtRv v0 r + 14 ≤ vtRv v0 (r + 1) := by
  rcases r with _ | r
  · simp [vtRv]
  · simp [vtRv]; omega

theorem vtGout_lt (v0 r : ℕ) : vtGout v0 r < vtRv v0 (r + 1) := by
  rcases r with _ | r
  · simp [vtGout, vtRv]
  · simp [vtGout, vtRv]; omega

section
variable {rd : Reader} {w : ℕ → E} {args : List E}

/-- What a side's rank `r` gives. -/
def RankOut (σ : Val) (v0 : ℕ) (e κ : ℕ → ℕ) (pre : ℕ → ℕ) (r : ℕ) : Prop :=
  σ (.n (vtRv v0 r)) = gen ^ e r ∧ σ (.n (vtRv v0 r + 9)) = gen ^ κ (e r) ∧
    σ (.n (vtGout v0 r)) = gen ^ pre (r + 1)

set_option maxHeartbeats 1000000 in
/-- **A side's ranks hold**, rank by rank. -/
theorem side_ranks (hl : args.length = 22) (hlow : LowDefB 8 rd) {v0 p0 R0 s base : ℕ}
    (κs : List ℕ) (hv0 : 186 ≤ v0)
    (hchk0 : tbStmtsEqb (vtRank0T v0 R0 s) ((vtPre.drop p0).take (vtRank0T v0 R0 s).length) = true)
    (hchk : ∀ r < κs.length, 1 ≤ r → tbStmtsEqb (vtRankAt v0 R0 s r)
      ((vtPre.drop (vtRp p0 r)).take (vtRankAt v0 R0 s r).length) = true)
    (hS0 : ∀ a ∈ vtRankReads v0 R0 ++ [.load (.n (v0 + 13)) (.n (v0 + 12)) 0], a ∉ vtSL)
    (hS : ∀ r < κs.length, 1 ≤ r → ∀ a ∈ vtRankReads (vtRv v0 r) (R0 + r) ++
      [.load (.n (vtRv v0 r + 23)) (.n (vtRv v0 r + 22)) 0], a ∉ vtSL)
    (hκ : ∀ c < κs.length, κs.getD c 0 < 34) (hbase : base + κs.length ≤ 153)
    (hso : ∀ r < κs.length, LoadHolds rd (vtσ rd w args (.n 30)) (R0 + r)
      (gen ^ (base + (tbStackOrder κs).getD r 0)))
    (hside : ∀ c < κs.length, LoadHolds rd (vtσ rd w args (.n 31)) (base + c) (word s 0 0))
    (hkap : ∀ c < κs.length, LoadHolds rd (vtσ rd w args (.n 12)) (base + c)
      (gen ^ κs.getD c 0))
    (hoff : ∀ c < κs.length, LoadHolds rd (vtσ rd w args (.n 185)) (base + c)
      (gen ^ (stackOffsets κs).1.getD c 0))
    (hsq : ∀ j < 34, LoadHolds rd (vtσ rd w args (.n 13)) j (gen ^ 2 ^ j)) :
    ∀ r < κs.length,
      (if r = 0 then ∀ st ∈ vtRank0T v0 R0 s, VSH (coreProgram.Rel rd) rd (vtσ rd w args) st
        else ∀ st ∈ vtRankAt v0 R0 s r, VSH (coreProgram.Rel rd) rd (vtσ rd w args) st) ∧
      RankOut (vtσ rd w args) v0 (fun r => base + (tbStackOrder κs).getD r 0)
        (fun b => κs.getD (b - base) 0) (ordPre κs) r := by
  have hc : ∀ r < κs.length, (tbStackOrder κs).getD r 0 < κs.length := fun r hr => ord_lt κs hr
  intro r hr
  induction r with
  | zero =>
    have hg := vt_goodL (rd := rd) (w := w) hl p0 _ hchk0
    have hc0 := hc 0 hr
    obtain ⟨hh, ev, e9, e13⟩ := rank0_ok (C := coreProgram.Rel rd) hlow (e := base + (tbStackOrder κs).getD 0 0)
      (κ := κs.getD ((tbStackOrder κs).getD 0 0) 0) (by omega) hg hS0 (hso 0 hr)
      (by rw [tb_loadHolds_mul_gen_pow, Nat.add_zero]; exact hside _ hc0)
      (by rw [tb_loadHolds_mul_gen_pow, Nat.add_zero]; exact hkap _ hc0)
      (by
        have h0 := hoff _ hc0
        rw [ordOff κs hr, ordPre_zero, pow_zero] at h0
        rw [tb_loadHolds_mul_gen_pow, Nat.add_zero]; exact h0)
      (by rw [tb_loadHolds_mul_gen_pow, Nat.add_zero]; exact hsq _ (hκ _ hc0)) (by omega)
    refine ⟨by simpa using hh, ev, ?_, ?_⟩
    · simp only [vtRv, ↓reduceIte, Nat.add_sub_cancel_left]; exact e9
    · simp only [vtGout, ↓reduceIte]
      rw [e13, ordPre_succ κs hr, ordPre_zero, Nat.zero_add]
  | succ r ih =>
    obtain ⟨-, evp, e9p, egp⟩ := ih (by omega)
    have hgr := vt_goodL (rd := rd) (w := w) hl _ _ (hchk (r + 1) hr (by omega))
    have hgb := vt_goodIte' (rd := rd) (w := w) hl
      (vt_mem_slice (hchk (r + 1) hr (by omega)) (vtRankAt_ite v0 R0 s (r + 1)))
    rw [List.append_nil] at hgb
    have hcr := hc (r + 1) hr
    have hcp := hc r (by omega)
    obtain ⟨hle, htie⟩ := ord_adj κs (r := r) hr
    have hpv := vtRv_step v0 r
    have hv1 := vtRv_ge v0 (r + 1)
    have hginl := vtGout_lt v0 r
    simp only [vtRankAt, Nat.add_sub_cancel] at hgr hgb
    rw [show (if r + 1 = 1 then v0 + 13 else vtRv v0 r + 24) = vtGout v0 r by
      unfold vtGout vtRv; split_ifs <;> omega] at hgr
    obtain ⟨hh, ev, e9, e24⟩ := rank_ok (C := coreProgram.Rel rd) hlow (v := vtRv v0 (r + 1))
      (R := R0 + (r + 1)) (s := s) (pk := vtRv v0 r + 9) (pc := vtRv v0 r) (gin := vtGout v0 r)
      (e := base + (tbStackOrder κs).getD (r + 1) 0) (κ := κs.getD ((tbStackOrder κs).getD (r + 1) 0) 0)
      (κp := κs.getD ((tbStackOrder κs).getD r 0) 0) (ep := base + (tbStackOrder κs).getD r 0) (P := ordPre κs (r + 1))
      (by omega) (by omega) hginl hgr hgb (hS (r + 1) hr (by omega)) (hso _ hr)
      (by rw [tb_loadHolds_mul_gen_pow, Nat.add_zero]; exact hside _ hcr)
      (by rw [tb_loadHolds_mul_gen_pow, Nat.add_zero]; exact hkap _ hcr)
      (by rw [tb_loadHolds_mul_gen_pow, Nat.add_zero, ← ordOff κs hr]; exact hoff _ hcr)
      (by rw [tb_loadHolds_mul_gen_pow, Nat.add_zero]; exact hsq _ (hκ _ hcr))
      (by rw [e9p]; simp) (by rw [evp]) egp (by omega) (hκ _ hcr) (hκ _ hcp) hle
      (fun h => by have := htie h; omega)
    refine ⟨?_, ev, ?_, ?_⟩
    · simp only [Nat.add_one_ne_zero, ↓reduceIte, vtRankAt, Nat.add_sub_cancel]
      rw [show (if r + 1 = 1 then v0 + 13 else vtRv v0 r + 24) = vtGout v0 r by
        unfold vtGout vtRv; split_ifs <;> omega]
      exact hh
    · rw [e9]; simp
    · have : vtGout v0 (r + 1) = vtRv v0 (r + 1) + 24 := by simp [vtGout]
      rw [this, e24, ordPre_succ κs hr]

end

end
end LeanVM.Guest.B1.Tables
