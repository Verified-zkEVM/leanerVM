/-
  LeanVM.Guest.B1.Placement.CertifyComplete

  `certify_placement`, completely: on a memory holding the base and the squares table, and its
  three buffers holding the columns' `g^κ`, `stackOffsets`'s order and `g^offset`, the honest
  valuation satisfies every statement, with the stack's total and the two buffers as returns.
-/

module

public import LeanVM.Guest.B1.Placement.Certify
public import LeanVM.Guest.B1.Placement.Kappas
public import LeanVM.Guest.B1.Selectors.LayoutBasic

/-!
# `certify_placement`, completely (TRIAGE G #67)

The inputs are the runs `cpLin`: `kappa_base = [1, g^log_mem, g^τ_0, …, g^τ_5]` at `ekb` and the
squares table at `esq`. The buffers (`cpOwn`), at any bases `e2`, `e120`, `e121`: the committed
columns' `g^κ` (`cpKs`), `stackOffsets`'s order (`tbStackOrder`, the honest `col_sort_order`
witness) and the columns' `g^offset`.

The honest valuation `cpσ` is written out value by value (`cpF`): the sizes (`cpInitV`), rank `0`
(`cpRank0V`) and ranks `1 .. 98` (`cpRankV`): the column of rank `r`, its size, the size gap to
rank `r - 1` and, on a tie, the column gap, each with its range check's complement and the words
the memory holds there, the running offset. The range checks read the memory at `g^a`, `a ≤ 98`:
the memory is defined below `2^7` (`LowDefB 7`).

`cp_holds`: the relation holds with the returns `[g^stackTotal, off, kap]`; `cp_ctx`: the buffers
satisfy `PCtx`. Hypotheses beyond the precondition of `certify_placement_Spec`: `τ_5 ≤ 27` (every
committed column's `κ = τ_5 + 6` of `q_keccak` below `SIZE_BITS = 34`, which the guest
range-checks; the deployed limits give `τ_5 ≤ 22`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The memory is defined below `2^k`. -/
def LowDefB (k : ℕ) (rd : Reader) : Prop := ∀ i < 2 ^ k, (rd (gpow i)).isSome

/-- The word at `g^a`, or `0`. -/
noncomputable def rdv (rd : Reader) (a : ℕ) : E := (rd (gpow a)).getD 0

theorem tb_ite_neg {c : Prop} [Decidable c] (h : ¬c) {α : Type} {a b : α} :
    (if c then a else b) = b := by simp [h]

theorem tb_ite_pos {c : Prop} [Decidable c] (h : c) {α : Type} {a b : α} :
    (if c then a else b) = a := by simp [h]

/-! ## The honest data -/

section
variable (lm : ℕ) (hs : List ℕ)

/-- The committed columns' sizes. -/
def cpKs : List ℕ := committedKappas (columnKappas lm guestLogBytecode hs)

/-- `stackOffsets`'s order of them. -/
def cpOrd : List ℕ := tbStackOrder (cpKs lm hs)

/-- Rank `r`'s column. -/
def cpColF (r : ℕ) : ℕ := (cpOrd lm hs).getD r 0

/-- Rank `r`'s size. -/
def cpKF (r : ℕ) : ℕ := (cpKs lm hs).getD (cpColF lm hs r) 0

/-- The running offset before rank `r`. -/
def cpPre (r : ℕ) : ℕ := tbPrefixSize ((cpKs lm hs).getD · 0) (cpOrd lm hs) r

/-- The inputs: the base and the squares table. -/
def cpLin (ekb esq : ℕ) : TLay :=
  [(ekb, 1 :: gen ^ lm :: hs.map (gen ^ ·)), (esq, gSquaresList)]

/-- The buffers: `g^κ` per column, the order, `g^offset` per column. -/
def cpOwn (e2 e120 e121 : ℕ) : TLay :=
  [(e2, (cpKs lm hs).map (gen ^ ·)), (e120, (cpOrd lm hs).map (gen ^ ·)),
    (e121, (stackOffsets (cpKs lm hs)).1.map (gen ^ ·))]

end

/-! ## The honest valuation -/

section
variable (lm : ℕ) (hs : List ℕ) (ekb esq e2 e120 e121 : ℕ) (rd : Reader)

/-- The columns' sizes, values `3 .. 119`. -/
def cpInitV (i : ℕ) : E :=
  if i < 7 then gen ^ lm
  else if i = 7 then 1
  else if i = 8 then word (2 ^ 19) 0 0
  else if i = 9 then gen ^ 19
  else if i = 10 then gen ^ hs.getD 5 0
  else if i = 11 then word (2 ^ 6) 0 0
  else if i = 12 then gen ^ (hs.getD 5 0 + 6)
  else gen ^ (cpKs lm hs).getD (i - 7) 0

/-- Rank `0`, values `108 .. 122`. -/
noncomputable def cpRank0V (j : ℕ) : E :=
  let c := cpColF lm hs 0
  let k := cpKF lm hs 0
  match j with
  | 0 => gen ^ c
  | 1 => w98
  | 2 => gen ^ (98 - c)
  | 3 => rdv rd c
  | 4 => rdv rd (98 - c)
  | 5 => ofK (gpow e2) * gen ^ c
  | 6 => gen ^ k
  | 7 => word 1 0 0
  | 8 => ofK (gpow e121) * gen ^ c
  | 9 => w33
  | 10 => gen ^ (33 - k)
  | 11 => rdv rd k
  | 12 => rdv rd (33 - k)
  | 13 => ofK (gpow esq) * gen ^ k
  | _ => gen ^ 2 ^ k

/-- Rank `r ≥ 1`, value `97 + 26·r + j`. -/
noncomputable def cpRankV (r j : ℕ) : E :=
  let c := cpColF lm hs r
  let k := cpKF lm hs r
  let cp := cpColF lm hs (r - 1)
  let kp := cpKF lm hs (r - 1)
  match j with
  | 0 => gen ^ c
  | 1 => w98
  | 2 => gen ^ (98 - c)
  | 3 => rdv rd c
  | 4 => rdv rd (98 - c)
  | 5 => ofK (gpow e2) * gen ^ c
  | 6 => gen ^ k
  | 7 => w33
  | 8 => gen ^ (kp - k)
  | 9 => gen ^ (33 - (kp - k))
  | 10 => rdv rd (kp - k)
  | 11 => rdv rd (33 - (kp - k))
  | 12 => gen ^ kp + gen ^ k
  | 13 => w98
  | 14 => gen ^ (c - cp)
  | 15 => gen ^ (98 - (c - cp))
  | 16 => rdv rd (c - cp)
  | 17 => rdv rd (98 - (c - cp))
  | 18 => ofK (gpow e121) * gen ^ c
  | 19 => w33
  | 20 => gen ^ (33 - k)
  | 21 => rdv rd k
  | 22 => rdv rd (33 - k)
  | 23 => ofK (gpow esq) * gen ^ k
  | 24 => gen ^ 2 ^ k
  | _ => gen ^ cpPre lm hs (r + 1)

/-- The honest words, by value number. -/
noncomputable def cpF (i : ℕ) : E :=
  if i = 0 then ofK (gpow ekb)
  else if i = 1 then ofK (gpow esq)
  else if i = 2 then ofK (gpow e2)
  else if i < 106 then cpInitV lm hs i
  else if i = 106 then ofK (gpow e120)
  else if i = 107 then ofK (gpow e121)
  else if i < 123 then cpRank0V lm hs esq e2 e121 rd (i - 108)
  else if i < 2671 then cpRankV lm hs esq e2 e121 rd ((i - 97) / 26) ((i - 97) % 26)
  else if i = 2671 then gen ^ cpPre lm hs 99
  else if i = 2672 then ofK (gpow e121)
  else ofK (gpow e2)

/-- **The honest valuation.** -/
noncomputable def cpσ : Val := fun v => cpF lm hs ekb esq e2 e120 e121 rd v.idx

theorem cpσ_rank {r j : ℕ} (hr1 : 1 ≤ r) (hr : r ≤ 98) (hj : j < 26) :
    cpσ lm hs ekb esq e2 e120 e121 rd (.n (97 + 26 * r + j)) =
      cpRankV lm hs esq e2 e121 rd r j := by
  show cpF lm hs ekb esq e2 e120 e121 rd (97 + 26 * r + j) = _
  have e1 : (97 + 26 * r + j - 97) / 26 = r := by omega
  have e2' : (97 + 26 * r + j - 97) % 26 = j := by omega
  unfold cpF
  rw [tb_ite_neg (by omega), tb_ite_neg (by omega), tb_ite_neg (by omega), tb_ite_neg (by omega), tb_ite_neg (by omega),
    tb_ite_neg (by omega), tb_ite_neg (by omega), tb_ite_pos (by omega), e1, e2']

theorem cpσ_rank0 {j : ℕ} (hj : j < 15) :
    cpσ lm hs ekb esq e2 e120 e121 rd (.n (108 + j)) = cpRank0V lm hs esq e2 e121 rd j := by
  show cpF lm hs ekb esq e2 e120 e121 rd (108 + j) = _
  unfold cpF
  rw [tb_ite_neg (by omega), tb_ite_neg (by omega), tb_ite_neg (by omega), tb_ite_neg (by omega), tb_ite_neg (by omega),
    tb_ite_neg (by omega), tb_ite_pos (by omega), Nat.add_sub_cancel_left]

theorem cpσ_init {i : ℕ} (h3 : 3 ≤ i) (hi : i < 106) :
    cpσ lm hs ekb esq e2 e120 e121 rd (.n i) = cpInitV lm hs i := by
  show cpF lm hs ekb esq e2 e120 e121 rd i = _
  unfold cpF
  rw [tb_ite_neg (by omega), tb_ite_neg (by omega), tb_ite_neg (by omega), tb_ite_pos hi]

end

/-! ## The honest data's facts -/

section
variable {lm : ℕ} {hs : List ℕ}

theorem cpKs_length : (cpKs lm hs).length = 99 :=
  committedKappas_length _ (columnKappas_length _ _ _)

theorem cpKs_getD (hl : hs.length = 6) {c : ℕ} (hc : c < 99) :
    (cpKs lm hs).getD c 0 = (0 :: lm :: hs).getD (colKappaSrc c) 0 + colKappaAdj c := by
  rw [cpKs, committedKappas_columnKappas lm hs hl, List.getD_eq_getElem _ _ (by simpa using hc)]
  simp

theorem cp_base_lt (hl : hs.length = 6) (hlm : lm ≤ 32) (hhs : ∀ h ∈ hs, h < 29) {s : ℕ}
    (hs8 : s < 8) : (0 :: lm :: hs).getD s 0 < 33 := by
  rcases Nat.lt_or_ge s 2 with h2 | h2
  · interval_cases s
    · simp
    · simp; omega
  · obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, by omega⟩
    simp only [List.getD_cons_succ]
    rw [List.getD_eq_getElem _ _ (by omega)]
    have := hhs _ (List.getElem_mem (by omega : t < hs.length))
    omega

theorem colKappaSrc_lt {c : ℕ} : colKappaSrc c < 8 := by unfold colKappaSrc; split_ifs <;> omega

theorem cpKs_lt (hl : hs.length = 6) (hlm : lm ≤ 32) (hhs : ∀ h ∈ hs, h < 29)
    (h5 : hs.getD 5 0 ≤ 27) {c : ℕ} (hc : c < 99) : (cpKs lm hs).getD c 0 < 34 := by
  rw [cpKs_getD hl hc]
  have hb := cp_base_lt hl hlm hhs (colKappaSrc_lt (c := c))
  by_cases h45 : c = 4 ∨ c = 5
  · rcases h45 with rfl | rfl
    · simp [colKappaSrc, colKappaAdj]
    · show (0 :: lm :: hs).getD 7 0 + 6 < 34
      simp only [List.getD_cons_succ]
      omega
  · have : colKappaAdj c = 0 := by unfold colKappaAdj; split_ifs <;> omega
    omega

theorem cpOrd_perm : (cpOrd lm hs).Perm (List.range 99) := by
  rw [cpOrd, tbStackOrder, cpKs_length]; exact List.mergeSort_perm _ _

theorem cpOrd_length : (cpOrd lm hs).length = 99 := by
  rw [(cpOrd_perm).length_eq, List.length_range]

theorem cpOrd_nodup : (cpOrd lm hs).Nodup :=
  (cpOrd_perm).nodup_iff.mpr List.nodup_range

theorem cpColF_lt {r : ℕ} (hr : r < 99) : cpColF lm hs r < 99 := by
  have hm : (cpOrd lm hs).getD r 0 ∈ cpOrd lm hs := by
    rw [List.getD_eq_getElem _ _ (by rw [cpOrd_length]; exact hr)]; exact List.getElem_mem _
  exact List.mem_range.mp ((cpOrd_perm).subset hm)

theorem cpOrd_sorted :
    (cpOrd lm hs).Pairwise fun a b => stackLe ((cpKs lm hs).getD · 0) a b = true := by
  rw [cpOrd, tbStackOrder]
  apply List.pairwise_mergeSort
  · intro a b c; simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega
  · intro a b; simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega

/-- **Adjacent ranks**: sizes do not increase, ties ascend by column. -/
theorem cpOrd_adj {r : ℕ} (hr : r + 1 < 99) :
    cpKF lm hs (r + 1) ≤ cpKF lm hs r ∧
      (cpKF lm hs (r + 1) = cpKF lm hs r → cpColF lm hs r < cpColF lm hs (r + 1)) := by
  have hlen := cpOrd_length (lm := lm) (hs := hs)
  have hp := List.pairwise_iff_getElem.mp (cpOrd_sorted (lm := lm) (hs := hs)) r (r + 1)
    (by omega) (by omega) (by omega)
  have hne : (cpOrd lm hs)[r]'(by omega) ≠ (cpOrd lm hs)[r + 1]'(by omega) := fun he =>
    absurd ((List.Nodup.getElem_inj_iff (cpOrd_nodup (lm := lm) (hs := hs))).mp he) (by omega)
  simp only [cpKF, cpColF, List.getD_eq_getElem _ _ (show r < (cpOrd lm hs).length by omega),
    List.getD_eq_getElem _ _ (show r + 1 < (cpOrd lm hs).length by omega)]
  simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hp
  omega

theorem cpPre_zero : cpPre lm hs 0 = 0 := by simp [cpPre, tbPrefixSize]

theorem cpPre_succ {r : ℕ} (hr : r < 99) :
    cpPre lm hs (r + 1) = cpPre lm hs r + 2 ^ cpKF lm hs r := by
  rw [cpPre, tb_prefixSize_succ _ _ _ (by rw [cpOrd_length]; exact hr)]; rfl

theorem cpOff {r : ℕ} (hr : r < 99) :
    (stackOffsets (cpKs lm hs)).1.getD (cpColF lm hs r) 0 = cpPre lm hs r :=
  tb_stackOffsets_fst (cpKs lm hs) r (by rw [cpKs_length]; exact hr)

theorem cpPre_total :
    cpPre lm hs 99 = stackTotal (columnKappas lm guestLogBytecode hs) := by
  have h := tb_prefixSize_full ((cpKs lm hs).getD · 0) (cpOrd lm hs)
  rw [cpOrd_length] at h
  have he : (List.range 99).map ((cpKs lm hs).getD · 0) = cpKs lm hs := by
    apply List.ext_getElem (by simp [cpKs_length])
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ h2]
  rw [cpPre, h, ((cpOrd_perm).map _).sum_eq, stackTotal, ← cpKs]
  conv_rhs => rw [← he]
  rw [List.map_map]
  rfl

end

/-! ## Reads -/

theorem ldef_load {rd : Reader} (hlow : LowDefB 7 rd) {a : ℕ} (ha : a < 128) :
    LoadHolds rd (gen ^ a) 0 (rdv rd a) := by
  rw [gen_pow_eq_ofK]
  refine ⟨tb_isInK_ofK _, ?_⟩
  rw [tb_addr_ofK, Nat.add_zero]
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hlow a (by norm_num; omega))
  rw [rdv, hv]; rfl

/-- **A range check of `g^a` against `g^K` passes**, on a memory defined below `2^7`. -/
theorem rc_ok {rd : Reader} (hlow : LowDefB 7 rd) {a K : ℕ} (ha : a ≤ K) (hK : K < 128) :
    LoadHolds rd (gen ^ a) 0 (rdv rd a) ∧ gen ^ K = gen ^ a * gen ^ (K - a) ∧
      LoadHolds rd (gen ^ (K - a)) 0 (rdv rd (K - a)) :=
  ⟨ldef_load hlow (by omega), by rw [← pow_add, Nat.add_sub_cancel' ha], ldef_load hlow (by omega)⟩

theorem w98_eq : w98 = gen ^ 98 := by rw [w98, word_g98, gen_pow_eq_ofK]

theorem w33_eq : w33 = gen ^ 33 := by rw [w33, word_g33, gen_pow_eq_ofK]

section
variable {lm : ℕ} {hs : List ℕ} {ekb esq e2 e120 e121 : ℕ} {rd : Reader}

theorem cp_reads (hl : hs.length = 6)
    (hm : MemLay rd (cpOwn lm hs e2 e120 e121 ++ cpLin lm hs ekb esq)) :
    (∀ c < 99, LoadHolds rd (ofK (gpow e2)) c (gen ^ (cpKs lm hs).getD c 0)) ∧
    (∀ r < 99, LoadHolds rd (ofK (gpow e120)) r (gen ^ cpColF lm hs r)) ∧
    (∀ c < 99, LoadHolds rd (ofK (gpow e121)) c (gen ^ (stackOffsets (cpKs lm hs)).1.getD c 0)) ∧
    (∀ s < 8, LoadHolds rd (ofK (gpow ekb)) s (gen ^ (0 :: lm :: hs).getD s 0)) ∧
    (∀ k < 34, LoadHolds rd (ofK (gpow esq)) k (gen ^ 2 ^ k)) := by
  obtain ⟨ho, hi⟩ := memLay_append.mp hm
  have r2 := tbReadsAt_map_iff.mp (ho (e2, (cpKs lm hs).map (gen ^ ·)) (by simp [cpOwn]))
  have r120 := tbReadsAt_map_iff.mp (ho (e120, (cpOrd lm hs).map (gen ^ ·)) (by simp [cpOwn]))
  have r121 := tbReadsAt_map_iff.mp
    (ho (e121, (stackOffsets (cpKs lm hs)).1.map (gen ^ ·)) (by simp [cpOwn]))
  have rkb := hi (ekb, 1 :: gen ^ lm :: hs.map (gen ^ ·)) (by simp [cpLin])
  have rsq := hi (esq, gSquaresList) (by simp [cpLin])
  refine ⟨fun c hc => r2 c (by rw [cpKs_length]; exact hc),
    fun r hr => r120 r (by rw [cpOrd_length]; exact hr),
    fun c hc => r121 c (by rw [tb_stackOffsets_length, cpKs_length]; exact hc), fun s hs8 => ?_,
    fun k hk => ?_⟩
  · have := rkb s (by simp [hl]; omega)
    have hb : (1 :: gen ^ lm :: hs.map (gen ^ ·))[s]'(by simp [hl]; omega) =
        gen ^ (0 :: lm :: hs).getD s 0 := by
      rcases Nat.lt_or_ge s 2 with h2 | h2
      · interval_cases s <;> simp
      · obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, by omega⟩
        simp only [List.getElem_cons_succ, List.getElem_map, List.getD_cons_succ]
        rw [List.getD_eq_getElem _ _ (by omega)]
    rwa [hb] at this
  · have := rsq k (by simp [gSquaresList]; exact hk)
    simpa [gSquaresList] using this

end

/-! ## Every statement -/

theorem isInK_gen_pow (a : ℕ) : IsInK (gen ^ a) := by rw [gen_pow_eq_ofK]; exact tb_isInK_ofK _

section
variable {lm : ℕ} {hs : List ℕ} {ekb esq e2 e120 e121 : ℕ} {rd : Reader}

/-- Rank `r + 1`'s statements hold. -/
theorem cp_rank (hlow : LowDefB 7 rd)
    (rK : ∀ c < 99, LoadHolds rd (ofK (gpow e2)) c (gen ^ (cpKs lm hs).getD c 0))
    (rO : ∀ r < 99, LoadHolds rd (ofK (gpow e120)) r (gen ^ cpColF lm hs r))
    (rF : ∀ c < 99, LoadHolds rd (ofK (gpow e121)) c (gen ^ (stackOffsets (cpKs lm hs)).1.getD c 0))
    (rS : ∀ k < 34, LoadHolds rd (ofK (gpow esq)) k (gen ^ 2 ^ k))
    (hK : ∀ r < 99, cpKF lm hs r < 34) {r : ℕ} (hr : r < 98)
    (vR : ∀ j < 26, cpσ lm hs ekb esq e2 e120 e121 rd (.n (97 + 26 * (r + 1) + j)) =
      cpRankV lm hs esq e2 e121 rd (r + 1) j)
    (vPk : cpσ lm hs ekb esq e2 e120 e121 rd (.n (cpPk (r + 1))) = gen ^ cpKF lm hs r)
    (vPc : cpσ lm hs ekb esq e2 e120 e121 rd (.n (cpPc (r + 1))) = gen ^ cpColF lm hs r)
    (vB1 : cpσ lm hs ekb esq e2 e120 e121 rd (.n (97 + 26 * (r + 1) - 1)) =
      gen ^ cpPre lm hs (r + 1))
    (v1 : cpσ lm hs ekb esq e2 e120 e121 rd (.n 1) = ofK (gpow esq))
    (v2 : cpσ lm hs ekb esq e2 e120 e121 rd (.n 2) = ofK (gpow e2))
    (v120 : cpσ lm hs ekb esq e2 e120 e121 rd (.n 106) = ofK (gpow e120))
    (v121 : cpσ lm hs ekb esq e2 e120 e121 rd (.n 107) = ofK (gpow e121)) :
    CpRankOk rd (cpσ lm hs ekb esq e2 e120 e121 rd) (r + 1) := by
  set σ := cpσ lm hs ekb esq e2 e120 e121 rd
  have vB : σ (.n (97 + 26 * (r + 1))) = gen ^ cpColF lm hs (r + 1) := vR 0 (by norm_num)
  have hc := cpColF_lt (lm := lm) (hs := hs) (r := r + 1) (by omega)
  have hcp := cpColF_lt (lm := lm) (hs := hs) (r := r) (by omega)
  have hk := hK (r + 1) (by omega)
  have hkp := hK r (by omega)
  obtain ⟨hle, htie⟩ := cpOrd_adj (lm := lm) (hs := hs) (r := r) (by omega)
  simp only [CpRankOk, TbRcHolds]
  rw [vB, vR 1 (by norm_num), vR 2 (by norm_num), vR 3 (by norm_num), vR 4 (by norm_num),
    vR 5 (by norm_num), vR 6 (by norm_num), vR 7 (by norm_num), vR 8 (by norm_num),
    vR 9 (by norm_num), vR 10 (by norm_num), vR 11 (by norm_num), vR 12 (by norm_num),
    vR 13 (by norm_num), vR 14 (by norm_num), vR 15 (by norm_num), vR 16 (by norm_num),
    vR 17 (by norm_num), vR 18 (by norm_num), vR 19 (by norm_num), vR 20 (by norm_num),
    vR 21 (by norm_num), vR 22 (by norm_num), vR 23 (by norm_num), vR 24 (by norm_num),
    vR 25 (by norm_num), vPk, vPc, vB1, v1, v2, v120, v121]
  simp only [cpRankV, Nat.add_sub_cancel]
  obtain ⟨c1, c2, c3⟩ := rc_ok hlow (a := cpColF lm hs (r + 1)) (K := 98) (by omega) (by norm_num)
  obtain ⟨d1, d2, d3⟩ := rc_ok hlow (a := cpKF lm hs r - cpKF lm hs (r + 1)) (K := 33)
    (by omega) (by norm_num)
  obtain ⟨f1, f2, f3⟩ := rc_ok hlow (a := cpKF lm hs (r + 1)) (K := 33) (by omega) (by norm_num)
  refine ⟨rO _ (by omega), trivial, ⟨c1, by rw [w98_eq, c2], c3⟩, trivial, ?_, trivial, ?_,
    ⟨d1, by rw [w33_eq, d2], d3⟩, trivial, ⟨isInK_add (isInK_gen_pow _) (isInK_gen_pow _), fun h0 => ?_⟩,
    trivial, ?_, trivial, ⟨f1, by rw [w33_eq, f2], f3⟩, trivial, ?_, ?_⟩
  · rw [tb_loadHolds_mul_gen_pow, Nat.add_zero]; exact rK _ hc
  · rw [← pow_add, Nat.sub_add_cancel hle]
  · have he : cpKF lm hs r = cpKF lm hs (r + 1) :=
      gen_pow_inj (by omega) (by omega) (e_add_eq_zero_iff.mp h0)
    have hlt := htie he.symm
    obtain ⟨g1, g2, g3⟩ := rc_ok hlow (a := cpColF lm hs (r + 1) - cpColF lm hs r) (K := 98)
      (by omega) (by norm_num)
    exact ⟨trivial, by rw [← pow_add, Nat.sub_add_cancel hlt.le], g1, by rw [w98_eq, g2], g3⟩
  · rw [tb_loadHolds_mul_gen_pow, Nat.add_zero, ← cpOff (r := r + 1) (by omega)]
    exact rF _ hc
  · rw [tb_loadHolds_mul_gen_pow, Nat.add_zero]; exact rS _ hk
  · rw [cpPre_succ (by omega), pow_add]

end

/-- **`certify_placement`'s body holds** of the honest valuation: on a memory holding its base and squares table, its
three buffers holding the columns' `g^κ`, `stackOffsets`'s order and `g^offset`, defined below
`2^7`, the relation holds with the stack's total and the buffers. -/
theorem cp_body_holds {lm : ℕ} {hs : List ℕ} (hl : hs.length = 6) (hlm : lm ≤ 32)
    (hhs : ∀ h ∈ hs, h < 29) (h5 : hs.getD 5 0 ≤ 27) (ekb esq e2 e120 e121 : ℕ) (rd : Reader)
    (hm : MemLay rd (cpOwn lm hs e2 e120 e121 ++ cpLin lm hs ekb esq)) (hlow : LowDefB 7 rd) :
    Stmt.HoldsList (coreProgram.Rel rd) rd (cpσ lm hs ekb esq e2 e120 e121 rd) cpBody False
      (fun rs => rs = [gen ^ stackTotal (columnKappas lm guestLogBytecode hs), ofK (gpow e121),
        ofK (gpow e2)]) := by
  obtain ⟨rK, rO, rF, rB, rS⟩ := cp_reads hl hm
  have hK : ∀ r < 99, cpKF lm hs r < 34 := fun r hr => cpKs_lt hl hlm hhs h5 (cpColF_lt hr)
  set σ := cpσ lm hs ekb esq e2 e120 e121 rd with hσ
  have v0 : σ (.n 0) = ofK (gpow ekb) := rfl
  have v1 : σ (.n 1) = ofK (gpow esq) := rfl
  have v2 : σ (.n 2) = ofK (gpow e2) := rfl
  have v120 : σ (.n 106) = ofK (gpow e120) := rfl
  have v121 : σ (.n 107) = ofK (gpow e121) := rfl
  have r0 : ∀ j < 15, σ (.n (108 + j)) = cpRank0V lm hs esq e2 e121 rd j := fun j hj =>
    cpσ_rank0 lm hs ekb esq e2 e120 e121 rd hj
  have hc0 := cpColF_lt (lm := lm) (hs := hs) (r := 0) (by norm_num)
  have hk0 := hK 0 (by norm_num)
  -- the sizes
  have hinit : ∀ c < 99, CpInitOk rd σ c := by
    intro c hc
    have hsrc := colKappaSrc_lt (c := c)
    have hkc := cpKs_getD (lm := lm) hl hc
    unfold CpInitOk
    rw [v0, v2]
    by_cases h4 : c < 4
    · have ew : cpW c = 3 + c := by unfold cpW; rw [tb_ite_pos h4]
      have ev : cpV c = 3 + c := by unfold cpV; rw [tb_ite_pos h4]
      have hs' : colKappaSrc c = 1 := by unfold colKappaSrc; rw [tb_ite_pos h4]
      have ha : colKappaAdj c = 0 := by unfold colKappaAdj; split_ifs <;> omega
      rw [ew, ev, show σ (.n (3 + c)) = cpInitV lm hs (3 + c) from
        cpσ_init lm hs ekb esq e2 e120 e121 rd (i := 3 + c) (by omega) (by omega)]
      have hiv : cpInitV lm hs (3 + c) = gen ^ lm := by simp [cpInitV]; omega
      refine ⟨?_, fun h => absurd ha h, ?_⟩
      · rw [hiv]; have := rB _ hsrc; rwa [hs'] at this ⊢
      · rw [hiv]; have := rK c hc; rwa [hkc, hs', ha] at this
    · by_cases h4' : c = 4
      · subst h4'
        refine ⟨?_, fun _ => ⟨?_, ?_⟩, ?_⟩
        · show LoadHolds rd (ofK (gpow ekb)) 0 (σ (.n 7))
          rw [show σ (.n 7) = 1 from rfl]
          have := rB 0 (by norm_num); simpa using this
        · rfl
        · show σ (.n 9) = σ (.n 7) * σ (.n 8)
          rw [show σ (.n 9) = gen ^ 19 from rfl, show σ (.n 7) = 1 from rfl,
            show σ (.n 8) = word (2 ^ 19) 0 0 from rfl, one_mul, tb_word_two_pow (by norm_num)]
        · show LoadHolds rd (ofK (gpow e2)) 4 (σ (.n 9))
          rw [show σ (.n 9) = gen ^ 19 from rfl]
          have := rK 4 hc; rwa [hkc] at this
      · by_cases h5' : c = 5
        · subst h5'
          refine ⟨?_, fun _ => ⟨?_, ?_⟩, ?_⟩
          · show LoadHolds rd (ofK (gpow ekb)) 7 (σ (.n 10))
            rw [show σ (.n 10) = gen ^ hs.getD 5 0 from rfl]
            have := rB 7 (by norm_num); simpa using this
          · rfl
          · show σ (.n 12) = σ (.n 10) * σ (.n 11)
            rw [show σ (.n 12) = gen ^ (hs.getD 5 0 + 6) from rfl,
              show σ (.n 10) = gen ^ hs.getD 5 0 from rfl,
              show σ (.n 11) = word (2 ^ 6) 0 0 from rfl, tb_word_two_pow (by norm_num), pow_add]
          · show LoadHolds rd (ofK (gpow e2)) 5 (σ (.n 12))
            rw [show σ (.n 12) = gen ^ (hs.getD 5 0 + 6) from rfl]
            have := rK 5 hc; rwa [hkc] at this
        · have ew : cpW c = c + 7 := by
            unfold cpW; rw [tb_ite_neg h4, tb_ite_neg h4', tb_ite_neg h5']
          have ev : cpV c = c + 7 := by
            unfold cpV; rw [tb_ite_neg h4, tb_ite_neg h4', tb_ite_neg h5']
          have ha : colKappaAdj c = 0 := by unfold colKappaAdj; split_ifs; omega
          rw [ew, ev, show σ (.n (c + 7)) = cpInitV lm hs (c + 7) from
            cpσ_init lm hs ekb esq e2 e120 e121 rd (i := c + 7) (by omega) (by omega)]
          have hiv : cpInitV lm hs (c + 7) = gen ^ (cpKs lm hs).getD c 0 := by
            unfold cpInitV
            rw [tb_ite_neg (by omega), tb_ite_neg (by omega), tb_ite_neg (by omega),
              tb_ite_neg (by omega), tb_ite_neg (by omega), tb_ite_neg (by omega),
              tb_ite_neg (by omega), Nat.add_sub_cancel]
          refine ⟨?_, fun h => absurd ha h, ?_⟩
          · rw [hiv, hkc, ha, Nat.add_zero]; exact rB _ hsrc
          · rw [hiv]; exact rK c hc
  -- rank 0
  have s122 : σ (.n 108) = gen ^ cpColF lm hs 0 := r0 0 (by norm_num)
  have s128 : σ (.n 114) = gen ^ cpKF lm hs 0 := r0 6 (by norm_num)
  have s136 : σ (.n 122) = gen ^ 2 ^ cpKF lm hs 0 := r0 14 (by norm_num)
  obtain ⟨c1, c2, c3⟩ := rc_ok hlow (a := cpColF lm hs 0) (K := 98) (by omega) (by norm_num)
  obtain ⟨f1, f2, f3⟩ := rc_ok hlow (a := cpKF lm hs 0) (K := 33) (by omega) (by norm_num)
  -- the ranks
  have hranks : ∀ r < 98, CpRankOk rd σ (r + 1) := by
    intro r hr
    have vR : ∀ j < 26, σ (.n (97 + 26 * (r + 1) + j)) = cpRankV lm hs esq e2 e121 rd (r + 1) j :=
      fun j hj => cpσ_rank lm hs ekb esq e2 e120 e121 rd (by omega) (by omega) hj
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · refine cp_rank hlow rK rO rF rS hK hr vR s128 s122 ?_ v1 v2 v120 v121
      show σ (.n 122) = _
      rw [s136, cpPre_succ (by norm_num), cpPre_zero, Nat.zero_add]
    · obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
      have vQ : ∀ j < 26, σ (.n (97 + 26 * (q + 1) + j)) = cpRankV lm hs esq e2 e121 rd (q + 1) j :=
        fun j hj => cpσ_rank lm hs ekb esq e2 e120 e121 rd (by omega) (by omega) hj
      refine cp_rank hlow rK rO rF rS hK hr vR ?_ ?_ ?_ v1 v2 v120 v121
      · rw [show cpPk (q + 1 + 1) = 97 + 26 * (q + 1) + 6 by simp [cpPk]; omega]
        exact vQ 6 (by norm_num)
      · rw [show cpPc (q + 1 + 1) = 97 + 26 * (q + 1) + 0 by simp [cpPc]; omega]
        exact vQ 0 (by norm_num)
      · rw [show 97 + 26 * (q + 1 + 1) - 1 = 97 + 26 * (q + 1) + 25 by omega]
        exact vQ 25 (by norm_num)
  have s3048 : σ (.n 2670) = gen ^ cpPre lm hs 99 :=
    cpσ_rank lm hs ekb esq e2 e120 e121 rd (r := 98) (j := 25) (by norm_num) (by norm_num)
      (by norm_num)
  rw [cp_body_iff]
  refine ⟨hinit, ?_, r0 1 (by norm_num), ⟨?_, ?_, ?_⟩, r0 5 (by norm_num), ?_,
    r0 7 (by norm_num), r0 8 (by norm_num), ?_, r0 9 (by norm_num), ⟨?_, ?_, ?_⟩,
    r0 13 (by norm_num), ?_, hranks, ?_, rfl, rfl, ?_⟩
  · rw [v120, s122]; exact rO 0 (by norm_num)
  · rw [s122, show σ (.n 111) = rdv rd (cpColF lm hs 0) from r0 3 (by norm_num)]; exact c1
  · rw [show σ (.n 109) = w98 from r0 1 (by norm_num), s122,
      show σ (.n 110) = gen ^ (98 - cpColF lm hs 0) from r0 2 (by norm_num), w98_eq, c2]
  · rw [show σ (.n 110) = gen ^ (98 - cpColF lm hs 0) from r0 2 (by norm_num),
      show σ (.n 112) = rdv rd (98 - cpColF lm hs 0) from r0 4 (by norm_num)]
    exact c3
  · rw [show σ (.n 113) = ofK (gpow e2) * gen ^ cpColF lm hs 0 from r0 5 (by norm_num), s128,
      tb_loadHolds_mul_gen_pow, Nat.add_zero]
    exact rK _ hc0
  · have h0 := rF _ hc0
    rw [cpOff (r := 0) (by norm_num), cpPre_zero, pow_zero] at h0
    rw [show σ (.n 116) = ofK (gpow e121) * gen ^ cpColF lm hs 0 from r0 8 (by norm_num),
      show σ (.n 115) = word 1 0 0 from r0 7 (by norm_num), tb_loadHolds_mul_gen_pow,
      Nat.add_zero, tb_word_one]
    exact h0
  · rw [s128, show σ (.n 119) = rdv rd (cpKF lm hs 0) from r0 11 (by norm_num)]; exact f1
  · rw [show σ (.n 117) = w33 from r0 9 (by norm_num), s128,
      show σ (.n 118) = gen ^ (33 - cpKF lm hs 0) from r0 10 (by norm_num), w33_eq, f2]
  · rw [show σ (.n 118) = gen ^ (33 - cpKF lm hs 0) from r0 10 (by norm_num),
      show σ (.n 120) = rdv rd (33 - cpKF lm hs 0) from r0 12 (by norm_num)]
    exact f3
  · rw [show σ (.n 121) = ofK (gpow esq) * gen ^ cpKF lm hs 0 from r0 13 (by norm_num), s136,
      tb_loadHolds_mul_gen_pow, Nat.add_zero]
    exact rS _ hk0
  · rw [s3048]; rfl
  · show [gen ^ cpPre lm hs 99, ofK (gpow e121), ofK (gpow e2)] = _
    rw [cpPre_total]

/-- **`certify_placement` is complete**: on a memory holding its base and squares table, its
three buffers holding the columns' `g^κ`, `stackOffsets`'s order and `g^offset`, defined below
`2^7`, the relation holds with the stack's total and the buffers. -/
theorem cp_holds {lm : ℕ} {hs : List ℕ} (hl : hs.length = 6) (hlm : lm ≤ 32)
    (hhs : ∀ h ∈ hs, h < 29) (h5 : hs.getD 5 0 ≤ 27) (ekb esq e2 e120 e121 : ℕ) (rd : Reader)
    (hm : MemLay rd (cpOwn lm hs e2 e120 e121 ++ cpLin lm hs ekb esq)) (hlow : LowDefB 7 rd) :
    coreProgram.Rel rd "certify_placement" [ofK (gpow ekb), ofK (gpow esq)]
      [gen ^ stackTotal (columnKappas lm guestLogBytecode hs), ofK (gpow e121), ofK (gpow e2)] := by
  rw [tb_rel_iff_sem (by exact Program.find?_of_indexOf? (j := 15) (by decide +kernel) rfl),
    core15_body]
  exact ⟨cpσ lm hs ekb esq e2 e120 e121 rd, rfl,
    cp_body_holds hl hlm hhs h5 ekb esq e2 e120 e121 rd hm hlow⟩

/-- **The buffers satisfy `PCtx`** on any memory holding them. -/
theorem cp_ctx {lm : ℕ} {hs : List ℕ} {e2 e120 e121 : ℕ} {rd : Reader}
    (hm : MemLay rd (cpOwn lm hs e2 e120 e121)) :
    PCtx rd (columnKappas lm guestLogBytecode hs) (ofK (gpow e121)) (ofK (gpow e2)) :=
  ⟨columnKappas_length _ _ _, hm _ List.mem_cons_self,
    hm _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩

end
end LeanVM.Guest.B1.Tables
