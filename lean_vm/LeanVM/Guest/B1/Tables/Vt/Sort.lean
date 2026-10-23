/-
  LeanVM.Guest.B1.Tables.Vt.Sort

  `verify_tables`' block certification: on the push and the count side, every block's offset cell
  holds `g^` its `stackOffsets` offset over the blocks' log-sizes.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.SortT
public import LeanVM.Guest.B1.Placement.StackCert

/-!
# A side's block offsets (G:1960-1993)

`vt_rank0`, `vt_rank`: what a rank's template gives (`VtRankFacts`). `vt_side_cert`: when every
block's `block_kappa` cell holds `g^κ` with `κ < 34`, the ranks of a side whose blocks are
`base .. base + n` certify that the side's `block_off_g` cells hold `g^` the `stackOffsets`
offsets of the side's sizes.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

theorem vtW152_eq : vtW152 = ofK (Parameters.gpow 152) := by
  rw [vtW152, tb_word_eOfNat]
  show ofK (K.ofBits 5452595200) = ofK (Parameters.gpow 152)
  rw [show K.ofBits 5452595200 = Parameters.gpow 152 by decide +kernel]

/-- Rank `r`'s offset written: the side's first rank writes `1`, the others the running value. -/
def vtGin (v0 r : ℕ) : ℕ := if r = 0 then v0 + 10 else if r = 1 then v0 + 13 else vtRv v0 (r - 1) + 24

/-- Rank `r`'s square read. -/
def vtSq (v0 r : ℕ) : ℕ := if r = 0 then v0 + 13 else vtRv v0 r + 23

/-- The running offset after rank `r`. -/
def vtGout (v0 r : ℕ) : ℕ := if r = 0 then v0 + 13 else vtRv v0 r + 24

/-- What rank `r` of a side gives. -/
def VtRankFacts (rd : Reader) (σ : Val) (v0 R0 s r : ℕ) : Prop :=
  let v := vtRv v0 r
  (∃ e < 153, σ (.n v) = gen ^ e) ∧ LoadHolds rd (σ (.n 30)) (R0 + r) (σ (.n v)) ∧
    LoadHolds rd (σ (.n 31) * σ (.n v)) 0 (word s 0 0) ∧
    LoadHolds rd (σ (.n 12) * σ (.n v)) 0 (σ (.n (v + 9))) ∧
    LoadHolds rd (σ (.n 185) * σ (.n v)) 0 (σ (.n (vtGin v0 r))) ∧
    LoadHolds rd (σ (.n 13) * σ (.n (v + 9))) 0 (σ (.n (vtSq v0 r))) ∧
    σ (.n (vtGout v0 r)) = σ (.n (vtGin v0 r)) * σ (.n (vtSq v0 r)) ∧
    (r = 0 → σ (.n (vtGin v0 r)) = 1) ∧
    (1 ≤ r → (∃ d < 34, σ (.n (vtRv v0 (r - 1) + 9)) = gen ^ d * σ (.n (v + 9))) ∧
      (σ (.n (vtRv v0 (r - 1) + 9)) + σ (.n (v + 9)) = 0 →
        ∃ e < 153, σ (.n v) = gen ^ e * σ (.n (vtRv v0 (r - 1)))))

section
variable {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemImage μ)
include hμ

theorem vt_rc {σ : Val} {x y t1 t2 k : V} {K : ℕ} (hK1 : 1 ≤ K) (hK : K ≤ 2 ^ 33)
    (hk : σ k = ofK (Parameters.gpow (K - 1)))
    (h : (Atom.rangeCheck x y t1 t2 k).Holds Lm.read σ) : ∃ e < K, σ x = gen ^ e :=
  tb_rc_sound' hμ Lm hK1 hK hk h.1 h.2.1 h.2.2

theorem vt_rank0 {σ : Val} {v0 R0 s : ℕ} {kret : List E → Prop}
    (h : Stmt.HoldsList (coreProgram.Rel Lm.read) Lm.read σ (vtRank0T v0 R0 s) True kret) :
    VtRankFacts Lm.read σ v0 R0 s 0 := by
  simp only [vtRank0T, Stmt.HoldsList, Stmt.Holds, and_true] at h
  obtain ⟨l0, c1, rc2, m5, l6, c7, q, m8, l9, c10, m11, l10, m12, l13⟩ := h
  simp only [Atom.Holds] at l0 c1 m5 l6 c7 q m8 l9 c10 m11 l10 m12 l13
  simp only [VtRankFacts, vtRv, vtGin, vtSq, vtGout, ↓reduceIte, Nat.add_zero]
  refine ⟨vt_rc hμ Lm (K := 153) (by omega) (by norm_num) (by rw [c1, vtW152_eq]) rc2, l0,
    ?_, by rw [← m8]; exact l9, by rw [← m11]; exact l10, by rw [← m12]; exact l13, ?_,
    fun _ => by rw [c10, tb_word_one], fun h => absurd h (by omega)⟩
  · rw [← m5, ← c7, ← e_add_eq_zero_iff.mp q]; exact l6
  · rw [c10, tb_word_one, one_mul]

theorem vt_rank {σ : Val} {v0 R0 s r : ℕ} (hr : 1 ≤ r) {kret : List E → Prop}
    (h : Stmt.HoldsList (coreProgram.Rel Lm.read) Lm.read σ (vtRankAt v0 R0 s r) True kret) :
    VtRankFacts Lm.read σ v0 R0 s r := by
  have hr0 : r ≠ 0 := by omega
  simp only [vtRankAt, vtRankT, Stmt.HoldsList] at h
  rw [tb_holds_ite_noRet _ _ _ rfl rfl] at h
  simp only [Stmt.HoldsList, Stmt.Holds, and_true] at h
  obtain ⟨l0, c1, rc2, m5, l6, c7, q, m8, l9, c10, mpk, rc11, a15, ⟨-, hz, -⟩, m21, lg, m22, l23,
    m24⟩ := h
  simp only [Atom.Holds] at l0 c1 m5 l6 c7 q m8 l9 c10 mpk a15 m21 lg m22 l23 m24
  have egin : vtGin v0 r = if r = 1 then v0 + 13 else vtRv v0 (r - 1) + 24 := by
    simp only [vtGin, hr0, ↓reduceIte]
  simp only [VtRankFacts, vtSq, vtGout, hr0, ↓reduceIte, egin]
  refine ⟨vt_rc hμ Lm (K := 153) (by omega) (by norm_num) (by rw [c1, vtW152_eq]) rc2, l0,
    ?_, by rw [← m8]; exact l9, by rw [← m21]; exact lg, by rw [← m22]; exact l23, m24,
    fun h => h.elim, fun _ => ⟨?_, fun h0 => ?_⟩⟩
  · rw [← m5, ← c7, ← e_add_eq_zero_iff.mp q]; exact l6
  · obtain ⟨d, hd, hq⟩ := vt_rc hμ Lm (K := 34) (by omega) (by norm_num)
      (by rw [c10]; exact word_g33) rc11
    exact ⟨d, hd, by rw [mpk, hq]⟩
  · rw [← a15] at h0
    obtain ⟨c16, m17, rc17⟩ := hz h0
    simp only [Atom.Holds] at c16 m17
    obtain ⟨e, he, hq⟩ := vt_rc hμ Lm (K := 153) (by omega) (by norm_num)
      (by rw [c16, vtW152_eq]) rc17
    exact ⟨e, he, by rw [m17, hq]⟩

end

theorem vt_gin_succ (v0 r : ℕ) : vtGin v0 (r + 1) = vtGout v0 r := by
  unfold vtGin vtGout
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  · simp only [Nat.add_one_ne_zero, ↓reduceIte, show r + 1 ≠ 1 by omega, Nat.add_sub_cancel,
      show r ≠ 0 by omega]

theorem vt_word_small_inj {a b : ℕ} (ha : a < 3) (hb : b < 3) (h : word a 0 0 = word b 0 0) :
    a = b := by
  rw [tb_word_eOfNat, tb_word_eOfNat] at h
  exact eOfNat_inj (by omega) (by omega) h

/-- **A side's certified offsets.** -/
theorem vt_side_cert {rd : Reader} {σ : Val} {v0 R0 s base n : ℕ} (hn : n ≤ 2 ^ 20)
    (hfacts : ∀ r < n, VtRankFacts rd σ v0 R0 s r) (hs : s < 3)
    (hside : ∀ e < 153, LoadHolds rd (σ (.n 31)) e (word (vtBlockSide e) 0 0))
    (hsideS : ∀ e < 153, vtBlockSide e = s ↔ base ≤ e ∧ e < base + n)
    (hkap : ∀ b < 153, ∃ κ < 34, LoadHolds rd (σ (.n 12)) b (gen ^ κ))
    (hsq : ∀ j < 34, LoadHolds rd (σ (.n 13)) j (gen ^ 2 ^ j)) :
    ∃ κs : List ℕ, κs.length = n ∧ (∀ c < n, LoadHolds rd (σ (.n 12)) (base + c) (gen ^ κs.getD c 0)) ∧
      ∀ c < n, LoadHolds rd (σ (.n 185)) (base + c) (gen ^ (stackOffsets κs).1.getD c 0) := by
  obtain ⟨e, he⟩ := tb_exists_fun_of_forall (n := n) (fun r hr => (hfacts r hr).1)
  have hes : ∀ r < n, base ≤ e r ∧ e r < base + n := fun r hr => by
    have h3 := (hfacts r hr).2.2.1
    rw [(he r hr).2, tb_loadHolds_mul_gen_pow, Nat.add_zero] at h3
    have := tb_loadHolds_unique h3 (hside _ (he r hr).1)
    exact (hsideS _ (he r hr).1).mp
      (vt_word_small_inj (by unfold vtBlockSide; split_ifs <;> omega) hs this.symm)
  obtain ⟨kf, hkf⟩ := tb_exists_fun_of_forall (n := n) (fun r hr => hkap (e r) (he r hr).1)
  have hkv : ∀ r < n, σ (.n (vtRv v0 r + 9)) = gen ^ kf r := fun r hr => by
    have h4 := (hfacts r hr).2.2.2.1
    rw [(he r hr).2, tb_loadHolds_mul_gen_pow, Nat.add_zero] at h4
    exact tb_loadHolds_unique h4 (hkf r hr).2
  have hsqv : ∀ r < n, σ (.n (vtSq v0 r)) = gen ^ 2 ^ kf r := fun r hr => by
    have h6 := (hfacts r hr).2.2.2.2.2.1
    rw [hkv r hr, tb_loadHolds_mul_gen_pow, Nat.add_zero] at h6
    exact tb_loadHolds_unique h6 (hsq _ (hkf r hr).1)
  have hG : ∀ r ≤ n, r < n → σ (.n (vtGin v0 r)) =
      gen ^ tbPrefixSize id ((List.range n).map kf) r := by
    intro r hrn hr
    induction r with
    | zero => rw [(hfacts 0 hr).2.2.2.2.2.2.2.1 rfl]; simp [tbPrefixSize]
    | succ r ih =>
      rw [vt_gin_succ, (hfacts r (by omega)).2.2.2.2.2.2.1, ih (by omega) (by omega),
        hsqv r (by omega), ← pow_add, tb_prefixSize_succ _ _ _ (by simp; omega)]
      simp [List.getElem?_range (show r < n by omega)]
  have hoff : ∀ r < n, LoadHolds rd (σ (.n 185) * gen ^ base) (e r - base)
      (gen ^ tbPrefixSize id ((List.range n).map kf) r) := fun r hr => by
    have h5 := (hfacts r hr).2.2.2.2.1
    rw [(he r hr).2, tb_loadHolds_mul_gen_pow, Nat.add_zero, hG r (by omega) hr] at h5
    rw [tb_loadHolds_mul_gen_pow, show base + (e r - base) = e r by have := hes r hr; omega]
    exact h5
  have hadj : ∀ i, i + 1 < n → kf (i + 1) ≤ kf i ∧ (kf (i + 1) = kf i → e i - base ≤ e (i + 1) - base) := by
    intro i hi
    obtain ⟨⟨d, hd, hq⟩, htie⟩ := (hfacts (i + 1) hi).2.2.2.2.2.2.2.2 (by omega)
    rw [Nat.add_sub_cancel, hkv i (by omega), hkv (i + 1) hi] at hq
    have e1 := tb_gen_pow_eq_mul (by have := (hkf i (by omega)).1; omega)
      (by have := (hkf (i + 1) hi).1; omega) (by omega) hq
    refine ⟨by omega, fun heq => ?_⟩
    rw [Nat.add_sub_cancel, hkv i (by omega), hkv (i + 1) hi, heq] at htie
    obtain ⟨e', he', hcol⟩ := htie (e_add_self _)
    rw [(he (i + 1) hi).2, (he i (by omega)).2] at hcol
    have := tb_gen_pow_eq_mul (by have := (he (i + 1) hi).1; omega)
      (by have := (he i (by omega)).1; omega) (by omega) hcol
    omega
  obtain ⟨κs, hlen, hκ, hsurj, hoffs, -⟩ := tb_stack_cert hn (fun r => e r - base) kf
    (fun r hr => by have := hes r hr; omega) (fun r hr => (hkf r hr).1) hoff hadj
  refine ⟨κs, hlen, fun c hc => ?_, fun c hc => ?_⟩
  · obtain ⟨r, hr, hrc⟩ := hsurj c hc
    rw [← hrc, hκ r hr, show base + (e r - base) = e r by have := hes r hr; omega]
    exact (hkf r hr).2
  · have := hoffs c hc
    rw [tb_loadHolds_mul_gen_pow] at this
    exact this

theorem vtSide_push : ∀ e < 153, vtBlockSide e = 0 ↔ 0 ≤ e ∧ e < 0 + 54 := by decide

theorem vtSide_count : ∀ e < 153, vtBlockSide e = 2 ↔ 108 ≤ e ∧ e < 108 + 45 := by decide

/-- `block_side_tab`'s cells. -/
theorem vt_side_tab {rd : Reader} {σ : Val} (h : VtH rd σ) :
    ∀ e < 153, LoadHolds rd (σ (.n 31)) e (word (vtBlockSide e) 0 0) := by
  obtain ⟨k, hs⟩ := h.slice 11 vtSideT vtSideT_check
  rw [vtSideT, tb_holdsList_flatten_range _ _ (fun _ => rfl)] at hs
  intro e he
  have := hs e he
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
  rw [← this.1]
  exact this.2

/-- **`verify_tables`' block certification** (G:1967-1993): when every block's `block_kappa` cell
holds `g^κ`, `κ < 34`, the push side's `54` blocks and the count side's `45` blocks have their
`block_off_g` cells holding `g^` the `stackOffsets` offsets of the side's log-sizes. -/
theorem vt_sort {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemImage μ) {σ : Val} (h : VtH Lm.read σ)
    (hkap : ∀ b < 153, ∃ κ < 34, LoadHolds Lm.read (σ (.n 12)) b (gen ^ κ))
    (hsq : ∀ j < 34, LoadHolds Lm.read (σ (.n 13)) j (gen ^ 2 ^ j)) :
    (∃ κs : List ℕ, κs.length = 54 ∧
      (∀ c < 54, LoadHolds Lm.read (σ (.n 12)) (0 + c) (gen ^ κs.getD c 0)) ∧
      ∀ c < 54, LoadHolds Lm.read (σ (.n 185)) (0 + c) (gen ^ (stackOffsets κs).1.getD c 0)) ∧
    (∃ κs : List ℕ, κs.length = 45 ∧
      (∀ c < 45, LoadHolds Lm.read (σ (.n 12)) (108 + c) (gen ^ κs.getD c 0)) ∧
      ∀ c < 45, LoadHolds Lm.read (σ (.n 185)) (108 + c) (gen ^ (stackOffsets κs).1.getD c 0)) := by
  have hside := vt_side_tab h
  refine ⟨vt_side_cert (v0 := 186) (R0 := 0) (s := 0) (base := 0) (n := 54) (by norm_num) (fun r hr => ?_) (by norm_num) hside
      vtSide_push hkap hsq,
    vt_side_cert (v0 := 1525) (R0 := 108) (s := 2) (base := 108) (n := 45) (by norm_num) (fun r hr => ?_) (by norm_num) hside
      vtSide_count hkap hsq⟩
  · rcases Nat.eq_zero_or_pos r with rfl | hr0
    · obtain ⟨k, hs⟩ := h.slice 318 _ vtPush0_check
      exact vt_rank0 hμ Lm hs
    · obtain ⟨k, hs⟩ := h.slice _ _ (vtPush_check r hr hr0)
      exact vt_rank hμ Lm hr0 hs
  · rcases Nat.eq_zero_or_pos r with rfl | hr0
    · obtain ⟨k, hs⟩ := h.slice 1339 _ vtCount0_check
      exact vt_rank0 hμ Lm hs
    · obtain ⟨k, hs⟩ := h.slice _ _ (vtCount_check r hr hr0)
      exact vt_rank hμ Lm hr0 hs

end
end LeanVM.Guest.B1.Tables
