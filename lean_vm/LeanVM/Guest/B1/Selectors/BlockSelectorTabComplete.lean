/-
  LeanVM.Guest.B1.Selectors.BlockSelectorTabComplete

  `block_selector_tab` is complete: for `n < 34` bits pinned in memory and a run's nibble tables
  in memory, their eq weight and `g`-power product are an outcome of `block_selector_tab__L{n}`.
-/

module

public import LeanVM.Guest.B1.Selectors.BlockSelectorTab

/-!
# `block_selector_tab` is complete (TRIAGE G #49)

The valuation `btkVal` gives every value of `block_selector_tab__L{n}`'s body its role
(`btkRole`): in nibble `k`, bit `t`'s word, its square, the one, the factor's constant, the
product, the factor and the running index (`btkP`); then the nibble's pointer into the eq table,
its eq weight (`btkXE`), the running eq product (`btkS`), the pointer into the `g` table, its share
(`btkXG`) and the running `g`-power product (`btkR`); the two returned copies. Every statement
holds of it: the bits and their squares by the bits in memory, the weights and shares by the
tables in memory, the rest by its definition.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Finset

@[expose] public section

/-! ## The roles -/

/-- Bit `t` of nibble `k`. -/
def btkB (bs : List Bool) (k t : ℕ) : Bool := bs.getD (4 * k + t) false

/-- The factor's constant of bit `t`. -/
def btkIm (t : ℕ) : E := word (imFactor t) 0 0

/-- The running index of nibble `k` after bit `t`. -/
def btkP (bs : List Bool) (k : ℕ) : ℕ → E
  | 0 => word 1 0 0 + bitE (btkB bs k 0) * btkIm 0
  | t + 1 => btkP bs k t * (word 1 0 0 + bitE (btkB bs k (t + 1)) * btkIm (t + 1))

/-- Nibble `k`'s index. -/
def btkU (n : ℕ) (bs : List Bool) (k : ℕ) : ℕ := bitsVal (btkB bs k) (btW n k)

/-- Nibble `k`'s eq weight. -/
def btkXE (n : ℕ) (bs : List Bool) (zs zs1 : List E) (k : ℕ) : E :=
  (eqLevels (nib zs k) (nib zs1 k)).getD (2 ^ btW n k - 2 + btkU n bs k) 0

/-- Nibble `k`'s share. -/
def btkXG (n : ℕ) (bs : List Bool) (gs : List E) (k : ℕ) : E :=
  (gTable (nib gs k)).getD (btkU n bs k) 0

/-- The running eq product after nibble `k`. -/
def btkS (n : ℕ) (bs : List Bool) (zs zs1 : List E) : ℕ → E
  | 0 => btkXE n bs zs zs1 0
  | k + 1 => btkS n bs zs zs1 k * btkXE n bs zs zs1 (k + 1)

/-- The running `g`-power product after nibble `k`. -/
def btkR (n : ℕ) (bs : List Bool) (gs : List E) : ℕ → E
  | 0 => btkXG n bs gs 0
  | k + 1 => btkR n bs gs k * btkXG n bs gs (k + 1)

/-- Value `r` of bit `t` of nibble `k`. -/
def btkBit (bs : List Bool) (k t r : ℕ) : E :=
  [bitE (btkB bs k t), bitE (btkB bs k t) * bitE (btkB bs k t), word 1 0 0, btkIm t,
    bitE (btkB bs k t) * btkIm t, word 1 0 0 + bitE (btkB bs k t) * btkIm t, btkP bs k t].getD r 0

/-- Value `s` of nibble `k`'s tail. -/
def btkTail (n : ℕ) (eqt gt : E) (bs : List Bool) (zs zs1 gs : List E) (k s : ℕ) : E :=
  if k = 0 then
    [eqt * btkP bs k (btW n k - 1), btkXE n bs zs zs1 k, gt * btkP bs k (btW n k - 1),
      btkXG n bs gs k].getD s 0
  else
    [eqt * btkP bs k (btW n k - 1), btkXE n bs zs zs1 k,
      btkS n bs zs zs1 (k - 1) * btkXE n bs zs zs1 k, gt * btkP bs k (btW n k - 1),
      btkXG n bs gs k, btkR n bs gs (k - 1) * btkXG n bs gs k].getD s 0

/-- Value `o` of nibble `k`. -/
def btkRole (n : ℕ) (eqt gt : E) (bs : List Bool) (zs zs1 gs : List E) (k o : ℕ) : E :=
  if o + 1 < 7 * btW n k then
    btkBit bs k ((o + 1) / 7) (if (o + 1) / 7 = 0 then o else o + 1 - 7 * ((o + 1) / 7))
  else btkTail n eqt gt bs zs zs1 gs k (o + 1 - 7 * btW n k)

/-- The length of nibble `k`'s values. -/
def btkLen (n k : ℕ) : ℕ := if k = 0 then 7 * btW n k + 3 else 7 * btW n k + 5

/-- **Value `x` of `block_selector_tab__L{n}`.** -/
def btkVal (n : ℕ) (sb eqt gt : E) (bs : List Bool) (zs zs1 gs : List E) (x : ℕ) : E :=
  if x = 0 then sb else if x = 1 then eqt else if x = 2 then gt
  else if n = 0 then word 1 0 0
  else if x = btE n (btN n - 1) then btkS n bs zs zs1 (btN n - 1)
  else if x = btE n (btN n - 1) + 1 then btkR n bs gs (btN n - 1)
  else btkRole n eqt gt bs zs zs1 gs (if x < 34 then 0 else (x - 34) / 33 + 1)
    (x - btC (if x < 34 then 0 else (x - 34) / 33 + 1))

/-! ## The arithmetic of the layout -/

theorem btE_eq (n k : ℕ) : btE n k = btC k + btkLen n k := by
  by_cases h : k = 0
  · subst h; simp [btE, btkLen]; omega
  · simp [btE, btkLen, h]; omega

theorem btW_full {n k : ℕ} (hk : k + 1 < btN n) : btW n k = 4 := by
  unfold btW btN at *; split <;> omega

theorem btkLen_le (n k : ℕ) : btkLen n k ≤ (if k = 0 then 31 else 33) := by
  have := btW_le n k
  rcases Nat.eq_zero_or_pos k with rfl | h
  · simp [btkLen]; omega
  · simp [btkLen, show k ≠ 0 by omega]; omega

theorem btE_le_C {n k : ℕ} (hk : k + 1 < btN n) : btE n k = btC (k + 1) := by
  rw [btE_eq, btkLen, btW_full hk]
  unfold btC; split <;> simp <;> omega

theorem btE_mono {n : ℕ} : ∀ {k : ℕ}, k + 1 ≤ btN n → btE n k ≤ btE n (btN n - 1)
  | k, hk => by
    rcases Nat.lt_or_ge (k + 1) (btN n) with h | h
    · have hle : ∀ j, k + 1 + j < btN n → btE n k ≤ btC (k + 1 + j) := by
        intro j
        induction j with
        | zero => intro h'; rw [Nat.add_zero, btE_le_C h']
        | succ j ih =>
          intro h'
          have := ih (by omega)
          rw [show k + 1 + (j + 1) = k + 1 + j + 1 by omega, ← btE_le_C (k := k + 1 + j) (by omega),
            btE_eq n (k + 1 + j)]
          omega
      have := hle (btN n - 1 - (k + 1)) (by omega)
      rw [show k + 1 + (btN n - 1 - (k + 1)) = btN n - 1 by omega] at this
      rw [btE_eq (k := btN n - 1)]; omega
    · rw [show k = btN n - 1 by omega]

theorem btC_ge (k : ℕ) : 3 ≤ btC k := by unfold btC; split <;> omega

/-- **Value `o` of nibble `k`.** -/
theorem btkVal_at {n : ℕ} (hn : n ≠ 0) (sb eqt gt : E) (bs : List Bool) (zs zs1 gs : List E)
    {k o : ℕ} (hk : k < btN n) (ho : o < btkLen n k) :
    btkVal n sb eqt gt bs zs zs1 gs (btC k + o) = btkRole n eqt gt bs zs zs1 gs k o := by
  have hC := btC_ge k
  have hE : btC k + o < btE n (btN n - 1) := by
    have := btE_mono (n := n) (k := k) (by omega)
    rw [btE_eq] at this; omega
  have hL := btkLen_le n k
  have hdec : (if btC k + o < 34 then 0 else (btC k + o - 34) / 33 + 1) = k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp only [btC, ↓reduceIte] at hL ⊢
      simp only [show 3 + o < 34 by omega, ↓reduceIte]
    · have hc : btC k = 34 + 33 * (k - 1) := by unfold btC; simp [show k ≠ 0 by omega]
      simp only [show k ≠ 0 by omega, ↓reduceIte] at hL
      rw [hc]
      simp only [show ¬ 34 + 33 * (k - 1) + o < 34 by omega, ↓reduceIte]; omega
  have h0 : btC k + o ≠ 0 := by omega
  have h1 : btC k + o ≠ 1 := by omega
  have h2 : btC k + o ≠ 2 := by omega
  have h3 : btC k + o ≠ btE n (btN n - 1) := by omega
  have h4 : btC k + o ≠ btE n (btN n - 1) + 1 := by omega
  simp only [btkVal, h0, h1, h2, hn, h3, h4, ↓reduceIte]
  rw [hdec, Nat.add_sub_cancel_left]

/-- Bit `t`'s values. -/
theorem btkVal_bit {n : ℕ} (hn : n ≠ 0) (sb eqt gt : E) (bs : List Bool) (zs zs1 gs : List E)
    {k t r : ℕ} (hk : k < btN n) (ht : t < btW n k) (hr : r < 7) (hr0 : t = 0 → r < 6) :
    btkVal n sb eqt gt bs zs zs1 gs (btBitV (btC k) t + r) = btkBit bs k t r := by
  have hw := btW_le n k
  have hb : btBitV (btC k) t + r = btC k + (if t = 0 then r else 7 * t - 1 + r) := by
    unfold btBitV; split <;> omega
  have hlen : (if t = 0 then r else 7 * t - 1 + r) < btkLen n k := by
    have hL : 7 * btW n k + 3 ≤ btkLen n k := by unfold btkLen; split <;> omega
    by_cases h' : t = 0
    · simp only [h', ↓reduceIte]; have := hr0 h'; omega
    · simp only [h', ↓reduceIte]; omega
  have hlt : (if t = 0 then r else 7 * t - 1 + r) + 1 < 7 * btW n k := by
    by_cases h' : t = 0 <;> simp [h'] <;> omega
  rw [hb, btkVal_at hn sb eqt gt bs zs zs1 gs hk hlen, btkRole]
  simp only [hlt, ↓reduceIte]
  by_cases h0 : t = 0
  · subst h0
    simp only [↓reduceIte]
    rw [show (r + 1) / 7 = 0 by have := hr0 rfl; omega]
    simp
  · simp only [h0, ↓reduceIte]
    rw [show (7 * t - 1 + r + 1) / 7 = t by omega]
    simp only [h0, ↓reduceIte]
    congr 1; omega

/-- The tail's values. -/
theorem btkVal_tail {n : ℕ} (hn : n ≠ 0) (sb eqt gt : E) (bs : List Bool) (zs zs1 gs : List E)
    {k s : ℕ} (hk : k < btN n) (hs : s < (if k = 0 then 4 else 6)) :
    btkVal n sb eqt gt bs zs zs1 gs (btC k + 7 * btW n k - 1 + s) =
      btkTail n eqt gt bs zs zs1 gs k s := by
  have hw1 := btW_pos hk
  have hlen : 7 * btW n k - 1 + s < btkLen n k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · simp [btkLen] at hs ⊢; omega
    · simp [btkLen, show k ≠ 0 by omega] at hs ⊢; omega
  rw [show btC k + 7 * btW n k - 1 + s = btC k + (7 * btW n k - 1 + s) by omega,
    btkVal_at hn sb eqt gt bs zs zs1 gs hk hlen, btkRole]
  simp only [show ¬ 7 * btW n k - 1 + s + 1 < 7 * btW n k by omega, ↓reduceIte]
  congr 1; omega

/-- The running index's value. -/
theorem btkVal_idx {n : ℕ} (hn : n ≠ 0) (sb eqt gt : E) (bs : List Bool) (zs zs1 gs : List E)
    {k t : ℕ} (hk : k < btN n) (ht : t < btW n k) :
    btkVal n sb eqt gt bs zs zs1 gs (btC k + 7 * t + 5) = btkP bs k t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht0
  · have := btkVal_bit hn sb eqt gt bs zs zs1 gs hk ht (r := 5) (by norm_num) (fun _ ↦ by norm_num)
    simp only [btBitV, ↓reduceIte] at this
    rw [show btC k + 7 * 0 + 5 = btC k + 5 by omega, this]; rfl
  · have := btkVal_bit hn sb eqt gt bs zs zs1 gs hk ht (r := 6) (by norm_num) (by omega)
    simp only [btBitV, show t ≠ 0 by omega, ↓reduceIte] at this
    rw [show btC k + 7 * t + 5 = btC k + 7 * t - 1 + 6 by omega, this]; rfl

/-- The running eq product's value. -/
theorem btkVal_sel {n : ℕ} (hn : n ≠ 0) (sb eqt gt : E) (bs : List Bool) (zs zs1 gs : List E)
    {k : ℕ} (hk : k < btN n) : btkVal n sb eqt gt bs zs zs1 gs (btSel n k) = btkS n bs zs zs1 k := by
  have hw1 := btW_pos hk
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · have := btkVal_tail hn sb eqt gt bs zs zs1 gs hk (s := 1) (by simp)
    rw [show btC 0 + 7 * btW n 0 - 1 + 1 = btSel n 0 by simp [btSel]; omega] at this
    rw [this]; simp [btkTail, btkS]
  · have := btkVal_tail hn sb eqt gt bs zs zs1 gs hk (s := 2) (by simp [show k ≠ 0 by omega])
    rw [show btC k + 7 * btW n k - 1 + 2 = btSel n k by
      simp [btSel, show k ≠ 0 by omega]; omega] at this
    rw [this]
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp [btkTail, btkS]

/-- The running `g`-power product's value. -/
theorem btkVal_rb {n : ℕ} (hn : n ≠ 0) (sb eqt gt : E) (bs : List Bool) (zs zs1 gs : List E)
    {k : ℕ} (hk : k < btN n) : btkVal n sb eqt gt bs zs zs1 gs (btRb n k) = btkR n bs gs k := by
  have hw1 := btW_pos hk
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · have := btkVal_tail hn sb eqt gt bs zs zs1 gs hk (s := 3) (by simp)
    rw [show btC 0 + 7 * btW n 0 - 1 + 3 = btRb n 0 by simp [btRb]; omega] at this
    rw [this]; simp [btkTail, btkR]
  · have := btkVal_tail hn sb eqt gt bs zs zs1 gs hk (s := 5) (by simp [show k ≠ 0 by omega])
    rw [show btC k + 7 * btW n k - 1 + 5 = btRb n k by
      simp [btRb, show k ≠ 0 by omega]; omega] at this
    rw [this]
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp [btkTail, btkR]

/-! ## The products -/

theorem btkP_eq (bs : List Bool) (k : ℕ) : ∀ t, t < 34 →
    btkP bs k t = gen ^ bitsVal (btkB bs k) (t + 1)
  | 0, _ => by
    rw [← prod_bitE_gen_pow, prod_range_one, btkP, btkIm, imFactor_eq (by norm_num), tb_word_one,
      add_comm (gen ^ 2 ^ 0) 1]
  | t + 1, ht => by
    rw [btkP, btkP_eq bs k t (by omega), ← prod_bitE_gen_pow, ← prod_bitE_gen_pow,
      prod_range_succ _ (t + 1), btkIm, imFactor_eq ht, tb_word_one, add_comm (gen ^ 2 ^ (t + 1)) 1]

theorem btkU_P {n : ℕ} (bs : List Bool) {k : ℕ} (hk : k < btN n) :
    btkP bs k (btW n k - 1) = gen ^ btkU n bs k := by
  have hw1 := btW_pos hk
  have hw4 := btW_le n k
  rw [btkP_eq bs k _ (by omega), show btW n k - 1 + 1 = btW n k by omega]; rfl

theorem btkS_eq (n : ℕ) (bs : List Bool) (zs zs1 : List E) : ∀ k,
    btkS n bs zs zs1 k = ∏ m ∈ range (k + 1), btkXE n bs zs zs1 m
  | 0 => by simp [btkS]
  | k + 1 => by rw [btkS, btkS_eq n bs zs zs1 k, prod_range_succ _ (k + 1)]

theorem btkR_eq (n : ℕ) (bs : List Bool) (gs : List E) : ∀ k,
    btkR n bs gs k = ∏ m ∈ range (k + 1), btkXG n bs gs m
  | 0 => by simp [btkR]
  | k + 1 => by rw [btkR, btkR_eq n bs gs k, prod_range_succ _ (k + 1)]

theorem btkVal_bit0 {n : ℕ} (hn : n ≠ 0) (sb eqt gt : E) (bs : List Bool) (zs zs1 gs : List E)
    {k t : ℕ} (hk : k < btN n) (ht : t < btW n k) :
    btkVal n sb eqt gt bs zs zs1 gs (btBitV (btC k) t) = bitE (btkB bs k t) :=
  btkVal_bit hn sb eqt gt bs zs zs1 gs (r := 0) hk ht (by norm_num) (fun _ ↦ by norm_num)

theorem btkVal_tail0 {n : ℕ} (hn : n ≠ 0) (sb eqt gt : E) (bs : List Bool) (zs zs1 gs : List E)
    {k : ℕ} (hk : k < btN n) :
    btkVal n sb eqt gt bs zs zs1 gs (btC k + 7 * btW n k - 1) = eqt * btkP bs k (btW n k - 1) := by
  have := btkVal_tail hn sb eqt gt bs zs zs1 gs hk (s := 0) (by split <;> norm_num)
  rw [Nat.add_zero] at this
  rw [this]; unfold btkTail; split <;> rfl

theorem btkVal_idxw {n : ℕ} (hn : n ≠ 0) (sb eqt gt : E) (bs : List Bool) (zs zs1 gs : List E)
    {k : ℕ} (hk : k < btN n) :
    btkVal n sb eqt gt bs zs zs1 gs (btC k + 7 * btW n k - 2) = btkP bs k (btW n k - 1) := by
  have hw1 := btW_pos hk
  have := btkVal_idx hn sb eqt gt bs zs zs1 gs hk (t := btW n k - 1) (by omega)
  rw [show btC k + 7 * (btW n k - 1) + 5 = btC k + 7 * btW n k - 2 by omega] at this
  exact this

/-- The bits in memory. -/
theorem btk_bitLoad {rd : Reader} {sb : E} {bs : List Bool} (hbr : TbReadsAt rd sb (bs.map bitE))
    {n k t : ℕ} (hbl : bs.length = n) (ht : t < btW n k) :
    LoadHolds rd sb (4 * k + t) (bitE (btkB bs k t)) := by
  have hi : 4 * k + t < n := by unfold btW at ht; split at ht <;> omega
  have := hbr (4 * k + t) (by simp; omega)
  rwa [List.getElem_map, ← List.getD_eq_getElem _ false] at this

/-- Nibble `k`'s eq weight in memory, at its index. -/
theorem btk_xeLoad {rd : Reader} {eqt gt : E} {n : ℕ} {zs zs1 gs : List E} {bs : List Bool}
    (hzl : zs.length = n) (hz1l : zs1.length = n) (hrt : RunTables rd eqt gt n zs zs1 gs)
    {k : ℕ} (hk : k < btN n) :
    LoadHolds rd (eqt * btkP bs k (btW n k - 1)) (32 * k + 2 ^ btW n k - 2)
      (btkXE n bs zs zs1 k) := by
  have hw1 := btW_pos hk
  have hlen := nib_length hzl hk
  have hlen1 := nib_length hz1l hk
  have hU := bitsVal_lt (btkB bs k) (btW n k)
  have h2 := two_le_two_pow hw1
  have hl : 2 ^ btW n k - 2 + btkU n bs k < (eqLevels (nib zs k) (nib zs1 k)).length := by
    rw [eqLevels_length hlen hlen1, pow_succ]; unfold btkU; omega
  have h1 := tbReadsAt_getD ((hrt k (by simpa [btN] using hk)).1) hl
  rw [tb_loadHolds_mul_gen_pow] at h1
  rw [btkU_P bs hk, tb_loadHolds_mul_gen_pow,
    show btkU n bs k + (32 * k + 2 ^ btW n k - 2) = 32 * k + (2 ^ btW n k - 2 + btkU n bs k) by
      omega]
  exact h1

/-- Nibble `k`'s share in memory, at its index. -/
theorem btk_xgLoad {rd : Reader} {eqt gt : E} {n : ℕ} {zs zs1 gs : List E} {bs : List Bool}
    (hgl : gs.length = n) (hrt : RunTables rd eqt gt n zs zs1 gs) {k : ℕ} (hk : k < btN n) :
    LoadHolds rd (gt * btkP bs k (btW n k - 1)) (16 * k) (btkXG n bs gs k) := by
  have hlen := nib_length hgl hk
  have hU := bitsVal_lt (btkB bs k) (btW n k)
  have hl : btkU n bs k < (gTable (nib gs k)).length := by rw [gTable_length hlen]; exact hU
  have h1 := tbReadsAt_getD ((hrt k (by simpa [btN] using hk)).2) hl
  rw [tb_loadHolds_mul_gen_pow] at h1
  rw [btkU_P bs hk, tb_loadHolds_mul_gen_pow, add_comm]
  exact h1

/-- Nibble `k`'s eq weight, as a product. -/
theorem btkXE_prod {n : ℕ} {zs zs1 : List E} {bs : List Bool} (hzl : zs.length = n)
    (hz1l : zs1.length = n) {k : ℕ} (hk : k < btN n) :
    btkXE n bs zs zs1 k = ∏ t ∈ range (btW n k),
      (if bs.getD (4 * k + t) false then zs.getD (4 * k + t) 0 else zs1.getD (4 * k + t) 0) := by
  have hw1 := btW_pos hk
  have hlen := nib_length hzl hk
  have hlen1 := nib_length hz1l hk
  rw [btkXE, btkU, eqLevels_getD (hlen.trans hlen1.symm) hw1 (by omega) (bitsVal_lt _ _)]
  refine prod_congr rfl fun t ht ↦ ?_
  have ht' := mem_range.mp ht
  rw [bitPick, testBit_bitsVal, nib_getD ht', nib_getD ht']
  simp [ht', btkB]

/-- Nibble `k`'s share, as a product. -/
theorem btkXG_prod {n : ℕ} {gs : List E} {bs : List Bool} (hgl : gs.length = n) {k : ℕ}
    (hk : k < btN n) :
    btkXG n bs gs k = ∏ t ∈ range (btW n k),
      (if bs.getD (4 * k + t) false then gs.getD (4 * k + t) 0 else 1) := by
  have hlen := nib_length hgl hk
  rw [btkXG, btkU, gTable_getD hlen (bitsVal_lt _ _)]
  refine prod_congr rfl fun t ht ↦ ?_
  have ht' := mem_range.mp ht
  rw [bitPick, testBit_bitsVal, nib_getD ht']
  simp [ht', btkB]

/-- **`block_selector_tab` is complete** at its 34 specializations. -/
theorem block_selector_tab_complete_holds : block_selector_tab_complete_Spec := by
  intro n hn rd sb eqt gt bs zs zs1 gs hbl hzl hz1l hgl hbr hrt
  obtain ⟨fn, hf, hp, hb⟩ := btFound hn
  set F := btkVal n sb eqt gt bs zs zs1 gs with hF
  have f0 : F 0 = sb := by simp [hF, btkVal]
  have f1 : F 1 = eqt := by simp [hF, btkVal]
  have f2 : F 2 = gt := by simp [hF, btkVal]
  refine (tb_rel_pre hf hb (btPre_noRet n) [sb, eqt, gt] _).mpr ⟨fun x ↦ F x.idx,
    by rw [hp]; simp only [List.map_cons, List.map_nil]; rw [f0, f1, f2], ?_, ?_⟩
  · by_cases h0 : n = 0
    · subst h0
      simp only [btPre, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
      simp [hF, btkVal]
    simp only [btPre, h0, ↓reduceIte]
    rw [tb_holdsList_append_noRet (tb_noRetList_flatten_range _ _ (btNibT_noRet n)),
      tb_holdsList_flatten_range _ _ (btNibT_noRet n)]
    refine ⟨fun k hk ↦ ?_, ?_⟩
    · -- nibble `k`
      have hw1 := btW_pos hk
      have hw4 := btW_le n k
      unfold btNibT
      rw [tb_holdsList_append_noRet (tb_noRetList_flatten_range _ _
          (fun t => btBitT_noRet k t _)), tb_holdsList_flatten_range _ _
          (fun t => btBitT_noRet k t _)]
      refine ⟨fun t ht ↦ ?_, ?_⟩
      · -- bit `t`
        have e : ∀ r, r < 7 → (t = 0 → r < 6) → F (btBitV (btC k) t + r) = btkBit bs k t r :=
          fun r hr hr0 ↦ btkVal_bit h0 sb eqt gt bs zs zs1 gs hk ht hr hr0
        have e0 : F (btBitV (btC k) t) = bitE (btkB bs k t) :=
          btkVal_bit0 h0 sb eqt gt bs zs zs1 gs hk ht
        have hl := btk_bitLoad hbr hbl ht
        by_cases ht0 : t = 0
        · subst ht0
          simp only [btBitT, ↓reduceIte, List.append_nil, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
            and_true]
          rw [f0, e0, e 1 (by norm_num) (fun _ ↦ by norm_num),
            e 2 (by norm_num) (fun _ ↦ by norm_num), e 3 (by norm_num) (fun _ ↦ by norm_num),
            e 4 (by norm_num) (fun _ ↦ by norm_num), e 5 (by norm_num) (fun _ ↦ by norm_num)]
          simp only [btkBit, List.getD_cons_zero, List.getD_cons_succ, btkIm, bitE_mul_self]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | exact hl | trivial
        · have eP : F (btC k + 7 * t - 2) = btkP bs k (t - 1) := by
            have := btkVal_idx h0 sb eqt gt bs zs zs1 gs hk (t := t - 1) (by omega)
            rwa [show btC k + 7 * (t - 1) + 5 = btC k + 7 * t - 2 by omega] at this
          simp only [btBitT, ht0, ↓reduceIte, List.cons_append, List.nil_append, Stmt.HoldsList,
            Stmt.Holds, Atom.Holds, and_true]
          rw [f0, e0, e 1 (by norm_num) (by omega), e 2 (by norm_num) (by omega),
            e 3 (by norm_num) (by omega), e 4 (by norm_num) (by omega),
            e 5 (by norm_num) (by omega), e 6 (by norm_num) (by omega), eP]
          obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
          simp only [btkBit, List.getD_cons_zero, List.getD_cons_succ, btkIm, bitE_mul_self,
            Nat.add_sub_cancel, btkP]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | exact hl | trivial
      · -- the tail
        have hxe := btk_xeLoad (bs := bs) hzl hz1l hrt hk
        have hxg := btk_xgLoad (bs := bs) hgl hrt hk
        have i0 : F (btC k + 7 * btW n k - 1) = eqt * btkP bs k (btW n k - 1) :=
          btkVal_tail0 h0 sb eqt gt bs zs zs1 gs hk
        have iw : F (btC k + 7 * btW n k - 2) = btkP bs k (btW n k - 1) :=
          btkVal_idxw h0 sb eqt gt bs zs zs1 gs hk
        have e : ∀ s, s < (if k = 0 then 4 else 6) →
            F (btC k + 7 * btW n k - 1 + s) = btkTail n eqt gt bs zs zs1 gs k s :=
          fun s hs ↦ btkVal_tail h0 sb eqt gt bs zs zs1 gs hk hs
        by_cases hk0 : k = 0
        · subst hk0
          simp only [↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
          rw [i0, iw, f1, f2, e 1 (by simp), e 2 (by simp), e 3 (by simp)]
          simp only [btkTail, ↓reduceIte, List.getD_cons_zero, List.getD_cons_succ]
          exact ⟨trivial, hxe, trivial, hxg⟩
        · have eS : F (btSel n (k - 1)) = btkS n bs zs zs1 (k - 1) :=
            btkVal_sel h0 sb eqt gt bs zs zs1 gs (k := k - 1) (by omega)
          have eR : F (btRb n (k - 1)) = btkR n bs gs (k - 1) :=
            btkVal_rb h0 sb eqt gt bs zs zs1 gs (k := k - 1) (by omega)
          simp only [hk0, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
          rw [i0, iw, f1, f2, eS, eR, e 1 (by simp [hk0]), e 2 (by simp [hk0]),
            e 3 (by simp [hk0]), e 4 (by simp [hk0]), e 5 (by simp [hk0])]
          simp only [btkTail, hk0, ↓reduceIte, List.getD_cons_zero, List.getD_cons_succ]
          exact ⟨trivial, hxe, trivial, trivial, hxg, trivial⟩
    · -- the copies
      have hN : 1 ≤ btN n := by simp only [btN]; omega
      have eS : F (btSel n (btN n - 1)) = btkS n bs zs zs1 (btN n - 1) :=
        btkVal_sel h0 sb eqt gt bs zs zs1 gs (by omega)
      have eR : F (btRb n (btN n - 1)) = btkR n bs gs (btN n - 1) :=
        btkVal_rb h0 sb eqt gt bs zs zs1 gs (by omega)
      have hC := btC_ge (btN n - 1)
      have hEe := btE_eq n (btN n - 1)
      have v1 : F (btE n (btN n - 1)) = btkS n bs zs zs1 (btN n - 1) := by
        simp [hF, btkVal, h0, show btE n (btN n - 1) ≠ 0 by omega,
          show btE n (btN n - 1) ≠ 1 by omega, show btE n (btN n - 1) ≠ 2 by omega]
      have v2 : F (btE n (btN n - 1) + 1) = btkR n bs gs (btN n - 1) := by
        simp [hF, btkVal, h0, show btE n (btN n - 1) ≠ 0 by omega,
          show btE n (btN n - 1) ≠ 1 by omega]
      simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
      rw [eS, eR, v1, v2]
      exact ⟨rfl, rfl⟩
  · -- the returns
    by_cases h0 : n = 0
    · subst h0
      obtain rfl := List.length_eq_zero_iff.mp hbl
      obtain rfl := List.length_eq_zero_iff.mp hzl
      obtain rfl := List.length_eq_zero_iff.mp hz1l
      obtain rfl := List.length_eq_zero_iff.mp hgl
      simp [btRet, hF, btkVal, bitsEq, bitsPow, tb_word_one]
    · have hN : 1 ≤ btN n := by simp only [btN]; omega
      simp only [btRet, h0, ↓reduceIte, List.map_cons, List.map_nil]
      have hC := btC_ge (btN n - 1)
      have hEe := btE_eq n (btN n - 1)
      have v1 : F (btE n (btN n - 1)) = btkS n bs zs zs1 (btN n - 1) := by
        simp [hF, btkVal, h0, show btE n (btN n - 1) ≠ 0 by omega,
          show btE n (btN n - 1) ≠ 1 by omega, show btE n (btN n - 1) ≠ 2 by omega]
      have v2 : F (btE n (btN n - 1) + 1) = btkR n bs gs (btN n - 1) := by
        simp [hF, btkVal, h0, show btE n (btN n - 1) ≠ 0 by omega,
          show btE n (btN n - 1) ≠ 1 by omega]
      show [F (btE n (btN n - 1)), F (btE n (btN n - 1) + 1)] = _
      rw [v1, v2, btkS_eq, btkR_eq, show btN n - 1 + 1 = btN n by omega,
        bitsEq_eq_prod (m := n) hbl hzl hz1l, bitsPow_eq_prod (m := n) hbl hgl,
        ← bt_reindex (fun i ↦ if bs.getD i false then zs.getD i 0 else zs1.getD i 0) n,
        ← bt_reindex (fun i ↦ if bs.getD i false then gs.getD i 0 else 1) n]
      rw [prod_congr rfl fun k hk ↦ btkXE_prod (bs := bs) hzl hz1l (mem_range.mp hk),
        prod_congr rfl fun k hk ↦ btkXG_prod (bs := bs) hgl (mem_range.mp hk)]

end
end LeanVM.Guest.B1.Tables
