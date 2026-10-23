/-
  LeanVM.Guest.B1.Selectors.ColumnSelectorComplete

  `column_selector` is complete: for an offset `g^o`, `o < 2^28` a multiple of `2^κ`, and the
  opening point's tables in memory, the eq weight of `o`'s bits above `κ` is an outcome of
  `column_selector__L{κ}`.
-/

module

public import LeanVM.Guest.B1.Selectors.ColumnSelector

/-!
# `column_selector` is complete (TRIAGE G #68)

The valuation `cskVal` gives every value of `column_selector__L{κ}`'s body its role: the hint's
28 bits are `o`'s; in nibble `k` (`j = κ/4 + k`), bit `t`'s one, factor constant, product, factor
and running index (`cskP`); then the nibble's pointer into the eq table, its eq weight
(`cskXE`), the running eq product (`cskS`), the pointer into the `g` table, its share (`cskXG`) and
the running `g`-power product (`cskR`); the returned copy. Every statement holds of it: the bits'
pins by booleanity, the weights and shares by the tables in memory, the assertion because the
shares of `o`'s bits above `κ` multiply to `g^o`. The returned value is then the eq weight by
`column_selector`'s soundness.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Finset

@[expose] public section

/-! ## The roles -/

/-- Bit `t` of nibble `k`: bit `4j + 3 - t` of `o`. -/
def cskB (κ o k t : ℕ) : Bool := o.testBit (4 * (κ / 4 + k) + 3 - t)

/-- The running index of nibble `k` after bit `t`. -/
def cskP (κ o k : ℕ) : ℕ → E
  | 0 => word 1 0 0 + bitE (cskB κ o k 0) * word (imFactor 0) 0 0
  | t + 1 => cskP κ o k t * (word 1 0 0 + bitE (cskB κ o k (t + 1)) * word (imFactor (t + 1)) 0 0)

/-- Nibble `k`'s index. -/
def cskU (κ o k : ℕ) : ℕ := bitsVal (cskB κ o k) (csW κ k)

/-- Nibble `k`'s eq weight. -/
def cskXE (κ o : ℕ) (p p1 : List E) (k : ℕ) : E :=
  (eqLevels (topNib p (κ / 4 + k)) (topNib p1 (κ / 4 + k))).getD (2 ^ csW κ k - 2 + cskU κ o k) 0

/-- Nibble `k`'s share. -/
def cskXG (κ o k : ℕ) : E := (gTable (topShares (κ / 4 + k))).getD (cskU κ o k) 0

/-- The running eq product after nibble `k`. -/
def cskS (κ o : ℕ) (p p1 : List E) : ℕ → E
  | 0 => cskXE κ o p p1 0
  | k + 1 => cskS κ o p p1 k * cskXE κ o p p1 (k + 1)

/-- The running `g`-power product after nibble `k`. -/
def cskR (κ o : ℕ) : ℕ → E
  | 0 => cskXG κ o 0
  | k + 1 => cskR κ o k * cskXG κ o (k + 1)

/-- Value `r` of bit `t` of nibble `k`. -/
def cskBit (κ o k t r : ℕ) : E :=
  [word 1 0 0, word (imFactor t) 0 0, bitE (cskB κ o k t) * word (imFactor t) 0 0,
    word 1 0 0 + bitE (cskB κ o k t) * word (imFactor t) 0 0, cskP κ o k t].getD r 0

/-- Value `s` of nibble `k`'s tail. -/
def cskTail (κ o : ℕ) (se sg : E) (p p1 : List E) (k s : ℕ) : E :=
  if k = 0 then
    [se * cskP κ o k (csW κ k - 1), cskXE κ o p p1 k, sg * cskP κ o k (csW κ k - 1),
      cskXG κ o k].getD s 0
  else
    [se * cskP κ o k (csW κ k - 1), cskXE κ o p p1 k, cskS κ o p p1 (k - 1) * cskXE κ o p p1 k,
      sg * cskP κ o k (csW κ k - 1), cskXG κ o k, cskR κ o (k - 1) * cskXG κ o k].getD s 0

/-- Value `x` of nibble `k`. -/
def cskRole (κ o : ℕ) (se sg : E) (p p1 : List E) (k x : ℕ) : E :=
  if x + 1 < 5 * csW κ k then
    cskBit κ o k ((x + 1) / 5) (if (x + 1) / 5 = 0 then x else x + 1 - 5 * ((x + 1) / 5))
  else cskTail κ o se sg p p1 k (x + 1 - 5 * csW κ k)

/-- The length of nibble `k`'s values. -/
def cskLen (κ k : ℕ) : ℕ := if k = 0 then 5 * csW κ k + 3 else 5 * csW κ k + 5

/-- **Value `x` of `column_selector__L{κ}`.** -/
def cskVal (κ o : ℕ) (se sg : E) (p p1 : List E) (x : ℕ) : E :=
  if x = 0 then gen ^ o else if x = 1 then se else if x = 2 then sg
  else if x < 31 then bitE (o.testBit (x - 3))
  else if κ = 28 then word 1 0 0
  else if x = csC κ (csN κ) then cskS κ o p p1 (csN κ - 1)
  else cskRole κ o se sg p p1 (if x < csC κ 1 then 0 else (x - csC κ 1) / 25 + 1)
    (x - csC κ (if x < csC κ 1 then 0 else (x - csC κ 1) / 25 + 1))

/-! ## The arithmetic of the layout -/

theorem csC_succ (κ k : ℕ) : csC κ (k + 1) = csC κ k + cskLen κ k := by
  unfold csC cskLen
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp; omega
  · simp only [show k ≠ 0 by omega, show k + 1 ≠ 0 by omega, ↓reduceIte, csW]; omega

theorem csC_ge (κ k : ℕ) : 31 ≤ csC κ k := by unfold csC; split <;> omega

theorem cskLen_bounds (κ k : ℕ) : cskLen κ k ≤ (if k = 0 then 23 else 25) ∧ 8 ≤ cskLen κ k := by
  obtain ⟨h1, h4⟩ := csW_bounds κ k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [cskLen]; omega
  · simp [cskLen, show k ≠ 0 by omega, csW]

theorem csC_one (κ : ℕ) : csC κ 1 = 31 + cskLen κ 0 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, csC_succ]; simp [csC]

theorem csC_k (κ k : ℕ) (hk : 1 ≤ k) : csC κ k = csC κ 1 + 25 * (k - 1) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  induction k' with
  | zero => simp
  | succ k' ih =>
    rw [csC_succ, ih (by omega)]
    simp [cskLen, csW]; omega

theorem csC_mono (κ : ℕ) {k m : ℕ} (h : k ≤ m) : csC κ k ≤ csC κ m := by
  induction m with
  | zero => rw [show k = 0 by omega]
  | succ m ih =>
    rcases Nat.lt_or_ge k (m + 1) with h' | h'
    · rw [csC_succ]; have := ih (by omega); omega
    · rw [show k = m + 1 by omega]

/-- **Value `x` of nibble `k`.** -/
theorem cskVal_at {κ : ℕ} (hκ : κ ≠ 28) (o : ℕ) (se sg : E) (p p1 : List E) {k x : ℕ}
    (hk : k < csN κ) (hx : x < cskLen κ k) :
    cskVal κ o se sg p p1 (csC κ k + x) = cskRole κ o se sg p p1 k x := by
  have hC := csC_ge κ k
  have hN : csC κ k + x < csC κ (csN κ) := by
    have := csC_mono κ (k := k + 1) (m := csN κ) (by omega)
    rw [csC_succ] at this; omega
  obtain ⟨hL, -⟩ := cskLen_bounds κ k
  have hdec : (if csC κ k + x < csC κ 1 then 0 else (csC κ k + x - csC κ 1) / 25 + 1) = k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [csC_one]; simp [csC] at hx ⊢; omega
    · rw [csC_k κ k hk0]
      simp only [show k ≠ 0 by omega, ↓reduceIte] at hL
      simp only [show ¬ csC κ 1 + 25 * (k - 1) + x < csC κ 1 by omega, ↓reduceIte]; omega
  have h0 : csC κ k + x ≠ 0 := by omega
  have h1 : csC κ k + x ≠ 1 := by omega
  have h2 : csC κ k + x ≠ 2 := by omega
  have h3 : ¬ csC κ k + x < 31 := by omega
  have h4 : csC κ k + x ≠ csC κ (csN κ) := by omega
  simp only [cskVal, h0, h1, h2, h3, hκ, h4, ↓reduceIte]
  rw [hdec, Nat.add_sub_cancel_left]

/-- Bit `t`'s values. -/
theorem cskVal_bit {κ : ℕ} (hκ : κ ≠ 28) (o : ℕ) (se sg : E) (p p1 : List E)
    {k t r : ℕ} (hk : k < csN κ) (ht : t < csW κ k) (hr : r < 5) (hr0 : t = 0 → r < 4) :
    cskVal κ o se sg p p1 (csC κ k + (if t = 0 then r else 5 * t - 1 + r)) = cskBit κ o k t r := by
  obtain ⟨hw1, hw⟩ := csW_bounds κ k
  have hlen : (if t = 0 then r else 5 * t - 1 + r) < cskLen κ k := by
    have hL : 5 * csW κ k + 3 ≤ cskLen κ k := by unfold cskLen; split <;> omega
    by_cases h' : t = 0
    · simp only [h', ↓reduceIte]; have := hr0 h'; omega
    · simp only [h', ↓reduceIte]; omega
  have hlt : (if t = 0 then r else 5 * t - 1 + r) + 1 < 5 * csW κ k := by
    by_cases h' : t = 0
    · simp only [h', ↓reduceIte]; have := hr0 h'; omega
    · simp only [h', ↓reduceIte]; omega
  rw [cskVal_at hκ o se sg p p1 hk hlen, cskRole]
  simp only [hlt, ↓reduceIte]
  by_cases h0 : t = 0
  · subst h0
    simp only [↓reduceIte]
    rw [show (r + 1) / 5 = 0 by have := hr0 rfl; omega]
    simp
  · simp only [h0, ↓reduceIte]
    rw [show (5 * t - 1 + r + 1) / 5 = t by omega]
    simp only [h0, ↓reduceIte]
    congr 1; omega

/-- The tail's values. -/
theorem cskVal_tail {κ : ℕ} (hκ : κ ≠ 28) (o : ℕ) (se sg : E) (p p1 : List E)
    {k s : ℕ} (hk : k < csN κ) (hs : s < (if k = 0 then 4 else 6)) :
    cskVal κ o se sg p p1 (csC κ k + 5 * csW κ k - 1 + s) = cskTail κ o se sg p p1 k s := by
  obtain ⟨hw1, -⟩ := csW_bounds κ k
  have hlen : 5 * csW κ k - 1 + s < cskLen κ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · simp [cskLen] at hs ⊢; omega
    · simp [cskLen, show k ≠ 0 by omega] at hs ⊢; omega
  rw [show csC κ k + 5 * csW κ k - 1 + s = csC κ k + (5 * csW κ k - 1 + s) by omega,
    cskVal_at hκ o se sg p p1 hk hlen, cskRole]
  simp only [show ¬ 5 * csW κ k - 1 + s + 1 < 5 * csW κ k by omega, ↓reduceIte]
  congr 1; omega

/-- The hinted bits. -/
theorem cskVal_hint {κ : ℕ} (o : ℕ) (se sg : E) (p p1 : List E) {i : ℕ} (hi : i < 28) :
    cskVal κ o se sg p p1 (csBitV i) = bitE (o.testBit i) := by
  simp only [cskVal, csBitV, show 3 + i ≠ 0 by omega, show 3 + i ≠ 1 by omega,
    show 3 + i ≠ 2 by omega, show 3 + i < 31 by omega, ↓reduceIte, Nat.add_sub_cancel_left]

/-! ## The products -/

theorem cskP_eq (κ o k : ℕ) : ∀ t, t < 34 →
    cskP κ o k t = gen ^ bitsVal (cskB κ o k) (t + 1)
  | 0, _ => by
    rw [← prod_bitE_gen_pow, prod_range_one, cskP, imFactor_eq (by norm_num), tb_word_one,
      add_comm (gen ^ 2 ^ 0) 1]
  | t + 1, ht => by
    rw [cskP, cskP_eq κ o k t (by omega), ← prod_bitE_gen_pow, ← prod_bitE_gen_pow,
      prod_range_succ _ (t + 1), imFactor_eq ht, tb_word_one, add_comm (gen ^ 2 ^ (t + 1)) 1]

theorem cskU_P (κ o k : ℕ) : cskP κ o k (csW κ k - 1) = gen ^ cskU κ o k := by
  obtain ⟨hw1, hw4⟩ := csW_bounds κ k
  rw [cskP_eq κ o k _ (by omega), show csW κ k - 1 + 1 = csW κ k by omega]; rfl

theorem cskR_eq (κ o : ℕ) : ∀ k, cskR κ o k = ∏ m ∈ range (k + 1), cskXG κ o m
  | 0 => by simp [cskR]
  | k + 1 => by rw [cskR, cskR_eq κ o k, prod_range_succ _ (k + 1)]

/-- Nibble `k`'s share, as a product of `g` to its bits. -/
theorem cskXG_prod (κ o k : ℕ) :
    cskXG κ o k = ∏ t ∈ range (csW κ k),
      gen ^ (2 ^ (4 * (κ / 4 + k) + 3 - t) * (o.testBit (4 * (κ / 4 + k) + 3 - t)).toNat) := by
  obtain ⟨hw1, hw4⟩ := csW_bounds κ k
  have hU := bitsVal_lt (cskB κ o k) (csW κ k)
  have hU16 : cskU κ o k < 2 ^ 4 :=
    lt_of_lt_of_le hU (Nat.pow_le_pow_right (by norm_num) hw4)
  rw [cskXG, gTable_getD (n := 4) (by simp [topShares]) hU16,
    show range 4 = range (csW κ k + (4 - csW κ k)) by rw [Nat.add_sub_of_le hw4], prod_range_add]
  have hrest : ∏ x ∈ range (4 - csW κ k),
      bitPick (cskU κ o k) (csW κ k + x) ((topShares (κ / 4 + k)).getD (csW κ k + x) 0) 1 = 1 :=
    prod_eq_one fun x _ => by simp [bitPick, cskU, testBit_bitsVal]
  rw [hrest, mul_one]
  refine prod_congr rfl fun t ht => ?_
  have ht' := mem_range.mp ht
  rw [bitPick, cskU, testBit_bitsVal, topShares_getD (by omega)]
  simp only [ht', decide_true, Bool.true_and, cskB]
  cases o.testBit (4 * (κ / 4 + k) + 3 - t) <;> simp

/-- **The shares multiply to `g^o`.** -/
theorem cskR_last {κ : ℕ} (hκ : κ < 28) {o : ℕ} (ho : o < 2 ^ 28) (hd : 2 ^ κ ∣ o) :
    cskR κ o (csN κ - 1) = gen ^ o := by
  have hN : 1 ≤ csN κ := by unfold csN; omega
  rw [cskR_eq, show csN κ - 1 + 1 = csN κ by omega,
    prod_congr rfl (fun k _ ↦ cskXG_prod κ o k),
    cs_reindex (fun i ↦ gen ^ (2 ^ i * (o.testBit i).toNat)) hκ,
    prod_gen_pow_bits κ (fun i ↦ o.testBit (κ + i)) (28 - κ)]
  obtain ⟨q, rfl⟩ := hd
  have hq : q < 2 ^ (28 - κ) := by
    have : 2 ^ κ * q < 2 ^ κ * 2 ^ (28 - κ) := by
      rw [← pow_add, Nat.add_sub_of_le (by omega)]; exact ho
    exact Nat.lt_of_mul_lt_mul_left this
  have hb : (fun i ↦ (2 ^ κ * q).testBit (κ + i)) = q.testBit := by
    funext i
    rw [Nat.testBit_two_pow_mul]
    simp
  rw [hb, bitsVal_testBit hq]

/-! ## The body -/

theorem cskVal_idx {κ : ℕ} (hκ : κ ≠ 28) (o : ℕ) (se sg : E) (p p1 : List E) {k t : ℕ}
    (hk : k < csN κ) (ht : t < csW κ k) :
    cskVal κ o se sg p p1 (csC κ k + 5 * t + 3) = cskP κ o k t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht0
  · have := cskVal_bit hκ o se sg p p1 hk ht (r := 3) (by norm_num) (fun _ ↦ by norm_num)
    simp only [↓reduceIte] at this
    rw [show csC κ k + 5 * 0 + 3 = csC κ k + 3 by omega, this]; rfl
  · have := cskVal_bit hκ o se sg p p1 hk ht (r := 4) (by norm_num) (by omega)
    simp only [show t ≠ 0 by omega, ↓reduceIte] at this
    rw [show csC κ k + 5 * t + 3 = csC κ k + (5 * t - 1 + 4) by omega, this]; rfl

theorem cskVal_sel {κ : ℕ} (hκ : κ ≠ 28) (o : ℕ) (se sg : E) (p p1 : List E) {k : ℕ}
    (hk : k < csN κ) : cskVal κ o se sg p p1 (csSel κ k) = cskS κ o p p1 k := by
  obtain ⟨hw1, -⟩ := csW_bounds κ k
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · have := cskVal_tail hκ o se sg p p1 hk (s := 1) (by simp)
    rw [show csC κ 0 + 5 * csW κ 0 - 1 + 1 = csSel κ 0 by simp [csSel]; omega] at this
    rw [this]; simp [cskTail, cskS]
  · have := cskVal_tail hκ o se sg p p1 hk (s := 2) (by simp [show k ≠ 0 by omega])
    rw [show csC κ k + 5 * csW κ k - 1 + 2 = csSel κ k by
      simp [csSel, csW, show k ≠ 0 by omega]] at this
    rw [this]
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp [cskTail, cskS]

theorem cskVal_rb {κ : ℕ} (hκ : κ ≠ 28) (o : ℕ) (se sg : E) (p p1 : List E) {k : ℕ}
    (hk : k < csN κ) : cskVal κ o se sg p p1 (csRb κ k) = cskR κ o k := by
  obtain ⟨hw1, -⟩ := csW_bounds κ k
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · have := cskVal_tail hκ o se sg p p1 hk (s := 3) (by simp)
    rw [show csC κ 0 + 5 * csW κ 0 - 1 + 3 = csRb κ 0 by simp [csRb]; omega] at this
    rw [this]; simp [cskTail, cskR]
  · have := cskVal_tail hκ o se sg p p1 hk (s := 5) (by simp [show k ≠ 0 by omega])
    rw [show csC κ k + 5 * csW κ k - 1 + 5 = csRb κ k by
      simp [csRb, csW, show k ≠ 0 by omega]] at this
    rw [this]
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp [cskTail, cskR]

/-- Nibble `k`'s eq weight in memory, at its index. -/
theorem csk_xeLoad {rd : Reader} {se : E} {p p1 : List E} (hp : p.length = 28)
    (hp1 : p1.length = 28) (hE : EqTabsAt rd se p p1) {κ o k : ℕ} (hk : k < csN κ) :
    LoadHolds rd (se * cskP κ o k (csW κ k - 1)) (30 * (κ / 4 + k) + 2 ^ csW κ k - 2)
      (cskXE κ o p p1 k) := by
  have hj : κ / 4 + k < 7 := by simp only [csN] at hk; omega
  obtain ⟨hw1, hw4⟩ := csW_bounds κ k
  have hlen : (topNib p (κ / 4 + k)).length = 4 := by simp [topNib, nib, hp]; omega
  have hlen1 : (topNib p1 (κ / 4 + k)).length = 4 := by simp [topNib, nib, hp1]; omega
  have hU := bitsVal_lt (cskB κ o k) (csW κ k)
  have hl : 2 ^ csW κ k - 2 + cskU κ o k <
      (eqLevels (topNib p (κ / 4 + k)) (topNib p1 (κ / 4 + k))).length := by
    rw [eqLevels_length hlen hlen1]
    have : 2 ^ (csW κ k + 1) ≤ 2 ^ (4 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := two_le_two_pow hw1
    unfold cskU
    rw [pow_succ] at *
    omega
  have h1 := tbReadsAt_getD (hE _ hj) hl
  rw [tb_loadHolds_mul_gen_pow] at h1
  have h2 := two_le_two_pow hw1
  rw [cskU_P, tb_loadHolds_mul_gen_pow,
    show cskU κ o k + (30 * (κ / 4 + k) + 2 ^ csW κ k - 2) =
      30 * (κ / 4 + k) + (2 ^ csW κ k - 2 + cskU κ o k) by omega]
  exact h1

/-- Nibble `k`'s share in memory, at its index. -/
theorem csk_xgLoad {rd : Reader} {sg : E} (hG : GTabsAt rd sg) {κ o k : ℕ} (hk : k < csN κ) :
    LoadHolds rd (sg * cskP κ o k (csW κ k - 1)) (16 * (κ / 4 + k)) (cskXG κ o k) := by
  have hj : κ / 4 + k < 7 := by simp only [csN] at hk; omega
  obtain ⟨hw1, hw4⟩ := csW_bounds κ k
  have hU16 : cskU κ o k < 2 ^ 4 :=
    lt_of_lt_of_le (bitsVal_lt _ _) (Nat.pow_le_pow_right (by norm_num) hw4)
  have hl : cskU κ o k < (gTable (topShares (κ / 4 + k))).length := by
    rw [gTable_length (n := 4) (by simp [topShares])]; exact hU16
  have h1 := tbReadsAt_getD (hG _ hj) hl
  rw [tb_loadHolds_mul_gen_pow] at h1
  rw [cskU_P, tb_loadHolds_mul_gen_pow, add_comm]
  exact h1

/-- **`column_selector`'s body holds** of the valuation. -/
theorem csk_rel {κ : ℕ} (hκ : κ < 29) {rd : Reader} {o : ℕ} {se sg : E} {p p1 : List E}
    (ho : o < 2 ^ 28) (hd : 2 ^ κ ∣ o) (hp : p.length = 28) (hp1 : p1.length = 28)
    (hE : EqTabsAt rd se p p1) (hG : GTabsAt rd sg) :
    coreProgram.Rel rd (lName "column_selector" κ) [gen ^ o, se, sg]
      [cskVal κ o se sg p p1 (csRet κ)] := by
  obtain ⟨fn, hf, hfp, hb⟩ := csFound hκ
  set F := cskVal κ o se sg p p1 with hF
  have f0 : F 0 = gen ^ o := by simp [hF, cskVal]
  have f1 : F 1 = se := by simp [hF, cskVal]
  have f2 : F 2 = sg := by simp [hF, cskVal]
  refine (tb_rel_pre hf hb (csPre_noRet κ) [gen ^ o, se, sg] _).mpr ⟨fun x ↦ F x.idx,
    by rw [hfp]; simp only [List.map_cons, List.map_nil]; rw [f0, f1, f2], ?_, rfl⟩
  by_cases h28 : κ = 28
  · subst h28
    have ho0 : o = 0 := by
      obtain ⟨q, rfl⟩ := hd
      have : q = 0 := by
        by_contra hq
        have : 2 ^ 28 * 1 ≤ 2 ^ 28 * q := Nat.mul_le_mul_left _ (by omega)
        omega
      simp [this]
    subst ho0
    simp only [csPre, ↓reduceIte, csHint, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true,
      true_and]
    have e31 : F 31 = word 1 0 0 := by simp [hF, cskVal]
    have e32 : F 32 = word 1 0 0 := by simp [hF, cskVal]
    rw [e31, e32, f0, tb_word_one, pow_zero]
    exact ⟨rfl, e_add_self 1, rfl⟩
  have hκ' : κ < 28 := by omega
  simp only [csPre, h28, ↓reduceIte, csHint, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and]
  rw [tb_holdsList_append_noRet (csNibs_noRet κ _),
    tb_holdsList_flatten_range _ _ (csNibT_noRet κ)]
  have hN1 : 1 ≤ csN κ := by unfold csN; omega
  refine ⟨fun k hk ↦ ?_, ?_⟩
  · -- nibble `k`
    obtain ⟨hw1, hw4⟩ := csW_bounds κ k
    have hj : κ / 4 + k < 7 := by simp only [csN] at hk; omega
    unfold csNibT
    rw [tb_holdsList_append_noRet (csBits_noRet _ _ _),
      tb_holdsList_flatten_range _ _ (fun t => csBitT_noRet _ t _)]
    refine ⟨fun t ht ↦ ?_, ?_⟩
    · -- bit `t`
      have hbi : F (csBitV (4 * (κ / 4 + k) + 3 - t)) = bitE (cskB κ o k t) :=
        cskVal_hint o se sg p p1 (by omega)
      have hpin : F (csBitV (4 * (κ / 4 + k) + 3 - t)) =
          F (csBitV (4 * (κ / 4 + k) + 3 - t)) * F (csBitV (4 * (κ / 4 + k) + 3 - t)) := by
        rw [hbi, bitE_mul_self]
      by_cases ht0 : t = 0
      · subst ht0
        have e : ∀ r, r < 4 → F (csC κ k + r) = cskBit κ o k 0 r := fun r hr ↦ by
          have := cskVal_bit h28 o se sg p p1 hk ht (r := r) (by omega) (fun _ ↦ hr)
          simpa using this
        have e0 : F (csC κ k) = cskBit κ o k 0 0 := by simpa using e 0 (by norm_num)
        simp only [csBitT, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
        rw [e0, e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num), hbi]
        rw [hbi] at hpin
        simp only [cskBit, List.getD_cons_zero, List.getD_cons_succ]
        exact ⟨hpin, trivial, trivial, trivial, trivial⟩
      · have e : ∀ r, r < 5 → F (csC κ k + 5 * t - 1 + r) = cskBit κ o k t r := fun r hr ↦ by
          have := cskVal_bit h28 o se sg p p1 hk ht (r := r) hr (by omega)
          simp only [ht0, ↓reduceIte] at this
          rwa [show csC κ k + (5 * t - 1 + r) = csC κ k + 5 * t - 1 + r by omega] at this
        have e0 : F (csC κ k + 5 * t - 1) = cskBit κ o k t 0 := by simpa using e 0 (by norm_num)
        have eP : F (csC κ k + 5 * t - 2) = cskP κ o k (t - 1) := by
          have := cskVal_idx h28 o se sg p p1 hk (t := t - 1) (by omega)
          rwa [show csC κ k + 5 * (t - 1) + 3 = csC κ k + 5 * t - 2 by omega] at this
        simp only [csBitT, ht0, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
        rw [e0, e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num), e 4 (by norm_num), eP,
          hbi]
        rw [hbi] at hpin
        obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        simp only [cskBit, List.getD_cons_zero, List.getD_cons_succ, Nat.add_sub_cancel, cskP]
        exact ⟨hpin, trivial, trivial, trivial, trivial, trivial⟩
    · -- the tail
      have hxe := csk_xeLoad (o := o) hp hp1 hE hk
      have hxg := csk_xgLoad (o := o) hG hk
      have e : ∀ s, s < (if k = 0 then 4 else 6) →
          F (csC κ k + 5 * csW κ k - 1 + s) = cskTail κ o se sg p p1 k s :=
        fun s hs ↦ cskVal_tail h28 o se sg p p1 hk hs
      have i0 : F (csC κ k + 5 * csW κ k - 1) = se * cskP κ o k (csW κ k - 1) := by
        have := e 0 (by split <;> norm_num)
        rw [Nat.add_zero] at this
        rw [this]; unfold cskTail; split <;> rfl
      have iw : F (csC κ k + 5 * csW κ k - 2) = cskP κ o k (csW κ k - 1) := by
        have := cskVal_idx h28 o se sg p p1 hk (t := csW κ k - 1) (by omega)
        rwa [show csC κ k + 5 * (csW κ k - 1) + 3 = csC κ k + 5 * csW κ k - 2 by omega] at this
      by_cases hk0 : k = 0
      · subst hk0
        simp only [↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, Nat.add_zero]
        rw [i0, iw, f1, f2, e 1 (by simp), e 2 (by simp), e 3 (by simp)]
        simp only [cskTail, ↓reduceIte, List.getD_cons_zero, List.getD_cons_succ]
        exact ⟨trivial, hxe, trivial, hxg⟩
      · have eS : F (csSel κ (k - 1)) = cskS κ o p p1 (k - 1) :=
          cskVal_sel h28 o se sg p p1 (k := k - 1) (by omega)
        have eR : F (csRb κ (k - 1)) = cskR κ o (k - 1) :=
          cskVal_rb h28 o se sg p p1 (k := k - 1) (by omega)
        simp only [hk0, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
        rw [i0, iw, f1, f2, eS, eR, e 1 (by simp [hk0]), e 2 (by simp [hk0]),
          e 3 (by simp [hk0]), e 4 (by simp [hk0]), e 5 (by simp [hk0])]
        simp only [cskTail, hk0, ↓reduceIte, List.getD_cons_zero, List.getD_cons_succ]
        exact ⟨trivial, hxe, trivial, trivial, hxg, trivial⟩
  · -- the assertion and the copy
    have eS : F (csSel κ (csN κ - 1)) = cskS κ o p p1 (csN κ - 1) :=
      cskVal_sel h28 o se sg p p1 (by omega)
    have eR : F (csRb κ (csN κ - 1)) = cskR κ o (csN κ - 1) :=
      cskVal_rb h28 o se sg p p1 (by omega)
    have hC := csC_ge κ (csN κ)
    have eC : F (csC κ (csN κ)) = cskS κ o p p1 (csN κ - 1) := by
      simp [hF, cskVal, h28, show csC κ (csN κ) ≠ 0 by omega, show csC κ (csN κ) ≠ 1 by omega,
        show csC κ (csN κ) ≠ 2 by omega, show ¬ csC κ (csN κ) < 31 by omega]
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    rw [eS, eR, eC, f0, cskR_last hκ' ho hd]
    exact ⟨e_add_self _, rfl⟩

/-- **`column_selector` is complete** at its 29 specializations. -/
theorem column_selector_complete_holds : column_selector_complete_Spec := by
  intro κ hκ rd o se sg p p1 ho hd hp hp1 hE hG
  have hR := csk_rel hκ ho hd hp hp1 hE hG
  obtain ⟨o', ho', -, hoff, hsel⟩ := column_selector_sound hκ hR hG
  have : o' = o := gen_pow_inj (by omega) (by omega) hoff.symm
  subst this
  rw [hsel p p1 hp hp1 hE] at hR
  exact hR

end
end LeanVM.Guest.B1.Tables
