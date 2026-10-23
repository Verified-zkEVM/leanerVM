/-
  LeanVM.Guest.B1.Selectors.ColumnSelector

  B1 for `column_selector`: its 29 specializations certify a column's offset aligned below
  `2^28` and return the eq weight of its bits above `κ`, a nibble at a time off the opening
  point's tables.
-/

module

public import LeanVM.Guest.B1.Selectors.TableLemmas

/-!
# `column_selector` (TRIAGE G #68)

`column_selector(offset, sel_eq, sel_g, κ)` (G:3025-3049) hints the 28 bits of `offset`'s exponent
and, for each nibble `j` from `κ / 4` to `6` (the first `4j + 4 - κ` wide, the others four), pins
its bits `4j + 3 - t` (`t < w`), folds them into `g^u` (`u`'s bit `t` the bit `4j + 3 - t`), reads
the nibble's eq weight at `sel_eq·g^u` (offset `30j + 2^w - 2`) and its share of `g^offset` at
`sel_g·g^u` (offset `16j`), and multiplies them up; then asserts the rebuilt power is `offset`.

The specialization `column_selector__L{κ}` is the template `csBody κ` (`csFound`, by kernel
evaluation for all `κ < 29`): the hint, nibble `k` from value `csC κ k` (`csNibT`, its bits by
`csBitT`), the assertion and the copy of the selector.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The template -/

/-- The number of nibbles of `column_selector__L{κ}`. -/
def csN (κ : ℕ) : ℕ := 7 - κ / 4

/-- The width of nibble `k`. -/
def csW (κ k : ℕ) : ℕ := if k = 0 then 4 * (κ / 4) + 4 - κ else 4

/-- The first value of nibble `k`. -/
def csC (κ k : ℕ) : ℕ := if k = 0 then 31 else 31 + 5 * csW κ 0 + 3 + 25 * (k - 1)

/-- The selector product after nibble `k`. -/
def csSel (κ k : ℕ) : ℕ := if k = 0 then csC κ 0 + 5 * csW κ 0 else csC κ k + 21

/-- The rebuilt product after nibble `k`. -/
def csRb (κ k : ℕ) : ℕ := if k = 0 then csC κ 0 + 5 * csW κ 0 + 2 else csC κ k + 24

/-- The hinted bit `i` of the offset's exponent: value `3 + i`. -/
def csBitV (i : ℕ) : ℕ := 3 + i

/-- Bit `t` of nibble `j`, from value `c`: the pin, then the factor `1 + b·(1 + g^(2^t))`
multiplied into the index. -/
def csBitT (j t c : ℕ) : List Stmt :=
  let bi := csBitV (4 * j + 3 - t)
  if t = 0 then
    [.atom (.mul (.n bi) (.n bi) (.n bi)), .atom (.const (.n c) (word 1 0 0)),
      .atom (.const (.n (c + 1)) (word (imFactor 0) 0 0)),
      .atom (.mul (.n (c + 2)) (.n bi) (.n (c + 1))), .atom (.add (.n (c + 3)) (.n c) (.n (c + 2)))]
  else
    let d := c + 5 * t - 1
    [.atom (.mul (.n bi) (.n bi) (.n bi)), .atom (.const (.n d) (word 1 0 0)),
      .atom (.const (.n (d + 1)) (word (imFactor t) 0 0)),
      .atom (.mul (.n (d + 2)) (.n bi) (.n (d + 1))), .atom (.add (.n (d + 3)) (.n d) (.n (d + 2))),
      .atom (.mul (.n (d + 4)) (.n (c + 5 * t - 2)) (.n (d + 3)))]

/-- Nibble `k` of `column_selector__L{κ}`. -/
def csNibT (κ k : ℕ) : List Stmt :=
  let j := κ / 4 + k
  let w := csW κ k
  let c := csC κ k
  let c1 := c + 5 * w - 1
  let idx := c + 5 * w - 2
  ((List.range w).map fun t ↦ csBitT j t c).flatten ++
    if k = 0 then
      [.atom (.mul (.n c1) (.n 1) (.n idx)), .atom (.load (.n (c1 + 1)) (.n c1) (30 * j + 2 ^ w - 2)),
        .atom (.mul (.n (c1 + 2)) (.n 2) (.n idx)),
        .atom (.load (.n (c1 + 3)) (.n (c1 + 2)) (16 * j))]
    else
      [.atom (.mul (.n c1) (.n 1) (.n idx)), .atom (.load (.n (c1 + 1)) (.n c1) (30 * j + 2 ^ w - 2)),
        .atom (.mul (.n (c1 + 2)) (.n (csSel κ (k - 1))) (.n (c1 + 1))),
        .atom (.mul (.n (c1 + 3)) (.n 2) (.n idx)),
        .atom (.load (.n (c1 + 4)) (.n (c1 + 3)) (16 * j)),
        .atom (.mul (.n (c1 + 5)) (.n (csRb κ (k - 1))) (.n (c1 + 4)))]

/-- The hint of the 28 bits. -/
def csHint : Stmt :=
  .atom (.hint (.bitsExp (.n 0) 28 (.stack ((List.range 28).map fun i ↦ .n (csBitV i)))))

/-- `column_selector__L{κ}`'s statements before its `ret`, the hint first. -/
def csPre (κ : ℕ) : List Stmt :=
  csHint :: if κ = 28 then
    [.atom (.const (.n 31) (word 1 0 0)), .atom (.assertEq (.n 31) (.n 0)),
      .atom (.const (.n 32) (word 1 0 0))]
  else ((List.range (csN κ)).map (csNibT κ)).flatten ++
    [.atom (.assertEq (.n (csRb κ (csN κ - 1))) (.n 0)),
      .atom (.copy (.n (csC κ (csN κ))) (.n (csSel κ (csN κ - 1))))]

/-- The value `column_selector__L{κ}` returns. -/
def csRet (κ : ℕ) : ℕ := if κ = 28 then 32 else csC κ (csN κ)

/-- The function found by name is the template. -/
noncomputable def csCheck (κ : ℕ) : Bool :=
  match coreProgram.find? (lName "column_selector" κ) with
  | some fn => decide (fn.params = [.n 0, .n 1, .n 2]) &&
      tbStmtsEqb fn.body (csPre κ ++ [.ret [.n (csRet κ)]])
  | none => false

theorem csCheck_all : (List.range 29).all csCheck = true := by decide +kernel

theorem csFound {κ : ℕ} (hκ : κ < 29) : ∃ fn : Fn,
    coreProgram.find? (lName "column_selector" κ) = some fn ∧ fn.params = [.n 0, .n 1, .n 2] ∧
      fn.body = csPre κ ++ [.ret [.n (csRet κ)]] := by
  have h := List.all_eq_true.mp csCheck_all κ (List.mem_range.mpr hκ)
  unfold csCheck at h
  split at h
  · rename_i fn hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fn, hf, h.1, tbStmtsEqb_sound h.2⟩
  · exact absurd h (by simp)

theorem csBitT_noRet (j t c : ℕ) : Stmt.noRetList (csBitT j t c) = true := by
  unfold csBitT; split <;> rfl

theorem csBits_noRet (j c : ℕ) : ∀ l : List ℕ, Stmt.noRetList (l.map fun t ↦ csBitT j t c).flatten = true
  | [] => rfl
  | t :: l => by
    rw [List.map_cons, List.flatten_cons, tb_noRetList_append, csBitT_noRet, csBits_noRet j c l]; rfl

theorem csNibT_noRet (κ k : ℕ) : Stmt.noRetList (csNibT κ k) = true := by
  unfold csNibT
  rw [tb_noRetList_append, csBits_noRet]
  split <;> rfl

theorem csNibs_noRet (κ : ℕ) : ∀ l : List ℕ, Stmt.noRetList (l.map (csNibT κ)).flatten = true
  | [] => rfl
  | t :: l => by
    rw [List.map_cons, List.flatten_cons, tb_noRetList_append, csNibT_noRet, csNibs_noRet κ l]; rfl

theorem csPre_noRet (κ : ℕ) : Stmt.noRetList (csPre κ) = true := by
  unfold csPre
  split
  · rfl
  · rw [Stmt.noRetList, tb_noRetList_append, csNibs_noRet]; rfl

/-! ## A nibble -/

section Sem

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- The factor of bit `t` of the index: `1 + b·(1 + g^(2^t))`. -/
def csFactor (b : E) (t : ℕ) : E := 1 + b * (1 + gen ^ 2 ^ t)

/-- **The bits of a nibble**: each pinned, and the index the product of their factors. -/
theorem holds_csBits {j w c : ℕ} (hw : w ≤ 4)
    (h : Stmt.HoldsList C rd σ ((List.range w).map fun t ↦ csBitT j t c).flatten True kret) :
    (∀ t < w, σ (.n (csBitV (4 * j + 3 - t))) * σ (.n (csBitV (4 * j + 3 - t))) =
      σ (.n (csBitV (4 * j + 3 - t)))) ∧
    ∀ t < w, σ (.n (c + 5 * t + 3)) =
      ∏ s ∈ Finset.range (t + 1), csFactor (σ (.n (csBitV (4 * j + 3 - s)))) s := by
  rw [holdsList_flatten _ (fun b hb => by
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hb; exact csBitT_noRet j t c)] at h
  have hb : ∀ t < w, Stmt.HoldsList C rd σ (csBitT j t c) True kret :=
    fun t ht => h.1 _ (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩)
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · have := hb t ht
    unfold csBitT at this
    split at this <;>
    · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
      exact this.1.symm
  · induction t with
    | zero =>
      have := hb 0 ht
      simp only [csBitT, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
      obtain ⟨-, h1, h2, h3, h4⟩ := this
      rw [show c + 5 * 0 + 3 = c + 3 by omega, h4, h3, h2, h1, tb_word_one,
        imFactor_eq (by decide), Finset.prod_range_one, csFactor]
    | succ t ih =>
      have := hb (t + 1) ht
      simp only [csBitT, Nat.succ_ne_zero, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
        and_true] at this
      obtain ⟨-, h1, h2, h3, h4, h5⟩ := this
      rw [Finset.prod_range_succ, ← ih (by omega),
        show c + 5 * (t + 1) + 3 = c + 5 * (t + 1) - 1 + 4 by omega, h5, h4, h3, h2, h1,
        tb_word_one, imFactor_eq (by omega), csFactor,
        show c + 5 * (t + 1) - 2 = c + 5 * t + 3 by omega]

/-- The pinned bit of value `csBitV i`. -/
def csF (σ : Val) (i : ℕ) : Bool := decide (σ (.n (csBitV i)) = 1)

theorem csW_bounds (κ k : ℕ) : 1 ≤ csW κ k ∧ csW κ k ≤ 4 := by
  unfold csW; split <;> omega

/-- **A nibble**: its bits pinned; the eq weight and the share it reads, at `g^u` past the tables'
offsets, `u` the bits; the running products. -/
theorem holds_csNib {κ k : ℕ}
    (h : Stmt.HoldsList C rd σ (csNibT κ k) True kret) :
    (∀ t < csW κ k, σ (.n (csBitV (4 * (κ / 4 + k) + 3 - t))) =
      bitE (csF σ (4 * (κ / 4 + k) + 3 - t))) ∧
    ∃ xe xg, LoadHolds rd (σ (.n 1)) (bitsVal (fun t ↦ csF σ (4 * (κ / 4 + k) + 3 - t)) (csW κ k) +
        (30 * (κ / 4 + k) + 2 ^ csW κ k - 2)) xe ∧
      LoadHolds rd (σ (.n 2)) (bitsVal (fun t ↦ csF σ (4 * (κ / 4 + k) + 3 - t)) (csW κ k) +
        16 * (κ / 4 + k)) xg ∧
      σ (.n (csSel κ k)) = (if k = 0 then 1 else σ (.n (csSel κ (k - 1)))) * xe ∧
      σ (.n (csRb κ k)) = (if k = 0 then 1 else σ (.n (csRb κ (k - 1)))) * xg := by
  obtain ⟨hw1, hw4⟩ := csW_bounds κ k
  unfold csNibT at h
  rw [holdsList_append, holdsList_noRet _ (csBits_noRet _ _ _)] at h
  obtain ⟨hbits, htail⟩ := h
  obtain ⟨hpin, hidx⟩ := holds_csBits hw4 hbits
  have hpin' : ∀ t < csW κ k, σ (.n (csBitV (4 * (κ / 4 + k) + 3 - t))) =
      bitE (csF σ (4 * (κ / 4 + k) + 3 - t)) := fun t ht => bitE_of_mul_self (hpin t ht)
  refine ⟨hpin', ?_⟩
  set j := κ / 4 + k
  set w := csW κ k
  set c := csC κ k
  set g : ℕ → Bool := fun t ↦ csF σ (4 * j + 3 - t)
  have hU : σ (.n (c + 5 * w - 2)) = gen ^ bitsVal g w := by
    rw [show c + 5 * w - 2 = c + 5 * (w - 1) + 3 by omega, hidx (w - 1) (by omega),
      show w - 1 + 1 = w by omega, ← prod_bitE_gen_pow]
    refine Finset.prod_congr rfl fun t ht => ?_
    rw [hpin' t (Finset.mem_range.mp ht), csFactor, add_comm (gen ^ 2 ^ t) 1]
  have hsel0 : csSel κ k = if k = 0 then c + 5 * w - 1 + 1 else c + 5 * w - 1 + 2 := by
    unfold csSel; split
    · rename_i hk; subst hk; simp only [c, w]; omega
    · rename_i hk; simp only [hk, ↓reduceIte, c, w, csW]; omega
  have hrb0 : csRb κ k = if k = 0 then c + 5 * w - 1 + 3 else c + 5 * w - 1 + 5 := by
    unfold csRb; split
    · rename_i hk; subst hk; simp only [c, w]; omega
    · rename_i hk; simp only [hk, ↓reduceIte, c, w, csW]; omega
  by_cases hk : k = 0
  · simp only [hk, ↓reduceIte] at htail hsel0 hrb0 ⊢
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at htail
    obtain ⟨h1, h2, h3, h4⟩ := htail
    rw [h1, hU, tb_loadHolds_mul_gen_pow] at h2
    rw [h3, hU, tb_loadHolds_mul_gen_pow] at h4
    exact ⟨_, _, h2, h4, by rw [hsel0, one_mul], by rw [hrb0, one_mul]⟩
  · simp only [hk, ↓reduceIte] at htail hsel0 hrb0 ⊢
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at htail
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := htail
    rw [h1, hU, tb_loadHolds_mul_gen_pow] at h2
    rw [h4, hU, tb_loadHolds_mul_gen_pow] at h5
    exact ⟨_, _, h2, h5, by rw [hsel0, h3], by rw [hrb0, h6]⟩

end Sem

/-! ## Products over the nibbles -/

theorem prod_range_four_blocks {M : Type} [CommMonoid M] (F : ℕ → M) (B : ℕ) : ∀ m : ℕ,
    ∏ k ∈ Finset.range m, ∏ s ∈ Finset.range 4, F (B + 4 * k + s) =
      ∏ i ∈ Finset.range (4 * m), F (B + i)
  | 0 => by simp
  | m + 1 => by
    rw [Finset.prod_range_succ, prod_range_four_blocks F B m, show 4 * (m + 1) = 4 * m + 4 by ring,
      Finset.prod_range_add]
    refine congrArg _ (Finset.prod_congr rfl fun s _ => ?_)
    rw [Nat.add_assoc]

/-- **The nibbles cover the bits `κ .. 27`**: nibble `k`'s bits `4j + 3 - t`, `t < w_k`. -/
theorem cs_reindex {M : Type} [CommMonoid M] (F : ℕ → M) {κ : ℕ} (hκ : κ < 28) :
    ∏ k ∈ Finset.range (csN κ), ∏ t ∈ Finset.range (csW κ k), F (4 * (κ / 4 + k) + 3 - t) =
      ∏ i ∈ Finset.range (28 - κ), F (κ + i) := by
  have hN : csN κ = (6 - κ / 4) + 1 := by unfold csN; omega
  have hw0 : csW κ 0 = 4 * (κ / 4) + 4 - κ := by simp [csW]
  rw [hN, Finset.prod_range_succ']
  have h0 : ∏ t ∈ Finset.range (csW κ 0), F (4 * (κ / 4 + 0) + 3 - t) =
      ∏ s ∈ Finset.range (csW κ 0), F (κ + s) := by
    rw [← Finset.prod_range_reflect (fun s ↦ F (κ + s))]
    refine Finset.prod_congr rfl fun t ht => ?_
    have := Finset.mem_range.mp ht
    congr 1; rw [hw0] at this ⊢; omega
  have h1 : ∀ k, ∏ t ∈ Finset.range (csW κ (k + 1)), F (4 * (κ / 4 + (k + 1)) + 3 - t) =
      ∏ s ∈ Finset.range 4, F (κ + csW κ 0 + 4 * k + s) := fun k => by
    rw [show csW κ (k + 1) = 4 by simp [csW],
      ← Finset.prod_range_reflect (fun s ↦ F (κ + csW κ 0 + 4 * k + s))]
    refine Finset.prod_congr rfl fun t ht => ?_
    have := Finset.mem_range.mp ht
    congr 1; rw [hw0]; omega
  simp only [h1, h0]
  rw [prod_range_four_blocks F (κ + csW κ 0), show 28 - κ = csW κ 0 + 4 * (6 - κ / 4) by
    rw [hw0]; omega, Finset.prod_range_add, mul_comm]
  refine congrArg _ (Finset.prod_congr rfl fun i _ => ?_)
  rw [Nat.add_assoc]

/-- `g` to the bits `κ, κ + 1, …` of `h`. -/
theorem prod_gen_pow_bits (κ : ℕ) (h : ℕ → Bool) : ∀ m : ℕ,
    ∏ i ∈ Finset.range m, gen ^ (2 ^ (κ + i) * (h i).toNat) = gen ^ (2 ^ κ * bitsVal h m)
  | 0 => by simp [bitsVal]
  | m + 1 => by
    rw [Finset.prod_range_succ, prod_gen_pow_bits κ h m, ← pow_add, bitsVal, Nat.mul_add,
      pow_add 2 κ m, Nat.mul_assoc]

/-- Coordinate `t < 4` of nibble `j < 7` read from its top is coordinate `4j + 3 - t`. -/
theorem topNib_getD {p : List E} (hp : p.length = 28) {j t : ℕ} (hj : j < 7) (ht : t < 4) :
    (topNib p j).getD t 0 = p.getD (4 * j + 3 - t) 0 := by
  have hl : (List.take 4 (List.drop (4 * j) p)).length = 4 := by simp [hp]; omega
  simp only [topNib, nib]
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_reverse, hl]; omega),
    List.getElem_reverse, List.getD_eq_getElem _ _ (by omega)]
  simp only [List.getElem_take, List.getElem_drop]
  congr 1; rw [hl]; omega

theorem topShares_getD {j t : ℕ} (ht : t < 4) : (topShares j).getD t 0 = gen ^ 2 ^ (4 * j + 3 - t) := by
  rw [topShares, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range]

/-- `bitsEq` as a product over the positions. -/
theorem bitsEq_eq_prod : ∀ {m : ℕ} {bs : List Bool} {zs zs1 : List E}, bs.length = m →
    zs.length = m → zs1.length = m →
    bitsEq bs zs zs1 = ∏ i ∈ Finset.range m,
      (if bs.getD i false then zs.getD i 0 else zs1.getD i 0)
  | 0, bs, zs, zs1, h1, _, _ => by rw [List.length_eq_zero_iff] at h1; subst h1; rfl
  | m + 1, b :: bs, z :: zs, z1 :: zs1, h1, h2, h3 => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2 h3
    rw [bitsEq, List.zip_cons_cons, List.zip_cons_cons, List.map_cons, List.prod_cons, ← bitsEq,
      bitsEq_eq_prod h1 h2 h3, Finset.prod_range_succ', mul_comm]
    simp


theorem eqLevels_length {zs zs1 : List E} {n : ℕ} (h : zs.length = n) (h1 : zs1.length = n) :
    (eqLevels zs zs1).length = 2 ^ (n + 1) - 2 := by
  rw [eqLevels, h]
  have key : ∀ m ≤ n, ((List.range m).flatMap fun t ↦ eqTable (zs.take (t + 1))
      (zs1.take (t + 1))).length = 2 ^ (m + 1) - 2 := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      rw [List.range_succ, List.flatMap_append, List.length_append, ih (by omega),
        List.flatMap_singleton, eqTable_length (n := m + 1) (by simp; omega) (by simp; omega),
        pow_succ 2 (m + 1)]
      have : 2 ≤ 2 ^ (m + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  exact key n le_rfl

theorem two_le_two_pow {w : ℕ} (hw : 1 ≤ w) : 2 ≤ 2 ^ w :=
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw

theorem tbReadsAt_getD {rd : Reader} {p : E} {xs : List E} (h : TbReadsAt rd p xs) {k : ℕ}
    (hk : k < xs.length) : LoadHolds rd p k (xs.getD k 0) := by
  rw [List.getD_eq_getElem _ _ hk]; exact h k hk

/-- **`column_selector` is sound**. -/
theorem column_selector_sound {κ : ℕ} (hκ : κ < 29) {rd : Reader} {args rets : List E}
    (h : coreProgram.Rel rd (lName "column_selector" κ) args rets) : ColSelOut κ rd args rets := by
  obtain ⟨fn, hf, hp, hb⟩ := csFound hκ
  obtain ⟨σ, hpar, hpre, hret⟩ := (tb_rel_pre hf hb (csPre_noRet κ) args rets).mp h
  rw [hp] at hpar
  simp only [List.map_cons, List.map_nil] at hpar hret
  subst hpar hret
  simp only [ColSelOut]
  intro hG
  by_cases h28 : κ = 28
  · subst h28
    simp only [csPre, ↓reduceIte, csHint, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true,
      true_and] at hpre
    obtain ⟨h1, h2, h3⟩ := hpre
    refine ⟨0, by norm_num, dvd_zero _, ?_, fun p p1 _ _ _ => ?_⟩
    · rw [pow_zero]; rw [h1, tb_word_one] at h2; exact (e_add_eq_zero_iff.mp h2).symm
    · simp only [csRet, ↓reduceIte, h3, tb_word_one]; rfl
  have hκ' : κ < 28 := by omega
  simp only [csPre, h28, ↓reduceIte, csHint, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
    true_and] at hpre
  rw [holdsList_append, holdsList_flatten _ (fun b hb => by
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hb; exact csNibT_noRet κ t)] at hpre
  obtain ⟨hnibs, htail⟩ := hpre
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at htail
  obtain ⟨hassert, hcopy⟩ := htail
  set N := csN κ with hNdef
  have hN1 : 1 ≤ N := by simp only [hNdef, csN]; omega
  have hNib : ∀ k < N, _ := fun k hk => holds_csNib (C := coreProgram.Rel rd) (rd := rd) (σ := σ)
    (kret := fun rs => rs = [σ (.n (csRet κ))]) (κ := κ) (k := k)
    (hnibs _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))
  choose xe xg hxe hxg hsel hrb using fun k (hk : k < N) => (hNib k hk).2
  -- the bits and the products over the nibbles
  let F : ℕ → Bool := csF σ
  let U : ℕ → ℕ := fun k ↦ bitsVal (fun t ↦ F (4 * (κ / 4 + k) + 3 - t)) (csW κ k)
  have hUlt : ∀ k, U k < 2 ^ csW κ k := fun k => bitsVal_lt _ _
  have hUbit : ∀ k t, (U k).testBit t = (decide (t < csW κ k) && F (4 * (κ / 4 + k) + 3 - t)) :=
    fun k t => testBit_bitsVal _ _ _
  let xe' : ℕ → E := fun k ↦ if hk : k < N then xe k hk else 1
  let xg' : ℕ → E := fun k ↦ if hk : k < N then xg k hk else 1
  have hS : ∀ k < N, σ (.n (csSel κ k)) = ∏ m ∈ Finset.range (k + 1), xe' m := by
    intro k hk
    induction k with
    | zero => rw [hsel 0 hk]; simp [xe', hk]
    | succ k ih =>
      rw [hsel (k + 1) hk, Finset.prod_range_succ]
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [ih (by omega)]; simp [xe', hk]
  have hR : ∀ k < N, σ (.n (csRb κ k)) = ∏ m ∈ Finset.range (k + 1), xg' m := by
    intro k hk
    induction k with
    | zero => rw [hrb 0 hk]; simp [xg', hk]
    | succ k ih =>
      rw [hrb (k + 1) hk, Finset.prod_range_succ]
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [ih (by omega)]; simp [xg', hk]
  -- the rebuilt power
  have hxg' : ∀ k < N, xg' k = ∏ t ∈ Finset.range (csW κ k),
      gen ^ (2 ^ (4 * (κ / 4 + k) + 3 - t) * (F (4 * (κ / 4 + k) + 3 - t)).toNat) := by
    intro k hk
    have hj : κ / 4 + k < 7 := by simp only [hNdef, csN] at hk; omega
    obtain ⟨hw1, hw4⟩ := csW_bounds κ k
    have hU16 : U k < 2 ^ 4 :=
      lt_of_lt_of_le (hUlt k) (Nat.pow_le_pow_right (by norm_num) hw4)
    have hl : U k < (gTable (topShares (κ / 4 + k))).length := by
      rw [gTable_length (n := 4) (by simp [topShares])]; exact hU16
    have h1 := tbReadsAt_getD (hG _ hj) hl
    rw [tb_loadHolds_mul_gen_pow, gTable_getD (n := 4) (by simp [topShares]) hU16] at h1
    have h2 := hxg k hk
    rw [show U k + 16 * (κ / 4 + k) = 16 * (κ / 4 + k) + U k by omega] at h2
    simp only [xg', hk, ↓reduceDIte]
    rw [tb_loadHolds_unique h2 h1, show Finset.range 4 = Finset.range (csW κ k + (4 - csW κ k)) by
      rw [Nat.add_sub_of_le hw4], Finset.prod_range_add]
    have hrest : ∏ x ∈ Finset.range (4 - csW κ k),
        bitPick (U k) (csW κ k + x) ((topShares (κ / 4 + k)).getD (csW κ k + x) 0) 1 = 1 :=
      Finset.prod_eq_one fun x _ => by simp [bitPick, hUbit]
    rw [hrest, mul_one]
    refine Finset.prod_congr rfl fun t ht => ?_
    have ht' := Finset.mem_range.mp ht
    rw [bitPick, hUbit, topShares_getD (by omega)]
    simp only [ht', decide_true, Bool.true_and]
    cases F (4 * (κ / 4 + k) + 3 - t) <;> simp
  -- the bits as one exponent
  let hbits : ℕ → Bool := fun i ↦ F (κ + i)
  let o := 2 ^ κ * bitsVal hbits (28 - κ)
  have ho : o.testBit = fun i ↦ decide (κ ≤ i) && (decide (i - κ < 28 - κ) && hbits (i - κ)) := by
    funext i
    simp only [o, Nat.testBit_two_pow_mul, testBit_bitsVal, ge_iff_le]
  refine ⟨o, ?_, Dvd.intro _ rfl, ?_, fun p p1 hp hp1 hE => ?_⟩
  · have := bitsVal_lt hbits (28 - κ)
    calc o < 2 ^ κ * 2 ^ (28 - κ) := Nat.mul_lt_mul_of_pos_left this (Nat.two_pow_pos κ)
      _ = 2 ^ 28 := by rw [← pow_add, Nat.add_sub_of_le (by omega : κ ≤ 28)]
  · have e0 := e_add_eq_zero_iff.mp hassert
    rw [← e0, hR (N - 1) (by omega), show N - 1 + 1 = N by omega,
      Finset.prod_congr rfl (fun k hk => hxg' k (Finset.mem_range.mp hk)),
      cs_reindex (fun i ↦ gen ^ (2 ^ i * (F i).toNat)) hκ']
    exact prod_gen_pow_bits κ hbits (28 - κ)
  · -- the selector
    have hxe' : ∀ k < N, xe' k = ∏ t ∈ Finset.range (csW κ k),
        (if F (4 * (κ / 4 + k) + 3 - t) then p.getD (4 * (κ / 4 + k) + 3 - t) 0
          else p1.getD (4 * (κ / 4 + k) + 3 - t) 0) := by
      intro k hk
      have hj : κ / 4 + k < 7 := by simp only [hNdef, csN] at hk; omega
      obtain ⟨hw1, hw4⟩ := csW_bounds κ k
      have hlen : (topNib p (κ / 4 + k)).length = 4 := by
        simp [topNib, nib, hp]; omega
      have hlen1 : (topNib p1 (κ / 4 + k)).length = 4 := by
        simp [topNib, nib, hp1]; omega
      have hl : 2 ^ csW κ k - 2 + U k < (eqLevels (topNib p (κ / 4 + k))
          (topNib p1 (κ / 4 + k))).length := by
        rw [eqLevels_length hlen hlen1]
        have : 2 ^ (csW κ k + 1) ≤ 2 ^ (4 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have := hUlt k
        have := two_le_two_pow hw1
        rw [pow_succ] at *
        omega
      have h1 := tbReadsAt_getD (hE _ hj) hl
      rw [tb_loadHolds_mul_gen_pow, eqLevels_getD (hlen.trans hlen1.symm) hw1 (by omega)
        (hUlt k)] at h1
      have h2 := hxe k hk
      have := two_le_two_pow hw1
      rw [show U k + (30 * (κ / 4 + k) + 2 ^ csW κ k - 2) =
        30 * (κ / 4 + k) + (2 ^ csW κ k - 2 + U k) by omega] at h2
      simp only [xe', hk, ↓reduceDIte]
      rw [tb_loadHolds_unique h2 h1]
      refine Finset.prod_congr rfl fun t ht => ?_
      have ht' := Finset.mem_range.mp ht
      rw [bitPick, hUbit, topNib_getD hp hj (by omega), topNib_getD hp1 hj (by omega)]
      simp only [ht', decide_true, Bool.true_and]
    rw [show csRet κ = csC κ N by simp only [csRet, h28, ↓reduceIte, hNdef], hcopy,
      hS (N - 1) (by omega), show N - 1 + 1 = N by omega,
      Finset.prod_congr rfl (fun k hk => hxe' k (Finset.mem_range.mp hk)),
      cs_reindex (fun i ↦ if F i then p.getD i 0 else p1.getD i 0) hκ',
      bitsEq_eq_prod (m := 28 - κ) (by simp) (by simp [hp]) (by simp [hp1])]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    have e1 : ((List.range (28 - κ)).map fun i ↦ o.testBit (κ + i)).getD i false = F (κ + i) := by
      rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map, List.getElem_range, ho]
      simp [hi', hbits]
    have e2 : ∀ q : List E, (q.drop κ).getD i 0 = q.getD (κ + i) 0 := fun q => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD]
    rw [e1, e2, e2]

theorem column_selector_holds : column_selector_Spec := fun _ hκ _ _ _ h => column_selector_sound hκ h

end
end LeanVM.Guest.B1.Tables
