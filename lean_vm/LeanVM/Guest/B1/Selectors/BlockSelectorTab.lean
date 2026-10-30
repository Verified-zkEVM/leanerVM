/-
  LeanVM.Guest.B1.Selectors.BlockSelectorTab

  B1 for `block_selector_tab`: its 34 specializations read pinned bits and, off the shared nibble
  tables, return their eq weight and `g`-power product.
-/

module

public import LeanVM.Guest.B1.Selectors.SelPartial

/-!
# `block_selector_tab` (TRIAGE G #49)

`block_selector_tab(sel_bits, eq_tab, g_tab, n)` (G:1864-1881) reads, for each nibble `j` of the
`n` bits (the last `n - 4j` wide), its bits `4j + t` at `sel_bits`, pins each by the write-once
store of its square, folds them into `g^u` (`u`'s bit `t` the bit `4j + t`), and multiplies the
eq weight at `eq_tab·g^u` (offset `32j + 2^w - 2`) and the share at `g_tab·g^u` (offset `16j`).

The body of `block_selector_tab__L{n}` is `btBody n` (`btFound`, by kernel evaluation): nibble `k`
from value `btC k`, its bits by `btBitT`, its tail as `column_selector`'s.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The template -/

/-- The number of nibbles of `n` bits. -/
def btN (n : ℕ) : ℕ := (n + 3) / 4

/-- The width of nibble `k`. -/
def btW (n k : ℕ) : ℕ := if 4 * k + 4 ≤ n then 4 else n - 4 * k

/-- The first value of nibble `k`. -/
def btC (k : ℕ) : ℕ := if k = 0 then 3 else 34 + 33 * (k - 1)

/-- The eq product after nibble `k`. -/
def btSel (n k : ℕ) : ℕ := if k = 0 then btC 0 + 7 * btW n 0 else btC k + 7 * btW n k + 1

/-- The rebuilt product after nibble `k`. -/
def btRb (n k : ℕ) : ℕ := if k = 0 then btC 0 + 7 * btW n 0 + 2 else btC k + 7 * btW n k + 4

/-- The next free value after nibble `k`. -/
def btE (n k : ℕ) : ℕ := if k = 0 then btC 0 + 7 * btW n 0 + 3 else btC k + 7 * btW n k + 5

/-- The bit value of bit `t` of the nibble from `c`. -/
def btBitV (c t : ℕ) : ℕ := if t = 0 then c else c + 7 * t - 1

/-- Bit `t` of nibble `j`, from value `c`: the load, its pinned square, the factor
`1 + b·(1 + g^(2^t))` multiplied into the index. -/
def btBitT (j t c : ℕ) : List Stmt :=
  let d := btBitV c t
  [.atom (.load (.n d) (.n 0) (4 * j + t)), .atom (.mul (.n (d + 1)) (.n d) (.n d)),
    .atom (.load (.n (d + 1)) (.n 0) (4 * j + t)), .atom (.const (.n (d + 2)) (word 1 0 0)),
    .atom (.const (.n (d + 3)) (word (imFactor t) 0 0)),
    .atom (.mul (.n (d + 4)) (.n d) (.n (d + 3))), .atom (.add (.n (d + 5)) (.n (d + 2)) (.n (d + 4)))] ++
  if t = 0 then [] else [.atom (.mul (.n (d + 6)) (.n (c + 7 * t - 2)) (.n (d + 5)))]

/-- Nibble `k` of `block_selector_tab__L{n}`. -/
def btNibT (n k : ℕ) : List Stmt :=
  let w := btW n k
  let c := btC k
  let c1 := c + 7 * w - 1
  let idx := c + 7 * w - 2
  ((List.range w).map fun t ↦ btBitT k t c).flatten ++
    if k = 0 then
      [.atom (.mul (.n c1) (.n 1) (.n idx)), .atom (.load (.n (c1 + 1)) (.n c1) (32 * k + 2 ^ w - 2)),
        .atom (.mul (.n (c1 + 2)) (.n 2) (.n idx)),
        .atom (.load (.n (c1 + 3)) (.n (c1 + 2)) (16 * k))]
    else
      [.atom (.mul (.n c1) (.n 1) (.n idx)), .atom (.load (.n (c1 + 1)) (.n c1) (32 * k + 2 ^ w - 2)),
        .atom (.mul (.n (c1 + 2)) (.n (btSel n (k - 1))) (.n (c1 + 1))),
        .atom (.mul (.n (c1 + 3)) (.n 2) (.n idx)),
        .atom (.load (.n (c1 + 4)) (.n (c1 + 3)) (16 * k)),
        .atom (.mul (.n (c1 + 5)) (.n (btRb n (k - 1))) (.n (c1 + 4)))]

/-- `block_selector_tab__L{n}`'s statements before its `ret`. -/
def btPre (n : ℕ) : List Stmt :=
  if n = 0 then [.atom (.const (.n 3) (word 1 0 0)), .atom (.const (.n 4) (word 1 0 0))]
  else ((List.range (btN n)).map (btNibT n)).flatten ++
    [.atom (.copy (.n (btE n (btN n - 1))) (.n (btSel n (btN n - 1)))),
      .atom (.copy (.n (btE n (btN n - 1) + 1)) (.n (btRb n (btN n - 1))))]

/-- The values `block_selector_tab__L{n}` returns. -/
def btRet (n : ℕ) : List V :=
  if n = 0 then [.n 3, .n 4] else [.n (btE n (btN n - 1)), .n (btE n (btN n - 1) + 1)]

/-- The function found by name is the template. -/
noncomputable def btCheck (n : ℕ) : Bool :=
  match coreProgram.find? (lName "block_selector_tab" n) with
  | some fn => decide (fn.params = [.n 0, .n 1, .n 2]) &&
      tbStmtsEqb fn.body (btPre n ++ [.ret (btRet n)])
  | none => false

theorem btCheck_all : (List.range 34).all btCheck = true := by decide +kernel

theorem btFound {n : ℕ} (hn : n < 34) : ∃ fn : Fn,
    coreProgram.find? (lName "block_selector_tab" n) = some fn ∧ fn.params = [.n 0, .n 1, .n 2] ∧
      fn.body = btPre n ++ [.ret (btRet n)] := by
  have h := List.all_eq_true.mp btCheck_all n (List.mem_range.mpr hn)
  unfold btCheck at h
  split at h
  · rename_i fn hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fn, hf, h.1, tbStmtsEqb_sound h.2⟩
  · exact absurd h (by simp)

theorem btBitT_noRet (j t c : ℕ) : Stmt.noRetList (btBitT j t c) = true := by
  unfold btBitT; split <;> rfl

theorem btNibT_noRet (n k : ℕ) : Stmt.noRetList (btNibT n k) = true := by
  unfold btNibT
  rw [tb_noRetList_append, tb_noRetList_flatten_range _ _ (fun t => btBitT_noRet k t _)]
  split <;> rfl

theorem btPre_noRet (n : ℕ) : Stmt.noRetList (btPre n) = true := by
  unfold btPre
  split
  · rfl
  · rw [tb_noRetList_append, tb_noRetList_flatten_range _ _ (btNibT_noRet n)]; rfl

section Sem

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- The pinned bit of value `btBitV c t`. -/
def btF (σ : Val) (c t : ℕ) : Bool := decide (σ (.n (btBitV c t)) = 1)

/-- **The bits of a nibble**: each read and pinned, and the index the product of their factors. -/
theorem holds_btBits {j w c : ℕ} (hw : w ≤ 4)
    (h : Stmt.HoldsList C rd σ ((List.range w).map fun t ↦ btBitT j t c).flatten True kret) :
    (∀ t < w, LoadHolds rd (σ (.n 0)) (4 * j + t) (σ (.n (btBitV c t))) ∧
      σ (.n (btBitV c t)) = bitE (btF σ c t)) ∧
    ∀ t < w, σ (.n (c + 7 * t + 5)) =
      ∏ s ∈ Finset.range (t + 1), csFactor (σ (.n (btBitV c s))) s := by
  rw [tb_holdsList_flatten_range _ _ (fun t => btBitT_noRet j t c)] at h
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · have := h t ht
    unfold btBitT at this
    rw [tb_holdsList_append_noRet rfl] at this
    obtain ⟨this, -⟩ := this
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
    exact ⟨this.1, tb_pinned_bit this.1 this.2.2.1 this.2.1⟩
  · induction t with
    | zero =>
      have := h 0 ht
      simp only [btBitT, btBitV, ↓reduceIte, List.append_nil, Stmt.HoldsList, Stmt.Holds,
        Atom.Holds, and_true] at this
      obtain ⟨-, -, -, h1, h2, h3, h4⟩ := this
      rw [show c + 7 * 0 + 5 = c + 5 by omega, h4, h3, h2, h1, tb_word_one,
        imFactor_eq (by decide), Finset.prod_range_one, csFactor]
      simp [btBitV]
    | succ t ih =>
      have := h (t + 1) ht
      simp only [btBitT, Nat.succ_ne_zero, ↓reduceIte, Stmt.HoldsList, Stmt.Holds,
        Atom.Holds, and_true, List.cons_append, List.nil_append] at this
      obtain ⟨-, -, -, h1, h2, h3, h4, h5⟩ := this
      have hb : btBitV c (t + 1) = c + 7 * (t + 1) - 1 := by simp [btBitV]
      rw [hb] at h1 h2 h3 h4 h5
      rw [Finset.prod_range_succ, ← ih (by omega),
        show c + 7 * (t + 1) + 5 = c + 7 * (t + 1) - 1 + 6 by omega, h5, h4, h3, h2, h1,
        tb_word_one, imFactor_eq (by omega), csFactor, hb,
        show c + 7 * (t + 1) - 2 = c + 7 * t + 5 by omega]

theorem btW_le (n k : ℕ) : btW n k ≤ 4 := by unfold btW; split <;> omega

theorem btW_pos {n k : ℕ} (hk : k < btN n) : 1 ≤ btW n k := by
  unfold btW btN at *; split <;> omega

/-- **A nibble**: its bits read and pinned; the eq weight and the share it reads; the running
products. -/
theorem holds_btNib {n k : ℕ} (hk : k < btN n) (h : Stmt.HoldsList C rd σ (btNibT n k) True kret) :
    (∀ t < btW n k, LoadHolds rd (σ (.n 0)) (4 * k + t) (σ (.n (btBitV (btC k) t))) ∧
      σ (.n (btBitV (btC k) t)) = bitE (btF σ (btC k) t)) ∧
    ∃ xe xg, LoadHolds rd (σ (.n 1)) (bitsVal (btF σ (btC k)) (btW n k) +
        (32 * k + 2 ^ btW n k - 2)) xe ∧
      LoadHolds rd (σ (.n 2)) (bitsVal (btF σ (btC k)) (btW n k) + 16 * k) xg ∧
      σ (.n (btSel n k)) = (if k = 0 then 1 else σ (.n (btSel n (k - 1)))) * xe ∧
      σ (.n (btRb n k)) = (if k = 0 then 1 else σ (.n (btRb n (k - 1)))) * xg := by
  have hw1 := btW_pos hk
  have hw4 := btW_le n k
  unfold btNibT at h
  rw [tb_holdsList_append_noRet (tb_noRetList_flatten_range _ _ (fun t => btBitT_noRet k t _))] at h
  obtain ⟨hbits, htail⟩ := h
  obtain ⟨hpin, hidx⟩ := holds_btBits hw4 hbits
  refine ⟨hpin, ?_⟩
  set w := btW n k
  set c := btC k
  have hU : σ (.n (c + 7 * w - 2)) = gen ^ bitsVal (btF σ c) w := by
    rw [show c + 7 * w - 2 = c + 7 * (w - 1) + 5 by omega, hidx (w - 1) (by omega),
      show w - 1 + 1 = w by omega, ← prod_bitE_gen_pow]
    refine Finset.prod_congr rfl fun t ht => ?_
    rw [(hpin t (Finset.mem_range.mp ht)).2, csFactor, add_comm (gen ^ 2 ^ t) 1]
  have hsel0 : btSel n k = if k = 0 then c + 7 * w - 1 + 1 else c + 7 * w - 1 + 2 := by
    unfold btSel; split
    · rename_i hk; subst hk; simp only [c, w]; omega
    · simp only [c, w]; omega
  have hrb0 : btRb n k = if k = 0 then c + 7 * w - 1 + 3 else c + 7 * w - 1 + 5 := by
    unfold btRb; split
    · rename_i hk; subst hk; simp only [c, w]; omega
    · simp only [c, w]; omega
  by_cases hk0 : k = 0
  · simp only [hk0, ↓reduceIte] at htail hsel0 hrb0 ⊢
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at htail
    obtain ⟨h1, h2, h3, h4⟩ := htail
    rw [h1, hU, tb_loadHolds_mul_gen_pow] at h2
    rw [h3, hU, tb_loadHolds_mul_gen_pow] at h4
    exact ⟨_, _, h2, h4, by rw [hsel0, one_mul], by rw [hrb0, one_mul]⟩
  · simp only [hk0, ↓reduceIte] at htail hsel0 hrb0 ⊢
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at htail
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := htail
    rw [h1, hU, tb_loadHolds_mul_gen_pow] at h2
    rw [h4, hU, tb_loadHolds_mul_gen_pow] at h5
    exact ⟨_, _, h2, h5, by rw [hsel0, h3], by rw [hrb0, h6]⟩

end Sem

/-! ## Products over the nibbles -/

/-- **The nibbles cover the bits `0 .. n - 1`**: nibble `k`'s bits `4k + t`, `t < w_k`. -/
theorem bt_reindex {M : Type} [CommMonoid M] (F : ℕ → M) (n : ℕ) :
    ∏ k ∈ Finset.range (btN n), ∏ t ∈ Finset.range (btW n k), F (4 * k + t) =
      ∏ i ∈ Finset.range n, F i := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 4 ∧ n = 4 * q + r := ⟨n / 4, n % 4, Nat.mod_lt _ (by decide),
    (Nat.div_add_mod n 4).symm⟩
  have hfull : ∏ k ∈ Finset.range q, ∏ t ∈ Finset.range (btW (4 * q + r) k), F (4 * k + t) =
      ∏ i ∈ Finset.range (4 * q), F i := by
    have h4 := prod_range_four_blocks F 0 q
    simp only [Nat.zero_add] at h4
    rw [← h4]
    refine Finset.prod_congr rfl fun k hk => ?_
    have := Finset.mem_range.mp hk
    rw [show btW (4 * q + r) k = 4 by simp only [btW]; split <;> omega]

  rw [Finset.prod_range_add]
  by_cases hr0 : r = 0
  · subst hr0
    rw [show btN (4 * q + 0) = q by simp only [btN]; omega, hfull, Finset.prod_range_zero, mul_one]
  · rw [show btN (4 * q + r) = q + 1 by simp only [btN]; omega, Finset.prod_range_succ, hfull,
      show btW (4 * q + r) q = r by simp only [btW]; split <;> omega]

/-- `bitsPow` as a product over the positions. -/
theorem bitsPow_eq_prod : ∀ {m : ℕ} {bs : List Bool} {gs : List E}, bs.length = m →
    gs.length = m → bitsPow bs gs = ∏ i ∈ Finset.range m, (if bs.getD i false then gs.getD i 0 else 1)
  | 0, bs, gs, h1, _ => by rw [List.length_eq_zero_iff] at h1; subst h1; rfl
  | m + 1, b :: bs, g :: gs, h1, h2 => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2
    rw [bitsPow, List.zip_cons_cons, List.map_cons, List.prod_cons, ← bitsPow,
      bitsPow_eq_prod h1 h2, Finset.prod_range_succ', mul_comm]
    simp

theorem nib_getD {l : List E} {n k t : ℕ} (ht : t < btW n k) :
    (nib l k).getD t 0 = l.getD (4 * k + t) 0 := by
  rw [nib, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by unfold btW at ht; split at ht <;> omega),
    List.getElem?_drop, ← List.getD_eq_getElem?_getD]

theorem nib_length {l : List E} {n k : ℕ} (hl : l.length = n) (hk : k < btN n) :
    (nib l k).length = btW n k := by
  simp only [nib, List.length_take, List.length_drop, hl, btW]
  unfold btN at hk
  split <;> omega

/-- **`block_selector_tab` is sound** at its 34 specializations. -/
theorem block_selector_tab_sound {n : ℕ} (hn : n < 34) {rd : Reader} {args rets : List E}
    (h : coreProgram.Rel rd (lName "block_selector_tab" n) args rets) :
    BlockSelTabOut n rd args rets := by
  obtain ⟨fn, hf, hp, hb⟩ := btFound hn
  obtain ⟨σ, hpar, hpre, hret⟩ := (tb_rel_pre hf hb (btPre_noRet n) args rets).mp h
  rw [hp] at hpar
  simp only [List.map_cons, List.map_nil] at hpar
  subst hpar hret
  by_cases h0 : n = 0
  · subst h0
    simp only [btPre, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hpre
    simp only [btRet, ↓reduceIte, List.map_cons, List.map_nil, BlockSelTabOut]
    refine ⟨[], rfl, tbReadsAt_nil _ _, fun zs zs1 gs hz hz1 hg _ => ?_⟩
    rw [List.length_eq_zero_iff] at hz hz1 hg
    subst hz hz1 hg
    simp [hpre.1, hpre.2, tb_word_one, bitsEq, bitsPow]
  simp only [btPre, h0, ↓reduceIte] at hpre
  rw [tb_holdsList_append_noRet (tb_noRetList_flatten_range _ _ (btNibT_noRet n)),
    tb_holdsList_flatten_range _ _ (btNibT_noRet n)] at hpre
  obtain ⟨hnibs, htail⟩ := hpre
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at htail
  obtain ⟨hc1, hc2⟩ := htail
  set N := btN n with hNdef
  have hN1 : 1 ≤ N := by simp only [hNdef, btN]; omega
  have hNib : ∀ k < N, _ := fun k hk => holds_btNib (C := coreProgram.Rel rd) (rd := rd) (σ := σ)
    (kret := fun rs => rs = (btRet n).map σ) hk (hnibs k hk)
  choose xe xg hxe hxg hsel hrb using fun k (hk : k < N) => (hNib k hk).2
  let xe' : ℕ → E := fun k ↦ if hk : k < N then xe k hk else 1
  let xg' : ℕ → E := fun k ↦ if hk : k < N then xg k hk else 1
  have hS : ∀ k < N, σ (.n (btSel n k)) = ∏ m ∈ Finset.range (k + 1), xe' m := by
    intro k hk
    induction k with
    | zero => rw [hsel 0 hk]; simp [xe', hk]
    | succ k ih =>
      rw [hsel (k + 1) hk, Finset.prod_range_succ]
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [ih (by omega)]; simp [xe', hk]
  have hR : ∀ k < N, σ (.n (btRb n k)) = ∏ m ∈ Finset.range (k + 1), xg' m := by
    intro k hk
    induction k with
    | zero => rw [hrb 0 hk]; simp [xg', hk]
    | succ k ih =>
      rw [hrb (k + 1) hk, Finset.prod_range_succ]
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [ih (by omega)]; simp [xg', hk]
  let F : ℕ → Bool := fun i ↦ btF σ (btC (i / 4)) (i % 4)
  have hF : ∀ k t, t < 4 → F (4 * k + t) = btF σ (btC k) t := fun k t ht => by
    simp only [F]
    rw [show (4 * k + t) / 4 = k by omega, show (4 * k + t) % 4 = t by omega]
  let bs := (List.range n).map F
  have hbs : ∀ i < n, bs.getD i false = F i := fun i hi => by
    simp [bs, List.getD_eq_getElem?_getD, hi]
  have hkt : ∀ i < n, i / 4 < N ∧ i % 4 < btW n (i / 4) := fun i hi => by
    simp only [hNdef, btN, btW]; constructor
    · omega
    · split <;> omega
  simp only [btRet, h0, ↓reduceIte, List.map_cons, List.map_nil, BlockSelTabOut]
  refine ⟨bs, by simp [bs], fun i hi => ?_, fun zs zs1 gs hz hz1 hg hRT => ⟨?_, ?_⟩⟩
  · simp only [bs, List.length_map, List.length_range] at hi
    simp only [bs, List.getElem_map, List.getElem_range]
    obtain ⟨hk, ht⟩ := hkt i hi
    obtain ⟨hl, hv⟩ := (hNib (i / 4) hk).1 (i % 4) ht
    rw [show 4 * (i / 4) + i % 4 = i by omega] at hl
    rw [hv] at hl
    exact hl
  · -- the eq weight
    have hxe' : ∀ k < N, xe' k = ∏ t ∈ Finset.range (btW n k),
        (if F (4 * k + t) then zs.getD (4 * k + t) 0 else zs1.getD (4 * k + t) 0) := by
      intro k hk
      have hw1 := btW_pos hk
      have hw4 := btW_le n k
      have hlen := nib_length hz hk
      have hlen1 := nib_length hz1 hk
      have hUlt := bitsVal_lt (btF σ (btC k)) (btW n k)
      have hl : 2 ^ btW n k - 2 + bitsVal (btF σ (btC k)) (btW n k) <
          (eqLevels (nib zs k) (nib zs1 k)).length := by
        rw [eqLevels_length hlen hlen1]
        have := two_le_two_pow hw1
        rw [pow_succ]; omega
      have h1 := tbReadsAt_getD ((hRT k (by simpa [hNdef, btN] using hk)).1) hl
      rw [tb_loadHolds_mul_gen_pow, eqLevels_getD (hlen.trans hlen1.symm) hw1 (by omega) hUlt] at h1
      have h2 := hxe k hk
      have := two_le_two_pow hw1
      rw [show bitsVal (btF σ (btC k)) (btW n k) + (32 * k + 2 ^ btW n k - 2) =
        32 * k + (2 ^ btW n k - 2 + bitsVal (btF σ (btC k)) (btW n k)) by omega] at h2
      simp only [xe', hk, ↓reduceDIte]
      rw [tb_loadHolds_unique h2 h1]
      refine Finset.prod_congr rfl fun t ht => ?_
      have ht' := Finset.mem_range.mp ht
      rw [bitPick, testBit_bitsVal, nib_getD ht', nib_getD ht', hF k t (by omega)]
      simp [ht']
    rw [hc1, hS (N - 1) (by omega), show N - 1 + 1 = N by omega,
      Finset.prod_congr rfl (fun k hk => hxe' k (Finset.mem_range.mp hk)),
      bt_reindex (fun i ↦ if F i then zs.getD i 0 else zs1.getD i 0) n,
      bitsEq_eq_prod (m := n) (by simp [bs]) hz hz1]
    exact Finset.prod_congr rfl fun i hi => by rw [hbs i (Finset.mem_range.mp hi)]
  · -- the rebuilt power
    have hxg' : ∀ k < N, xg' k = ∏ t ∈ Finset.range (btW n k),
        (if F (4 * k + t) then gs.getD (4 * k + t) 0 else 1) := by
      intro k hk
      have hlen := nib_length hg hk
      have hUlt := bitsVal_lt (btF σ (btC k)) (btW n k)
      have hl : bitsVal (btF σ (btC k)) (btW n k) < (gTable (nib gs k)).length := by
        rw [gTable_length hlen]; exact hUlt
      have h1 := tbReadsAt_getD ((hRT k (by simpa [hNdef, btN] using hk)).2) hl
      rw [tb_loadHolds_mul_gen_pow, gTable_getD hlen hUlt] at h1
      have h2 := hxg k hk
      rw [show bitsVal (btF σ (btC k)) (btW n k) + 16 * k =
        16 * k + bitsVal (btF σ (btC k)) (btW n k) by omega] at h2
      simp only [xg', hk, ↓reduceDIte]
      rw [tb_loadHolds_unique h2 h1]
      refine Finset.prod_congr rfl fun t ht => ?_
      have ht' := Finset.mem_range.mp ht
      have hw4 := btW_le n k
      rw [bitPick, testBit_bitsVal, nib_getD ht', hF k t (by omega)]
      simp [ht']
    rw [hc2, hR (N - 1) (by omega), show N - 1 + 1 = N by omega,
      Finset.prod_congr rfl (fun k hk => hxg' k (Finset.mem_range.mp hk)),
      bt_reindex (fun i ↦ if F i then gs.getD i 0 else 1) n,
      bitsPow_eq_prod (m := n) (by simp [bs]) hg]
    exact Finset.prod_congr rfl fun i hi => by rw [hbs i (Finset.mem_range.mp hi)]

theorem block_selector_tab_holds : block_selector_tab_Spec :=
  fun _ hn _ _ _ h => block_selector_tab_sound hn h

end
end LeanVM.Guest.B1.Tables
