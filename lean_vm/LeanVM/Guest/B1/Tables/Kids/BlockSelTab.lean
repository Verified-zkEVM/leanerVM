/-
  LeanVM.Guest.B1.Tables.Kids.BlockSelTab

  `block_selector_tab__L{n}` loads from any region holding its bits and its run's nibble tables.
-/

module

public import LeanVM.Guest.B1.Tables.Kids.Walk
public import LeanVM.Guest.B1.Selectors.BlockSelectorTab

/-!
# `block_selector_tab`, loading from a region

Nibble `k` of `block_selector_tab__L{n}` (width `w ≤ 4`) reads its bits at `sel_bits·g^(4k+t)`,
then the eq level at `eq_tab·g^v` and the share product at `g_tab·g^v`, `v < 2^w` the nibble's
value (`btNib_ptr`): the eq table's offset `32k + 2^w - 2` and the `g` table's `16k`.
`block_selector_tab_relIn`: it loads from `R` when the bits' `n` words, the eq tables'
`32⌈n/4⌉` and the `g` tables' `16⌈n/4⌉` lie in `R`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- Nibble `k`'s eq pointer value. -/
def btPe (n k : ℕ) : ℕ := btC k + 7 * btW n k - 1

/-- Nibble `k`'s `g` pointer value. -/
def btPg (n k : ℕ) : ℕ := if k = 0 then btPe n k + 2 else btPe n k + 3

/-- The pointers `block_selector_tab__L{n}` loads through, with their runs. -/
def btTbl (n : ℕ) : List (ℕ × ℕ) :=
  (0, n) :: (List.range (btN n)).flatMap fun k ↦
    [(btPe n k, 32 * k + 2 ^ btW n k - 1), (btPg n k, 16 * k + 1)]

theorem bt_loads : ∀ n < 34, (btPre n).all (loadsViaB (btTbl n)) = true := by decide +kernel

theorem bt_flat : ∀ n < 34, (btPre n).all Stmt.flat = true := by decide +kernel

theorem bt_noLoadIte : ∀ n < 34, (btPre n).all noLoadIte = true := by decide +kernel

theorem bt_noCall : ∀ n < 34, (btPre n).all noCallSB = true := by decide +kernel

section
variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- **A nibble's pointers**: the eq level's and the share product's, each the table's times
`g^v`, `v` the nibble's value. -/
theorem btNib_ptr {n k : ℕ} (hk : k < btN n) (h : Stmt.HoldsList C rd σ (btNibT n k) True kret) :
    σ (.n (btPe n k)) = σ (.n 1) * gen ^ bitsVal (btF σ (btC k)) (btW n k) ∧
      σ (.n (btPg n k)) = σ (.n 2) * gen ^ bitsVal (btF σ (btC k)) (btW n k) := by
  have hw1 := btW_pos hk
  have hw4 := btW_le n k
  unfold btNibT at h
  rw [tb_holdsList_append_noRet (tb_noRetList_flatten_range _ _ (fun t => btBitT_noRet k t _))] at h
  obtain ⟨hbits, htail⟩ := h
  obtain ⟨hpin, hidx⟩ := holds_btBits hw4 hbits
  set w := btW n k
  set c := btC k
  have hU : σ (.n (c + 7 * w - 2)) = gen ^ bitsVal (btF σ c) w := by
    rw [show c + 7 * w - 2 = c + 7 * (w - 1) + 5 by omega, hidx (w - 1) (by omega),
      show w - 1 + 1 = w by omega, ← prod_bitE_gen_pow]
    refine Finset.prod_congr rfl fun t ht => ?_
    rw [(hpin t (Finset.mem_range.mp ht)).2, csFactor, add_comm (gen ^ 2 ^ t) 1]
  have hpe : btPe n k = c + 7 * w - 1 := rfl
  by_cases hk0 : k = 0
  · subst hk0
    simp only [↓reduceIte] at htail
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at htail
    obtain ⟨h1, -, h3, -⟩ := htail
    refine ⟨by rw [hpe, h1, hU], ?_⟩
    simp only [btPg, ↓reduceIte]
    rw [hpe, h3, hU]
  · simp only [hk0, ↓reduceIte] at htail
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at htail
    obtain ⟨h1, -, -, h4, -, -⟩ := htail
    refine ⟨by rw [hpe, h1, hU], ?_⟩
    simp only [btPg, hk0, ↓reduceIte]
    rw [hpe, h4, hU]

end

/-- **`block_selector_tab__L{n}` loads from `R`.** -/
theorem block_selector_tab_relIn {n : ℕ} (hn : n < 34) {rd : Reader} {R : ℕ → Prop}
    {sb eqt gt : E} {rets : List E} (hsb : PtrIn R sb n) (he : PtrIn R eqt (32 * btN n))
    (hg : PtrIn R gt (16 * btN n))
    (h : coreProgram.Rel rd (lName "block_selector_tab" n) [sb, eqt, gt] rets) :
    coreProgram.RelIn rd R (lName "block_selector_tab" n) [sb, eqt, gt] rets := by
  obtain ⟨fn, hf, hp, hb⟩ := btFound hn
  refine relIn_of_flatRel (hnl := bt_noLoadIte n hn) hf hb (bt_flat n hn) h fun σ hpar hh ↦ ?_
  rw [hp] at hpar
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
  obtain ⟨p0, p1, p2⟩ := hpar
  have hnc : ∀ s ∈ btPre n, noCallSB s = true :=
    fun s hs ↦ List.all_eq_true.mp (bt_noCall n hn) s hs
  refine ⟨fun s hs ↦ ?_, loads_via (bt_loads n hn) fun pb hpb ↦ ?_, fun c hc _ ↦ ?_⟩
  · exact dispOk_of_noCall (hnc s hs)
  · rw [hb, holdsList_append, holdsList_noRet _ (btPre_noRet n)] at hh
    obtain ⟨hpre, -⟩ := hh
    simp only [btTbl, List.mem_cons, List.mem_flatMap, List.mem_range, List.not_mem_nil,
      or_false] at hpb
    rcases hpb with rfl | ⟨k, hk, hpb | hpb⟩
    · rw [p0]; exact hsb
    · have h0 : n ≠ 0 := by intro h0; subst h0; simp [btN] at hk
      simp only [btPre, h0, ↓reduceIte] at hpre
      rw [tb_holdsList_append_noRet (tb_noRetList_flatten_range _ _ (btNibT_noRet n)),
        tb_holdsList_flatten_range _ _ (btNibT_noRet n)] at hpre
      obtain ⟨he', -⟩ := btNib_ptr hk (hpre.1 k hk)
      subst hpb
      rw [he', p1]
      have hv := bitsVal_lt (btF σ (btC k)) (btW n k)
      have hw4 := btW_le n k
      refine ptrIn_mul (ptrIn_mono he ?_)
      have : 2 ^ btW n k ≤ 16 := by
        calc 2 ^ btW n k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hw4
          _ = 16 := by norm_num
      have : k + 1 ≤ btN n := hk
      omega
    · have h0 : n ≠ 0 := by intro h0; subst h0; simp [btN] at hk
      simp only [btPre, h0, ↓reduceIte] at hpre
      rw [tb_holdsList_append_noRet (tb_noRetList_flatten_range _ _ (btNibT_noRet n)),
        tb_holdsList_flatten_range _ _ (btNibT_noRet n)] at hpre
      obtain ⟨-, hg'⟩ := btNib_ptr hk (hpre.1 k hk)
      subst hpb
      rw [hg', p2]
      have hv := bitsVal_lt (btF σ (btC k)) (btW n k)
      have hw4 := btW_le n k
      refine ptrIn_mul (ptrIn_mono hg ?_)
      have : 2 ^ btW n k ≤ 16 := by
        calc 2 ^ btW n k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hw4
          _ = 16 := by norm_num
      have : k + 1 ≤ btN n := hk
      omega
  · exfalso
    obtain ⟨t, ht, -⟩ := List.mem_map.mp hc
    obtain ⟨s, hs, hst⟩ := List.mem_filterMap.mp ht
    have := hnc s hs
    cases s <;> simp_all [noCallSB, Stmt.callSF, Main.Stmt.callS]

end
end LeanVM.Guest.B1.Tables
