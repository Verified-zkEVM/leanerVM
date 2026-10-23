/-
  LeanVM.Guest.B1.VerifySub.Known

  `col_kappas` is in range after `verify_sub`'s placement and the stack's log check
  (G:3310-3315): the tail of `VsKnown`.
-/

module

public import LeanVM.Guest.B1.VerifySub.Mid
public import LeanVM.Guest.B1.Placement.Certify
public import LeanVM.Guest.B1.Placement.Kappas

/-!
# The columns' logs, from the placement and the stack's log

`vsKnown_tail`: from `kappa_base = [1, g^logMem, g^h…]` (`logMem ≤ 32`, the six heights below
`29`) and the exponent tables, the first statements of `vsTailT` — `certify_placement`,
`m = max 15 (log2Ceil total)` in the exponent, and `g^(m - 22)` range-checked below `g^6` — give
`m ≤ 28`, so every committed column's log in `col_kappas` is below `29` (`hypKappa_holds`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {σ : Val} {next : Prop} {kret : List E → Prop}

/-- `LIG_MIN_SHIFT_INV = g^-22`. -/
theorem kn_word_ginv22_mul : word 8198552432976855044 0 0 * gen ^ 22 = 1 := by
  rw [show gen ^ 22 = ofK (K.ofBits (2 ^ 22)) by
      rw [← word_two_pow (a := 22) (by decide)]; exact word_eOfNat _,
    show word 8198552432976855044 0 0 = ofK (K.ofBits 8198552432976855044) from word_eOfNat _,
    ← ofK_mul, show K.ofBits 8198552432976855044 * K.ofBits (2 ^ 22) = 1 by decide +kernel, ofK_one]

theorem kn_hs_getD_le {hs : List ℕ} (hh : ∀ x ∈ hs, x < 29) (i : ℕ) : hs.getD i 0 ≤ 28 := by
  rw [List.getD_eq_getElem?_getD]
  rcases hx : hs[i]? with _ | x
  · simp
  · have := hh x (List.mem_of_getElem? hx)
    simp only [Option.getD_some]; omega

theorem kn_columnKappas_le {logMem : ℕ} {hs : List ℕ} (hh : ∀ x ∈ hs, x < 29) (hm : logMem ≤ 32) :
    ∀ x ∈ columnKappas logMem Tables.guestLogBytecode hs, x ≤ 34 := by
  intro x hx
  unfold columnKappas at hx
  rw [List.mem_append] at hx
  have hq : qkeccakSlotBits = 6 := by decide
  rcases hx with hx | hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · omega
    · omega
    · omega
    · omega
    · show 19 ≤ 34; omega
    · have := kn_hs_getD_le hh opKeccak; omega
  · rw [List.mem_flatMap] at hx
    obtain ⟨t, -, ht⟩ := hx
    rw [(List.mem_replicate.1 ht).2]
    have := kn_hs_getD_le hh t.opcode; omega

theorem kn_stackTotal_lt {kappas : List ℕ} (hl : kappas.length = 163) (hk : ∀ x ∈ kappas, x ≤ 34) :
    Tables.stackTotal kappas < 2 ^ 60 := by
  have hle := List.sum_le_length_nsmul ((Tables.committedKappas kappas).map (2 ^ ·)) (2 ^ 34) (by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    refine Nat.pow_le_pow_right (by norm_num) ?_
    simp only [Tables.committedKappas, List.mem_map] at hx
    obtain ⟨c, -, rfl⟩ := hx
    rw [List.getD_eq_getElem?_getD]
    rcases hc : kappas[c]? with _ | z
    · simp
    · simp only [Option.getD_some]; exact hk z (List.mem_of_getElem? hc))
  have hlen : (Tables.committedKappas kappas).length ≤ 163 := by
    simp only [Tables.committedKappas, Tables.committedCols, List.length_map]
    exact (List.length_filter_le _ _).trans (by simp [hl])
  simp only [List.length_map, smul_eq_mul] at hle
  unfold Tables.stackTotal
  calc _ ≤ _ := hle
    _ ≤ 163 * 2 ^ 34 := Nat.mul_le_mul_right _ hlen
    _ < 2 ^ 60 := by norm_num

/-- **The tail of `VsKnown`**: the placement and the stack's log check put every committed
column's log in `col_kappas` below `29`. -/
theorem vsKnown_tail {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (L : MemImage κ)
    (hC : CallRel.Le C (coreProgram.Rel L.read)) (hexp : B1.ExpTables L.read (σ (.n 4)) (σ (.n 5)))
    {logMem : ℕ} {hs : List ℕ} (hm : logMem ≤ 32) (hl : hs.length = 6) (hh : ∀ x ∈ hs, x < 29)
    (hkb : ReadsAt L.read (σ (.n 141)) (1 :: gen ^ logMem :: hs.map (gen ^ ·)))
    (h : Stmt.HoldsList C L.read σ (vsTailT.take 14) next kret) :
    ∀ c < 113, ∃ e < 29, LoadHolds L.read (σ (.n 1889)) c (ofK (gpow e)) := by
  simp only [vsTailT, List.cons_append, List.take_succ_cons, Stmt.HoldsList, Stmt.Holds, vsCall,
    vsConst, vsMul, vsRange, List.map_cons, List.map_nil, Atom.Holds] at h
  obtain ⟨c1, c2, e1891, m1892, e1893, r1892, -⟩ := h
  -- the placement
  have hsq : Tables.TbReadsAt L.read (σ (.n 5)) Tables.gSquaresList := by
    intro k hk
    simp only [Tables.gSquaresList, List.length_map, List.length_range] at hk
    simp only [Tables.gSquaresList, List.getElem_map, List.getElem_range]
    exact (hexp k hk).2
  obtain ⟨off, kap, hr, hP⟩ := Tables.certify_placement_holds hκ L logMem hs _ _ _ hm hl hh hkb
    hsq (hC _ _ _ c1)
  simp only [List.cons.injEq, and_true] at hr
  obtain ⟨h1887, -, h1889⟩ := hr
  -- the stack's log
  obtain ⟨N, hN, hgN, hlt, -, -, hr2⟩ :=
    (log2_ceil_in_the_exponent_L15_L34_iff hκ hκ6 L hexp _).1 (hC _ _ _ c2)
  simp only [List.cons.injEq, and_true] at hr2
  have hST : Tables.stackTotal (columnKappas logMem Tables.guestLogBytecode hs) = N := by
    refine gen_pow_inj ?_ (by omega) (h1887.symm.trans hgN)
    have := kn_stackTotal_lt hP.1 (kn_columnKappas_le hh hm)
    omega
  obtain ⟨e, he, h1892⟩ := rc_pow hκ hκ6 L (a := 6) (by norm_num)
    (by rw [e1893, show (64 : ℕ) = 2 ^ 6 from rfl, word_pow2 (by norm_num)]) r1892
  have hm28 : max 15 (log2Ceil N) = e + 22 := by
    have := congrArg (· * gen ^ 22) (m1892.symm.trans h1892)
    simp only [hr2, e1891, mul_assoc, kn_word_ginv22_mul, mul_one, ← pow_add] at this
    exact gen_pow_inj (by omega) (by omega) this
  have h28 : log2Ceil (Tables.stackTotal (columnKappas logMem Tables.guestLogBytecode hs)) ≤ 28 := by
    rw [hST]; omega
  intro c hc
  obtain ⟨k, hk, hload⟩ := Tables.hypKappa_holds L.read _ off kap hP h28 c hc
  exact ⟨k, hk, by rw [h1889, ← gen_pow_eq_ofK]; exact hload⟩

end
end LeanVM.Guest.B1.VerifySub
