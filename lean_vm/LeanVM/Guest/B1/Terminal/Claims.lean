/-
  LeanVM.Guest.B1.Terminal.Claims

  Each claim's term of `check_opening_terminal`'s sum is the claim's batched weight on the stack.
-/

module

public import LeanVM.Guest.B1.Terminal.Blocks
public import LeanVM.Guest.B1.Terminal.Weights
public import LeanVM.Guest.B1.Terminal.Layout

/-!
# The claims' terms

`TermCtx` collects what the head of `check_opening_terminal` and its precondition establish about
the words the claims' blocks read: the batching powers, the selectors (`selProd` of each committed
column's offset bits), the chains at `zeta` and `chi` (the points' weights), the slot points, the
public input's chain, the columns' sizes and placements and the claims' points. `claimTerm_eq`:
claim `j`'s term is `λ^(1 + poolRank j)` times its weight on the stack, `0` for an output lane.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier Finset

@[expose] public section

/-- The claims' global columns: the bus's `0 .. 4`, the tables' `6 .. 162`, the public input's
`0 .. 2`. -/
def claimColOf (j : ℕ) : ℕ := if j < 5 then j else if j < 162 then j + 1 else j - 162

theorem claimColumns_eq : Tables.claimColumns = (List.range 165).map claimColOf := by
  decide +kernel

theorem claimColumns_getD {j : ℕ} (hj : j < 165) : Tables.claimColumns.getD j 0 = claimColOf j := by
  rw [claimColumns_eq, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map,
    List.getElem_range]

theorem claimCol_out {j : ℕ} (hj : j < 165) :
    Tables.claimColumns.getD j 0 ∈ keccakOutputColumns ↔ 110 ≤ j ∧ j < 135 := by
  rw [claimColumns_getD hj, keccakOutputColumns_eq, claimColOf]
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨a, ha, he⟩; split at he <;> [omega; split at he <;> omega]
  · rintro ⟨h1, h2⟩; exact ⟨j - 110, by omega, by split <;> [omega; split <;> omega]⟩

theorem gen_pow_inj_le {a b : ℕ} (ha : a ≤ 64) (hb : b ≤ 64) (h : gen ^ a = gen ^ b) : a = b :=
  gen_pow_inj (lt_of_le_of_lt ha (by norm_num)) (lt_of_le_of_lt hb (by norm_num)) h

/-- What the head and the precondition give the claims' blocks. -/
structure TermCtx (rd : Reader) (σ : Val) (layout : Layout) (kappas : List ℕ)
    (claims : List ColumnClaim) (zs chis x : List E) (lam rm : E) (cp : ℕ → ℕ) : Prop where
  hkap : kappas.length = 163
  hP : layout.placements = (placementsOf kappas).1
  hx : x.length = layout.stackLog
  hL : layout.stackLog ≤ 28
  hK : ∀ c < Tables.nCommittedCols, (Tables.committedKappas kappas).getD c 0 ≤ layout.stackLog
  hq : 2 ^ (Tables.committedKappas kappas).getD 5 0 ∣
    (stackOffsets (Tables.committedKappas kappas)).1.getD 5 0
  hK5 : (Tables.committedKappas kappas).getD 5 0 = layout.tableLogHeights.getD opKeccak 0 + 6
  hlane : ∀ g, 73 ≤ g → g < 163 → kappas.getD g 0 = layout.tableLogHeights.getD opKeccak 0
  hmem : ∀ c < 3, (Tables.committedKappas kappas).getD c 0 = layout.logMemory
  hlm : 1 ≤ layout.logMemory
  hmem0 : (layout.placement memory0).vars = layout.logMemory
  hcols : claims.map (·.column) = Tables.claimColumns
  hzs : zs.length ≤ 40
  hchis : chis.length ≤ zs.length
  hpz : ∀ j < 5, (claims.getD j default).point = zs.take (claims.getD j default).point.length
  hpc : ∀ j, 5 ≤ j → j < 162 →
    (claims.getD j default).point = chis.take (claims.getD j default).point.length
  hpp : ∀ j, 162 ≤ j → j < 165 → (claims.getD j default).point =
    rm :: List.replicate ((layout.placement memory0).vars - 1) 0
  hcp : ∀ j < 162, cp j = (claims.getD j default).point.length
  hlam : ∀ j < 165, termKind j ≠ 4 → valOf rd (σ (.n 9)) j = lam ^ (1 + poolRank j)
  hsel : ∀ c < Tables.nCommittedCols, σ (.n (selV c)) =
    selProd ((stackOffsets (Tables.committedKappas kappas)).1.getD c 0)
      ((Tables.committedKappas kappas).getD c 0)
      (layout.stackLog - (Tables.committedKappas kappas).getD c 0) x
  hzc : ∀ n ≤ zs.length, n ≤ layout.stackLog →
    valOf rd (σ (.n 19)) n = eqEval (zs.take n) (x.take n)
  hrc : ∀ n ≤ chis.length, n ≤ layout.stackLog →
    valOf rd (σ (.n 21)) n = eqEval (chis.take n) (x.take n)
  hs1 : ∀ k < 6, valOf rd (σ (.n 23)) k = x.getD (layout.tableLogHeights.getD opKeccak 0 + k) 0
  hs0 : ∀ k < 6, valOf rd (σ (.n 24)) k = 1 + x.getD (layout.tableLogHeights.getD opKeccak 0 + k) 0
  h33 : σ (.n 33) = eqEval (rm :: List.replicate (layout.logMemory - 1) 0) (x.take layout.logMemory)
  hok : ∀ j < 165, ClaimOk rd σ cp j
  hkv : ∀ c < Tables.nCommittedCols, valOf rd (σ (.n 11)) c = gen ^ (Tables.committedKappas kappas).getD c 0

theorem claim_column {claims : List ColumnClaim} (hcols : claims.map (·.column) = Tables.claimColumns)
    {j : ℕ} (hj : j < 165) : (claims.getD j default).column = claimColOf j := by
  have hl : claims.length = 165 := by
    rw [← List.length_map (f := (·.column)), hcols, claimColumns_eq]; simp
  rw [← claimColumns_getD hj, ← hcols, List.getD_eq_getElem _ _ (by omega),
    List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map]

/-- A pooled claim on a committed column, its point a prefix of `A` read by the chain `ch`. -/
theorem term_committed {layout : Layout} {kappas : List ℕ} {x : List E} {c : ColumnClaim}
    {cc : ℕ} (hcc : cc < Tables.nCommittedCols) (hkap : kappas.length = 163)
    (hP : layout.placements = (placementsOf kappas).1)
    (hcol : c.column = (Tables.committedCols 163).getD cc 0)
    (hx : x.length = layout.stackLog) (hK : (Tables.committedKappas kappas).getD cc 0 ≤ layout.stackLog)
    (hlen : c.point.length = (Tables.committedKappas kappas).getD cc 0) {L chainV sel : E}
    (hch : chainV = eqEval c.point (x.take c.point.length))
    (hsel : sel = selProd ((stackOffsets (Tables.committedKappas kappas)).1.getD cc 0)
      ((Tables.committedKappas kappas).getD cc 0)
      (layout.stackLog - (Tables.committedKappas kappas).getD cc 0) x) :
    L * chainV * sel = L * wOf layout x c := by
  rw [wOf_committed (by rw [hcol]; exact placement_committed hkap hP hcc) hlen hx hK, hch, hsel,
    hlen, mul_assoc]

/-- The slot factor is the slot's bits' weight. -/
theorem slotProd_eq {τ s : ℕ} {x : List E} {s1 s0 : ℕ → E} (h1 : ∀ k < 6, s1 k = x.getD (τ + k) 0)
    (h0 : ∀ k < 6, s0 k = 1 + x.getD (τ + k) 0) :
    slotProd s1 s0 s = ∏ i ∈ range 6, bitF (s.testBit i) (x.getD (τ + i) 0) := by
  have hf : ∀ k < 6, (if s.testBit k then s1 k else s0 k) = bitF (s.testBit k) (x.getD (τ + k) 0) := by
    intro k hk
    unfold bitF
    split
    · exact h1 k hk
    · exact h0 k hk
  simp only [slotProd, prod_range_succ, prod_range_zero, one_mul]
  rw [hf 0 (by decide), hf 1 (by decide), hf 2 (by decide), hf 3 (by decide), hf 4 (by decide),
    hf 5 (by decide)]
  ring

/-- **Claim `j`'s term** is its batched weight on the stack, `0` on an output lane. -/
theorem claimTerm_eq {rd : Reader} {σ : Val} {layout : Layout} {kappas : List ℕ}
    {claims : List ColumnClaim} {zs chis x : List E} {lam rm : E} {cp : ℕ → ℕ}
    (T : TermCtx rd σ layout kappas claims zs chis x lam rm cp) {j : ℕ} (hj : j < 165) :
    claimTerm rd σ cp j = if Tables.claimColumns.getD j 0 ∉ keccakOutputColumns then
      lam ^ (1 + poolRank j) * wOf layout x (claims.getD j default) else 0 := by
  have hcolj := claim_column T.hcols hj
  have hout := claimCol_out hj
  by_cases h4 : 110 ≤ j ∧ j < 135
  · have hk : termKind j = 4 := by unfold termKind; split_ifs <;> omega
    simp only [claimTerm, hk, hout.mpr h4, not_true_eq_false, ↓reduceIte]
  have hnot : Tables.claimColumns.getD j 0 ∉ keccakOutputColumns := fun h ↦ h4 (hout.mp h)
  simp only [hnot, not_false_eq_true, ↓reduceIte]
  have hok := T.hok j hj
  have hL := T.hL
  have hzs := T.hzs
  have hchis := T.hchis
  have hNC : Tables.nCommittedCols = 99 := rfl
  by_cases h0 : j < 5
  · have hk : termKind j = 0 := by unfold termKind; simp [h0]
    have ht : termCol j = j := by unfold termCol; simp [h0]
    simp only [claimTerm, ClaimOk, hk, ht] at hok ⊢
    rw [T.hlam j hj (by omega)]
    have hp := T.hpz j h0
    have hpl : (claims.getD j default).point.length ≤ zs.length := by
      have := congrArg List.length hp; rw [List.length_take] at this; omega
    rw [T.hkv j (by omega), T.hcp j (by omega)] at hok
    have hKj := T.hK j (by omega)
    have hκ := gen_pow_inj_le (by omega) (by omega) hok
    refine term_committed (cc := j) (by omega) T.hkap T.hP ?_ T.hx hKj hκ ?_
      (T.hsel j (by omega))
    · rw [hcolj, committedCols_getD (by omega)]; simp [claimColOf, colOfCommitted, h0]; omega
    · rw [T.hcp j (by omega), T.hzc _ hpl (by rw [hκ]; exact hKj), ← hp]
  by_cases h1 : j < 72 ∨ (136 ≤ j ∧ j < 162)
  · have hk : termKind j = 1 := by unfold termKind; split_ifs <;> omega
    have ht : termCol j = if j < 72 then j + 1 else j - 63 := by
      unfold termCol; split_ifs <;> omega
    simp only [claimTerm, ClaimOk, hk] at hok ⊢
    rw [T.hlam j hj (by omega)]
    have hp := T.hpc j (by omega) (by omega)
    have hpl : (claims.getD j default).point.length ≤ chis.length := by
      have := congrArg List.length hp; rw [List.length_take] at this; omega
    have hcc : termCol j < Tables.nCommittedCols := by rw [ht]; split <;> omega
    rw [T.hkv _ hcc, T.hcp j (by omega)] at hok
    have hKj := T.hK _ hcc
    have hκ := gen_pow_inj_le (by omega) (by omega) hok
    refine term_committed (cc := termCol j) hcc T.hkap T.hP ?_ T.hx hKj hκ ?_ (T.hsel _ hcc)
    · rw [hcolj, committedCols_getD hcc, ht, claimColOf, colOfCommitted]; split_ifs <;> omega
    · rw [T.hcp j (by omega), T.hrc _ hpl (by rw [hκ]; exact hKj), ← hp]
  by_cases h2 : (72 ≤ j ∧ j < 110) ∨ j = 135
  · have hk : termKind j = 2 := by unfold termKind; split_ifs <;> omega
    simp only [claimTerm, ClaimOk, hk] at hok ⊢
    rw [T.hlam j hj (by omega)]
    have hp := T.hpc j (by omega) (by omega)
    have hpl : (claims.getD j default).point.length ≤ chis.length := by
      have := congrArg List.length hp; rw [List.length_take] at this; omega
    have hw : word 64 0 0 = gen ^ 6 := word_two_pow (a := 6) (by decide)
    rw [T.hkv 5 (by decide), T.hK5, T.hcp j (by omega), hw, ← pow_add] at hok
    have hK5 := T.hK 5 (by decide)
    rw [T.hK5] at hK5
    have hκ : (claims.getD j default).point.length = layout.tableLogHeights.getD opKeccak 0 := by
      have := gen_pow_inj_le (by omega) (by omega) hok
      omega
    have hpl' : layout.placement (claims.getD j default).column =
        Placement.mk (layout.tableLogHeights.getD opKeccak 0)
          ((stackOffsets (Tables.committedKappas kappas)).1.getD 5 0 +
            termSlot j * 2 ^ layout.tableLogHeights.getD opKeccak 0) 0 := by
      have e1 : claimColOf j = j + 1 := by simp [claimColOf, show ¬ j < 5 by omega, show j < 162 by omega]
      have es : slotOfCol (j + 1) = some (termSlot j) := by
        unfold slotOfCol termSlot; split_ifs <;> first | rfl | omega
      rw [hcolj, e1, placement_slot T.hkap T.hP (by omega) es, T.hlane _ (by omega) (by omega)]
    have hslot : termSlot j < 64 := by unfold termSlot; split_ifs <;> omega
    have hq := T.hq
    rw [T.hK5] at hq
    rw [wOf_lane hpl' hκ T.hx hK5 hq hslot, T.hsel 5 (by decide), T.hK5,
      slotProd_eq (τ := layout.tableLogHeights.getD opKeccak 0) (fun k hk ↦ T.hs1 k hk)
        (fun k hk ↦ T.hs0 k hk),
      T.hcp j (by omega), T.hrc _ hpl (by omega), ← hp, hκ]
    ring
  -- the public input's claims
  have h3 : 162 ≤ j := by omega
  have hk : termKind j = 3 := by unfold termKind; split_ifs <;> omega
  have ht : termCol j = j - 162 := by unfold termCol; split_ifs <;> omega
  simp only [claimTerm, hk, ht]
  rw [T.hlam j hj (by omega)]
  have hp := T.hpp j h3 hj
  rw [T.hmem0] at hp
  have hlen : (claims.getD j default).point.length =
      (Tables.committedKappas kappas).getD (j - 162) 0 := by
    rw [hp, T.hmem _ (by omega)]; simp; have := T.hlm; omega
  refine term_committed (cc := j - 162) (by omega) T.hkap T.hP ?_ T.hx (T.hK _ (by omega)) hlen ?_
    (T.hsel _ (by omega))
  · rw [hcolj, committedCols_getD (by omega)]
    simp [claimColOf, colOfCommitted, show ¬ j < 5 by omega, show ¬ j < 162 by omega,
      show j - 162 < 73 by omega]
  · rw [T.h33, hlen, T.hmem _ (by omega), hp]

end
end LeanVM.Guest.B1.VerifySub
