/-
  LeanVM.Guest.B1.Tables.Vt.SelBlock

  What a table block's selector statements give: its eq weight is `eqAbove` at its placement.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.SelBlocks

/-!
# A table block's selector

`vt_selblock`: from a table block's statements (`vtSelT`), its table's shared tables (`vt_shared`)
and its certified offset (`vt_sort`), the block's eq weight is `eqAbove ⟨τ_t, offset⟩` at the bus
point, its copy is it, and the running `selector_sum` grows by it.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- The running sum after a block: the eq weight at the side's first block, else the sum. -/
def vtSelSum (w t : ℕ) (prev : Option ℕ) : ℕ := if prev.isNone then vtSelE w t else vtSelE w t + 3

/-- The block's copy of its eq weight. -/
def vtSelCopy (w t : ℕ) (prev : Option ℕ) : ℕ := if prev.isNone then vtSelE w t + 3 else vtSelE w t + 4

/-- **A table block's selector.** -/
theorem vt_selblock {rd : Reader} {σ : Val} (h : VtH rd σ) {w b t pos : ℕ} {prev : Option ℕ}
    (hcheck : tbStmtsEqb (vtSelT w b t prev) ((vtPre.drop pos).take (vtSelT w b t prev).length) =
      true) (ht : t < 6) {point : List E} {d τ : ℕ} (hpl : point.length = d + τ) (hd34 : d + τ ≤ 34)
    (hdv : σ (.n (vtShLen t)) = gen ^ d)
    (hrun : RunTables rd (σ (.n 2769) * gen ^ (288 * t)) (σ (.n 2770) * gen ^ (144 * t)) d
      (point.drop τ) ((point.map (1 + ·)).drop τ) ((gSquaresList.drop τ).take d))
    {off : ℕ} (hoff : LoadHolds rd (σ (.n 185)) b (gen ^ off)) (hob : off < 2 ^ 62) :
    σ (.n (vtSelE w t)) = Placement.eqAbove ⟨τ, off, 0⟩ point ∧
      σ (.n (vtSelCopy w t prev)) = σ (.n (vtSelE w t)) ∧
      σ (.n (vtSelSum w t prev)) = (match prev with | none => 0 | some p => σ (.n p)) +
        σ (.n (vtSelE w t)) := by
  obtain ⟨k, hs⟩ := h.slice pos _ hcheck
  -- the template's facts, uniformly in `t`
  obtain ⟨eqt, gt, heqt, hgt, hd, hl, hq, hrest⟩ : ∃ eqt gt : V,
      σ eqt = σ (.n 2769) * gen ^ (288 * t) ∧ σ gt = σ (.n 2770) * gen ^ (144 * t) ∧
      (∃ (j : ℕ) (hj : j < vtBstNames.length), σ (.n (vtShLen t)) = ofK (Parameters.gpow j) ∧
        coreProgram.Rel rd vtBstNames[j] [σ (.n (w + 9)), σ eqt, σ gt]
          [σ (.n (vtSelE w t)), σ (.n (vtSelE w t + 1))]) ∧
      LoadHolds rd (σ (.n 185)) b (σ (.n (vtSelE w t + 2))) ∧
      σ (.n (vtSelE w t + 1)) = σ (.n (vtSelE w t + 2)) ∧
      Stmt.HoldsList (coreProgram.Rel rd) rd σ (vtSelTail w t prev) True k := by
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · simp only [vtSelT, ↓reduceIte, List.nil_append, List.cons_append,
        Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hs
      obtain ⟨-, -, -, -, -, -, -, -, -, hdisp, lE, qE, hr⟩ := hs
      simp only [Atom.Holds] at lE qE
      exact ⟨.n 2769, .n 2770, by simp, by simp, hdisp, lE, e_add_eq_zero_iff.mp qE, hr⟩
    · have ht' : t ≠ 0 := by omega
      simp only [vtSelT, ht', ↓reduceIte, List.cons_append, List.nil_append,
        Stmt.HoldsList, Stmt.Holds] at hs
      obtain ⟨-, -, -, -, -, -, -, -, -, c10, m11, c12, m13, hdisp, lE, qE, hr⟩ := hs
      simp only [Atom.Holds] at c10 m11 c12 m13 lE qE
      refine ⟨.n (w + 11), .n (w + 13), ?_, ?_, hdisp, lE, e_add_eq_zero_iff.mp qE, hr⟩
      · rw [m11, c10, vtShC1_word ht]
      · rw [m13, c12, vtShC2_word ht]
  -- the arm
  obtain ⟨j, hj, hjv, hrel⟩ := hd
  have hj34 : j < 34 := by simpa [vtBstNames] using hj
  rw [hdv, ← gen_pow_eq_ofK] at hjv
  obtain rfl := gen_pow_inj (by omega) (by omega) hjv
  simp only [vtBstNames, List.getElem_map, List.getElem_range] at hrel
  have hb := block_selector_tab_holds _ hj34 _ _ _ hrel
  simp only [BlockSelTabOut] at hb
  obtain ⟨bs, hbl, -, hout⟩ := hb
  rw [heqt, hgt] at hout
  have hsq := gSquaresList
  obtain ⟨he, hg⟩ := hout _ _ _ (by simp; omega) (by simp; omega)
    (by simp [gSquaresList]; omega) hrun
  rw [vt_bitsPow_sq hbl (by omega)] at hg
  have hoff' := tb_loadHolds_unique hl hoff
  rw [← hq, hg] at hoff'
  have e := vt_offset_bits (by omega) hob hoff'
  refine ⟨by rw [he, vt_eqAbove hbl (by omega), ← e], ?_, ?_⟩
  · cases prev with
    | none =>
      simp only [vtSelTail, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hrest
      simp only [vtSelCopy, Option.isNone_none, ↓reduceIte]; exact hrest
    | some p =>
      simp only [vtSelTail, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hrest
      simp only [vtSelCopy, Option.isNone_some, Bool.false_eq_true, ↓reduceIte]; exact hrest.2
  · cases prev with
    | none => simp [vtSelSum]
    | some p =>
      simp only [vtSelTail, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hrest
      simp only [vtSelSum, Option.isNone_some, Bool.false_eq_true, ↓reduceIte]; exact hrest.1

end
end LeanVM.Guest.B1.Tables
