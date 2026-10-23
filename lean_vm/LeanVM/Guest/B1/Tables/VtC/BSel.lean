/-
  LeanVM.Guest.B1.Tables.VtC.BSel

  `verify_tables`' block selectors complete: a table block's (`vtSelT`, `block_selector_tab`) and
  a framework block's (`vtFwSelT`, `block_selector`), on an aligned offset whose bits the memory
  holds, the callee returning the honest eq weight and `g^offset`.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.BBase
public import LeanVM.Guest.B1.Tables.Vt.SelBlock
public import LeanVM.Guest.B1.Tables.Vt.SelFw
public import LeanVM.Guest.B1.Selectors.BlockSelectorTabComplete
public import LeanVM.Guest.B1.Selectors.BlockSelectorComplete

/-!
# The block selectors, complete

`offBits off`: the `34` bits of an offset, as the `bitsExp` hint writes them; `selBitsOf off τ d`:
its bits `τ ..< τ + d`, whose value shifted by `τ` is the offset when it is aligned to `2^τ` and
below `2^(τ + d)` (`selBitsOf_val`).

`vtc_selblock`: a table block's statements hold, its eq weight is `eqAbove ⟨τ, off⟩` at the bus
point, its copy is it, its running sum grows by it. `vtc_fwblock`: the same for a framework block.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Fwd LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- The `34` bits of an offset, as words. -/
def offBits (off : ℕ) : List E := (List.range 34).map fun j ↦ bitE (off.testBit j)

/-- Bits `τ ..< τ + d` of an offset. -/
def selBitsOf (off τ d : ℕ) : List Bool := (List.range d).map fun i ↦ off.testBit (τ + i)

theorem selBitsOf_length (off τ d : ℕ) : (selBitsOf off τ d).length = d := by simp [selBitsOf]

theorem selBitsOf_val {off τ d : ℕ} (hal : 2 ^ τ ∣ off) (hob : off < 2 ^ (τ + d)) :
    2 ^ τ * vtBitsV (selBitsOf off τ d) d = off := by
  have hq : off / 2 ^ τ < 2 ^ d := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos τ), ← pow_add, Nat.add_comm]; exact hob
  have e : vtBitsV (selBitsOf off τ d) d = off / 2 ^ τ := by
    rw [vtBitsV, bitsVal_congr (f' := (off / 2 ^ τ).testBit) (fun i hi ↦ ?_), bitsVal_testBit hq]
    rw [Nat.testBit_div_two_pow, selBitsOf, List.getD_eq_getElem _ _ (by simpa using hi)]
    simp [Nat.add_comm]
  rw [e, Nat.mul_div_cancel' hal]

/-- The selector bits the shifted pointer reads. -/
theorem selBits_reads {rd : Reader} {p : E} {off τ d : ℕ} (hd : τ + d ≤ 34)
    (h : TbReadsAt rd p (offBits off)) :
    TbReadsAt rd (p * gen ^ τ) ((selBitsOf off τ d).map bitE) := by
  have e : (selBitsOf off τ d).map bitE = ((offBits off).drop τ).take d := by
    apply List.ext_getElem (by simp [selBitsOf, offBits]; omega)
    intro i h1 _
    simp only [selBitsOf, List.length_map, List.length_range] at h1
    simp [selBitsOf, offBits]
  rw [e]
  exact tbReadsAt_take (tbReadsAt_drop h τ) d

section
variable {rd : Reader} {wo : ℕ → E} {args : List E}

set_option maxHeartbeats 1000000 in
/-- **A table block's selector, complete.** -/
theorem vtc_selblock (hl : args.length = 22) {v b t pos : ℕ} {prev : Option ℕ}
    (hcheck : tbStmtsEqb (vtSelT v b t prev) ((vtPre.drop pos).take (vtSelT v b t prev).length) =
      true) (ht : t < 6) (hv : 2770 < v)
    (hS : Atom.load (.n v) (.n 12) b ∉ vtSL ∧ Atom.load (.n (v + 7)) (.n 185) b ∉ vtSL ∧
      Atom.load (.n (v + 8)) (.n 10) (t + 1) ∉ vtSL ∧
      Atom.load (.n (vtSelE v t + 2)) (.n 185) b ∉ vtSL)
    {point : List E} {d τ : ℕ} (hpl : point.length = d + τ) (hml : point.length < 33) (hτ : τ < 29)
    (hdv : vtσ rd wo args (.n (vtShLen t)) = gen ^ d)
    (hrun : RunTables rd (vtσ rd wo args (.n 2769) * gen ^ (288 * t))
      (vtσ rd wo args (.n 2770) * gen ^ (144 * t)) d
      (point.drop τ) ((point.map (1 + ·)).drop τ) ((gSquaresList.drop τ).take d))
    (hbk : LoadHolds rd (vtσ rd wo args (.n 12)) b (gen ^ τ))
    (hdim : LoadHolds rd (vtσ rd wo args (.n 10)) (t + 1) (gen ^ τ))
    {off : ℕ} (hoff : LoadHolds rd (vtσ rd wo args (.n 185)) b (gen ^ off)) (hal : 2 ^ τ ∣ off)
    (hob : off < 2 ^ point.length)
    (hbits : TbReadsAt rd (vtσ rd wo args (.n (v + 6))) (offBits off))
    (hw0 : wo (vtSelE v t) = Placement.eqAbove ⟨τ, off, 0⟩ point)
    (hw1 : wo (vtSelE v t + 1) = gen ^ off)
    (hlow : ∀ i < 34, (rd (Parameters.gpow i)).isSome) :
    (∀ s ∈ vtSelT v b t prev, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s) ∧
      vtσ rd wo args (.n (vtSelE v t)) = Placement.eqAbove ⟨τ, off, 0⟩ point ∧
      vtσ rd wo args (.n (vtSelCopy v t prev)) = vtσ rd wo args (.n (vtSelE v t)) ∧
      vtσ rd wo args (.n (vtSelSum v t prev)) =
        (match prev with | none => 0 | some p => vtσ rd wo args (.n p)) +
          vtσ rd wo args (.n (vtSelE v t)) := by
  have hmem : ∀ s ∈ vtSelT v b t prev, s ∈ vtPre := fun s hs ↦ vt_mem_slice hcheck hs
  have hd34 : d + τ ≤ 32 := by omega
  obtain ⟨hS0, hS7, hS8, hSE⟩ := hS
  -- the reads
  have r0 := vtB_readM hl (hmem _ (by simp [vtSelT])) hS0 hbk
  have r7 := vtB_readM hl (hmem _ (by simp [vtSelT])) hS7 hoff
  have r8 := vtB_readM hl (hmem _ (by simp [vtSelT])) hS8 hdim
  have rE := vtB_readM hl (hmem _ (by simp [vtSelT])) hSE hoff
  -- the equations
  have hG : ∀ s ∈ vtSelT v b t prev, GoodS rd vtSL wo (vtσ rd wo args) (fixNe s) :=
    fun s hs ↦ vt_goodS hl (hmem s hs)
  have g1 := hG (.atom (.const (.n (v + 1)) vtW33)) (by simp [vtSelT])
  have g9 := hG (.atom (.mul (.n (v + 9)) (.n (v + 6)) (.n (v + 8)))) (by simp [vtSelT])
  simp only [fixNe, GoodS, Good] at g1 g9
  rw [ite_pos' (by simp)] at g9
  -- the table pointers
  obtain ⟨eqt, gt, heqt, hgt, hdm⟩ : ∃ eqt gt : V,
      (vtσ rd wo args) eqt = (vtσ rd wo args) (.n 2769) * gen ^ (288 * t) ∧ (vtσ rd wo args) gt = (vtσ rd wo args) (.n 2770) * gen ^ (144 * t) ∧
      Stmt.dispatch (.n (vtShLen t)) vtBstNames [.n (v + 9), eqt, gt]
        [.n (vtSelE v t), .n (vtSelE v t + 1)] ∈ vtSelT v b t prev := by
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · exact ⟨.n 2769, .n 2770, by simp, by simp, by simp [vtSelT]⟩
    · have ht' : t ≠ 0 := by omega
      have c10 := hG (.atom (.const (.n (v + 10)) (word (vtShC1.getD t 0) 0 0)))
        (by simp [vtSelT, ht'])
      have m11 := hG (.atom (.mul (.n (v + 11)) (.n 2769) (.n (v + 10)))) (by simp [vtSelT, ht'])
      have c12 := hG (.atom (.const (.n (v + 12)) (word (vtShC2.getD t 0) 0 0)))
        (by simp [vtSelT, ht'])
      have m13 := hG (.atom (.mul (.n (v + 13)) (.n 2770) (.n (v + 12)))) (by simp [vtSelT, ht'])
      simp only [fixNe, GoodS, Good] at c10 m11 c12 m13
      rw [ite_pos' (by simp; omega)] at m11 m13
      refine ⟨.n (v + 11), .n (v + 13), ?_, ?_, by simp [vtSelT, ht']⟩
      · rw [m11, c10, vtShC1_word ht]
      · rw [m13, c12, vtShC2_word ht]
  have hrets := vtB_retsM (rd := rd) (w := wo) hl (hmem _ hdm)
  have e0 : (vtσ rd wo args) (.n (vtSelE v t)) = Placement.eqAbove ⟨τ, off, 0⟩ point := by
    rw [hrets _ (by simp), ← hw0]
  have e1 : (vtσ rd wo args) (.n (vtSelE v t + 1)) = gen ^ off := by rw [hrets _ (by simp), ← hw1]
  -- the callee
  set bs := selBitsOf off τ d with hbs
  have hbl : bs.length = d := selBitsOf_length off τ d
  have hval := selBitsOf_val hal (by rw [Nat.add_comm, ← hpl]; exact hob)
  have hsb : TbReadsAt rd ((vtσ rd wo args) (.n (v + 9))) (bs.map bitE) := by
    rw [g9, r8.1]; exact selBits_reads (by omega) hbits
  have hrel := block_selector_tab_complete_holds d (by omega) rd ((vtσ rd wo args) (.n (v + 9))) ((vtσ rd wo args) eqt) ((vtσ rd wo args) gt)
    bs (point.drop τ) ((point.map (1 + ·)).drop τ) ((gSquaresList.drop τ).take d) hbl
    (by simp; omega) (by simp; omega) (by simp [gSquaresList]; omega) hsb
    (by rw [heqt, hgt]; exact hrun)
  rw [vt_eqAbove (κ := τ) hbl (by omega), hval, vt_bitsPow_sq (κ := τ) hbl (by omega), hval] at hrel
  -- the tail
  have hT : ∀ s ∈ vtSelTail v t prev, GoodS rd vtSL wo (vtσ rd wo args) (fixNe s) :=
    fun s hs ↦ hG s (by simp only [vtSelT, List.mem_append]; exact Or.inr hs)
  have hcopy : (vtσ rd wo args) (.n (vtSelCopy v t prev)) = (vtσ rd wo args) (.n (vtSelE v t)) := by
    cases prev with
    | none =>
      have := hT (.atom (.copy (.n (vtSelE v t + 3)) (.n (vtSelE v t)))) (by simp [vtSelTail])
      simpa [vtSelCopy, fixNe, GoodS, Good] using this
    | some p =>
      have := hT (.atom (.copy (.n (vtSelE v t + 4)) (.n (vtSelE v t)))) (by simp [vtSelTail])
      simpa [vtSelCopy, fixNe, GoodS, Good] using this
  refine ⟨?_, e0, hcopy, ?_⟩
  swap
  · cases prev with
    | none =>
      show vtσ rd wo args (.n (vtSelE v t)) = 0 + _
      rw [zero_add]
    | some p =>
      have := hT (.atom (.add (.n (vtSelE v t + 3)) (.n p) (.n (vtSelE v t)))) (by simp [vtSelTail])
      simpa [vtSelSum, fixNe, GoodS, Good] using this
  -- every statement
  refine vtB_blockA hl pos _ hcheck fun s hs ha ↦ ?_
  have hd34' : d < vtBstNames.length := by simp [vtBstNames]; omega
  rcases Nat.eq_zero_or_pos t with rfl | ht0
  · simp only [vtSelT, ↓reduceIte, List.nil_append, List.cons_append, List.mem_cons] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hs
    · exact r0.2
    · simp [autoB, pureB, hintB] at ha
    · exact vshB_rcM hl (hmem _ (by simp [vtSelT])) (by simp) (K := 34) r0.1 (by rw [g1]; exact word_g33.trans (gen_pow_eq_ofK 33).symm) (by omega) hlow
    · simp [autoB, pureB, hintB] at ha
    · simp [autoB, pureB, hintB] at ha
    · exact r7.2
    · simp [autoB, pureB, hintB] at ha
    · exact r8.2
    · simp [autoB, pureB, hintB] at ha
    · refine vshB_dispatch hd34' hdv ?_
      simp only [vtBstNames, List.getElem_map, List.getElem_range, List.map_cons, List.map_nil]
      rw [e0, e1]
      simpa [heqt, hgt] using hrel
    · exact rE.2
    · exact vshB_eq (by rw [e1, rE.1])
    · cases prev <;> simp only [vtSelTail, List.mem_cons, List.not_mem_nil, or_false] at hs <;>
        rcases hs with rfl | rfl <;> simp [autoB, pureB, hintB] at ha
  · have ht' : t ≠ 0 := by omega
    simp only [vtSelT, ht', ↓reduceIte, List.cons_append, List.mem_cons, List.nil_append] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | hs
    · exact r0.2
    · simp [autoB, pureB, hintB] at ha
    · exact vshB_rcM hl (hmem _ (by simp [vtSelT])) (by simp) (K := 34) r0.1 (by rw [g1]; exact word_g33.trans (gen_pow_eq_ofK 33).symm) (by omega) hlow
    · simp [autoB, pureB, hintB] at ha
    · simp [autoB, pureB, hintB] at ha
    · exact r7.2
    · simp [autoB, pureB, hintB] at ha
    · exact r8.2
    · simp [autoB, pureB, hintB] at ha
    · simp [autoB, pureB, hintB] at ha
    · simp [autoB, pureB, hintB] at ha; omega
    · simp [autoB, pureB, hintB] at ha
    · simp [autoB, pureB, hintB] at ha; omega
    · refine vshB_dispatch hd34' hdv ?_
      simp only [vtBstNames, List.getElem_map, List.getElem_range, List.map_cons, List.map_nil]
      have c10 := hG (.atom (.const (.n (v + 10)) (word (vtShC1.getD t 0) 0 0)))
        (by simp [vtSelT, ht'])
      have m11 := hG (.atom (.mul (.n (v + 11)) (.n 2769) (.n (v + 10)))) (by simp [vtSelT, ht'])
      have c12 := hG (.atom (.const (.n (v + 12)) (word (vtShC2.getD t 0) 0 0)))
        (by simp [vtSelT, ht'])
      have m13 := hG (.atom (.mul (.n (v + 13)) (.n 2770) (.n (v + 12)))) (by simp [vtSelT, ht'])
      simp only [fixNe, GoodS, Good] at c10 m11 c12 m13
      rw [ite_pos' (by simp; omega)] at m11 m13
      rw [e0, e1, m11, c10, vtShC1_word ht, m13, c12, vtShC2_word ht, ← heqt, ← hgt]
      exact hrel
    · exact rE.2
    · exact vshB_eq (by rw [e1, rE.1])
    · cases prev <;> simp only [vtSelTail, List.mem_cons, List.not_mem_nil, or_false] at hs <;>
        rcases hs with rfl | rfl <;> simp [autoB, pureB, hintB] at ha

set_option maxHeartbeats 1000000 in
/-- **A framework block's selector, complete.** -/
theorem vtc_fwblock (hl : args.length = 22) {v b pos : ℕ} {prev : Option ℕ}
    (hcheck : tbStmtsEqb (vtFwSelT v b prev) ((vtPre.drop pos).take (vtFwSelT v b prev).length) =
      true) (hv : 2767 < v)
    (hS : Atom.load (.n v) (.n 12) b ∉ vtSL ∧ Atom.load (.n (v + 7)) (.n 185) b ∉ vtSL ∧
      Atom.load (.n (v + 18)) (.n 185) b ∉ vtSL)
    {point : List E} (hmu : vtσ rd wo args (.n 9) = gen ^ point.length) (hml : point.length < 33)
    (hz1 : TbReadsAt rd (vtσ rd wo args (.n 2767)) (point.map (1 + ·)))
    (hidxc : TbReadsAt rd (vtσ rd wo args (.n 2732)) vtIdxcList)
    {κ : ℕ} (hκ : LoadHolds rd (vtσ rd wo args (.n 12)) b (gen ^ κ)) (hκμ : κ ≤ point.length)
    {off : ℕ} (hoff : LoadHolds rd (vtσ rd wo args (.n 185)) b (gen ^ off)) (hal : 2 ^ κ ∣ off)
    (hob : off < 2 ^ point.length)
    (hbits : TbReadsAt rd (vtσ rd wo args (.n (v + 6))) (offBits off))
    (hw0 : wo (v + 16) = Placement.eqAbove ⟨κ, off, 0⟩ point) (hw1 : wo (v + 17) = gen ^ off)
    (hlow : ∀ i < 34, (rd (Parameters.gpow i)).isSome) :
    (∀ s ∈ vtFwSelT v b prev, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s) ∧
      vtσ rd wo args (.n (v + 16)) = Placement.eqAbove ⟨κ, off, 0⟩ point ∧
      vtσ rd wo args (.n (if prev.isNone then v + 19 else v + 20)) = vtσ rd wo args (.n (v + 16)) ∧
      vtσ rd wo args (.n (if prev.isNone then v + 16 else v + 19)) =
        (match prev with | none => 0 | some p => vtσ rd wo args (.n p)) +
          vtσ rd wo args (.n (v + 16)) := by
  have hmem : ∀ s ∈ vtFwSelT v b prev, s ∈ vtPre := fun s hs ↦ vt_mem_slice hcheck hs
  obtain ⟨hS0, hS7, hSE⟩ := hS
  obtain ⟨d, hpl⟩ : ∃ d, point.length = κ + d := ⟨point.length - κ, by omega⟩
  have r0 := vtB_readM hl (hmem _ (by simp [vtFwSelT])) hS0 hκ
  have r7 := vtB_readM hl (hmem _ (by simp [vtFwSelT])) hS7 hoff
  have rE := vtB_readM hl (hmem _ (by simp [vtFwSelT])) hSE hoff
  have hG : ∀ s ∈ vtFwSelT v b prev, GoodS rd vtSL wo (vtσ rd wo args) (fixNe s) :=
    fun s hs ↦ vt_goodS hl (hmem s hs)
  have g1 := hG (.atom (.const (.n (v + 1)) vtW33)) (by simp [vtFwSelT])
  have g8 := hG (.atom (.mul (.n 9) (.n (v + 8)) (.n v))) (by simp [vtFwSelT])
  have g9 := hG (.atom (.const (.n (v + 9)) vtW33)) (by simp [vtFwSelT])
  have g13 := hG (.atom (.mul (.n (v + 13)) (.n (v + 6)) (.n v))) (by simp [vtFwSelT])
  have g14 := hG (.atom (.mul (.n (v + 14)) (.n 2767) (.n v))) (by simp [vtFwSelT])
  have g15 := hG (.atom (.mul (.n (v + 15)) (.n 2732) (.n v))) (by simp [vtFwSelT])
  simp only [fixNe, GoodS, Good] at g1 g8 g9 g13 g14 g15
  rw [ite_neg' (by omega)] at g8
  rw [ite_pos' (by simp)] at g13
  rw [ite_pos' (by simp; omega)] at g14 g15
  have e8 : vtσ rd wo args (.n (v + 8)) = gen ^ d := by
    rw [g8, hmu, r0.1, hpl, ← pow_sub₀ _ gen_ne_zero (by omega : κ ≤ κ + d), Nat.add_sub_cancel_left]
  have hrets := vtB_retsM (rd := rd) (w := wo) hl (hmem _ (by simp [vtFwSelT] :
    Stmt.dispatch (.n (v + 8)) vtBsNames [.n (v + 13), .n (v + 14), .n (v + 15)]
      [.n (v + 16), .n (v + 17)] ∈ vtFwSelT v b prev))
  have e16 : vtσ rd wo args (.n (v + 16)) = Placement.eqAbove ⟨κ, off, 0⟩ point := by
    rw [hrets _ (by simp), ← hw0]
  have e17 : vtσ rd wo args (.n (v + 17)) = gen ^ off := by rw [hrets _ (by simp), ← hw1]
  -- the callee
  have hbl : (selBitsOf off κ d).length = d := selBitsOf_length off κ d
  have hval := selBitsOf_val hal (by rw [← hpl]; exact hob)
  have hsb : TbReadsAt rd (vtσ rd wo args (.n (v + 13))) ((selBitsOf off κ d).map bitE) := by
    rw [g13, r0.1]; exact selBits_reads (by omega) hbits
  have hz1' : TbReadsAt rd (vtσ rd wo args (.n (v + 14))) ((point.map (1 + ·)).drop κ) := by
    rw [g14, r0.1]; exact tbReadsAt_drop hz1 κ
  have hic : TbReadsAt rd (vtσ rd wo args (.n (v + 15))) ((vtIdxcList.drop κ).take d) := by
    rw [g15, r0.1]; exact tbReadsAt_take (tbReadsAt_drop hidxc κ) d
  have hrel := block_selector_complete_holds d (by omega) rd
    [vtσ rd wo args (.n (v + 13)), vtσ rd wo args (.n (v + 14)), vtσ rd wo args (.n (v + 15))]
    [Placement.eqAbove ⟨κ, off, 0⟩ point, gen ^ off]
    ⟨selBitsOf off κ d, (point.map (1 + ·)).drop κ, (vtIdxcList.drop κ).take d, hbl,
      by simp; omega, by simp [vtIdxcList]; omega, hsb, hz1', hic, ?_, ?_⟩
  rotate_left
  · rw [← List.map_drop, vt_eq_plusOne, List.map_drop, vt_eqAbove (κ := κ) hbl hpl, hval]
  · rw [vt_idxcProd (κ := κ) hbl (by omega), hval]
  have hT : ∀ s ∈ vtFwTail v prev, GoodS rd vtSL wo (vtσ rd wo args) (fixNe s) :=
    fun s hs ↦ hG s (by simp only [vtFwSelT, List.cons_append, List.mem_cons]; simp [hs])
  refine ⟨?_, e16, ?_, ?_⟩
  rotate_left
  · cases prev with
    | none =>
      have := hT (.atom (.copy (.n (v + 19)) (.n (v + 16)))) (by simp [vtFwTail])
      simpa [fixNe, GoodS, Good] using this
    | some p =>
      have := hT (.atom (.copy (.n (v + 20)) (.n (v + 16)))) (by simp [vtFwTail])
      simpa [fixNe, GoodS, Good] using this
  · cases prev with
    | none =>
      show vtσ rd wo args (.n (v + 16)) = 0 + _
      rw [zero_add]
    | some p =>
      have := hT (.atom (.add (.n (v + 19)) (.n p) (.n (v + 16)))) (by simp [vtFwTail])
      simpa [fixNe, GoodS, Good] using this
  refine vtB_blockA hl pos _ hcheck fun s hs ha ↦ ?_
  simp only [vtFwSelT, List.cons_append, List.mem_cons] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | hs
  · exact r0.2
  · simp [autoB, pureB, hintB] at ha
  · exact vshB_rcM hl (hmem _ (by simp [vtFwSelT])) (by simp) (K := 34) r0.1
      (by rw [g1]; exact word_g33.trans (gen_pow_eq_ofK 33).symm) (by omega) hlow
  · simp [autoB, pureB, hintB] at ha
  · simp [autoB, pureB, hintB] at ha
  · exact r7.2
  · simp [autoB, pureB, hintB] at ha
  · show vtσ rd wo args (.n 9) = vtσ rd wo args (.n (v + 8)) * vtσ rd wo args (.n v)
    rw [hmu, e8, r0.1, hpl, ← pow_add, Nat.add_comm]
  · simp [autoB, pureB, hintB] at ha
  · exact vshB_rcM hl (hmem _ (by simp [vtFwSelT])) (by simp) (K := 34) e8
      (by rw [g9]; exact word_g33.trans (gen_pow_eq_ofK 33).symm) (by omega) hlow
  · simp [autoB, pureB, hintB] at ha
  · simp [autoB, pureB, hintB] at ha; omega
  · simp [autoB, pureB, hintB] at ha; omega
  · refine vshB_dispatch (j := d) (by simp [vtBsNames]; omega) e8 ?_
    simp only [vtBsNames, List.getElem_map, List.getElem_range, List.map_cons, List.map_nil]
    rw [e16, e17]
    exact hrel
  · exact rE.2
  · exact vshB_eq (by rw [e17, rE.1])
  · cases prev with
    | none =>
      simp [vtFwTail] at hs
      subst hs; simp [autoB, pureB, hintB] at ha
    | some p =>
      simp [vtFwTail] at hs
      rcases hs with rfl | rfl <;> simp [autoB, pureB, hintB] at ha

end

end
end LeanVM.Guest.B1.Tables
