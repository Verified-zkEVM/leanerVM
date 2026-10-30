/-
  LeanVM.Guest.B1.Gkr.VbgC

  `verify_bus_gkr`'s body, completely: on a memory holding the root slot, the tables, the odd
  step's and the layers' words and the last slot, its honest valuation satisfies the body and
  returns the last slot's capacity, cursor and values.
-/

module

public import LeanVM.Guest.B1.Gkr.VbgOdd
public import LeanVM.Guest.B1.Gkr.Loop8Complete
public import LeanVM.Guest.B1.Selectors.LayoutBasic

/-!
# `verify_bus_gkr`'s body, completely (G:1617-1783)

`vbg_holds_of`: the body evaluated forward (`vbgEvL`, the allocations answered by the buffers'
pointers), its regions `vbR1 .. vbR8`: the range check of `g^depth` (the memory defined at `g^depth`
and `g^(32 - depth)`), the two roots read and the count asserted nonzero, the root slot stored,
the tables, the binary layer at an odd depth (`odc_holds`), the layer loop (`ly_complete`), the
point's copy (`l8_complete`) and the last slot read.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-! ## The regions of the body -/

/-- The depth's powers, the allocations, the range check, the capacity's copies. -/
def vbR1 : List Stmt :=
  [.atom (.const (.n 8) (word 4 0 0)), .atom (.mul (.n 9) (.n 6) (.n 8)),
    .atom (.mul (.n 10) (.n 9) (.n 9)), .atom (.mul (.n 11) (.n 10) (.n 10)),
    .atom (.mul (.n 12) (.n 11) (.n 11)), .atom (.mul (.n 13) (.n 12) (.n 12)),
    .atom (.mul (.n 14) (.n 13) (.n 9)), .atom (.hint (.allocDyn (.n 15) (.n 14))),
    .atom (.hint (.alloc (.n 16) 6034)), .atom (.hint (.alloc (.n 17) 1640)),
    .atom (.const (.n 18) (word 4294967296 0 0)),
    .atom (.rangeCheck (.n 6) (.n 19) (.n 20) (.n 21) (.n 18)),
    .atom (.copy (.n 22) (.n 0)), .atom (.copy (.n 23) (.n 1)), .atom (.copy (.n 24) (.n 2)),
    .atom (.copy (.n 25) (.n 3)), .atom (.copy (.n 26) (.n 4))]

/-- The two roots. -/
def vbR2 : List Stmt := fsNextT (.n 5) 0 27 ++ fsNextT (.n 5) 1 37

/-- The count asserted nonzero, the root slot, the tables' allocations. -/
def vbR3 : List Stmt :=
  [.atom (.const (.n 47) (word 0 0 0)), .atom (.add (.n 48) (.n 37) (.n 47)),
    .atom (.hint (.inverse (.n 48) (.n 49))), .atom (.assertNe (.n 48) (.n 49) (.n 50)),
    .atom (.load (.n 22) (.n 15) 0), .atom (.load (.n 23) (.n 15) 1),
    .atom (.load (.n 24) (.n 15) 2), .atom (.load (.n 25) (.n 15) 3),
    .atom (.load (.n 26) (.n 15) 4), .atom (.load (.n 34) (.n 15) 13),
    .atom (.load (.n 36) (.n 15) 14), .atom (.load (.n 44) (.n 15) 15),
    .atom (.load (.n 46) (.n 15) 16), .atom (.const (.n 51) (word 4 0 0)),
    .atom (.mul (.n 52) (.n 5) (.n 51)), .atom (.load (.n 52) (.n 15) 5),
    .atom (.load (.n 27) (.n 15) 6), .atom (.load (.n 27) (.n 15) 7),
    .atom (.load (.n 37) (.n 15) 8), .atom (.load (.n 17) (.n 15) 9),
    .atom (.const (.n 53) (word 1 0 0)), .atom (.load (.n 53) (.n 15) 10),
    .atom (.const (.n 54) (word 1 0 0)), .atom (.load (.n 54) (.n 15) 11),
    .atom (.const (.n 55) (word 0 0 0)), .atom (.load (.n 55) (.n 15) 12),
    .atom (.hint (.alloc (.n 56) 33)), .atom (.hint (.alloc (.n 57) 33))]

/-- The tables `pairs[d] = g^(d/2)`, `depth_shift[d] = g^(d % 2)`. -/
def vbTab (k : ℕ) : List Stmt :=
  [.atom (.const (.n (58 + 2 * k)) (word (2 ^ (k / 2)) 0 0)),
    .atom (.load (.n (58 + 2 * k)) (.n 56) k),
    .atom (.const (.n (59 + 2 * k)) (word (2 ^ (k % 2)) 0 0)),
    .atom (.load (.n (59 + 2 * k)) (.n 57) k)]

/-- The tables. -/
def vbR4 : List Stmt := ((List.range 33).map vbTab).flatten

/-- The depth's parity. -/
def vbR5 : List Stmt :=
  [.atom (.mul (.n 124) (.n 57) (.n 6)), .atom (.load (.n 125) (.n 124) 0),
    .atom (.const (.n 126) (word 1 0 0)), .atom (.add (.n 127) (.n 125) (.n 126))]

/-- The binary layer at an odd depth. -/
def vbR6 : List Stmt := [.ite (.n 127) [] odBody]

/-- The layer loop. -/
def vbR7 : List Stmt :=
  [.atom (.const (.n 300) (word 1 0 0)), .atom (.mul (.n 301) (.n 56) (.n 6)),
    .atom (.load (.n 302) (.n 301) 0), .atom (.add (.n 303) (.n 300) (.n 302)),
    .atom (.const (.n 304) (word 1 0 0)), .atom (.mul (.n 305) (.n 56) (.n 6)),
    .atom (.load (.n 306) (.n 305) 0),
    .callIf (.n 303) "__loop6" [.n 304, .n 306, .n 57, .n 6, .n 15, .n 16]]

/-- The last slot, the point's copy, the returns. -/
def vbR8 : List Stmt :=
  [.atom (.mul (.n 307) (.n 6) (.n 6)), .atom (.mul (.n 308) (.n 307) (.n 307)),
    .atom (.mul (.n 309) (.n 308) (.n 308)), .atom (.mul (.n 310) (.n 309) (.n 309)),
    .atom (.mul (.n 311) (.n 310) (.n 6)), .atom (.mul (.n 312) (.n 15) (.n 311)),
    .atom (.load (.n 313) (.n 312) 5), .atom (.load (.n 314) (.n 312) 9),
    .atom (.const (.n 315) (word 1 0 0)), .atom (.add (.n 316) (.n 315) (.n 6)),
    .atom (.const (.n 317) (word 1 0 0)),
    .callIf (.n 316) "__loop7" [.n 317, .n 6, .n 7, .n 314],
    .atom (.load (.n 318) (.n 312) 0), .atom (.load (.n 319) (.n 312) 1),
    .atom (.load (.n 320) (.n 312) 2), .atom (.load (.n 321) (.n 312) 3),
    .atom (.load (.n 322) (.n 312) 4), .atom (.copy (.n 323) (.n 313)),
    .atom (.load (.n 324) (.n 312) 6), .atom (.load (.n 325) (.n 312) 7),
    .atom (.load (.n 326) (.n 312) 8)]

theorem vbgPre_eq' : vbgPre = vbR1 ++ vbR2 ++ vbR3 ++ vbR4 ++ vbR5 ++ vbR6 ++ vbR7 ++ vbR8 :=
  tbStmtsEqb_sound (by decide +kernel)

theorem tb_word_four : word 4 0 0 = gen ^ 2 := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, tb_word_two_pow (by norm_num)]

/-- The rate cells of the two roots waiting. -/
theorem rateOf_two_getD (x0 x1 : E) :
    (rateOf [(x0, dsObserve), (x1, dsObserve)]).getD 0 0 = (Keccak.scalarCells x0 dsObserve).1 ∧
      (rateOf [(x0, dsObserve), (x1, dsObserve)]).getD 1 0 =
        (Keccak.scalarCells x0 dsObserve).2 ∧
      (rateOf [(x0, dsObserve), (x1, dsObserve)]).getD 2 0 =
        (Keccak.scalarCells x1 dsObserve).1 ∧
      (rateOf [(x0, dsObserve), (x1, dsObserve)]).getD 3 0 =
        (Keccak.scalarCells x1 dsObserve).2 := by
  rw [rateOf_eq_cells _ (by simp)]
  simp [pendCells]

theorem tb_list5_eq {l : List E} (h : l.length = 5) : ∃ a0 a1 a2 a3 a4, l = [a0, a1, a2, a3, a4] := by
  match l, h with
  | [a0, a1, a2, a3, a4], _ => exact ⟨a0, a1, a2, a3, a4, rfl⟩

theorem tb_list3_eq {l : List E} (h : l.length = 3) : ∃ a0 a1 a2, l = [a0, a1, a2] := by
  match l, h with
  | [a0, a1, a2], _ => exact ⟨a0, a1, a2, rfl⟩

/-- The allocations' pointers: the layers, the rounds' records, the rows, `pairs`,
`depth_shift`. -/
def vbgW (layers rounds rows pairs dsh : E) : ℕ → E := fun i ↦
  if i = 15 then layers else if i = 16 then rounds else if i = 17 then rows else
    if i = 56 then pairs else dsh

section Body

variable {rd : Reader} {w : ℕ → E} {σ : Val}

/-- A block of the body without an `ite` or an `assertNe` satisfies its equations. -/
theorem vb_goodB (hG : ∀ s ∈ vbgEvL, GoodS rd vbgS w σ s) (n : ℕ) (blk : List Stmt)
    (heq : tbStmtsEqb blk ((vbgPre.drop n).take blk.length) = true)
    (hne : blk.all noNeB = true) (hni : blk.all notIteB = true) :
    ∀ s ∈ blk, GoodS rd vbgS w σ s := by
  intro s hs
  have h := good_slice (G := fun s => GoodS rd vbgS w σ (fixNe s))
    (fun s hs => hG _ (List.mem_map_of_mem hs)) n blk heq hni s hs
  rwa [fixNe_of_noNe (List.all_eq_true.mp hne s hs)] at h

/-- A statement of the body satisfies the equations of its evaluation. -/
theorem vb_goodS (hG : ∀ s ∈ vbgEvL, GoodS rd vbgS w σ s) (n : ℕ) (s : Stmt)
    (heq : tbStmtsEqb [s] ((vbgPre.drop n).take 1) = true) (hni : notIteB s = true) :
    GoodS rd vbgS w σ (fixNe s) :=
  good_slice (G := fun s => GoodS rd vbgS w σ (fixNe s))
    (fun s hs => hG _ (List.mem_map_of_mem hs)) n [s] heq (by simp [hni]) s List.mem_cons_self

set_option maxHeartbeats 800000 in
/-- **`verify_bus_gkr`'s body, completely**, on its honest valuation, at `1 ≤ depth ≤ 32`: the range check's words
defined, the two roots at the cursor (the count nonzero), the root slot, the tables, the binary
layer's words at an odd depth, every layer's words (`LyIter`), and the last slot with its point at
`zeta` give the relation, returning the last slot's capacity, cursor and values. -/
theorem vbg_body_of {depth : ℕ} (hd1 : 1 ≤ depth) (hd : depth ≤ 32) {cap0 : List E}
    (hcl : cap0.length = 5) {cur zeta layers rounds rows pairs dsh : E}
    (hrc : (rd (gpow depth)).isSome = true ∧ (rd (gpow (32 - depth))).isSome = true)
    {x0 x1 : E} (hx0 : LoadHolds rd cur 0 x0) (hx1 : LoadHolds rd cur 1 x1) (hcnt : x1 ≠ 0)
    (hroot : GkSlotC rd layers 0 ⟨cap0, [(x0, dsObserve), (x1, dsObserve)]⟩ (cur * gen ^ 2)
      ⟨[x0, x0, x1], []⟩ rows 1 1 0)
    (hpairs : TbReadsAt rd pairs ((List.range 33).map fun k ↦ gen ^ (k / 2)))
    (hdsh : TbReadsAt rd dsh ((List.range 33).map fun k ↦ gen ^ (k % 2)))
    (hodd : depth % 2 = 1 → ∃ D : GkStepD,
      D.Ok ⟨cap0, [(x0, dsObserve), (x1, dsObserve)]⟩ ⟨[x0, x0, x1], []⟩ 1 ∧
      TbReadsAt rd (cur * gen ^ 2) D.xs ∧
      GkSlotC rd layers 1 (D.s' ⟨cap0, [(x0, dsObserve), (x1, dsObserve)]⟩ ⟨[x0, x0, x1], []⟩ 1)
        (cur * gen ^ 2 * gen ^ 6)
        (D.st' ⟨cap0, [(x0, dsObserve), (x1, dsObserve)]⟩ ⟨[x0, x0, x1], []⟩ 1)
        (rows * gen ^ 40) gen 1 0)
    (hit : ∀ j < depth / 2, LyIter rd layers rounds (depth % 2) j)
    {sF : Fs} {curF : E} {stF : GkrState} {rowF posF halfF parF : E}
    (hlast : GkSlotC rd layers depth sF curF stF rowF posF halfF parF)
    (hz : TbReadsAt rd zeta stF.point) :
    Stmt.HoldsList (coreProgram.Rel rd) rd
        (B1.Val.ofArgs (ev rd (vbgW layers rounds rows pairs dsh) (cap0 ++ [cur, gen ^ depth, zeta])
          vbgEvL)) vbgPre True (fun rs => rs = sF.cap ++ [curF] ++ stF.values) ∧
      vbgRets.map (B1.Val.ofArgs (ev rd (vbgW layers rounds rows pairs dsh)
        (cap0 ++ [cur, gen ^ depth, zeta]) vbgEvL)) = sF.cap ++ [curF] ++ stF.values := by
  obtain ⟨a0, a1, a2, a3, a4, rfl⟩ := tb_list5_eq hcl
  simp only [List.cons_append, List.nil_append]
  obtain ⟨fn, hf, hp, hb⟩ := vbgFound
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp vb_chk
  set args : List E := [a0, a1, a2, a3, a4, cur, gen ^ depth, zeta] with hargs
  have hc8 : chk args.length vbgEvL = some c' := hc'
  set W : ℕ → E := vbgW layers rounds rows pairs dsh with hW
  set σ : Val := B1.Val.ofArgs (ev rd W args vbgEvL) with hσ
  have hG : ∀ s ∈ vbgEvL, GoodS rd vbgS W σ s := (ev_spec rd W vbgEvL args hc8).2.2
  have par : ∀ i < 8, σ (.n i) = args.getD i 0 := fun i hi =>
    ev_params rd W hc8 (by simpa [hargs] using hi)
  have e0 : σ (.n 0) = a0 := par 0 (by omega)
  have e1 : σ (.n 1) = a1 := par 1 (by omega)
  have e2 : σ (.n 2) = a2 := par 2 (by omega)
  have e3 : σ (.n 3) = a3 := par 3 (by omega)
  have e4 : σ (.n 4) = a4 := par 4 (by omega)
  have e5 : σ (.n 5) = cur := par 5 (by omega)
  have e6 : σ (.n 6) = gen ^ depth := par 6 (by omega)
  have e7 : σ (.n 7) = zeta := par 7 (by omega)
  have g := fun n a heq hf => vb_good (rd := rd) (w := W) (σ := σ) hG n a heq hf
  set m := depth / 2 with hm
  set sh := depth % 2 with hsh
  have hd0 : depth = 2 * m + sh := by omega
  -- the depth's powers, the allocations, the range check
  have c8 : σ (.n 8) = word 4 0 0 := g 0 (.const (.n 8) (word 4 0 0)) (by decide +kernel) rfl
  have m9 := good_mul (g 1 (.mul (.n 9) (.n 6) (.n 8)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have m10 := good_mul (g 2 (.mul (.n 10) (.n 9) (.n 9)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have m11 := good_mul (g 3 (.mul (.n 11) (.n 10) (.n 10)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have m12 := good_mul (g 4 (.mul (.n 12) (.n 11) (.n 11)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have m13 := good_mul (g 5 (.mul (.n 13) (.n 12) (.n 12)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have m14 := good_mul (g 6 (.mul (.n 14) (.n 13) (.n 9)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have e15 : σ (.n 15) = layers := by
    have h : σ (.n 15) = W 15 := g 7 (.hint (.allocDyn (.n 15) (.n 14))) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  have e16 : σ (.n 16) = rounds := by
    have h : σ (.n 16) = W 16 := g 8 (.hint (.alloc (.n 16) 6034)) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  have e17 : σ (.n 17) = rows := by
    have h : σ (.n 17) = W 17 := g 9 (.hint (.alloc (.n 17) 1640)) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  have c18 : σ (.n 18) = word 4294967296 0 0 :=
    g 10 (.const (.n 18) (word 4294967296 0 0)) (by decide +kernel) rfl
  have w32 : word 4294967296 0 0 = gen ^ 32 := by
    rw [show (4294967296 : ℕ) = 2 ^ 32 by norm_num, tb_word_two_pow (by norm_num)]
  have grc := g 11 (.rangeCheck (.n 6) (.n 19) (.n 20) (.n 21) (.n 18)) (by decide +kernel) rfl
  have h1819 : (V.n 18).idx < (V.n 19).idx := show 18 < 19 by norm_num
  have e19 : σ (.n 19) = gen ^ (32 - depth) := by
    have h3 : σ (.n 19) = σ (.n 18) * (σ (.n 6))⁻¹ := by
      have := grc.2.2
      simpa only [h1819, ↓reduceIte] using this
    have hp32 : gen ^ 32 = gen ^ (32 - depth) * gen ^ depth := by
      rw [← pow_add, Nat.sub_add_cancel hd]
    rw [h3, c18, w32, e6, hp32, mul_assoc, mul_inv_cancel₀ (gen_pow_ne_zero _), mul_one]
  have hrcH : (Atom.rangeCheck (.n 6) (.n 19) (.n 20) (.n 21) (.n 18)).Holds rd σ := by
    refine holds_of_good grc ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [e6]; exact tb_gen_pow_isInK _
    · rw [e6, gen_pow_eq_ofK, tb_addr_ofK, Nat.add_zero]
      exact hrc.1
    · rw [e19]; exact tb_gen_pow_isInK _
    · rw [e19, gen_pow_eq_ofK, tb_addr_ofK, Nat.add_zero]
      exact hrc.2
    · show (if (V.n 18).idx < (V.n 19).idx then σ (.n 6) ≠ 0 else True)
      simp only [h1819, ↓reduceIte]
      rw [e6]; exact gen_pow_ne_zero _
  have q22 : σ (.n 22) = σ (.n 0) := g 12 (.copy (.n 22) (.n 0)) (by decide +kernel) rfl
  have q23 : σ (.n 23) = σ (.n 1) := g 13 (.copy (.n 23) (.n 1)) (by decide +kernel) rfl
  have q24 : σ (.n 24) = σ (.n 2) := g 14 (.copy (.n 24) (.n 2)) (by decide +kernel) rfl
  have q25 : σ (.n 25) = σ (.n 3) := g 15 (.copy (.n 25) (.n 3)) (by decide +kernel) rfl
  have q26 : σ (.n 26) = σ (.n 4) := g 16 (.copy (.n 26) (.n 4)) (by decide +kernel) rfl
  -- the two roots
  obtain ⟨e27, cl27, hfs27⟩ := fsNextT_good (C := coreProgram.Rel rd)
    (kret := fun rs => rs = sF.cap ++ [curF] ++ stF.values)
    (vb_goodB hG 17 (fsNextT (.n 5) 0 27) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (by decide +kernel) (by rw [e5]; exact hx0)
  obtain ⟨e37, cl37, hfs37⟩ := fsNextT_good (C := coreProgram.Rel rd)
    (kret := fun rs => rs = sF.cap ++ [curF] ++ stF.values)
    (vb_goodB hG 26 (fsNextT (.n 5) 1 37) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (by decide +kernel) (by rw [e5]; exact hx1)
  obtain ⟨e34, e36⟩ := Prod.ext_iff.mp cl27
  obtain ⟨e44, e46⟩ := Prod.ext_iff.mp cl37
  simp only [Nat.reduceAdd] at e34 e36 e44 e46
  -- the count asserted nonzero, the root slot
  have hroot' := hroot
  obtain ⟨-, -, -, hcap0, hrate0, hcur0, -, hval0, hrow0, -, -, hpos0, hhalf0, hpar0⟩ := hroot'
  simp only [Nat.mul_zero, Nat.zero_add] at hcap0 hrate0 hcur0 hval0 hrow0 hpos0 hhalf0 hpar0
  have c47 : σ (.n 47) = word 0 0 0 := g 35 (.const (.n 47) (word 0 0 0)) (by decide +kernel) rfl
  have a48 : σ (.n 48) = σ (.n 37) + σ (.n 47) :=
    g 36 (.add (.n 48) (.n 37) (.n 47)) (by decide +kernel) rfl
  have i49 : σ (.n 49) = (σ (.n 48))⁻¹ :=
    g 37 (.hint (.inverse (.n 48) (.n 49))) (by decide +kernel) rfl
  have m50 : σ (.n 50) = σ (.n 48) * σ (.n 49) :=
    good_mulS (vb_goodS hG 38 (.atom (.assertNe (.n 48) (.n 49) (.n 50))) (by decide +kernel) rfl)
      (by omega) (by omega)
  have e48 : σ (.n 48) = x1 := by rw [a48, c47, tb_word_zero, add_zero, e37]
  have c51 : σ (.n 51) = word 4 0 0 := g 48 (.const (.n 51) (word 4 0 0)) (by decide +kernel) rfl
  have m52 := good_mul (g 49 (.mul (.n 52) (.n 5) (.n 51)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have c53 : σ (.n 53) = word 1 0 0 := g 55 (.const (.n 53) (word 1 0 0)) (by decide +kernel) rfl
  have c54 : σ (.n 54) = word 1 0 0 := g 57 (.const (.n 54) (word 1 0 0)) (by decide +kernel) rfl
  have c55 : σ (.n 55) = word 0 0 0 := g 59 (.const (.n 55) (word 0 0 0)) (by decide +kernel) rfl
  have e56 : σ (.n 56) = pairs := by
    have h : σ (.n 56) = W 56 := g 61 (.hint (.alloc (.n 56) 33)) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  have e57 : σ (.n 57) = dsh := by
    have h : σ (.n 57) = W 57 := g 62 (.hint (.alloc (.n 57) 33)) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  have hr2 := rateOf_two_getD x0 x1
  have R3 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR3 True
      (fun rs => rs = sF.cap ++ [curF] ++ stF.values) := by
    simp only [vbR3, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    refine ⟨c47, a48, trivial, ⟨m50, by rw [m50, i49, mul_inv_cancel₀ (by rw [e48]; exact hcnt)]⟩,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, c51, m52, ?_, ?_, ?_, ?_, ?_, c53, ?_, c54, ?_, c55, ?_⟩
    · rw [e15, q22, e0]; exact hcap0 0 (by omega)
    · rw [e15, q23, e1]; exact hcap0 1 (by omega)
    · rw [e15, q24, e2]; exact hcap0 2 (by omega)
    · rw [e15, q25, e3]; exact hcap0 3 (by omega)
    · rw [e15, q26, e4]; exact hcap0 4 (by omega)
    · rw [e15, e34, ← hr2.1]; exact hrate0 0 (by omega)
    · rw [e15, e36, ← hr2.2.1]; exact hrate0 1 (by omega)
    · rw [e15, e44, ← hr2.2.2.1]; exact hrate0 2 (by omega)
    · rw [e15, e46, ← hr2.2.2.2]; exact hrate0 3 (by omega)
    · rw [e15, m52, e5, c51, tb_word_four]; exact hcur0
    · rw [e15, e27]; exact hval0 0 (by omega)
    · rw [e15, e27]; exact hval0 1 (by omega)
    · rw [e15, e37]; exact hval0 2 (by omega)
    · rw [e15, e17]; exact hrow0
    · rw [e15, c53, tb_word_one]; exact hpos0
    · rw [e15, c54, tb_word_one]; exact hhalf0
    · rw [e15, c55, tb_word_zero]; exact hpar0
  -- the tables
  have gT := vb_goodB hG 63 vbR4 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hpk : ∀ k < 33, LoadHolds rd pairs k (gen ^ (k / 2)) := fun k hk => by
    have := hpairs k (by simpa using hk)
    simpa using this
  have hdk : ∀ k < 33, LoadHolds rd dsh k (gen ^ (k % 2)) := fun k hk => by
    have := hdsh k (by simpa using hk)
    simpa using this
  have R4 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR4 True
      (fun rs => rs = sF.cap ++ [curF] ++ stF.values) := by
    refine (tb_holdsList_flatten_range 33 vbTab fun _ => rfl).mpr fun k hk => ?_
    have mem : ∀ t ∈ vbTab k, t ∈ vbR4 := fun t ht =>
      List.mem_flatten.mpr ⟨vbTab k, List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩, ht⟩
    have c0 : σ (.n (58 + 2 * k)) = word (2 ^ (k / 2)) 0 0 :=
      gT (.atom (.const (.n (58 + 2 * k)) (word (2 ^ (k / 2)) 0 0))) (mem _ (by simp [vbTab]))
    have c1 : σ (.n (59 + 2 * k)) = word (2 ^ (k % 2)) 0 0 :=
      gT (.atom (.const (.n (59 + 2 * k)) (word (2 ^ (k % 2)) 0 0))) (mem _ (by simp [vbTab]))
    rw [tb_word_two_pow (by omega)] at c0 c1
    simp only [vbTab, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    refine ⟨by rw [c0, tb_word_two_pow (by omega)], by rw [e56, c0]; exact hpk k hk,
      by rw [c1, tb_word_two_pow (by omega)], by rw [e57, c1]; exact hdk k hk⟩
  -- the depth's parity
  have m124 := good_mul (g 195 (.mul (.n 124) (.n 57) (.n 6)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have hdd : LoadHolds rd (σ (.n 124)) 0 (gen ^ sh) := by
    rw [m124, e57, e6, tb_loadHolds_mul_gen_pow, Nat.add_zero]; exact hdk depth (by omega)
  obtain ⟨e125, l125⟩ := good_read (g 196 (.load (.n 125) (.n 124) 0) (by decide +kernel) rfl)
    (by decide +kernel) hdd
  have c126 : σ (.n 126) = word 1 0 0 := g 197 (.const (.n 126) (word 1 0 0)) (by decide +kernel) rfl
  have a127 : σ (.n 127) = σ (.n 125) + σ (.n 126) :=
    g 198 (.add (.n 127) (.n 125) (.n 126)) (by decide +kernel) rfl
  have R5 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR5 True
      (fun rs => rs = sF.cap ++ [curF] ++ stF.values) := by
    simp only [vbR5, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    exact ⟨m124, l125, c126, a127⟩
  -- the binary layer at an odd depth
  have R6 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR6 True
      (fun rs => rs = sF.cap ++ [curF] ++ stF.values) := by
    simp only [vbR6, Stmt.HoldsList]
    rw [tb_holds_ite_noRet _ _ _ rfl odBody_noRet]
    refine ⟨⟨?_, fun _ => trivial, fun hne => ?_⟩, trivial⟩
    · rw [a127, e125, c126, tb_word_one]
      exact tb_isInK_add (tb_gen_pow_isInK _) tb_isInK_one
    · have hsh1 : sh = 1 := by
        by_contra h
        rw [a127, e125, c126, tb_word_one, show sh = 0 by omega, pow_zero, e_add_self] at hne
        exact hne rfl
      obtain ⟨D, hD, hxD, hS'⟩ := hodd hsh1
      exact odc_holds hG (by rw [e15]; exact hroot) hD rfl hxD
        (by rw [e15]; exact hS')
  -- the layer loop
  have c300 : σ (.n 300) = word 1 0 0 := g 200 (.const (.n 300) (word 1 0 0)) (by decide +kernel) rfl
  have m301 := good_mul (g 201 (.mul (.n 301) (.n 56) (.n 6)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have hpp : ∀ p, p = σ (.n 56) * σ (.n 6) → LoadHolds rd p 0 (gen ^ m) := fun p hp => by
    rw [hp, e56, e6, tb_loadHolds_mul_gen_pow, Nat.add_zero]; exact hpk depth (by omega)
  obtain ⟨e302, l302⟩ := good_read (g 202 (.load (.n 302) (.n 301) 0) (by decide +kernel) rfl)
    (by decide +kernel) (hpp _ m301)
  have a303 : σ (.n 303) = σ (.n 300) + σ (.n 302) :=
    g 203 (.add (.n 303) (.n 300) (.n 302)) (by decide +kernel) rfl
  have c304 : σ (.n 304) = word 1 0 0 := g 204 (.const (.n 304) (word 1 0 0)) (by decide +kernel) rfl
  have m305 := good_mul (g 205 (.mul (.n 305) (.n 56) (.n 6)) (by decide +kernel) rfl) (by omega)
    (by omega)
  obtain ⟨e306, l306⟩ := good_read (g 206 (.load (.n 306) (.n 305) 0) (by decide +kernel) rfl)
    (by decide +kernel) (hpp _ m305)
  have R7 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR7 True
      (fun rs => rs = sF.cap ++ [curF] ++ stF.values) := by
    simp only [vbR7, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, List.map_cons, List.map_nil]
    refine ⟨c300, m301, l302, a303, c304, m305, l306, ?_, fun hne => ?_⟩
    · rw [a303, c300, e302, tb_word_one]
      exact tb_isInK_add tb_isInK_one (tb_gen_pow_isInK _)
    · have hm0 : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [a303, c300, e302, tb_word_one, h0, pow_zero, e_add_self] at hne
          exact absurd rfl hne
        · exact h0
      rw [c304, tb_word_one, e306, e57, e6, e15, e16]
      exact ly_complete hm0 (by omega) (by omega)
        (by rw [m124, e57, e6] at hdd; exact hdd) hit
  -- the last slot, the point's copy
  obtain ⟨hclF, -, -, hcapF, -, hcurF, hvlF, hvalF, hrowF, hplF, hptF, -, -, -⟩ := hlast
  have m307 := good_mul (g 208 (.mul (.n 307) (.n 6) (.n 6)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have m308 := good_mul (g 209 (.mul (.n 308) (.n 307) (.n 307)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m309 := good_mul (g 210 (.mul (.n 309) (.n 308) (.n 308)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m310 := good_mul (g 211 (.mul (.n 310) (.n 309) (.n 309)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m311 := good_mul (g 212 (.mul (.n 311) (.n 310) (.n 6)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m312 := good_mul (g 213 (.mul (.n 312) (.n 15) (.n 311)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have e312 : σ (.n 312) = layers * gen ^ (17 * depth) := by
    rw [m312, m311, m310, m309, m308, m307, e6, e15, ← pow_add, ← pow_add, ← pow_add, ← pow_add,
      ← pow_add]
    ring_nf
  have ld : ∀ k v, LoadHolds rd layers (17 * depth + k) v → LoadHolds rd (σ (.n 312)) k v :=
    fun k v h => by rw [e312, tb_loadHolds_mul_gen_pow]; exact h
  obtain ⟨e313, l313⟩ := good_read (g 214 (.load (.n 313) (.n 312) 5) (by decide +kernel) rfl)
    (by decide +kernel) (ld 5 _ hcurF)
  obtain ⟨e314, l314⟩ := good_read (g 215 (.load (.n 314) (.n 312) 9) (by decide +kernel) rfl)
    (by decide +kernel) (ld 9 _ hrowF)
  have c315 : σ (.n 315) = word 1 0 0 := g 216 (.const (.n 315) (word 1 0 0)) (by decide +kernel) rfl
  have a316 : σ (.n 316) = σ (.n 315) + σ (.n 6) :=
    g 217 (.add (.n 316) (.n 315) (.n 6)) (by decide +kernel) rfl
  have c317 : σ (.n 317) = word 1 0 0 := g 218 (.const (.n 317) (word 1 0 0)) (by decide +kernel) rfl
  obtain ⟨e318, l318⟩ := good_read (g 220 (.load (.n 318) (.n 312) 0) (by decide +kernel) rfl)
    (by decide +kernel) (ld 0 _ (hcapF 0 (by omega)))
  obtain ⟨e319, l319⟩ := good_read (g 221 (.load (.n 319) (.n 312) 1) (by decide +kernel) rfl)
    (by decide +kernel) (ld 1 _ (hcapF 1 (by omega)))
  obtain ⟨e320, l320⟩ := good_read (g 222 (.load (.n 320) (.n 312) 2) (by decide +kernel) rfl)
    (by decide +kernel) (ld 2 _ (hcapF 2 (by omega)))
  obtain ⟨e321, l321⟩ := good_read (g 223 (.load (.n 321) (.n 312) 3) (by decide +kernel) rfl)
    (by decide +kernel) (ld 3 _ (hcapF 3 (by omega)))
  obtain ⟨e322, l322⟩ := good_read (g 224 (.load (.n 322) (.n 312) 4) (by decide +kernel) rfl)
    (by decide +kernel) (ld 4 _ (hcapF 4 (by omega)))
  have q323 : σ (.n 323) = σ (.n 313) := g 225 (.copy (.n 323) (.n 313)) (by decide +kernel) rfl
  obtain ⟨e324, l324⟩ := good_read (g 226 (.load (.n 324) (.n 312) 6) (by decide +kernel) rfl)
    (by decide +kernel) (ld 6 _ (hvalF 0 (by omega)))
  obtain ⟨e325, l325⟩ := good_read (g 227 (.load (.n 325) (.n 312) 7) (by decide +kernel) rfl)
    (by decide +kernel) (ld 7 _ (hvalF 1 (by omega)))
  obtain ⟨e326, l326⟩ := good_read (g 228 (.load (.n 326) (.n 312) 8) (by decide +kernel) rfl)
    (by decide +kernel) (ld 8 _ (hvalF 2 (by omega)))
  have R8 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR8 True
      (fun rs => rs = sF.cap ++ [curF] ++ stF.values) := by
    simp only [vbR8, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, List.map_cons, List.map_nil]
    refine ⟨m307, m308, m309, m310, m311, m312, l313, l314, c315, a316, c317, ?_, fun hne => ?_,
      l318, l319, l320, l321, l322, q323, l324, l325, l326⟩
    · rw [a316, c315, tb_word_one, e6]
      exact tb_isInK_add tb_isInK_one (tb_gen_pow_isInK _)
    · rw [c317, tb_word_one, e6, e7, e314]
      exact l8_complete (by omega) (by omega) hplF hptF hz
  -- the relation
  have R1 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR1 True
      (fun rs => rs = sF.cap ++ [curF] ++ stF.values) := by
    simp only [vbR1, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    exact ⟨c8, m9, m10, m11, m12, m13, m14, trivial, trivial, trivial, c18, hrcH, q22, q23, q24,
      q25, q26⟩
  have R2 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR2 True
      (fun rs => rs = sF.cap ++ [curF] ++ stF.values) := by
    unfold vbR2
    rw [tb_holdsList_append_noRet (by decide +kernel)]
    exact ⟨hfs27, hfs37⟩
  obtain ⟨f0, f1, f2, f3, f4, hf5⟩ := tb_list5_eq hclF
  obtain ⟨v0, v1, v2, hv3⟩ := tb_list3_eq hvlF
  refine ⟨?_, ?_⟩
  · rw [vbgPre_eq']
    repeat rw [tb_holdsList_append_noRet (by decide +kernel)]
    exact ⟨⟨⟨⟨⟨⟨⟨R1, R2⟩, R3⟩, R4⟩, R5⟩, R6⟩, R7⟩, R8⟩
  · simp only [vbgRets, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append, hf5, hv3]
    rw [e318, e319, e320, e321, e322, q323, e313, e324, e325, e326, hf5, hv3]
    rfl


/-- **`verify_bus_gkr`'s body, completely**, at `1 ≤ depth ≤ 32`: the range check's words
defined, the two roots at the cursor (the count nonzero), the root slot, the tables, the binary
layer's words at an odd depth, every layer's words (`LyIter`), and the last slot with its point at
`zeta` give the relation, returning the last slot's capacity, cursor and values. -/
theorem vbg_holds_of {depth : ℕ} (hd1 : 1 ≤ depth) (hd : depth ≤ 32) {cap0 : List E}
    (hcl : cap0.length = 5) {cur zeta layers rounds rows pairs dsh : E}
    (hrc : (rd (gpow depth)).isSome = true ∧ (rd (gpow (32 - depth))).isSome = true)
    {x0 x1 : E} (hx0 : LoadHolds rd cur 0 x0) (hx1 : LoadHolds rd cur 1 x1) (hcnt : x1 ≠ 0)
    (hroot : GkSlotC rd layers 0 ⟨cap0, [(x0, dsObserve), (x1, dsObserve)]⟩ (cur * gen ^ 2)
      ⟨[x0, x0, x1], []⟩ rows 1 1 0)
    (hpairs : TbReadsAt rd pairs ((List.range 33).map fun k ↦ gen ^ (k / 2)))
    (hdsh : TbReadsAt rd dsh ((List.range 33).map fun k ↦ gen ^ (k % 2)))
    (hodd : depth % 2 = 1 → ∃ D : GkStepD,
      D.Ok ⟨cap0, [(x0, dsObserve), (x1, dsObserve)]⟩ ⟨[x0, x0, x1], []⟩ 1 ∧
      TbReadsAt rd (cur * gen ^ 2) D.xs ∧
      GkSlotC rd layers 1 (D.s' ⟨cap0, [(x0, dsObserve), (x1, dsObserve)]⟩ ⟨[x0, x0, x1], []⟩ 1)
        (cur * gen ^ 2 * gen ^ 6)
        (D.st' ⟨cap0, [(x0, dsObserve), (x1, dsObserve)]⟩ ⟨[x0, x0, x1], []⟩ 1)
        (rows * gen ^ 40) gen 1 0)
    (hit : ∀ j < depth / 2, LyIter rd layers rounds (depth % 2) j)
    {sF : Fs} {curF : E} {stF : GkrState} {rowF posF halfF parF : E}
    (hlast : GkSlotC rd layers depth sF curF stF rowF posF halfF parF)
    (hz : TbReadsAt rd zeta stF.point) :
    coreProgram.Rel rd "verify_bus_gkr" (cap0 ++ [cur, gen ^ depth, zeta])
      (sF.cap ++ [curF] ++ stF.values) := by
  obtain ⟨fn, hf, hp, hb⟩ := vbgFound
  obtain ⟨hh, hr⟩ := vbg_body_of hd1 hd hcl hrc hx0 hx1 hcnt hroot hpairs hdsh hodd hit hlast hz
  refine (tb_rel_pre hf hb vbgPre_noRet _ _).mpr ⟨_, ?_, hh, hr⟩
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp vb_chk
  have hl : (cap0 ++ [cur, gen ^ depth, zeta]).length = 8 := by simp [hcl]
  rw [hp]
  apply List.ext_getElem (by simp [hl])
  intro i h1 _
  simp only [List.getElem_map, List.getElem_range]
  have hi : i < 8 := by simpa using h1
  rw [← List.getD_eq_getElem _ 0 (by omega)]
  exact ev_params rd _ (by rw [hl]; exact hc') (by rw [hl]; exact hi)

end Body

end
end LeanVM.Guest.B1.Tables
