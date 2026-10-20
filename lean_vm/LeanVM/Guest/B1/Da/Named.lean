/-
  LeanVM.Guest.B1.Da.Named

  The DA check's callees with their witnesses named: each function's outcome on a valuation of
  its body, its part of the blob matrix an explicit function of the valuation and of its callees'
  witness functions.
-/

module

public import LeanVM.Guest.B1.Da.Witness

/-!
# The DA check's witnesses, named

The matrix `da_verify` checks is hinted by its leaves: `da_verify_cell` hints a cell's 256
symbols (`vcSyms`, `CellOut`) and `da_vector_cell__L{final}` a chunk of 256 weights of the vector
(`vxWs`, `VecOut`). Each function between them and `da_verify` passes its callees' witnesses on, as
a function of its valuation and of a witness function per callee (`wg args rets`, applied to the
call's argument and return words), its outcome stated for any witness:

* `da_vector_dispatch` (`vdWit`, `VdOut`): its callee's weights;
* the row loops `__loop484`, `__loop486` (`rowWit`, `RowsOut`): the cells' symbols of the
  remaining rows, a list (`LoopW`: item `j` is iteration `x·g^j`);
* `da_verify_column__L{store}` (`colWit`, `ColOutW`): the column's weights and its cells
  (`DaColumn`);
* the column loops `__loop90`, `__loop91` (`colLoopWit`, `ColsOut`): the remaining columns.

`col_facts_w` reads a column's facts (`ColOk`, `CellOk`) off its outcome, the weights and the
symbols the witness's.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-! ## Loops with a witness -/

/-- **A `mul_range` loop from `x` to `W`, item `j` of `L` its iteration `x·g^j`**: `L` has the
loop's `m ≥ 1` iterations, `W = x·g^m` is reached first at `m`, and `B` holds at each iteration of
its item. -/
def LoopW {α : Type} (x W : E) (B : E → α → Prop) (L : List α) : Prop :=
  0 < L.length ∧ W = x * gen ^ L.length ∧ (∀ j, 0 < j → j < L.length → x * gen ^ j ≠ W) ∧
    ∀ j (h : j < L.length), B (x * gen ^ j) L[j]

theorem loopW_start {α : Type} {x x' W : E} {B : E → α → Prop} {L : List α} (h : x' = x)
    (hl : LoopW x' W B L) : LoopW x W B L := h ▸ hl

/-- **One iteration**: the body at `x` with its item `a`, the loop going on at `x·g` exactly when
the test `c = x·g + W` is not zero. -/
theorem loopW_step {α : Type} {x W c : E} {B : E → α → Prop} {a : α} {L : List α}
    (hc : c = x * gen + W) (ha : B x a) (hL : c ≠ 0 → LoopW (x * gen) W B L) :
    LoopW x W B (a :: if c = 0 then [] else L) := by
  by_cases h0 : c = 0
  · have hW : x * gen = W := e_add_eq_zero_iff.mp (hc ▸ h0)
    rw [ite_pos' h0]
    refine ⟨by simp, by simp [hW], fun j h1 h2 => by simp at h2; omega, fun j hj => ?_⟩
    obtain rfl : j = 0 := by simpa using hj
    simpa using ha
  · rw [ite_neg' h0]
    obtain ⟨-, hW, hfirst, hB⟩ := hL h0
    have hne : x * gen ≠ W := fun he => h0 (by rw [hc, he]; exact e_add_eq_zero_iff.mpr rfl)
    refine ⟨by simp, ?_, fun j h1 h2 => ?_, fun j hj => ?_⟩
    · rw [hW, List.length_cons, pow_succ', mul_assoc]
    · simp only [List.length_cons] at h2
      rcases Nat.lt_or_ge j 2 with hj | hj
      · rw [show j = 1 by omega, pow_one]; exact hne
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        rw [pow_succ', ← mul_assoc]; exact hfirst i (by omega) (by omega)
    · cases j with
      | zero => simpa using ha
      | succ i =>
        simp only [List.length_cons] at hj
        have := hB i (by omega)
        rw [pow_succ', ← mul_assoc]
        simpa using this

/-- **A loop from `g^a` to `g^(a+n)`** has `n` items, item `j` its iteration `g^(a+j)`. -/
theorem loopW_pow {α : Type} {B : E → α → Prop} {L : List α} {a n : ℕ} (hn : a + n < 2 ^ 33)
    (hpos : 0 < n) (h : LoopW (gen ^ a) (gen ^ (a + n)) B L) :
    L.length = n ∧ ∀ j (hj : j < L.length), B (gen ^ (a + j)) L[j] := by
  obtain ⟨-, hW, hfirst, hB⟩ := h
  have hlen : a + L.length = a + n :=
    loop_end_exact (k := a) hn (by omega) (hW.trans (pow_add gen a L.length).symm) fun j h1 h2 he => by
      obtain ⟨i, rfl⟩ : ∃ i, j = a + i := ⟨j - a, by omega⟩
      exact hfirst i (by omega) (by omega) (by rw [← pow_add]; exact he)
  refine ⟨by omega, fun j hj => ?_⟩
  rw [pow_add]
  exact hB j hj

/-- **A loop from `1` to `g^n`** has `n` items, item `j` its iteration `g^j`. -/
theorem loopW_one {α : Type} {B : E → α → Prop} {L : List α} {n : ℕ} (hn : n < 2 ^ 33) (hpos : 0 < n)
    (h : LoopW 1 (gen ^ n) B L) : L.length = n ∧ ∀ j (hj : j < L.length), B (gen ^ j) L[j] := by
  have h' : LoopW (gen ^ 0) (gen ^ (0 + n)) B L := by rwa [pow_zero, zero_add]
  simpa using loopW_pow (by omega) hpos h'

/-! ## `da_vector_dispatch` -/

/-- **`da_vector_dispatch`'s outcome, its weights named** `ws`: `xb` is in `K`, and the vector
cell's outcome, final exactly at `xb = g^127`. -/
def VdOut (rd : Reader) (args rets : List E) (ws : List E) : Prop :=
  ∃ xb rest, args = xb :: rest ∧ IsInK xb ∧ VecOut (decide (xb = gen ^ 127)) rd args rets ws

/-- `da_vector_dispatch`'s weights: its callee's (`wv final`, `__L1` at `final`). -/
def vdWit (σ : Val) (wv : Bool → List E → List E → List E) : List E :=
  if σ (.n 5) = 0 then wv true [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3)] [σ (.n 6), σ (.n 7), σ (.n 8)]
  else wv false [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3)] [σ (.n 12), σ (.n 13), σ (.n 14)]

/-- **`da_vector_dispatch`, its witness named**. -/
theorem vd_out {C : CallRel} {rd : Reader} {σ : Val} {args rets : List E}
    {wv : Bool → List E → List E → List E}
    (hv : ∀ final a r, C (vxName final) a r → VecOut final rd a r (wv final a r))
    (hp : ([.n 0, .n 1, .n 2, .n 3] : List V).map σ = args)
    (hb : Stmt.HoldsList C rd σ vdBody False (fun rs => rs = rets)) : VdOut rd args rets (vdWit σ wv) := by
  simp only [vdBody, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hb hp
  subst hp
  obtain ⟨c4, a5, hk5, hz, hnz⟩ := hb
  have hk := isInK_gen_pow 127
  have e5 : σ (.n 5) = σ (.n 0) + gen ^ 127 := by rw [a5, c4, word_g127]
  rw [e5] at hk5 hz hnz
  have hx : IsInK (σ (.n 0)) := by
    rw [add_comm] at hk5; exact (isInK_add_left hk).mp hk5
  refine ⟨σ (.n 0), [σ (.n 1), σ (.n 2), σ (.n 3)], rfl, hx, ?_⟩
  unfold vdWit
  by_cases h : σ (.n 0) = gen ^ 127
  · have h0 : σ (.n 5) = 0 := by rw [e5]; exact e_add_eq_zero_iff.mpr h
    obtain ⟨hc, c9, c10, c11, c15, c16, c17, hr⟩ := hz (e_add_eq_zero_iff.mpr h)
    rw [ite_pos' h0, decide_eq_true h, ← hr, c15, c16, c17, c9, c10, c11]
    exact hv true _ _ hc
  · have h0 : σ (.n 5) ≠ 0 := by rw [e5]; exact fun h' => h (e_add_eq_zero_iff.mp h')
    obtain ⟨hc, c9, c10, c11, c15, c16, c17, hr⟩ := hnz (fun h' => h (e_add_eq_zero_iff.mp h'))
    rw [ite_neg' h0, decide_eq_false h, ← hr, c15, c16, c17, c9, c10, c11]
    exact hv false _ _ hc

/-! ## The row loops -/

/-- **Row `x` of a column, its cell's symbols named** `syms`: `RowCell` with `da_verify_cell`'s
outcome. -/
def RowCellW (store : Bool) (rd : Reader) (lv rb xb node pb x : E) (syms : List K) : Prop :=
  ∃ d0 d1 s R a, CellOut rd [lv] [d0, d1, s] syms ∧ LoadHolds rd (rb * x) 0 R ∧
    LoadHolds rd (R * xb) 0 a ∧ LoadHolds rd (R * xb) 1 (a + s) ∧ CellsAt rd (node * (x * x)) [d0, d1] ∧
    (store = true → ∃ P, LoadHolds rd (pb * x) 0 P ∧ CellsAt rd (P * (xb * xb)) [d0, d1])

theorem rowCell_of_w {store : Bool} {rd : Reader} {lv rb xb node pb x : E} {syms : List K}
    (h : RowCellW store rd lv rb xb node pb x syms) : RowCell store rd lv rb xb node pb x :=
  let ⟨d0, d1, s, R, a, hc, h'⟩ := h
  ⟨d0, d1, s, R, a, meaning_of_cellOut hc, h'⟩

/-- **The row loop's outcome, its rows' symbols named** `L`: from `x` to `W`, row `x·g^j`'s cell
of symbols `L[j]`. -/
def RowsOut (store : Bool) (rd : Reader) (args rets : List E) (L : List (List K)) : Prop :=
  ∃ x W lv rb xb node pb, args = [x, W, lv, rb, xb, node, pb] ∧ rets = [] ∧
    LoopW x W (RowCellW store rd lv rb xb node pb) L

/-- The row loop's test value. -/
def rowTest (store : Bool) : ℕ := if store then 23 else 19

/-- The row loop's next row. -/
def rowNext (store : Bool) : ℕ := if store then 25 else 21

/-- The row loop's witness: its cell's symbols, then the remaining rows'. -/
def rowWit (store : Bool) (σ : Val) (wc : List E → List E → List K)
    (wr : List E → List E → List (List K)) : List (List K) :=
  wc [σ (.n 2)] [σ (.n 7), σ (.n 8), σ (.n 9)] ::
    if σ (.n (rowTest store)) = 0 then [] else
      wr [σ (.n (rowNext store)), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6)] []

/-- **One frame of the row loop**: its parameters, its row's cell with the symbols `wc` of the
cell call's words, its test and next row, and the loop's call on. -/
theorem row_step_w (store : Bool) {C : CallRel} {rd : Reader} {σ : Val} {args rets : List E}
    {wc : List E → List E → List K}
    (hc : ∀ a r, C "da_verify_cell" a r → CellOut rd a r (wc a r))
    (hp : ([.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] : List V).map σ = args)
    (hb : Stmt.HoldsList C rd σ (rowBody store) False (fun rs => rs = rets)) :
    args = [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6)] ∧ rets = [] ∧
      RowCellW store rd (σ (.n 2)) (σ (.n 3)) (σ (.n 4)) (σ (.n 5)) (σ (.n 6)) (σ (.n 0))
        (wc [σ (.n 2)] [σ (.n 7), σ (.n 8), σ (.n 9)]) ∧
      σ (.n (rowTest store)) = σ (.n 0) * gen + σ (.n 1) ∧ σ (.n (rowNext store)) = σ (.n 0) * gen ∧
      (σ (.n (rowTest store)) ≠ 0 → C (rowName store)
        [σ (.n (rowNext store)), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6)] []) := by
  cases store
  · simp only [rowBody, Bool.false_eq_true, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
      List.map_cons, List.map_nil, word_gen] at hb hp
    obtain ⟨hcall, m10, l11, m12, l13, a14, l14, m15, m16, l7, l8, c17, m18, a19, c20, m21, -, hnext,
      hret⟩ := hb
    rw [m10] at l11
    rw [m12] at l13 l14
    rw [a14] at l14
    rw [m16, m15] at l7 l8
    refine ⟨hp.symm, hret.symm, ⟨_, _, _, _, _, hc _ _ hcall, l11, l13, l14, cellsAt_two.mpr ⟨l7, l8⟩,
      fun h => absurd h (by simp)⟩, ?_, ?_, hnext⟩
    · show σ (.n 19) = _; rw [a19, m18, c17]
    · show σ (.n 21) = _; rw [m21, c20]
  · simp only [rowBody, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
      List.map_cons, List.map_nil, word_gen] at hb hp
    obtain ⟨hcall, m10, l11, m12, l13, a14, l14, m15, m16, l7, l8, m17, l18, m19, m20, l7', l8',
      c21, m22, a23, c24, m25, -, hnext, hret⟩ := hb
    rw [m10] at l11
    rw [m12] at l13 l14
    rw [a14] at l14
    rw [m16, m15] at l7 l8
    rw [m17] at l18
    rw [m20, m19] at l7' l8'
    refine ⟨hp.symm, hret.symm, ⟨_, _, _, _, _, hc _ _ hcall, l11, l13, l14, cellsAt_two.mpr ⟨l7, l8⟩,
      fun _ => ⟨_, l18, cellsAt_two.mpr ⟨l7', l8'⟩⟩⟩, ?_, ?_, hnext⟩
    · show σ (.n 23) = _; rw [a23, m22, c21]
    · show σ (.n 25) = _; rw [m25, c24]

/-- **The row loop, its witness named**. -/
theorem row_loop_out (store : Bool) {C : CallRel} {rd : Reader} {σ : Val} {args rets : List E}
    {wc : List E → List E → List K} {wr : List E → List E → List (List K)}
    (hc : ∀ a r, C "da_verify_cell" a r → CellOut rd a r (wc a r))
    (hr : ∀ a r, C (rowName store) a r → RowsOut store rd a r (wr a r))
    (hp : ([.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] : List V).map σ = args)
    (hb : Stmt.HoldsList C rd σ (rowBody store) False (fun rs => rs = rets)) :
    RowsOut store rd args rets (rowWit store σ wc wr) := by
  obtain ⟨rfl, rfl, hcell, ht, hn, hnext⟩ := row_step_w store hc hp hb
  refine ⟨_, _, _, _, _, _, _, rfl, rfl, ?_⟩
  show LoopW _ _ _ (_ :: if σ (.n (rowTest store)) = 0 then [] else _)
  refine loopW_step ht hcell fun h => ?_
  obtain ⟨x, W, lv, rb, xb, node, pb, ha, -, hl⟩ := hr _ _ (hnext h)
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := ha
  exact loopW_start hn hl

/-! ## A column -/

/-- **A column's witness**: its chunk of the vector and its rows' cells. -/
structure DaColumn where
  /-- The column's 256 weights. -/
  weights : List E
  /-- Its cells' symbols, one list a row. -/
  cells : List (List K)
  deriving Inhabited

/-- **`da_verify_column__L{store}`'s outcome, its witness named** `cw`: `Meaning_da_verify_column`
with the dispatch's weights `cw.weights` and the rows' cells `cw.cells`. -/
def ColOutW (store : Bool) (rd : Reader) (args rets : List E) (cw : DaColumn) : Prop :=
  ∃ xb nb np gap glp pb ct rb hs ctr, args = [xb, nb, np, gap, glp, pb, ct, rb, hs, ctr] ∧
    rets = [] ∧ ∃ h0 h1 o0 o1 lv node c0 c1,
      CellsAt rd (hs * (xb * xb)) [h0, h1] ∧
      VdOut rd [xb, h0, h1, ctr] [o0, o1, lv] cw.weights ∧
      CellsAt rd (hs * (xb * gen * (xb * gen))) [o0, o1] ∧
      IsInK nb ∧ (nb ≠ 1 → LoopW 1 nb (RowCellW store rd lv rb xb node pb) cw.cells) ∧
      IsInK gap ∧ (gap ≠ 1 → LoopTo gap fun j => GapStep rd node nb (gen ^ j)) ∧
      (∃ k < 11, glp = gen ^ k ∧ Meaning_da_levels k rd [node] [c0, c1]) ∧
      CellsAt rd (ct * (xb * xb)) [c0, c1]

/-- A column's witness: the dispatch's weights and the row loop's cells. -/
def colWit (σ : Val) (wd : List E → List E → List E) (wr : List E → List E → List (List K)) : DaColumn :=
  ⟨wd [σ (.n 0), σ (.n 12), σ (.n 13), σ (.n 9)] [σ (.n 14), σ (.n 15), σ (.n 16)],
    if σ (.n 25) = 0 then [] else
      wr [σ (.n 26), σ (.n 1), σ (.n 16), σ (.n 7), σ (.n 0), σ (.n 23), σ (.n 5)] []⟩

/-- **`da_verify_column__L{store}`, its witness named**, under any call relation below the
program's. -/
theorem col_out (store : Bool) {C : CallRel} {rd : Reader} (hC : CallRel.Le C (coreProgram.Rel rd))
    {σ : Val} {args rets : List E} {wd : List E → List E → List E} {wr : List E → List E → List (List K)}
    (hd : ∀ a r, C "da_vector_dispatch" a r → VdOut rd a r (wd a r))
    (hr : ∀ a r, C (rowName store) a r → RowsOut store rd a r (wr a r))
    (hp : ([.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9] : List V).map σ = args)
    (hb : Stmt.HoldsList C rd σ (colBody store) False (fun rs => rs = rets)) :
    ColOutW store rd args rets (colWit σ wd wr) := by
  simp only [colBody, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil,
    true_and, word_one, word_gen] at hb hp
  obtain ⟨m10, m11, l12, l13, hdisp, c17, m18, m19, m20, l14, l15, m21, m22, c24, a25, c26,
    hk25, hrow, c27, a28, c29, hk28, hgap, hdl, m32, m33, l30, l31, hret⟩ := hb
  subst hp hret
  rw [a25, c24] at hk25 hrow
  rw [a28, c27] at hk28 hgap
  rw [c29] at hgap
  rw [m11, m10] at l12 l13
  rw [m20, m19, m18, c17] at l14 l15
  rw [m33, m32] at l30 l31
  refine ⟨_, _, _, _, _, _, _, _, _, _, rfl, rfl, σ (.n 12), σ (.n 13), σ (.n 14), σ (.n 15),
    σ (.n 16), σ (.n 23), σ (.n 30), σ (.n 31), cellsAt_two.mpr ⟨l12, l13⟩, hd _ _ hdisp,
    cellsAt_two.mpr ⟨l14, l15⟩, isInK_one_add.mp hk25, fun h => ?_, isInK_one_add.mp hk28,
    fun h => (gap_loop_meaning store rd _ _ _).mp (hC _ _ _ (hgap (one_add_ne_zero.mpr h))),
    dl_dispatch.mp (let ⟨j, hj, hx, hc⟩ := hdl; ⟨j, hj, hx, hC _ _ _ hc⟩), cellsAt_two.mpr ⟨l30, l31⟩⟩
  have h25 : σ (.n 25) ≠ 0 := by rw [a25, c24]; exact one_add_ne_zero.mpr h
  show LoopW _ _ _ (if σ (.n 25) = 0 then [] else _)
  rw [ite_neg' h25]
  obtain ⟨x, W, lv, rb, xb, node, pb, ha, -, hl⟩ := hr _ _ (hrow (one_add_ne_zero.mpr h))
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := ha
  exact loopW_start c26 hl

/-- **A column's facts, from its outcome**: the column's (`ColOk`) with the witness's weights,
`r` cells, and each cell's (`CellOk`) with the witness's symbols. -/
theorem col_facts_w {rd : Reader} {r : ℕ} (hr1 : 1 ≤ r) (hr2 : r ≤ LeanDa.maxRows) {pb ct rb hs ctr : E}
    (hctr : ∀ k < 385, ∀ w, rd (ctr.limb 0 * Parameters.gpow k) = some w → w = word (k * 2048) 0 0)
    {b : ℕ} (hb : b < 128) {cw : DaColumn}
    (h : ColOutW (decide (b < 64)) rd [gen ^ b, gen ^ r, gen ^ LeanDa.nPad r,
      gen ^ (LeanDa.nPad r - r), gen ^ LeanDa.logPad r, pb, ct, rb, hs, ctr] [] cw) :
    ∃ c : ColW, ColOk rd r pb ct rb hs b c ∧ c.ws = cw.weights ∧ cw.cells.length = r ∧
      ∀ i < r, ∃ g : CellW, CellOk rd (decide (b < 64)) c.lv rb (gen ^ b) c.node pb (gen ^ i) g ∧
        g.syms = cw.cells.getD i [] := by
  have hr33 : r < 2 ^ 33 := by unfold LeanDa.maxRows at hr2; omega
  have hlp := logPad_le hr2
  have hN := nPad_le hr2
  obtain ⟨xb, nb, np, gap, glp, pb', ct', rb', hs', ctr', ha, -, h0, h1, o0, o1, lv, node, c0, c1, hh, hdisp,
    ho, -, hrow, -, hgap, ⟨k, hk, hglp, hlv⟩, hc⟩ := h
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := ha
  obtain ⟨xb, rest, hxa, -, hvc⟩ := hdisp
  simp only [List.cons.injEq] at hxa
  obtain ⟨rfl, rfl⟩ := hxa
  obtain ⟨_, _, _, _, _, _, wp, ha, hr, hwl, cv, hcl, hcv, hch, hfr⟩ := hvc
  simp only [List.cons.injEq, and_true] at ha hr
  obtain ⟨rfl, rfl, rfl, rfl⟩ := ha
  obtain ⟨rfl, rfl, rfl⟩ := hr
  have hkl : k = LeanDa.logPad r := gen_pow_inj' (by omega) (by omega) hglp.symm
  subst hkl
  have hfinal : decide (gen ^ b = gen ^ 127) = decide (b = 127) := by
    by_cases h127 : b = 127
    · rw [decide_eq_true h127, decide_eq_true (by rw [h127])]
    · rw [decide_eq_false h127, decide_eq_false fun he => h127 (gen_pow_inj' (by omega) (by omega) he)]
  have hcv' : ∀ k < 4, cv.getD k 0 = cvOf b k := by
    intro k hk
    have hl := hcv k (by omega)
    rw [show gen ^ b * gen ^ b * gen ^ b = gen ^ (3 * b) by rw [← pow_add, ← pow_add]; congr 1; ring,
      loadHolds_mul_gen_pow] at hl
    rw [List.getD_eq_getElem _ _ (by omega), hctr (3 * b + k) (by omega) _ hl.2, cvOf, Nat.add_mul]
  rw [hfinal, chainCells_congr (b' := vxBlocks (cw.weights.getD · 0)) (md' := vxMd (decide (b = 127)) (cvOf b))
    (fun _ _ => rfl) (fun j hj => vxMd_congr hcv' hj)] at hch
  obtain ⟨hlen, hcells⟩ := loopW_one hr33 hr1 (hrow (gen_pow_ne_one' hr1 hr33))
  refine ⟨⟨h0, h1, o0, o1, lv, node, c0, c1, cw.weights⟩, ⟨hwl, ?_, ?_, hch, hfr,
    fun i hi => rowCell_of_w (hcells i (by omega)), fun d hd => ?_, hlv, ?_⟩, rfl, hlen, fun i hi => ?_⟩
  · have e : gen ^ b * gen ^ b = gen ^ (2 * b) := by rw [← pow_add, two_mul]
    rw [e] at hh; exact hh
  · have e : gen ^ b * gen * (gen ^ b * gen) = gen ^ (2 * b + 2) := by
      rw [← pow_succ, ← pow_add]; congr 1; ring
    rw [e] at ho; exact ho
  · exact loopTo_all (by omega) (hgap (gen_pow_ne_one' (by omega) (by omega))) d hd
  · have e : gen ^ b * gen ^ b = gen ^ (2 * b) := by rw [← pow_add, two_mul]
    rw [e] at hc; exact hc
  · have hi' : i < cw.cells.length := by omega
    obtain ⟨d0, d1, s, R, a, hcell, hR, ha, has, hn, hst⟩ := hcells i hi'
    obtain ⟨_, _, _, _, hargs, hrets, hsl, wsc, hwl', hws, hd, hs⟩ := hcell
    simp only [List.cons.injEq, and_true] at hargs hrets
    obtain ⟨rfl⟩ := hargs
    obtain ⟨rfl, rfl, rfl⟩ := hrets
    exact ⟨⟨_, _, _, R, a, cw.cells[i], wsc⟩, ⟨hsl, hwl', hws, hd, hs, hR, ha, has, hn, hst⟩,
      (List.getD_eq_getElem _ _ hi').symm⟩

/-! ## The column loops -/

/-- **The column loop's outcome, its columns named** `L`: from `x` to the loop's end, column
`x·g^j`'s outcome of witness `L[j]`. -/
def ColsOut (store : Bool) (rd : Reader) (args rets : List E) (L : List DaColumn) : Prop :=
  ∃ x ps, args = x :: ps ∧ rets = [] ∧
    LoopW x (colLoopEnd store) (fun y cw => ColOutW store rd (y :: ps) [] cw) L

/-- The column loop's witness: its column's, then the remaining columns'. -/
def colLoopWit (σ : Val) (wc : List E → List E → DaColumn) (wl : List E → List E → List DaColumn) :
    List DaColumn :=
  wc [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7), σ (.n 8), σ (.n 9)] [] ::
    if σ (.n 13) = 0 then [] else
      wl [σ (.n 15), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7), σ (.n 8), σ (.n 9)] []

/-- **One frame of the column loop**: its parameters, its column's call, its test and next column,
and the loop's call on. -/
theorem colLoop_step_w (store : Bool) {C : CallRel} {rd : Reader} {σ : Val} {args rets : List E}
    (hp : ([.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9] : List V).map σ = args)
    (hb : Stmt.HoldsList C rd σ (colLoopBody store) False (fun rs => rs = rets)) :
    args = [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7), σ (.n 8),
      σ (.n 9)] ∧ rets = [] ∧
      C (colName store) [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7),
        σ (.n 8), σ (.n 9)] [] ∧
      σ (.n 13) = σ (.n 0) * gen + colLoopEnd store ∧ σ (.n 15) = σ (.n 0) * gen ∧
      (σ (.n 13) ≠ 0 → C (colLoopName store) [σ (.n 15), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5),
        σ (.n 6), σ (.n 7), σ (.n 8), σ (.n 9)] []) := by
  simp only [colLoopBody, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil,
    word_gen] at hb hp
  obtain ⟨hcall, c10, m11, c12, a13, c14, m15, -, hnext, hret⟩ := hb
  exact ⟨hp.symm, hret.symm, hcall, by rw [a13, m11, c10, c12], by rw [m15, c14], hnext⟩

/-- **The column loop, its witness named**. -/
theorem colLoop_out (store : Bool) {C : CallRel} {rd : Reader} {σ : Val} {args rets : List E}
    {wc : List E → List E → DaColumn} {wl : List E → List E → List DaColumn}
    (hc : ∀ a r, C (colName store) a r → ColOutW store rd a r (wc a r))
    (hl : ∀ a r, C (colLoopName store) a r → ColsOut store rd a r (wl a r))
    (hp : ([.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9] : List V).map σ = args)
    (hb : Stmt.HoldsList C rd σ (colLoopBody store) False (fun rs => rs = rets)) :
    ColsOut store rd args rets (colLoopWit σ wc wl) := by
  obtain ⟨rfl, rfl, hcall, ht, hn, hnext⟩ := colLoop_step_w store hp hb
  refine ⟨_, _, rfl, rfl, loopW_step ht (hc _ _ hcall) fun h => ?_⟩
  obtain ⟨x, ps, ha, -, hl'⟩ := hl _ _ (hnext h)
  simp only [List.cons.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  exact loopW_start hn hl'

end
end LeanVM.Guest.B1.Digest

namespace LeanVM.Guest.B1
export Digest (LoopW loopW_step loopW_pow loopW_one VdOut vdWit vd_out RowCellW RowsOut rowWit
  row_step_w row_loop_out DaColumn ColOutW colWit col_out col_facts_w ColsOut colLoopWit colLoop_step_w colLoop_out)
end LeanVM.Guest.B1
