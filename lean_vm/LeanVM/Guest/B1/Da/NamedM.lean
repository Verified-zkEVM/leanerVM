/-
  LeanVM.Guest.B1.Da.NamedM

  The DA check's callees with their witnesses named, under a hash model, and `da_verify` soundly
  under a model with its witness named (`da_verify_sound_wM`).
-/

module

public import LeanVM.Guest.B1.Da.VerifyM

/-!
# The DA check's witnesses, named, over a hash model

`Named.lean` and `da_verify_sound_w` state each function of the DA check with its witness a
function of its valuation and of its callees' witness functions, as `Located/Da.lean` decodes
them from memory. Over a `HashModel` the same witnesses (`vcSyms`, `vxWs`, `vdWit`, `rowWit`,
`colWit`, `colLoopWit`, `dvWit`) satisfy the outcomes over the model (`CellOutM`, `VecOutB`,
`VdOutB`, `RowsOutM`, `ColOutWM`, `ColsOutM`), each `_out` lemma the deployed one's proof under
`Stmt.HoldsListB M.sem`, and `da_verify_sound_wM` concludes `DaOutM`: the returned words decode to
a root and a vector digest that `dvWit σ w90 w91` opens over the model (`Witness.OpensWith`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-! ## `da_vector_dispatch` -/

/-- **`da_vector_dispatch`'s outcome under `S`, its weights named** `ws` (`VdOut`). -/
def VdOutB (S : BlakeSem) (rd : Reader) (args rets : List E) (ws : List E) : Prop :=
  ∃ xb rest, args = xb :: rest ∧ IsInK xb ∧ VecOutB S (decide (xb = gen ^ 127)) rd args rets ws

/-- **`da_vector_dispatch` under `S`, its witness named** (`vd_out`). -/
theorem vd_outB {S : BlakeSem} {C : CallRel} {rd : Reader} {σ : Val} {args rets : List E}
    {wv : Bool → List E → List E → List E}
    (hv : ∀ final a r, C (vxName final) a r → VecOutB S final rd a r (wv final a r))
    (hp : ([.n 0, .n 1, .n 2, .n 3] : List V).map σ = args)
    (hb : Stmt.HoldsListB S C rd σ vdBody False (fun rs => rs = rets)) :
    VdOutB S rd args rets (vdWit σ wv) := by
  simp only [vdBody, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons,
    List.map_nil] at hb hp
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

/-- **Row `x` of a column over a model, its cell's symbols named** `syms` (`RowCellW`). -/
def RowCellWM (M : HashModel) (store : Bool) (rd : Reader) (lv rb xb node pb x : E)
    (syms : List K) : Prop :=
  ∃ d0 d1 s R a, CellOutM M rd [lv] [d0, d1, s] syms ∧ LoadHolds rd (rb * x) 0 R ∧
    LoadHolds rd (R * xb) 0 a ∧ LoadHolds rd (R * xb) 1 (a + s) ∧
    CellsAt rd (node * (x * x)) [d0, d1] ∧
    (store = true → ∃ P, LoadHolds rd (pb * x) 0 P ∧ CellsAt rd (P * (xb * xb)) [d0, d1])

/-- A row with its cell's symbols named gives the row's facts. -/
theorem rowCellM_of_w {M : HashModel} {store : Bool} {rd : Reader} {lv rb xb node pb x : E}
    {syms : List K} (h : RowCellWM M store rd lv rb xb node pb x syms) :
    RowCellM M store rd lv rb xb node pb x :=
  let ⟨d0, d1, s, R, a, hc, h'⟩ := h
  ⟨d0, d1, s, R, a, meaning_of_cellOutM hc, h'⟩

/-- **The row loop's outcome over a model, its rows' symbols named** `L` (`RowsOut`). -/
def RowsOutM (M : HashModel) (store : Bool) (rd : Reader) (args rets : List E)
    (L : List (List K)) : Prop :=
  ∃ x W lv rb xb node pb, args = [x, W, lv, rb, xb, node, pb] ∧ rets = [] ∧
    LoopW x W (RowCellWM M store rd lv rb xb node pb) L

/-- **One frame of the row loop, under a model** (`row_step_w`). -/
theorem row_step_wB {M : HashModel} (store : Bool) {C : CallRel} {rd : Reader} {σ : Val}
    {args rets : List E} {wc : List E → List E → List K}
    (hc : ∀ a r, C "da_verify_cell" a r → CellOutM M rd a r (wc a r))
    (hp : ([.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] : List V).map σ = args)
    (hb : Stmt.HoldsListB M.sem C rd σ (rowBody store) False (fun rs => rs = rets)) :
    args = [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6)] ∧ rets = [] ∧
      RowCellWM M store rd (σ (.n 2)) (σ (.n 3)) (σ (.n 4)) (σ (.n 5)) (σ (.n 6)) (σ (.n 0))
        (wc [σ (.n 2)] [σ (.n 7), σ (.n 8), σ (.n 9)]) ∧
      σ (.n (rowTest store)) = σ (.n 0) * gen + σ (.n 1) ∧
      σ (.n (rowNext store)) = σ (.n 0) * gen ∧
      (σ (.n (rowTest store)) ≠ 0 → C (rowName store)
        [σ (.n (rowNext store)), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6)]
        []) := by
  cases store
  · simp only [rowBody, Bool.false_eq_true, ↓reduceIte, Stmt.HoldsListB, Stmt.HoldsB,
      Atom.HoldsB, List.map_cons, List.map_nil, word_gen] at hb hp
    obtain ⟨hcall, m10, l11, m12, l13, a14, l14, m15, m16, l7, l8, c17, m18, a19, c20, m21, -,
      hnext, hret⟩ := hb
    rw [m10] at l11
    rw [m12] at l13 l14
    rw [a14] at l14
    rw [m16, m15] at l7 l8
    refine ⟨hp.symm, hret.symm, ⟨_, _, _, _, _, hc _ _ hcall, l11, l13, l14,
      cellsAt_two.mpr ⟨l7, l8⟩, fun h => absurd h (by simp)⟩, ?_, ?_, hnext⟩
    · show σ (.n 19) = _; rw [a19, m18, c17]
    · show σ (.n 21) = _; rw [m21, c20]
  · simp only [rowBody, ↓reduceIte, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB,
      List.map_cons, List.map_nil, word_gen] at hb hp
    obtain ⟨hcall, m10, l11, m12, l13, a14, l14, m15, m16, l7, l8, m17, l18, m19, m20, l7', l8',
      c21, m22, a23, c24, m25, -, hnext, hret⟩ := hb
    rw [m10] at l11
    rw [m12] at l13 l14
    rw [a14] at l14
    rw [m16, m15] at l7 l8
    rw [m17] at l18
    rw [m20, m19] at l7' l8'
    refine ⟨hp.symm, hret.symm, ⟨_, _, _, _, _, hc _ _ hcall, l11, l13, l14,
      cellsAt_two.mpr ⟨l7, l8⟩, fun _ => ⟨_, l18, cellsAt_two.mpr ⟨l7', l8'⟩⟩⟩, ?_, ?_, hnext⟩
    · show σ (.n 23) = _; rw [a23, m22, c21]
    · show σ (.n 25) = _; rw [m25, c24]

/-- **The row loop under a model, its witness named** (`row_loop_out`). -/
theorem row_loop_outB {M : HashModel} (store : Bool) {C : CallRel} {rd : Reader} {σ : Val}
    {args rets : List E} {wc : List E → List E → List K} {wr : List E → List E → List (List K)}
    (hc : ∀ a r, C "da_verify_cell" a r → CellOutM M rd a r (wc a r))
    (hr : ∀ a r, C (rowName store) a r → RowsOutM M store rd a r (wr a r))
    (hp : ([.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] : List V).map σ = args)
    (hb : Stmt.HoldsListB M.sem C rd σ (rowBody store) False (fun rs => rs = rets)) :
    RowsOutM M store rd args rets (rowWit store σ wc wr) := by
  obtain ⟨rfl, rfl, hcell, ht, hn, hnext⟩ := row_step_wB store hc hp hb
  refine ⟨_, _, _, _, _, _, _, rfl, rfl, ?_⟩
  show LoopW _ _ _ (_ :: if σ (.n (rowTest store)) = 0 then [] else _)
  refine loopW_step ht hcell fun h => ?_
  obtain ⟨x, W, lv, rb, xb, node, pb, ha, -, hl⟩ := hr _ _ (hnext h)
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := ha
  exact loopW_start hn hl

/-! ## A column -/

/-- **`da_verify_column__L{store}`'s outcome over a model, its witness named** `cw`
(`ColOutW`). -/
def ColOutWM (M : HashModel) (store : Bool) (rd : Reader) (args rets : List E) (cw : DaColumn) :
    Prop :=
  ∃ xb nb np gap glp pb ct rb hs ctr, args = [xb, nb, np, gap, glp, pb, ct, rb, hs, ctr] ∧
    rets = [] ∧ ∃ h0 h1 o0 o1 lv node c0 c1,
      CellsAt rd (hs * (xb * xb)) [h0, h1] ∧
      VdOutB M.sem rd [xb, h0, h1, ctr] [o0, o1, lv] cw.weights ∧
      CellsAt rd (hs * (xb * gen * (xb * gen))) [o0, o1] ∧
      IsInK nb ∧ (nb ≠ 1 → LoopW 1 nb (RowCellWM M store rd lv rb xb node pb) cw.cells) ∧
      IsInK gap ∧ (gap ≠ 1 → LoopTo gap fun j => GapStep rd node nb (gen ^ j)) ∧
      (∃ k < 11, glp = gen ^ k ∧ Meaning_da_levelsWith M k rd [node] [c0, c1]) ∧
      CellsAt rd (ct * (xb * xb)) [c0, c1]

/-- **`da_verify_column__L{store}` under a model, its witness named** (`col_out`), under any call
relation below the program's. -/
theorem col_outB {M : HashModel} (store : Bool) {C : CallRel} {rd : Reader}
    (hC : CallRel.Le C (coreProgram.RelB M.sem rd)) {σ : Val} {args rets : List E}
    {wd : List E → List E → List E} {wr : List E → List E → List (List K)}
    (hd : ∀ a r, C "da_vector_dispatch" a r → VdOutB M.sem rd a r (wd a r))
    (hr : ∀ a r, C (rowName store) a r → RowsOutM M store rd a r (wr a r))
    (hp : ([.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9] : List V).map σ = args)
    (hb : Stmt.HoldsListB M.sem C rd σ (colBody store) False (fun rs => rs = rets)) :
    ColOutWM M store rd args rets (colWit σ wd wr) := by
  simp only [colBody, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil,
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
    fun h => gap_loop_B store rd _ _ _ (hC _ _ _ (hgap (one_add_ne_zero.mpr h))),
    dl_dispatchM (let ⟨j, hj, hx, hc⟩ := hdl; ⟨j, hj, hx, hC _ _ _ hc⟩),
    cellsAt_two.mpr ⟨l30, l31⟩⟩
  have h25 : σ (.n 25) ≠ 0 := by rw [a25, c24]; exact one_add_ne_zero.mpr h
  show LoopW _ _ _ (if σ (.n 25) = 0 then [] else _)
  rw [ite_neg' h25]
  obtain ⟨x, W, lv, rb, xb, node, pb, ha, -, hl⟩ := hr _ _ (hrow (one_add_ne_zero.mpr h))
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := ha
  exact loopW_start c26 hl

/-- **A column's facts over a model, from its outcome** (`col_facts_w`): `ColOkM` with the
witness's weights, `r` cells, and each cell's `CellOkM` with the witness's symbols. -/
theorem col_facts_wM {M : HashModel} {rd : Reader} {r : ℕ} (hr1 : 1 ≤ r)
    (hr2 : r ≤ LeanDa.maxRows) {pb ct rb hs ctr : E}
    (hctr : ∀ k < 385, ∀ w, rd (ctr.limb 0 * Parameters.gpow k) = some w → w = word (k * 2048) 0 0)
    {b : ℕ} (hb : b < 128) {cw : DaColumn}
    (h : ColOutWM M (decide (b < 64)) rd [gen ^ b, gen ^ r, gen ^ LeanDa.nPad r,
      gen ^ (LeanDa.nPad r - r), gen ^ LeanDa.logPad r, pb, ct, rb, hs, ctr] [] cw) :
    ∃ c : ColW, ColOkM M rd r pb ct rb hs b c ∧ c.ws = cw.weights ∧ cw.cells.length = r ∧
      ∀ i < r, ∃ g : CellW, CellOkM M rd (decide (b < 64)) c.lv rb (gen ^ b) c.node pb (gen ^ i) g ∧
        g.syms = cw.cells.getD i [] := by
  have hr33 : r < 2 ^ 33 := by unfold LeanDa.maxRows at hr2; omega
  have hlp := logPad_le hr2
  have hN := nPad_le hr2
  obtain ⟨xb, nb, np, gap, glp, pb', ct', rb', hs', ctr', ha, -, h0, h1, o0, o1, lv, node, c0, c1,
    hh, hdisp, ho, -, hrow, -, hgap, ⟨k, hk, hglp, hlv⟩, hc⟩ := h
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
  rw [hfinal, chainSteps_congr (b' := vxBlocks (cw.weights.getD · 0))
    (md' := vxMd (decide (b = 127)) (cvOf b)) (fun _ _ => rfl) (fun j hj => vxMd_congr hcv' hj)]
    at hch
  obtain ⟨hlen, hcells⟩ := loopW_one hr33 hr1 (hrow (gen_pow_ne_one' hr1 hr33))
  refine ⟨⟨h0, h1, o0, o1, lv, node, c0, c1, cw.weights⟩, ⟨hwl, ?_, ?_, hch, hfr,
    fun i hi => rowCellM_of_w (hcells i (by omega)), fun d hd => ?_, hlv, ?_⟩, rfl, hlen,
    fun i hi => ?_⟩
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

/-- **The column loop's outcome over a model, its columns named** `L` (`ColsOut`). -/
def ColsOutM (M : HashModel) (store : Bool) (rd : Reader) (args rets : List E)
    (L : List DaColumn) : Prop :=
  ∃ x ps, args = x :: ps ∧ rets = [] ∧
    LoopW x (colLoopEnd store) (fun y cw => ColOutWM M store rd (y :: ps) [] cw) L

/-- **One frame of the column loop under `S`** (`colLoop_step_w`). -/
theorem colLoop_step_wB {S : BlakeSem} (store : Bool) {C : CallRel} {rd : Reader} {σ : Val}
    {args rets : List E}
    (hp : ([.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9] : List V).map σ = args)
    (hb : Stmt.HoldsListB S C rd σ (colLoopBody store) False (fun rs => rs = rets)) :
    args = [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7),
      σ (.n 8), σ (.n 9)] ∧ rets = [] ∧
      C (colName store) [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6),
        σ (.n 7), σ (.n 8), σ (.n 9)] [] ∧
      σ (.n 13) = σ (.n 0) * gen + colLoopEnd store ∧ σ (.n 15) = σ (.n 0) * gen ∧
      (σ (.n 13) ≠ 0 → C (colLoopName store) [σ (.n 15), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4),
        σ (.n 5), σ (.n 6), σ (.n 7), σ (.n 8), σ (.n 9)] []) := by
  simp only [colLoopBody, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil,
    word_gen] at hb hp
  obtain ⟨hcall, c10, m11, c12, a13, c14, m15, -, hnext, hret⟩ := hb
  exact ⟨hp.symm, hret.symm, hcall, by rw [a13, m11, c10, c12], by rw [m15, c14], hnext⟩

/-- **The column loop under a model, its witness named** (`colLoop_out`). -/
theorem colLoop_outB {M : HashModel} (store : Bool) {C : CallRel} {rd : Reader} {σ : Val}
    {args rets : List E} {wc : List E → List E → DaColumn} {wl : List E → List E → List DaColumn}
    (hc : ∀ a r, C (colName store) a r → ColOutWM M store rd a r (wc a r))
    (hl : ∀ a r, C (colLoopName store) a r → ColsOutM M store rd a r (wl a r))
    (hp : ([.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9] : List V).map σ = args)
    (hb : Stmt.HoldsListB M.sem C rd σ (colLoopBody store) False (fun rs => rs = rets)) :
    ColsOutM M store rd args rets (colLoopWit σ wc wl) := by
  obtain ⟨rfl, rfl, hcall, ht, hn, hnext⟩ := colLoop_step_wB store hp hb
  refine ⟨_, _, rfl, rfl, loopW_step ht (hc _ _ hcall) fun h => ?_⟩
  obtain ⟨x, ps, ha, -, hl'⟩ := hl _ _ (hnext h)
  simp only [List.cons.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  exact loopW_start hn hl'

/-! ## `da_verify`, its witness named -/

/-- **`da_verify`'s outcome over a model, its witness named** `w` (`DaOut`): the returned words
decode to a root and a vector digest that `w` opens over the model, the padding digests the
guest's. -/
def DaOutM (M : HashModel) (_rd : Reader) (_gsq : E) (r0 r1 v0 v1 : E) (w : Da.Witness) : Prop :=
  ∃ root ∈ digestOfScalars (r0, r1), ∃ vd ∈ digestOfScalars (v0, v1),
    w.OpensWith M.H (Da.toBytes padCellD) (Da.toBytes padRowD) root vd

/-- `DaOutM` is the root, the vector digest and the opening with the witness given. -/
theorem daOutM_iff {M : HashModel} {rd : Reader} {gsq r0 r1 v0 v1 : E} {w : Da.Witness} :
    DaOutM M rd gsq r0 r1 v0 v1 w ↔
      ∃ root vd : Digest, (r0, r1) = digestScalars root ∧ (v0, v1) = digestScalars vd ∧
        w.OpensWith M.H (Da.toBytes padCellD) (Da.toBytes padRowD) root vd := by
  constructor
  · rintro ⟨root, h1, vd, h2, h⟩
    exact ⟨root, vd, (digestScalars_digestOfScalars h1).symm,
      (digestScalars_digestOfScalars h2).symm, h⟩
  · rintro ⟨root, vd, h1, h2, h⟩
    refine ⟨root, ?_, vd, ?_, h⟩
    · rw [h1]; exact digestOfScalars_digestScalars root
    · rw [h2]; exact digestOfScalars_digestScalars vd

/-- At the deployed model the outcome is the deployed one. -/
theorem daOutM_deployed {rd : Reader} {gsq r0 r1 v0 v1 : E} {w : Da.Witness} :
    DaOutM HashModel.deployed rd gsq r0 r1 v0 v1 w ↔ DaOut rd gsq r0 r1 v0 v1 w := by
  unfold DaOutM DaOut
  simp only [opensWith_deployed_iff]

/-- **`da_verify`, soundly under a hash model, its witness named** (`da_verify_sound_w`): on a
valuation of its body under a call relation below the program's, whose column loops give their
columns' witnesses `w90`, `w91` over the model, the returned words are a root and a vector digest
that `dvWit σ w90 w91` opens over the model. -/
theorem da_verify_sound_wM {M : HashModel} {C : CallRel} {rd : Reader}
    (hC : CallRel.Le C (coreProgram.RelB M.sem rd)) (hm : MemOk rd) {gsq : E}
    (hT : SquaresAt rd gsq) {w90 w91 : List E → List E → List DaColumn}
    (h90 : ∀ args rets, C "__loop90" args rets → ColsOutM M true rd args rets (w90 args rets))
    (h91 : ∀ args rets, C "__loop91" args rets → ColsOutM M false rd args rets (w91 args rets))
    {σ : Val} {r0 r1 v0 v1 : E} (hp : ([.n 0] : List V).map σ = [gsq])
    (hb : Stmt.HoldsListB M.sem C rd σ dvBody False (fun rs => rs = [r0, r1, v0, v1])) :
    DaOutM M rd gsq r0 r1 v0 v1 (dvWit σ w90 w91) := by
  obtain ⟨r, c420, c421, hnb, hnp, hgap, hglp, hrest, hc90, hc91⟩ := da_verify_restM hC hm hT hp hb
  obtain ⟨hr1, hr2, -, -, -, -, hctr, -⟩ := id hrest
  -- the prefix columns
  obtain ⟨x, ps, ha, -, hl⟩ := h90 _ _ hc90
  unfold dvColArgs at ha
  rw [c420, hnb, hnp, hgap, hglp] at ha
  simp only [List.cons.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  rw [colLoopEnd_eq, ite_pos' rfl] at hl
  obtain ⟨hl90, hB90⟩ := loopW_one (n := 64) (by norm_num) (by norm_num) hl
  -- the other columns
  obtain ⟨x, ps', ha, -, hl⟩ := h91 _ _ hc91
  unfold dvColArgs at ha
  rw [c421, hnb, hnp, hgap, hglp] at ha
  simp only [List.cons.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  rw [colLoopEnd_eq, ite_neg' (by decide)] at hl
  obtain ⟨hl91, hB91⟩ := loopW_pow (a := 64) (n := 64) (by norm_num) (by norm_num) hl
  -- each column, and its cells
  have hcol : ∀ b < 128, ColOutWM M (decide (b < 64)) rd [gen ^ b, gen ^ r, gen ^ LeanDa.nPad r,
      gen ^ (LeanDa.nPad r - r), gen ^ LeanDa.logPad r, σ (.n 13), σ (.n 419), σ (.n 415),
      σ (.n 17), σ (.n 405)] [] (dvCol σ w90 w91 b) := by
    intro b hb
    unfold dvCol
    by_cases h64 : b < 64
    · rw [ite_pos' h64, decide_eq_true h64, List.getD_eq_getElem _ _ (by omega)]
      exact hB90 b (by omega)
    · rw [ite_neg' h64, decide_eq_false h64, List.getD_eq_getElem _ _ (by omega)]
      have := hB91 (b - 64) (by omega)
      rwa [show 64 + (b - 64) = b by omega] at this
  obtain ⟨F, hF⟩ := choose_lt (fun b hb => col_facts_wM hr1 hr2 hctr hb (hcol b hb))
  obtain ⟨G, hG⟩ := choose_lt₂ (n := 128) (m := r) (P := fun b i g =>
      CellOkM M rd (decide (b < 64)) (F b).lv (σ (.n 415)) (gen ^ b) (F b).node (σ (.n 13))
        (gen ^ i) g ∧ g.syms = (dvCol σ w90 w91 b).cells.getD i [])
    (fun b hb i hi => (hF b hb).2.2.2 i hi)
  obtain ⟨root, vd, e1, e2, ho⟩ :=
    opens_ofM hrest F G (fun b hb => (hF b hb).1) (fun b hb i hi => (hG b hb i hi).1)
  have hw : daWitOf r (fun b i => (G b i).syms) (fun b => (F b).ws) = dvWit σ w90 w91 := by
    unfold dvWit
    rw [(hF 0 (by norm_num)).2.2.1]
    exact daWitOf_congr (fun b hb i hi => (hG b hb i hi).2) (fun b hb => (hF b hb).2.1)
  rw [← hw]
  exact daOutM_iff.mpr ⟨root, vd, e1, e2, ho⟩

end
end LeanVM.Guest.B1.Digest
