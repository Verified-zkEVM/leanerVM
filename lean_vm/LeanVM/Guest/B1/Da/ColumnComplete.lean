/-
  LeanVM.Guest.B1.Da.ColumnComplete

  `da_verify_column`, completely: its row loops' and gap loops' iterations, and the column, from
  the memory an honest run holds.
-/

module

public import LeanVM.Guest.B1.Da.ColumnCChk
public import LeanVM.Guest.B1.Da.LevelsComplete
public import LeanVM.Guest.B1.Digest.LoopComplete

/-!
# A column, completely

* `row_block1`, `row_block0`: a row loop's block at row `x`, its cell check holding and the
  running sum, the node and (the prefix columns) the prefix holding the cell's words;
* `gap_block`: a gap loop's block, the padding cell at the node;
* `col_rel`: a column, its vector check, its row and gap loops' blocks at every row and padding
  row, its tree's root (`da_levels`) and the root's cells in the column tree.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

variable {rd : Reader}

/-! ## Loop blocks -/

theorem splitLoopF_append {c : V} {f : String} {args : List V} :
    ∀ pre : List Stmt, pre.all Stmt.flat = true →
      splitLoopF (pre ++ [.callIf c f args, .ret []]) = some (pre, c, f, args)
  | [], _ => rfl
  | [s], h => by
    simp only [List.all_cons, List.all_nil, Bool.and_true] at h
    simp [splitLoopF, h]
  | s :: t :: rest, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := splitLoopF_append (c := c) (f := f) (args := args) (t :: rest) (by simp only [List.all_cons, Bool.and_eq_true]; exact h.2)
    obtain ⟨u, rest', hu⟩ : ∃ u rest', rest ++ [Stmt.callIf c f args, Stmt.ret []] = u :: rest' := by
      cases rest <;> exact ⟨_, _, rfl⟩
    simp only [List.cons_append, hu] at ih ⊢
    rw [show splitLoopF (s :: t :: u :: rest') = if Stmt.flat s then
        (splitLoopF (t :: u :: rest')).map (fun p => (s :: p.1, p.2)) else none from rfl,
      ite_pos' h.1, ih]
    rfl

theorem loopPre_of_body {fn : Fn} {pre : List Stmt} {c : V} {f : String} {args : List V}
    (h : fn.body = pre ++ [.callIf c f args, .ret []]) (hf : pre.all Stmt.flat = true) :
    loopPre fn = pre := by
  simp [loopPre, h, splitLoopF_append pre hf]

theorem params_of_shape {fn : Fn} {f : String} {n : ℕ} (hs : loopShapeF fn f = true)
    (hl : fn.params.length = n) : fn.params = (List.range n).map V.n := by
  simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs
  rw [hs.1.2, hl]

set_option maxRecDepth 100000 in
theorem row417_shape : loopShapeF (coreProgram.getD 874 default) "__loop415" = true ∧
    (coreProgram.getD 874 default).params.length = 7 := by decide +kernel

set_option maxRecDepth 100000 in
theorem row419_shape : loopShapeF (coreProgram.getD 876 default) "__loop417" = true ∧
    (coreProgram.getD 876 default).params.length = 7 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gap418_shape : loopShapeF (coreProgram.getD 875 default) "__loop416" = true ∧
    (coreProgram.getD 875 default).params.length = 4 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gap420_shape : loopShapeF (coreProgram.getD 877 default) "__loop418" = true ∧
    (coreProgram.getD 877 default).params.length = 4 := by decide +kernel

set_option maxRecDepth 20000 in
/-- **A prefix column's row** (`__loop415`): the cell check, the running sum's step, the cell's
words at the node and in the row's prefix. -/
theorem row_block1 {x N lv rowbase xb node pb d0 d1 s a prev pp : E}
    (hcell : coreProgram.Rel rd "da_verify_cell" [lv] [d0, d1, s])
    (ha : LoadHolds rd (rowbase * x) 0 a) (hprev : LoadHolds rd (a * xb) 0 prev)
    (hnew : LoadHolds rd (a * xb) 1 (prev + s)) (hn0 : LoadHolds rd (node * (x * x)) 0 d0)
    (hn1 : LoadHolds rd (node * (x * x)) 1 d1) (hpp : LoadHolds rd (pb * x) 0 pp)
    (hq0 : LoadHolds rd (pp * (xb * xb)) 0 d0) (hq1 : LoadHolds rd (pp * (xb * xb)) 1 d1) :
    LoopBlock rd (coreProgram.getD 874 default) x N [lv, rowbase, xb, node, pb] := by
  obtain ⟨hs, hl⟩ := row417_shape
  refine ⟨Val.ofArgs [x, N, lv, rowbase, xb, node, pb, d0, d1, s, rowbase * x, a, a * xb, prev,
    prev + s, x * x, node * (x * x), pb * x, pp, xb * xb, pp * (xb * xb), word 2 0 0, x * word 2 0 0,
    x * word 2 0 0 + N, word 2 0 0, x * word 2 0 0], by rw [params_of_shape hs hl]; rfl, ?_⟩
  rw [loopPre_of_body core874_body (by decide)]
  intro st hst
  simp only [rowPre, ite_true, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hst
  rcases hst with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp (config := {failIfUnchanged := false}) only [Stmt.Holds, Atom.Holds, ofArgs_n,
    List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero, and_true]
  exacts [hcell, ha, hprev, hnew, hn0, hn1, hpp, hq0, hq1]

set_option maxRecDepth 20000 in
/-- **A row of the other columns** (`__loop417`). -/
theorem row_block0 {x N lv rowbase xb node pb d0 d1 s a prev : E}
    (hcell : coreProgram.Rel rd "da_verify_cell" [lv] [d0, d1, s])
    (ha : LoadHolds rd (rowbase * x) 0 a) (hprev : LoadHolds rd (a * xb) 0 prev)
    (hnew : LoadHolds rd (a * xb) 1 (prev + s)) (hn0 : LoadHolds rd (node * (x * x)) 0 d0)
    (hn1 : LoadHolds rd (node * (x * x)) 1 d1) :
    LoopBlock rd (coreProgram.getD 876 default) x N [lv, rowbase, xb, node, pb] := by
  obtain ⟨hs, hl⟩ := row419_shape
  refine ⟨Val.ofArgs [x, N, lv, rowbase, xb, node, pb, d0, d1, s, rowbase * x, a, a * xb, prev,
    prev + s, x * x, node * (x * x), word 2 0 0, x * word 2 0 0, x * word 2 0 0 + N, word 2 0 0,
    x * word 2 0 0], by rw [params_of_shape hs hl]; rfl, ?_⟩
  rw [loopPre_of_body core876_body (by decide)]
  intro st hst
  simp only [rowPre, Bool.false_eq_true, ite_false, List.cons_append, List.nil_append,
    List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hst
  rcases hst with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp (config := {failIfUnchanged := false}) only [Stmt.Holds, Atom.Holds, ofArgs_n,
    List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero, and_true]
  exacts [hcell, ha, hprev, hnew, hn0, hn1]

set_option maxRecDepth 20000 in
/-- **A padding row of a column** (`__loop416`, `__loop418`): the padding cell at the node. -/
theorem gap_block {j : ℕ} {f : String} (hs : loopShapeF (coreProgram.getD j default) f = true)
    (hl : (coreProgram.getD j default).params.length = 4)
    (hb : Fn.body (coreProgram.getD j default) = gapBody f) {x N node nb : E}
    (h0 : LoadHolds rd (node * (nb * nb) * (x * x)) 0 (digestScalars daPadCellDigest).1)
    (h1 : LoadHolds rd (node * (nb * nb) * (x * x)) 1 (digestScalars daPadCellDigest).2) :
    LoopBlock rd (coreProgram.getD j default) x N [node, nb] := by
  have e := daPadCell_cells
  simp only [Prod.ext_iff] at e
  refine ⟨Val.ofArgs [x, N, node, nb, nb * nb, node * (nb * nb), x * x, node * (nb * nb) * (x * x),
    word 15569472805043175342 18354418831448413762 0, word 11782766640862828499 15718207409690975807 0,
    word 2 0 0, x * word 2 0 0, x * word 2 0 0 + N, word 2 0 0, x * word 2 0 0],
    by rw [params_of_shape hs hl]; rfl, ?_⟩
  rw [loopPre_of_body hb (by decide)]
  intro st hst
  simp only [gapPre, List.mem_cons, List.not_mem_nil, or_false] at hst
  rw [← e.1] at h0
  rw [← e.2] at h1
  rcases hst with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp (config := {failIfUnchanged := false}) only [Stmt.Holds, Atom.Holds, ofArgs_n,
    List.getD_cons_succ, List.getD_cons_zero, and_true]
  · exact h0
  · exact h1

/-! ## A column -/

/-- A column's honest valuation. -/
def colσ (xb : E) (r gp L : ℕ) (pb coltree rowbase cd lv node c0 c1 : E) : Val :=
  Val.ofArgs [xb, gen ^ r, gen ^ 2 ^ L, gen ^ gp, gen ^ L, pb,
    coltree, rowbase, cd, xb * xb, cd * (xb * xb), lv, gen ^ 2 ^ L * gen ^ 2 ^ L,
    gen ^ 2 ^ L * gen ^ 2 ^ L * (gen ^ 2 ^ L * gen ^ 2 ^ L), node, word 1 0 0, word 1 0 0 + gen ^ r,
    word 1 0 0, word 1 0 0, word 1 0 0 + gen ^ gp, word 1 0 0, c0, c1, xb * xb, coltree * (xb * xb)]

set_option maxRecDepth 20000 in
/-- **A column's body holds** on its honest valuation, its vector check, its rows' and padding
rows' blocks, its tree's root, and the root's cells in the column tree. -/
theorem col_holds {rl gl : String} {jr jg : ℕ}
    (hfr : coreProgram.find? rl = some (coreProgram.getD jr default))
    (hsr : loopShapeF (coreProgram.getD jr default) rl = true)
    (hfg : coreProgram.find? gl = some (coreProgram.getD jg default))
    (hsg : loopShapeF (coreProgram.getD jg default) gl = true)
    {xb pb coltree rowbase cd lv node c0 c1 : E} {r gp L : ℕ} (hL : L ≤ 10)
    (hvec : coreProgram.Rel rd "da_vector_cell" [cd * (xb * xb)] [lv])
    (hrows : ∀ i < r, LoopBlock rd (coreProgram.getD jr default) (gen ^ i) (gen ^ r)
      [lv, rowbase, xb, node, pb])
    (hgaps : ∀ d < gp, LoopBlock rd (coreProgram.getD jg default) (gen ^ d) (gen ^ gp)
      [node, gen ^ r])
    (hlev : coreProgram.Rel rd (daLevelsName L) [node] [c0, c1])
    (hs0 : LoadHolds rd (coltree * (xb * xb)) 0 c0) (hs1 : LoadHolds rd (coltree * (xb * xb)) 1 c1) :
    Stmt.HoldsList (coreProgram.Rel rd) rd (colσ xb r gp L pb coltree rowbase cd lv node c0 c1)
      (colBody rl gl) False (fun rs => rs = []) := by
  have gr := guard_complete hfr hsr hrows
  have gg := guard_complete hfg hsg hgaps
  rw [← word_one] at gr gg
  simp only [colσ, colBody, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil,
    ofArgs_n, List.getD_cons_succ, List.getD_cons_zero, true_and, and_true]
  have hlt : L < dlNames.length := by simp [dlNames]; omega
  exact ⟨hvec, gr.1, gr.2, gg.1, gg.2, ⟨L, hlt, gen_pow_eq_ofK L, by
    rw [show dlNames[L] = daLevelsName L by simp [dlNames]]; exact hlev⟩, hs0, hs1⟩

/-- **A column holds**, its vector check, its rows' and padding rows' blocks, its tree's root, and
the root's cells in the column tree. -/
theorem col_rel {fname rl gl : String} {jc jr jg : ℕ}
    (hfc : coreProgram.find? fname = some (coreProgram.getD jc default))
    (hbody : Fn.body (coreProgram.getD jc default) = colBody rl gl)
    (hpar : (coreProgram.getD jc default).params = (List.range 9).map V.n)
    (hfr : coreProgram.find? rl = some (coreProgram.getD jr default))
    (hsr : loopShapeF (coreProgram.getD jr default) rl = true)
    (hfg : coreProgram.find? gl = some (coreProgram.getD jg default))
    (hsg : loopShapeF (coreProgram.getD jg default) gl = true)
    {xb pb coltree rowbase cd lv node c0 c1 : E} {r gp L : ℕ} (hL : L ≤ 10)
    (hvec : coreProgram.Rel rd "da_vector_cell" [cd * (xb * xb)] [lv])
    (hrows : ∀ i < r, LoopBlock rd (coreProgram.getD jr default) (gen ^ i) (gen ^ r)
      [lv, rowbase, xb, node, pb])
    (hgaps : ∀ d < gp, LoopBlock rd (coreProgram.getD jg default) (gen ^ d) (gen ^ gp)
      [node, gen ^ r])
    (hlev : coreProgram.Rel rd (daLevelsName L) [node] [c0, c1])
    (hs0 : LoadHolds rd (coltree * (xb * xb)) 0 c0) (hs1 : LoadHolds rd (coltree * (xb * xb)) 1 c1) :
    coreProgram.Rel rd fname [xb, gen ^ r, gen ^ 2 ^ L, gen ^ gp, gen ^ L, pb, coltree, rowbase, cd]
      [] := by
  refine (rel_iff_sem hfc _ _).mpr ⟨colσ xb r gp L pb coltree rowbase cd lv node c0 c1,
    by rw [hpar]; rfl, ?_⟩
  rw [hbody]
  exact col_holds hfr hsr hfg hsg hL hvec hrows hgaps hlev hs0 hs1

end
end LeanVM.Guest.B1.Da
