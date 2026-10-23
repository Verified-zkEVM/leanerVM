/-
  LeanVM.Guest.B1.Tables.VtC.BBase

  Tools for `verify_tables`' completeness on its bus sides (statements `2404 ..< 5152`): the
  equations of its pure atoms and its weight reads as a predicate the soundness's algebra can be
  replayed on (`VtP`), and the statements' relations from the honest valuation: reads, range
  checks, dispatches, equality checks.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.Hon
public import LeanVM.Guest.B1.Tables.Vt.SelMath

/-!
# Tools for the bus sides

`VtP rd σ`: every atom of `vtPre` that `okP` selects (constants, sums, copies, products of
older values, reads of the bus weights `fp_w` below `16`) holds; `VtP.atom` reads one with the
selection decided. `vtP_honest`: the honest valuation satisfies it when the memory holds `16`
weights at `fp_w`. The soundness's algebraic lemmas, stated on `VtH`, replay on `VtP`.

`vsh_read`: a read of a word the memory holds; `vsh_rc`: a range check `log x < K` on
`x = g^e`, `e < K`, the memory defined at `g^i`, `i < K`; `vsh_eq`: an equality check.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier

@[expose] public section

/-- The atoms `VtP` keeps: constants, sums, copies, products of older values, reads through
`fp_w` (`.n 14`) below `16`. -/
def okP : Atom → Bool
  | .load _ p off => decide (p = .n 14) && decide (off < 16)
  | .const .. => true
  | .add .. => true
  | .copy .. => true
  | .mul d x y => decide (x.idx < d.idx) && decide (y.idx < d.idx)
  | _ => false

/-- **The kept atoms of `vtPre` hold.** -/
def VtP (rd : Reader) (σ : Val) : Prop :=
  ∀ (n : ℕ) (a : Atom), tbStmtsEqb [.atom a] ((vtPre.drop n).take 1) = true → okP a = true →
    a.Holds rd σ

theorem VtP.atom {rd : Reader} {σ : Val} (h : VtP rd σ) (n : ℕ) (a : Atom)
    (heq : tbStmtsEqb [.atom a] ((vtPre.drop n).take 1) = true) (hok : okP a = true := by decide) :
    a.Holds rd σ :=
  h n a heq hok

/-- No store goes through `fp_w`. -/
theorem vtSL_no14 : vtSL.all (fun a ↦ match a with
    | .load _ p _ => !decide (p = .n 14)
    | _ => true) = true := by decide +kernel

section
variable {rd : Reader} {w : ℕ → E} {args : List E}

/-- **The honest valuation satisfies `VtP`.** -/
theorem vtP_honest (hl : args.length = 22) {W : List E} (hW16 : 16 ≤ W.length)
    (hW : TbReadsAt rd (vtσ rd w args (.n 14)) W) : VtP rd (vtσ rd w args) := by
  intro n a heq hok
  have hs : Stmt.atom a ∈ vtPre := vt_mem_slice (blk := [_]) heq List.mem_cons_self
  have hg := vt_goodS (rd := rd) (w := w) hl hs
  rw [fixNe_atom] at hg
  cases a with
  | load d p off =>
    simp only [okP, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨rfl, hoff⟩ := hok
    have hS : Atom.load d (.n 14) off ∉ vtSL := by
      intro hm
      have := List.all_eq_true.mp vtSL_no14 _ hm
      simp at this
    simp only [fixA, GoodS, Good] at hg
    have hm := hW off (by omega)
    show LoadHolds rd _ off _
    rw [hg.resolve_left hS, rdAt, hm.2]
    exact hm
  | const => exact hg
  | add => exact hg
  | copy => exact hg
  | mul d x y =>
    simp only [okP, Bool.and_eq_true, decide_eq_true_eq] at hok
    simp only [fixA, GoodS, Good] at hg
    rw [ite_pos' hok] at hg
    exact hg
  | _ => simp [okP] at hok

/-! ## Statements -/

/-- A read of a word the memory holds. -/
theorem vsh_read (hl : args.length = 22) (n : ℕ) {d p : V} {off : ℕ}
    (heq : tbStmtsEqb [.atom (.load d p off)] ((vtPre.drop n).take 1) = true)
    (hS : Atom.load d p off ∉ vtSL) {W : List E} (hW : TbReadsAt rd (vtσ rd w args p) W)
    (hoff : off < W.length) :
    VSH (coreProgram.Rel rd) rd (vtσ rd w args) (.atom (.load d p off)) :=
  (vt_readH hl n heq hS (hW off hoff)).2

/-- The word of a read: the memory's. -/
theorem vt_readW (hl : args.length = 22) (n : ℕ) {d p : V} {off : ℕ}
    (heq : tbStmtsEqb [.atom (.load d p off)] ((vtPre.drop n).take 1) = true)
    (hS : Atom.load d p off ∉ vtSL) {v : E} (hm : LoadHolds rd (vtσ rd w args p) off v) :
    vtσ rd w args d = v :=
  (vt_readH hl n heq hS hm).1

theorem gpow_isSome_of {K : ℕ} (hlow : ∀ i < K, (rd (Parameters.gpow i)).isSome) {e : ℕ}
    (he : e < K) : ∃ v, LoadHolds rd (gen ^ e) 0 v ∧ rdAt rd (gen ^ e) 0 = v := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hlow e he)
  have ha : (gen ^ e).limb 0 * Parameters.gpow 0 = Parameters.gpow e := by
    rw [gen_pow_eq_ofK]; simp [Parameters.gpow]
  refine ⟨v, ⟨tb_gen_pow_isInK e, by rw [ha, hv]⟩, ?_⟩
  rw [rdAt, ha, hv]; rfl

/-- **A range check** `log x < K` on `x = g^e`, `e < K`, the memory defined at `g^i`, `i < K`. -/
theorem vsh_rc (hl : args.length = 22) (n : ℕ) {x y t1 t2 k : V}
    (heq : tbStmtsEqb [.atom (.rangeCheck x y t1 t2 k)] ((vtPre.drop n).take 1) = true)
    (hky : k.idx < y.idx) {K e : ℕ} (hx : vtσ rd w args x = gen ^ e)
    (hk : vtσ rd w args k = gen ^ (K - 1)) (he : e < K)
    (hlow : ∀ i < K, (rd (Parameters.gpow i)).isSome) :
    VSH (coreProgram.Rel rd) rd (vtσ rd w args) (.atom (.rangeCheck x y t1 t2 k)) := by
  have hg := vt_goodS (rd := rd) (w := w) hl (vt_mem_slice (blk := [_]) heq List.mem_cons_self)
  simp only [fixNe, GoodS, Good] at hg
  rw [ite_pos' hky] at hg
  obtain ⟨g1, g2, g3⟩ := hg
  have hy : vtσ rd w args y = gen ^ (K - 1 - e) := by
    rw [g3, hk, hx, ← pow_sub₀ _ gen_ne_zero (by omega : e ≤ K - 1)]
  obtain ⟨v1, l1, r1⟩ := gpow_isSome_of hlow he
  obtain ⟨v2, l2, r2⟩ := gpow_isSome_of hlow (e := K - 1 - e) (by omega)
  show LoadHolds rd _ 0 _ ∧ _ ∧ LoadHolds rd _ 0 _
  refine ⟨?_, ?_, ?_⟩
  · rw [g1, hx, r1]; exact l1
  · rw [hk, hx, hy, ← pow_add, show e + (K - 1 - e) = K - 1 by omega]
  · rw [g2, hy, r2]; exact l2

/-- **An equality check.** -/
theorem vsh_eq {σ : Val} {x y : V} (h : σ x = σ y) :
    VSH (coreProgram.Rel rd) rd σ (.atom (.assertEq x y)) := by
  exact e_add_eq_zero_iff.mpr h

/-- **A dispatch**, its arm `j` named by `g^j`, its returns the oracle's. -/
theorem vsh_dispatch {σ : Val} {x : V} {fs : List String} {args' rets : List V} {j : ℕ}
    (hj : j < fs.length) (hx : σ x = gen ^ j)
    (hr : coreProgram.Rel rd fs[j] (args'.map σ) (rets.map σ)) :
    VSH (coreProgram.Rel rd) rd σ (.dispatch x fs args' rets) :=
  ⟨j, hj, by rw [hx, gen_pow_eq_ofK], hr⟩

/-- The returns of a dispatch: the oracle's. -/
theorem vt_retsW (hl : args.length = 22) (n : ℕ) {x : V} {fs : List String} {args' rets : List V}
    (heq : tbStmtsEqb [.dispatch x fs args' rets] ((vtPre.drop n).take 1) = true) :
    ∀ v ∈ rets, vtσ rd w args v = w v.idx := by
  have hg := vt_goodS (rd := rd) (w := w) hl (vt_mem_slice (blk := [_]) heq List.mem_cons_self)
  exact hg


/-! ## By membership -/

/-- A read of a word the memory holds, the statement in `vtPre`. -/
theorem vt_readM (hl : args.length = 22) {d p : V} {off : ℕ}
    (hs : Stmt.atom (.load d p off) ∈ vtPre) (hS : Atom.load d p off ∉ vtSL) {v : E}
    (hm : LoadHolds rd (vtσ rd w args p) off v) :
    vtσ rd w args d = v ∧ VSH (coreProgram.Rel rd) rd (vtσ rd w args) (.atom (.load d p off)) := by
  have hg := vt_goodS (rd := rd) (w := w) hl hs
  simp only [fixNe, GoodS, Good] at hg
  have e : vtσ rd w args d = v := by rw [hg.resolve_left hS, rdAt, hm.2]; rfl
  refine ⟨e, ?_⟩
  show LoadHolds rd _ _ _
  rw [e]; exact hm

/-- A range check, the statement in `vtPre`. -/
theorem vsh_rcM (hl : args.length = 22) {x y t1 t2 k : V}
    (hs : Stmt.atom (.rangeCheck x y t1 t2 k) ∈ vtPre)
    (hky : k.idx < y.idx) {K e : ℕ} (hx : vtσ rd w args x = gen ^ e)
    (hk : vtσ rd w args k = gen ^ (K - 1)) (he : e < K)
    (hlow : ∀ i < K, (rd (Parameters.gpow i)).isSome) :
    VSH (coreProgram.Rel rd) rd (vtσ rd w args) (.atom (.rangeCheck x y t1 t2 k)) := by
  have hg := vt_goodS (rd := rd) (w := w) hl hs
  simp only [fixNe, GoodS, Good] at hg
  rw [ite_pos' hky] at hg
  obtain ⟨g1, g2, g3⟩ := hg
  have hy : vtσ rd w args y = gen ^ (K - 1 - e) := by
    rw [g3, hk, hx, ← pow_sub₀ _ gen_ne_zero (by omega : e ≤ K - 1)]
  obtain ⟨v1, l1, r1⟩ := gpow_isSome_of hlow he
  obtain ⟨v2, l2, r2⟩ := gpow_isSome_of hlow (e := K - 1 - e) (by omega)
  show LoadHolds rd _ 0 _ ∧ _ ∧ LoadHolds rd _ 0 _
  refine ⟨?_, ?_, ?_⟩
  · rw [g1, hx, r1]; exact l1
  · rw [hk, hx, hy, ← pow_add, show e + (K - 1 - e) = K - 1 by omega]
  · rw [g2, hy, r2]; exact l2

/-- The returns of a dispatch in `vtPre`: the oracle's. -/
theorem vt_retsM (hl : args.length = 22) {x : V} {fs : List String} {args' rets : List V}
    (hs : Stmt.dispatch x fs args' rets ∈ vtPre) : ∀ v ∈ rets, vtσ rd w args v = w v.idx :=
  vt_goodS (rd := rd) (w := w) hl hs

/-- **A block's statements hold** when those evaluation alone does not settle do. -/
theorem vt_blockA (hl : args.length = 22) (n : ℕ) (blk : List Stmt)
    (heq : tbStmtsEqb blk ((vtPre.drop n).take blk.length) = true)
    (h : ∀ s ∈ blk, autoB s = false → VSH (coreProgram.Rel rd) rd (vtσ rd w args) s) :
    ∀ s ∈ blk, VSH (coreProgram.Rel rd) rd (vtσ rd w args) s := by
  intro s hs
  cases ha : autoB s
  · exact h s hs ha
  · exact vsh_auto hl (vt_mem_slice heq hs) ha

end

end
end LeanVM.Guest.B1.Tables
