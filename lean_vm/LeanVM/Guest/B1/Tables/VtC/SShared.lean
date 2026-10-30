/-
  LeanVM.Guest.B1.Tables.VtC.SShared

  `idxc_tab`, `zeta1` and the six tables' shared selector tables hold on the honest valuation.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.SBase
public import LeanVM.Guest.B1.Selectors.SharedTablesComplete

/-!
# The index factors, `1 + ζ` and the shared tables (G:2017-2035)

`vtIdxcW`: `idxc_tab`'s words `1 + g^(2^t)`; `idxc_ok`: its stores hold on a memory holding them.
`zeta1_ok`: `plus_one_run` on `g^μ` holds when `zeta1` holds `1 + ζ_k`. `sh_ok`, `sh0_ok`: table
`t`'s run of `μ - τ` coordinates, its tables at `shared_eq·g^(288t)`, `shared_g·g^(144t)` holding
their nibble tables (`RunTables`), holds, and `shared_len[t] = g^(μ - τ)`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- `idxc_tab`'s words. -/
def vtIdxcW : List E := (List.range 34).map fun t ↦ 1 + gen ^ 2 ^ t

theorem vtIdxc_word {t : ℕ} (ht : t < 34) :
    word (tbGSquaresBits.getD t 0 ^^^ 1) 0 0 = 1 + gen ^ 2 ^ t := by
  rw [tb_word_eOfNat, eOfNat_xor, eOfNat_one, gen_pow_two_pow_eq ht, add_comm]

theorem vtIdxcT_length : vtIdxcT.length = 68 := by decide +kernel

variable {rd : Reader} {w : ℕ → E} {args : List E}

/-- **`idxc_tab`'s stores.** -/
theorem idxc_ok (hl : args.length = 22) (h : TbReadsAt rd (vtσ rd w args (.n 2732)) vtIdxcW) :
    ∀ st ∈ vtIdxcT, VSH (coreProgram.Rel rd) rd (vtσ rd w args) st := by
  intro st hst
  have hst' := hst
  simp only [vtIdxcT, List.mem_flatten, List.mem_map, List.mem_range] at hst'
  obtain ⟨_, ⟨t, ht, rfl⟩, hm⟩ := hst'
  have hc : vtσ rd w args (.n (2733 + t)) = 1 + gen ^ 2 ^ t := by
    have := vt_goodS (rd := rd) (w := w) hl (vt_mem_slice vtIdxc_check
      (show Stmt.atom (.const (.n (2733 + t)) (word (tbGSquaresBits.getD t 0 ^^^ 1) 0 0)) ∈
        vtIdxcT by
          simp only [vtIdxcT, List.mem_flatten, List.mem_map, List.mem_range]
          exact ⟨_, ⟨t, ht, rfl⟩, List.mem_cons_self⟩))
    simp only [fixNe, GoodS, Good] at this
    rw [this, vtIdxc_word ht]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · show _ = _
    rw [hc, vtIdxc_word ht]
  · show LoadHolds rd _ _ _
    rw [hc]
    have := h t (by simp [vtIdxcW]; exact ht)
    simpa [vtIdxcW] using this

/-- **`zeta1`'s `plus_one_run`.** -/
theorem zeta1_ok (hl : args.length = 22) {point : List E}
    (h9 : vtσ rd w args (.n 9) = gen ^ point.length) (hμ : point.length ≤ 33)
    (hz : TbReadsAt rd (vtσ rd w args (.n 8)) point)
    (hz1 : TbReadsAt rd (vtσ rd w args (.n 2767)) (point.map (1 + ·))) (hw : w 2768 = 0) :
    VSH (coreProgram.Rel rd) rd (vtσ rd w args)
      (.dispatch (.n 9) plusOneRunNames [.n 2767, .n 8] [.n 2768]) := by
  have hg := vt_goodS (rd := rd) (w := w) hl (vt_mem_slice (blk := [_]) vtZeta1_check
    List.mem_cons_self)
  simp only [fixNe, GoodS, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hg
  rw [vsh_dispatch]
  have hj : point.length < plusOneRunNames.length := by simp [plusOneRunNames]; omega
  refine ⟨point.length, hj, by rw [h9, gen_pow_eq_ofK], ?_⟩
  rw [← List.getD_eq_getElem _ ""]
  refine (plus_one_run_holds _ hμ rd _ _).mpr ?_
  simp only [List.map_cons, List.map_nil, MeaningPlusOneRun]
  exact ⟨⟨point, rfl, hz, hz1⟩, by rw [hg]; simp [hw]⟩

theorem sh_call {t μ τ : ℕ} {point : List E} (hμ : point.length = μ) (hμ33 : μ < 33)
    (hτμ : τ ≤ μ) {eqt gt z z1 gsq : E}
    (hzv : TbReadsAt rd z (point.drop τ)) (hz1v : TbReadsAt rd z1 ((point.map (1 + ·)).drop τ))
    (hsqv : TbReadsAt rd gsq ((gSquaresList.drop τ).take (μ - τ)))
    (hrun : RunTables rd eqt gt (μ - τ) (point.drop τ) ((point.map (1 + ·)).drop τ)
      ((gSquaresList.drop τ).take (μ - τ))) :
    coreProgram.Rel rd "shared_selector_tables" [eqt, gt, z, z1, gsq, gen ^ (μ - τ)] [] := by
  have _ := t
  have hsql : gSquaresList.length = 34 := by simp [gSquaresList]
  exact shared_selector_tables_complete_holds rd eqt gt z z1 gsq (μ - τ) _ _ _ (by omega)
    (by simp; omega) (by simp; omega) (by simp [hsql]; omega) hzv hz1v hsqv hrun

set_option maxHeartbeats 1000000 in
/-- **Table `t ≥ 1`'s shared tables.** -/
theorem sh_ok (hlow : LowDefB 8 rd) {v t μ τ : ℕ} {point : List E}
    (hv : 2781 ≤ v) (ht : t < 6)
    (hg : GoodL rd w (vtσ rd w args) (vtShT v t))
    (hS : Atom.load (.n v) (.n 10) (t + 1) ∉ vtSL)
    (hdim : LoadHolds rd (vtσ rd w args (.n 10)) (t + 1) (gen ^ τ))
    (h9 : vtσ rd w args (.n 9) = gen ^ μ) (hμ : point.length = μ) (hμ33 : μ < 33) (hτμ : τ ≤ μ)
    (hz : TbReadsAt rd (vtσ rd w args (.n 8)) point)
    (hz1 : TbReadsAt rd (vtσ rd w args (.n 2767)) (point.map (1 + ·)))
    (hsq : TbReadsAt rd (vtσ rd w args (.n 13)) gSquaresList)
    (hrun : RunTables rd (vtσ rd w args (.n 2769) * gen ^ (288 * t))
      (vtσ rd w args (.n 2770) * gen ^ (144 * t)) (μ - τ) (point.drop τ)
      ((point.map (1 + ·)).drop τ) ((gSquaresList.drop τ).take (μ - τ))) :
    (∀ st ∈ vtShT v t, VSH (coreProgram.Rel rd) rd (vtσ rd w args) st) ∧
      vtσ rd w args (.n (v + 2)) = gen ^ (μ - τ) := by
  set σ := vtσ rd w args with hσ
  simp only [vtShT, GoodL, GoodS, fixNe, Good, and_true, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true] at hg
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩ := hg
  simp only [show ¬ (v + 1 < 9 ∧ v < 9) from fun h => by omega,
    show (2769 : ℕ) < v + 8 ∧ v + 7 < v + 8 from ⟨by omega, by omega⟩,
    show (2770 : ℕ) < v + 10 ∧ v + 9 < v + 10 from ⟨by omega, by omega⟩,
    show (8 : ℕ) < v + 11 ∧ v < v + 11 from ⟨by omega, by omega⟩,
    show (2767 : ℕ) < v + 12 ∧ v < v + 12 from ⟨by omega, by omega⟩,
    show (13 : ℕ) < v + 13 ∧ v < v + 13 from ⟨by omega, by omega⟩,
    show v + 3 < v + 4 by omega, ↓reduceIte] at g1 g4 g6 g8 g9 g10 g11
  obtain ⟨ev, l0⟩ := read_of (g0.resolve_left hS) hdim
  have e1 : σ (.n (v + 1)) = gen ^ (μ - τ) := by rw [g1, h9, ev, gen_pow_div hτμ]
  have e2 : σ (.n (v + 2)) = gen ^ (μ - τ) := by rw [g2, e1]
  obtain ⟨r1, r2, r3⟩ := g4
  obtain ⟨hrc, -⟩ := rc_holds (κ := 8) hlow r1 r2 r3 e2 (by rw [g3, vtW33_gen]) (by omega)
    (by norm_num)
  refine ⟨?_, e2⟩
  simp only [vtShT, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true, vsh_atom, vsh_call]
  refine ⟨l0, mulDiv_holds g1 (by rw [ev]; exact gen_pow_ne_zero _), g2, g3, hrc, g5, g6, g7, g8,
    g9, g10, g11, ?_⟩
  simp only [List.map_cons, List.map_nil]
  rw [g6, g5, vtShC1_word ht, g8, g7, vtShC2_word ht, g9, g10, g11, ev, e2]
  exact sh_call (t := t) hμ hμ33 hτμ (tbReadsAt_drop hz τ) (by
      have := tbReadsAt_drop hz1 τ; exact this)
    (tbReadsAt_take (tbReadsAt_drop hsq τ) _) hrun

set_option maxHeartbeats 1000000 in
/-- **Table `0`'s shared tables.** -/
theorem sh0_ok (hlow : LowDefB 8 rd) {μ τ : ℕ} {point : List E}
    (hg : GoodL rd w (vtσ rd w args) vtSh0T)
    (hS : Atom.load (.n 2771) (.n 10) 1 ∉ vtSL)
    (hdim : LoadHolds rd (vtσ rd w args (.n 10)) 1 (gen ^ τ))
    (h9 : vtσ rd w args (.n 9) = gen ^ μ) (hμ : point.length = μ) (hμ33 : μ < 33) (hτμ : τ ≤ μ)
    (hz : TbReadsAt rd (vtσ rd w args (.n 8)) point)
    (hz1 : TbReadsAt rd (vtσ rd w args (.n 2767)) (point.map (1 + ·)))
    (hsq : TbReadsAt rd (vtσ rd w args (.n 13)) gSquaresList)
    (hrun : RunTables rd (vtσ rd w args (.n 2769)) (vtσ rd w args (.n 2770)) (μ - τ)
      (point.drop τ) ((point.map (1 + ·)).drop τ) ((gSquaresList.drop τ).take (μ - τ))) :
    (∀ st ∈ vtSh0T, VSH (coreProgram.Rel rd) rd (vtσ rd w args) st) ∧
      vtσ rd w args (.n 2773) = gen ^ (μ - τ) := by
  set σ := vtσ rd w args with hσ
  simp only [vtSh0T, GoodL, GoodS, fixNe, Good, and_true, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true] at hg
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := hg
  simp only [show ¬ (2772 < 9 ∧ 2771 < 9) from fun h => by omega,
    show (8 : ℕ) < 2778 ∧ 2771 < 2778 from ⟨by omega, by omega⟩,
    show (2767 : ℕ) < 2779 ∧ 2771 < 2779 from ⟨by omega, by omega⟩,
    show (13 : ℕ) < 2780 ∧ 2771 < 2780 from ⟨by omega, by omega⟩,
    show 2774 < 2775 by omega, ↓reduceIte] at g1 g4 g5 g6 g7
  obtain ⟨ev, l0⟩ := read_of (g0.resolve_left hS) hdim
  have e1 : σ (.n 2772) = gen ^ (μ - τ) := by rw [g1, h9, ev, gen_pow_div hτμ]
  have e2 : σ (.n 2773) = gen ^ (μ - τ) := by rw [g2, e1]
  obtain ⟨r1, r2, r3⟩ := g4
  obtain ⟨hrc, -⟩ := rc_holds (κ := 8) hlow r1 r2 r3 e2 (by rw [g3, vtW33_gen]) (by omega)
    (by norm_num)
  refine ⟨?_, e2⟩
  simp only [vtSh0T, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true, vsh_atom, vsh_call]
  refine ⟨l0, mulDiv_holds g1 (by rw [ev]; exact gen_pow_ne_zero _), g2, g3, hrc, g5, g6, g7, ?_⟩
  simp only [List.map_cons, List.map_nil]
  rw [g5, g6, g7, ev, e2]
  exact sh_call (t := 0) hμ hμ33 hτμ (tbReadsAt_drop hz τ) (tbReadsAt_drop hz1 τ)
    (tbReadsAt_take (tbReadsAt_drop hsq τ) _) hrun

end
end LeanVM.Guest.B1.Tables
