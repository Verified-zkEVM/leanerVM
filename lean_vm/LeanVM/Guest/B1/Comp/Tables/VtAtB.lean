/-
  LeanVM.Guest.B1.Comp.Tables.VtAtB

  `verify_tables`' body holding up to a statement under any semantics of `BLAKE2S`, and the
  values the completeness proof reads off it.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesCSem
public import LeanVM.Guest.B1.Tables.VerifyTablesFreeB

/-!
# The body up to `M`, under any semantics

`VerifyTablesCAt.lean` and `VerifyTablesCSem.lean` under `S : BlakeSem`: `VtHoldsAtB S M`, the
first `M` statements holding under `S` at `coreProgram.RelB S`; its atoms other than `BLAKE2S`
hold as deployed (`VtHoldsAtB.atom`), its runs free of `BLAKE2S` over `vtFree` too
(`VtHoldsAtB.slice`), and its windows evaluate by reflection (`window_eval_atB`). The values the
completeness proof needs are read as deployed: `vt_vals_atB`, `vt_eqhi_atB`, `vt_air_atB`,
`vt_totals_cB`, `vt_final_cB`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The first `M` statements of `verify_tables` hold under `S` (`VtHoldsAt`). -/
def VtHoldsAtB (S : BlakeSem) (M : ℕ) (rd : Reader) (σ : Val) : Prop :=
  ∃ kret : List E → Prop, Stmt.HoldsListB S (coreProgram.RelB S rd) rd σ (vtPre.take M) True kret

section
variable {S : BlakeSem} {rd : Reader} {σ : Val} {M : ℕ}

theorem VtHoldsAtB.atom (h : VtHoldsAtB S M rd σ) (n : ℕ) (a : Atom)
    (heq : stmtsEqb [.atom a] (((vtPre.take M).drop n).take 1) = true)
    (hnb : Stmt.noBlakeList [.atom a] = true := by rfl) : a.Holds rd σ := by
  obtain ⟨k, h⟩ := h
  exact holdsB_atom (vtPre_take_noRet M) h n a (by rw [heq, hnb]; rfl)

theorem VtHoldsAtB.slice (h : VtHoldsAtB S M rd σ) (n : ℕ) (blk : List Stmt)
    (heq : stmtsEqb blk (((vtPre.take M).drop n).take blk.length) = true)
    (hf : Stmt.freeInList vtFree blk = true) :
    ∃ kret : List E → Prop, Stmt.HoldsList (coreProgram.Rel rd) rd σ blk True kret := by
  obtain ⟨k, h⟩ := h
  exact ⟨k, (holdsListB_vtFree hf).mp (holdsB_slice (vtPre_take_noRet M) h n blk heq)⟩

/-- **A value of a window of the body up to `M` under `S`, by reflection** (`window_eval_at`). -/
theorem window_eval_atB (h : VtHoldsAtB S M rd σ) {χ : ℕ → E} {L : LoadTab} (hL : L.Sound rd σ χ)
    (n len k : ℕ) (e : Ex) (hb : n + len ≤ M)
    (heq : ((symExec L [] (((vtPre.drop n).take len).filterMap atomOf)).get k).norm = e.norm) :
    σ (.n k) = e.eval (fun k => σ (.n k)) χ := by
  obtain ⟨kr, hh⟩ := h
  refine window_evalB (vtPre_take_noRet M) hh hL n len k e ?_
  rw [take_drop_take _ hb]; exact heq

/-! ## The soundness side's values, on a prefix -/

/-- `vt_vals` on the first `7854` statements. -/
theorem vt_vals_atB (h : VtHoldsAtB S 7854 rd σ) {w : List E} (hw : 16 ≤ w.length)
    (hfw : ReadsAt rd (σ (.n 11)) w) (h1 : LoadHolds rd (σ (.n 1852)) 1 (σ (.n 1931)))
    (h2 : LoadHolds rd (σ (.n 1852)) 2 (σ (.n 2035)))
    (hm : ReadsAt rd (σ (.n 13)) [σ (.n 1937), σ (.n 1955), σ (.n 1973)]) :
    σ (.n 3326) = pushTotalEx.eval (fun k => σ (.n k)) (fun i => w.getD i 0) ∧
      σ (.n 3705) = pullTotalEx.eval (fun k => σ (.n k)) (fun i => w.getD i 0) ∧
      σ (.n 4553) = countTotalEx.eval (fun k => σ (.n k)) (fun i => w.getD i 0) ∧
      (∀ t : Fin 6, σ (.n (vtCeVars.getD t 0)) =
        (ceEx t).eval (fun k => σ (.n k)) (fun i => w.getD i 0)) ∧
      σ (.n 4631) = σ (.n 4624) * σ (.n 3326) + σ (.n 4625) * σ (.n 3705) +
        σ (.n 4626) * σ (.n 4553) := by
  have hL := vt_fpw_sound hw hfw
  have hE : LoadTab.Sound rd σ (fun i => w.getD i 0) [] := fun _ hq => absurd hq (by simp)
  refine ⟨window_eval_atB h hL 1505 1587 3326 pushTotalEx (by norm_num) vt_push_total,
    window_eval_atB h (vt_pullTab_sound hw hfw h1 h2 hm) 1505 1892 3705 pullTotalEx (by norm_num)
      vt_pull_total,
    window_eval_atB h hE 3397 876 4553 countTotalEx (by norm_num) vt_count_total, fun t => ?_, ?_⟩
  · fin_cases t
    · exact window_eval_atB h hL 4374 481 5140 (ceEx 0) (by norm_num) vt_ce0
    · exact window_eval_atB h hL 4862 521 5668 (ceEx 1) (by norm_num) vt_ce1
    · exact window_eval_atB h hL 5391 269 5945 (ceEx 2) (by norm_num) vt_ce2
    · exact window_eval_atB h hL 5668 515 6468 (ceEx 3) (by norm_num) vt_ce3
    · exact window_eval_atB h hL 6191 494 6970 (ceEx 4) (by norm_num) vt_ce4
    · exact window_eval_atB h hL 6693 1153 8131 (ceEx 5) (by norm_num) vt_ce5
  · have a0 := h.atom 4333 (.mul (.n 4627) (.n 4624) (.n 3326)) (by decide +kernel)
    have a1 := h.atom 4334 (.mul (.n 4628) (.n 4625) (.n 3705)) (by decide +kernel)
    have a2 := h.atom 4335 (.add (.n 4629) (.n 4627) (.n 4628)) (by decide +kernel)
    have a3 := h.atom 4336 (.mul (.n 4630) (.n 4626) (.n 4553)) (by decide +kernel)
    have a4 := h.atom 4337 (.add (.n 4631) (.n 4629) (.n 4630)) (by decide +kernel)
    simp only [Atom.Holds] at a0 a1 a2 a3 a4
    rw [a4, a2, a0, a1, a3]

/-- `vt_resolve` on the first `M` statements, `M ≥ 4273`. -/
theorem vt_resolve_atB (h : VtHoldsAtB S M rd σ) (hM : 4273 ≤ M) :
    ∀ fuel v, σ (.n v) = σ (.n (vtResolve fuel v))
  | 0, v => rfl
  | fuel + 1, v => by
    unfold vtResolve
    split
    · next c hc =>
      have hm := List.mem_of_find?_eq_some hc
      have hv : c.2.1 = v := by simpa using List.find?_some hc
      have hok := List.all_eq_true.mp vt_copies_ok c hm
      have hc1 : c.1 + 1 ≤ 4273 := by
        have : ∀ c ∈ vtCopies, c.1 + 1 ≤ 4273 := by decide
        exact this c hm
      have := h.atom c.1 (.copy (.n c.2.1) (.n c.2.2)) (by rw [take_drop_take _ (by omega)]; exact hok)
      simp only [Atom.Holds] at this
      rw [← hv, this]
      exact vt_resolve_atB h hM fuel c.2.2
    · rfl

theorem vt_eqhi_atB (h : VtHoldsAtB S M rd σ) (hM : 4273 ≤ M) {t s k : ℕ} (ht : t < 6) (hs : s < 3)
    (hk : k < ((vtEqhiVars.getD t []).getD s []).length) :
    σ (.n (((vtEqhiVars.getD t []).getD s []).getD k 0)) =
      σ (.n (selVal.getD (eqhiSel t s k) 0 + 23)) := by
  rw [vt_resolve_atB h hM 2, vt_eqhi_ok t ht s hs k hk]

/-- `vt_air` on the first `7854` statements. -/
theorem vt_air_atB (h : VtHoldsAtB S 7854 rd σ) {n : ℕ} (τ : ℕ → ℕ)
    (hτ : ∀ t < 6, τ t ≤ n) (hgn : σ (.n 4554) = gen ^ n)
    (htau : ∀ t < 6, σ (.n (airTau.getD t 0)) = gen ^ τ t) {cp pq : ℕ → E}
    (hcp : ∀ j ≤ n, LoadHolds rd (σ (.n 4639)) j (cp j))
    (hpq : ∀ k ≤ n, LoadHolds rd (σ (.n 4655)) k (pq k)) :
    ∀ t < 6, σ (.n (airAcc t)) = ((List.range (t + 1)).map fun s =>
      cp (n - τ s) * pq (τ s) * σ (.n (airCe.getD s 0))).sum := by
  have hbl : ∀ t < 6, airStmt.getD t 0 + 8 ≤ 7854 := by decide
  have hterm : ∀ t < 6, σ (.n (airQ.getD t 0 + 6)) =
      cp (n - τ t) * pq (τ t) * σ (.n (airCe.getD t 0)) := by
    intro t ht
    obtain ⟨hb, -, -⟩ := air_blocks t ht
    obtain ⟨k, hb⟩ := h.slice (airStmt.getD t 0) (airT (airQ.getD t 0) (airTau.getD t 0) (airCe.getD t 0))
      (by rw [show (airT (airQ.getD t 0) (airTau.getD t 0) (airCe.getD t 0)).length = 7 from rfl,
            take_drop_take _ (show airStmt.getD t 0 + 7 ≤ 7854 by have := hbl t ht; omega)]; exact hb)
      (air_free t ht)
    simp only [airT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hb
    obtain ⟨m0, m1, l2, m3, l4, m5, m6⟩ := hb
    rw [hgn, htau t ht] at m0
    have hq := gen_pow_cancel (hτ t ht) m0
    rw [m1, hq, loadHolds_gen_pow_mul, Nat.add_zero] at l2
    rw [m3, htau t ht, loadHolds_gen_pow_mul, Nat.add_zero] at l4
    rw [m6, m5, loadHolds_unique l2 (hcp _ (by omega)), loadHolds_unique l4 (hpq _ (hτ t ht))]
  intro t ht
  induction t with
  | zero => simpa [airAcc, airQ] using hterm 0 (by omega)
  | succ t ih =>
    obtain ⟨-, hadd, -⟩ := air_blocks (t + 1) ht
    have ha := h.atom _ _ (by rw [take_drop_take _ (by have := hbl (t + 1) ht; omega)]; exact hadd (by omega))
    simp only [Atom.Holds, Nat.add_sub_cancel] at ha
    rw [ha, ih (by omega), hterm (t + 1) ht, List.range_succ (n := t + 1), List.map_append,
      List.sum_append]
    simp

end

section
variable {S : BlakeSem} {rd : Reader} {σ : Val}

/-- **The bus totals under `S`** (`vt_totals_c`) are the three values the guest computes by statement `4273`. -/
theorem vt_totals_cB (hP4 : PushTotalEval) (hP5 : PullTotalEval) (hP6 : CountTotalEval)
    {bytecode : List K} (hb : bytecode.length = 2 ^ 22) {logMem : ℕ} {rows : List ℕ}
    (hr : rows.length = 6) {alphas point : List E} (hal : alphas.length = 4)
    (h : VtHoldsAtB S 4273 rd σ) (hfw : ReadsAt rd (σ (.n 11)) (eqKernel alphas))
    (h1 : LoadHolds rd (σ (.n 1852)) 1 (σ (.n 1931))) (h2 : LoadHolds rd (σ (.n 1852)) 2 (σ (.n 2035)))
    (hm : ReadsAt rd (σ (.n 13)) [σ (.n 1937), σ (.n 1955), σ (.n 1973)])
    (hsel : ∀ i < 37, σ (.n (selVal.getD i 0 + 23)) =
      (((busLayout [0, logMem, 18] (layoutOf bytecode logMem rows).push).framework ++
        (busLayout [0, logMem, 18] (layoutOf bytecode logMem rows).push).tables).getD i
          default).eqAbove point)
    (hselc : ∀ j < 28, σ (.n (selVal.getD (37 + j) 0 + 23)) =
      ((busLayout [] (layoutOf bytecode logMem rows).count).tables.getD j default).eqAbove point)
    (hpw : ∀ t < 6, σ (.n (1739 + 14 * t)) =
      paddingWeight (point.take (log2Ceil (rows.getD t 0))) (rows.getD t 0))
    (hidx1 : σ (.n 1931) = indexMle (point.take logMem)) (hidx2 : σ (.n 2035) = indexMle (point.take 18)) :
    (busVal (layoutOf bytecode logMem rows) alphas (σ (.n 12)) point [σ (.n 21), σ (.n 22), σ (.n 23)]
      [σ (.n 1937), σ (.n 1955), σ (.n 1973)] (σ (.n 3359)) (σ (.n 3409)) (σ (.n 1732))).totals =
      [σ (.n 3326), σ (.n 3705), σ (.n 4553)] := by
  have hw : 16 ≤ (eqKernel alphas).length := by rw [length_eqKernel, hal]; decide
  have hL := vt_fpw_sound hw hfw
  have hE : LoadTab.Sound rd σ (fun i => (eqKernel alphas).getD i 0) [] := fun _ hq => absurd hq (by simp)
  rw [vt_bus_totals (ρ := fun k => σ (.n k)) (χ := fun i => (eqKernel alphas).getD i 0) hP4 hP5 hP6 hb
    hr hal (fun _ _ => rfl) hsel hselc hpw hidx1 hidx2,
    window_eval_atB h hL 1505 1587 3326 pushTotalEx (by norm_num) vt_push_total,
    window_eval_atB h (vt_pullTab_sound hw hfw h1 h2 hm) 1505 1892 3705 pullTotalEx (by norm_num)
      vt_pull_total,
    window_eval_atB h hE 3397 876 4553 countTotalEx (by norm_num) vt_count_total]

/-- **The accumulated terms are the table sumcheck's terms' sum under `S`** (`vt_final_c`) on the guest's evaluations: with
`n` the tables' largest log-height, the challenges `rs` (in round order) whose running products
and equality prefix the two buffers at `4639` and `4655` hold, and `ξ`'s powers at
`4622 ..< 4627`. -/
theorem vt_final_cB (hP2 : CeExEval) {bytecode : List K} (hb : bytecode.length = 2 ^ 22) {logMem : ℕ}
    {rows : List ℕ} (hr : rows.length = 6) {alphas point : List E} (hal : alphas.length = 4)
    (h : VtHoldsAtB S 7854 rd σ) (hfw : ReadsAt rd (σ (.n 11)) (eqKernel alphas))
    (h1 : LoadHolds rd (σ (.n 1852)) 1 (σ (.n 1931))) (h2 : LoadHolds rd (σ (.n 1852)) 2 (σ (.n 2035)))
    (hm : ReadsAt rd (σ (.n 13)) [σ (.n 1937), σ (.n 1955), σ (.n 1973)])
    (hsel : ∀ i < 37, σ (.n (selVal.getD i 0 + 23)) =
      (((busLayout [0, logMem, 18] (layoutOf bytecode logMem rows).push).framework ++
        (busLayout [0, logMem, 18] (layoutOf bytecode logMem rows).push).tables).getD i
          default).eqAbove point)
    (hselc : ∀ j < 28, σ (.n (selVal.getD (37 + j) 0 + 23)) =
      ((busLayout [] (layoutOf bytecode logMem rows).count).tables.getD j default).eqAbove point)
    {rs : List E} (hrsl : rs.length = vtN (layoutOf bytecode logMem rows))
    (hnp : vtN (layoutOf bytecode logMem rows) ≤ point.length)
    (hgn : σ (.n 4554) = gen ^ vtN (layoutOf bytecode logMem rows))
    (htau : ∀ t < 6, σ (.n (airTau.getD t 0)) = gen ^ log2Ceil (rows.getD t 0))
    (hcp : ∀ j ≤ vtN (layoutOf bytecode logMem rows), LoadHolds rd (σ (.n 4639)) j (prodE (rs.take j)))
    (hpq : ∀ k ≤ vtN (layoutOf bytecode logMem rows),
      LoadHolds rd (σ (.n 4655)) k (eqEval (point.take k) (rs.reverse.take k)))
    {xi : E} (hxi : ∀ k < 5, σ (.n (4622 + k)) = xi ^ k)
    (tv memory : List E) (mF bF bv : E) :
    σ (.n 8139) = (ttVal ((powers xi (vtNC + 3)).take vtNC) ((powers xi (vtNC + 3)).drop vtNC) rs.reverse
      (vtRows (layoutOf bytecode logMem rows)
        (busVal (layoutOf bytecode logMem rows) alphas (σ (.n 12)) point tv memory mF bF bv) rs.reverse)
      (vtEvalVars.map (·.map fun k => σ (.n k))) 0 0 []).1 := by
  set L := layoutOf bytecode logMem rows with hLd
  set n := vtN L with hn
  set τ : ℕ → ℕ := fun t => log2Ceil (rows.getD t 0) with hτd
  set bus := busVal L alphas (σ (.n 12)) point tv memory mF bF bv with hbus
  have hheights : L.tableLogHeights = (List.range 6).map τ := by
    show rows.map log2Ceil = _
    apply List.ext_getElem (by simp [hr])
    intro t h1 h2
    simp only [List.getElem_map, List.getElem_range, hτd]
    rw [List.getD_eq_getElem _ _ (by simpa [hr] using h1)]
  have hτn : ∀ t < 6, τ t ≤ n := fun t ht => by
    rw [hn, vtN, hheights]
    exact vt_le_foldl_max _ 0 _ (Or.inl (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩))
  have hχ : ∀ i < 16, (eqKernel alphas).getD i 0 = (fun i => (eqKernel alphas).getD i 0) i :=
    fun _ _ => rfl
  have heqhi : ∀ t < 6, ∀ s < 3, ∀ k < ((vtEqhiVars.getD t []).getD s []).length,
      (fun k => σ (.n k)) (((vtEqhiVars.getD t []).getD s []).getD k 0) =
        (fun k => σ (.n k)) (selVal.getD (eqhiSel t s k) 0 + 23) :=
    fun t ht s hs k hk => vt_eqhi_atB h (by norm_num) ht hs hk
  have hforms := fun t (ht : t < 6) ev => vt_bus_forms (ρ := fun k => σ (.n k))
    (χ := fun i => (eqKernel alphas).getD i 0) (point := point) hb hr hal hχ hsel hselc heqhi
    tv memory mF bF bv ht ev
  have hws6 := tableWeights_eq L.tableLogHeights bus.point rs
    (fun h hh => by
      rw [hheights] at hh; obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hh
      rw [hrsl]; exact hτn t (List.mem_range.mp ht))
    (fun h hh => by
      rw [hheights] at hh; obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hh
      exact le_trans (hτn t (List.mem_range.mp ht)) hnp)
  have hfsh := (hforms 0 (by omega) (fun _ => 0)).2.2.2
  have hbfl : bus.forms.length = 6 := hfsh.1
  have hair := vt_air_atB h τ hτn hgn htau hcp hpq 5 (by omega)
  have hxi' : ∀ k < 5, (fun k => σ (.n k)) (vtXiVars.getD k 0) = xi ^ k := fun k hk => by
    interval_cases k
    · exact hxi 0 (by omega)
    · exact hxi 1 (by omega)
    · exact hxi 2 (by omega)
    · exact hxi 3 (by omega)
    · exact hxi 4 (by omega)
  have hw16 : 16 ≤ (eqKernel alphas).length := by rw [length_eqKernel, hal]; decide
  have vCe := (vt_vals_atB h hw16 hfw h1 h2 hm).2.2.2.1
  have hfin := vt_final hP2 hxi' vCe rs.reverse L.tableLogHeights (by rw [hheights]; simp)
    bus.forms hbfl hfsh.2 (fun t => ⟨(hforms t t.2 (vtCol (fun k => σ (.n k)) t)).1,
      (hforms t t.2 (vtCol (fun k => σ (.n k)) t)).2.1,
      (hforms t t.2 (vtCol (fun k => σ (.n k)) t)).2.2.1⟩)
    (tableWeights L.tableLogHeights bus.point rs.reverse) (by rw [hws6, hheights]; simp)
  rw [show vtNC = 2 from rfl, powers_five]
  refine Eq.trans ?_ hfin.symm
  rw [show (8139 : ℕ) = airAcc 5 from rfl, hair, hws6, hheights]
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  have ht' := List.mem_range.mp ht
  simp only [List.map_map, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht',
    Option.map_some, Option.getD_some, Function.comp_apply, hrsl]
  rfl

end

end
end LeanVM.Guest.B1.VerifySub
