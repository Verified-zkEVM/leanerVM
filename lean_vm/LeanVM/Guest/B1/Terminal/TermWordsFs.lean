/-
  LeanVM.Guest.B1.Terminal.TermWordsFs

  The terminal's callees' words at the frame sizes `B2C.fs`, from the words certificates (and
  `rs_eq_run`'s by hand), and `check_opening_terminal` complete within `38888` words there.
-/

module

public import LeanVM.Guest.B1.Terminal.TermCompleteB
public import LeanVM.Guest.B1.Eq.RsWords
public import LeanVM.Guest.Memory.GuestWords

/-!
# The terminal's words at `B2C.fs`

The hypotheses of `check_opening_terminal_completeAtB`, `rst_completeAtB` and `rsw_completeAtB` at
`B2C.fs`:

* `eqc_totalLe_fs`: `eq_prefix_chain` within `184` (its certificate);
* `l15_totalLeOn_fs`, `l6_totalLeOn_fs`: `__loop15`, `__loop6` within `38`, `948` words per
  iteration (their certificates);
* `l14_totalLeOn_fs`: `__loop14` from `1` (to its constant end `g^8`) within `8 · 1322`;
* `cs_totalLe_fs`, `cs_fs_le`: each `column_selector__L{κ}`, `κ < 29`, within `157` words, its frame
  at most `157` (its certificate is its frame);
* `rs_totalLeOn_fs`: `rs_eq_run` on `c ≤ 34` coordinates within `317 + 17 · 948 = 16433`
  (`rs_totalLeOn34`).

Then `check_opening_terminal_completeAtB_fs`: within `1795 + 146 + 3·184 + 32·38 + (366 + 322) +
99·157 + (275 + 2240 + 16433) = 38888` words; `rst_completeAtB_fs` within `12 + 18 + 10576 =
10606` (its words certificate's constant); `rsw_completeAtB_fs` within `275 + 64·(count + 1) +
16433` on `count ≤ 34` coordinates.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-! ## The frame sizes -/

/-- `B2C.fs` by core index. -/
theorem fsB_idx {j : ℕ} {f : String} (h : (coreProgram[j]?).map Fn.name = some f) :
    B2C.fs f = wfsJ j := by
  rcases hj : coreProgram[j]? with _ | fn
  · rw [hj] at h; cases h
  · rw [hj] at h
    obtain ⟨hlt, hfn⟩ := List.getElem?_eq_some_iff.mp hj
    simp only [Option.map_some, Option.some.injEq] at h
    rw [← h, ← hfn]
    exact wfs_eq hlt

theorem fs_cot : B2C.fs "check_opening_terminal" = 1795 := by
  rw [fsB_idx (j := 17) (by decide +kernel)]; decide +kernel

theorem fs_l15 : B2C.fs "__loop15" = 19 := by
  rw [fsB_idx (j := 263) (by decide +kernel)]; decide +kernel

theorem fs_st : B2C.fs "selector_tables" = 366 := by
  rw [fsB_idx (j := 16) (by decide +kernel)]; decide +kernel

theorem fs_rsw : B2C.fs "ring_switch_weight" = 275 := by
  rw [fsB_idx (j := 14) (by decide +kernel)]; decide +kernel

theorem fs_rst : B2C.fs "ring_switch_target" = 12 := by
  rw [fsB_idx (j := 13) (by decide +kernel)]; decide +kernel

theorem fs_rs : B2C.fs "rs_eq_run" = 317 := by
  rw [fsB_idx (j := 5) (by decide +kernel)]; decide +kernel

theorem fs_l6 : B2C.fs "__loop6" = 474 := by
  rw [fsB_idx (j := 79) (by decide +kernel)]; decide +kernel

/-! ## The callees' words -/

/-- `eq_prefix_chain` within `184` words. -/
theorem eqc_totalLe_fs : TotalLe coreProgram B2C.fs "eq_prefix_chain" fun _ => 184 :=
  fs_totalLe (by rw [wcertOf_of_idx (j := 4) (by decide +kernel)]; rfl :
    wcertOf "eq_prefix_chain" = .stat [] ⟨184, []⟩ [])

/-- A loop helper ending at its argument `1`, `K` words per iteration by its certificate: within
`K` per unit of its end's exponent from a start below its end. -/
theorem loopTotalLeOn_fs {f : String} {K : ℕ} {ks : List (V × ℕ)}
    (hcf : wcertOf f = .loop none [] ⟨K, []⟩ ks) :
    TotalLeOn coreProgram B2C.fs f LoopPre fun a => logG (a.getD 1 0) * K := by
  intro rd t args rets hn ⟨a, e, ha, he, hae, heo⟩ hv hb
  have := fs_total_le_of_loop hcf hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)
  show _ ≤ logG (args.getD 1 0) * K
  rw [he, logG_spec heo]
  simp only [Aff.eval, List.map_nil, List.sum_nil, add_zero] at this
  exact this.trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _))

/-- `__loop15` within `38` words per iteration. -/
theorem l15_totalLeOn_fs :
    TotalLeOn coreProgram B2C.fs "__loop15" LoopPre fun a => logG (a.getD 1 0) * 38 :=
  loopTotalLeOn_fs (by rw [wcertOf_of_idx (j := 263) (by decide +kernel)]; rfl :
    wcertOf "__loop15" = .loop none [] ⟨38, []⟩ [])

/-- `__loop6` within `948` words per iteration. -/
theorem l6_totalLeOn_fs :
    TotalLeOn coreProgram B2C.fs "__loop6" LoopPre fun a => logG (a.getD 1 0) * 948 :=
  loopTotalLeOn_fs (by rw [wcertOf_of_idx (j := 79) (by decide +kernel)]; rfl :
    wcertOf "__loop6" = .loop none [] ⟨948, []⟩ [])

/-- `__loop14` from `1` (to its constant end `g^8`) within `8 · 1322` words. -/
theorem l14_totalLeOn_fs :
    TotalLeOn coreProgram B2C.fs "__loop14" (fun a => a.getD 0 0 = 1) fun _ => 10576 := by
  intro rd t args rets hn ha hv hb
  have := fs_total_le_of_loop (by rw [wcertOf_of_idx (j := 262) (by decide +kernel)]; rfl :
      wcertOf "__loop14" = .loop (some 8) [] ⟨1322, []⟩ []) hn hv hb (a := 0) (e := 8)
    (by rw [ha]; simp [Parameters.gpow]) rfl (by decide) (by decide)
    (fun _ h => (List.not_mem_nil h).elim)
  simpa [Aff.eval] using this

/-- A constant words certificate within `157`. -/
def csCertOk : Cert → Bool
  | .stat [] ⟨b, []⟩ _ => decide (b ≤ 157)
  | _ => false

theorem csCertOk_spec {c : Cert} (h : csCertOk c = true) :
    ∃ b ks, c = .stat [] ⟨b, []⟩ ks ∧ b ≤ 157 := by
  unfold csCertOk at h
  split at h
  · exact ⟨_, _, rfl, of_decide_eq_true h⟩
  · cases h

/-- The column selectors: core functions `264 + κ`, constant words certificates within `157`, frames
within `157`. -/
theorem cs_ok : (List.range 29).all (fun κ =>
    decide ((coreProgram[264 + κ]?).map Fn.name = some (Tables.lName "column_selector" κ)) &&
      csCertOk (Data.wcertJ (264 + κ)) && decide (wfsJ (264 + κ) ≤ 157)) = true := by
  decide +kernel

theorem cs_facts {κ : ℕ} (hκ : κ < 29) :
    (coreProgram[264 + κ]?).map Fn.name = some (Tables.lName "column_selector" κ) ∧
      csCertOk (Data.wcertJ (264 + κ)) = true ∧ wfsJ (264 + κ) ≤ 157 := by
  have h := List.all_eq_true.mp cs_ok κ (List.mem_range.mpr hκ)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **Each `column_selector__L{κ}` within `157` words.** -/
theorem cs_totalLe_fs : ∀ κ < 29,
    TotalLe coreProgram B2C.fs (Tables.lName "column_selector" κ) fun _ => 157 := by
  intro κ hκ rd t args rets hn hv hb
  obtain ⟨hname, hc, -⟩ := cs_facts hκ
  obtain ⟨b, ks, hcb, hb157⟩ := csCertOk_spec hc
  exact (fs_totalLe ((wcertOf_of_idx hname).trans hcb) rd t args rets hn hv hb).trans hb157

/-- **Each `column_selector__L{κ}`'s frame at most `157` words.** -/
theorem cs_fs_le : ∀ κ < 29, B2C.fs (Tables.lName "column_selector" κ) ≤ 157 := by
  intro κ hκ
  obtain ⟨hname, -, hF⟩ := cs_facts hκ
  rw [fsB_idx hname]
  exact hF

/-- **`rs_eq_run` on at most `34` coordinates within `16433` words** (`rs_totalLeOn34`:
`317 + max 474 (17 · 948)`). -/
theorem rs_totalLeOn_fs : ∀ c ≤ 34,
    TotalLeOn coreProgram B2C.fs "rs_eq_run" (fun a => a.getD 3 0 = gen ^ c) fun _ => 16433 := by
  intro c hc rd t args rets hn hp hv hb
  refine (rs_totalLeOn34 l6_totalLeOn_fs c hc rd t args rets hn hp hv hb).trans ?_
  show B2C.fs "rs_eq_run" + max (B2C.fs "__loop6") (17 * 948) ≤ 16433
  rw [fs_rs, fs_l6]
  decide

/-! ## At `B2C.fs` -/

/-- **`ring_switch_target` is complete, placed, within `10606` words at `B2C.fs`.** -/
theorem rst_completeAtB_fs (cert : String → V → ℕ) (κ : ℕ) {bs bm : ℕ} {s chs : List E}
    (hs : s.length = 64) (hc : chs.length = 6) :
    CompleteAtB B2C.fs cert κ "ring_switch_target" [(bs, s), (bm, chs)]
      [ofK (Parameters.gpow bs), ofK (Parameters.gpow bm)]
      (Returns [polyEval (s.map (phiMap · chs)) gen]) 10606 :=
  (rst_completeAtB κ hs hc l14_totalLeOn_fs).mono le_rfl (by rw [fs_rst])

/-- **`ring_switch_weight` is complete, placed, within `275 + 64 · (count + 1) + 16433` words at
`B2C.fs`**, on at most `34` coordinates. -/
theorem rsw_completeAtB_fs (cert : String → V → ℕ) (κ : ℕ) {bz bp bc count : ℕ}
    {zs ps cs : List E} (hcount : count ≤ 34) (hz : zs.length = count) (hp : ps.length = count)
    (hc : cs.length = 64) :
    CompleteAtB B2C.fs cert κ "ring_switch_weight" [(bz, zs), (bp, ps), (bc, cs)]
      [ofK (Parameters.gpow bz), ofK (Parameters.gpow bp), ofK (Parameters.gpow bc), gen ^ count]
      (Returns [ringWeight zs (ps.map (1 + ·)) cs]) (275 + 64 * (count + 1) + 16433) :=
  (rsw_completeAtB κ (by omega) hz hp hc (rs_totalLeOn_fs count hcount)).mono le_rfl
    (by rw [fs_rsw])

set_option maxHeartbeats 400000 in
/-- **`check_opening_terminal` is complete, placed, within `38888` words at `B2C.fs`**
(`check_opening_terminal_completeAtB` with the callees' words of the certificates and
`rs_totalLeOn_fs`). -/
theorem check_opening_terminal_completeAtB_fs (cert : String → V → ℕ) (κ : ℕ) (hκ : 6 ≤ κ)
    (B : TermBases) (Lin : Main.Layout)
    {layout : Verifier.Layout} {bus : BusResult} {claims : List ColumnClaim} {out : ColumnClaim}
    {lam : E} {ringPoint coeffs x : List E} {rm gmu gzcn glm gtau lamOut inner yr target : E}
    {nc : ℕ} (hnc : nc ≤ 40) (hgz : gzcn = gen ^ nc)
    (hpre : ∀ rd, LowDef κ rd → MemL rd Lin → TermPre rd layout bus claims out lam ringPoint coeffs x
      (termArgs B rm gmu gzcn glm gtau lamOut inner yr target))
    (hreg : ∀ i, TermRegion B bus.point.length nc (layout.tableLogHeights.getD opKeccak 0) i →
      RegionL Lin i)
    (hbus : bus.point.length ≤ 34)
    (hlen : ∀ c ∈ claims, c.point.length =
      (columnKappas layout.logMemory layout.logBytecode layout.tableLogHeights).getD c.column 0)
    (hfin : (inner + stackWeight layout (openedClaims claims [out]) ringPoint coeffs lam x) * yr =
      target) :
    CompleteAtB B2C.fs cert κ "check_opening_terminal" Lin
      (termArgs B rm gmu gzcn glm gtau lamOut inner yr target) (Returns []) 38888 :=
  (check_opening_terminal_completeAtB κ hκ B Lin hnc hgz hpre hreg hbus hlen hfin eqc_totalLe_fs
    l15_totalLeOn_fs cs_totalLe_fs cs_fs_le rs_totalLeOn_fs).mono le_rfl
    (by rw [fs_cot, fs_l15, fs_st, fs_rsw]; decide)

end
end LeanVM.Guest.B1.VerifySub
