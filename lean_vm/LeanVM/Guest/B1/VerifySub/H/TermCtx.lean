/-
  LeanVM.Guest.B1.VerifySub.H.TermCtx

  What `check_opening_terminal` takes of an honest child's claims: `verify_tables`' context
  (`TCtx`) on the honest memory, and the WHIR terminal point's length.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.KidsC
public import LeanVM.Guest.B1.Whir.BrBody
public import LeanVM.Guest.B1.Terminal.Layout

/-!
# The terminal's context

`ptsP H j`: honest claim `j`'s point (the bus point cut to `logMemory` four times, to `19` once,
`chi` cut to evaluation `j - 5`'s table's height, the public input's point); `vtH_ptsP`: the
honest claims' points are those. `vtH_tctx`: on a memory holding the bus point at `zeta`, `chi`'s
words and `claim_cplen_g`'s, `TCtx` holds of the honest layout, bus result and claims.
`whir_point_length`: an accepted opening's terminal point has `μ` coordinates.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

namespace VtHonest

/-- Honest claim `j`'s point. -/
noncomputable def ptsP (H : VtHonest) (j : ℕ) : List E :=
  if j < 4 then H.point.take H.lm else if j = 4 then H.point.take 19
  else if j < 162 then H.chiW.take (vtHt H.rows (vtEvTab (j - 5)))
  else H.rm :: List.replicate ((H.L.placement memory0).vars - 1) 0

variable {H : VtHonest}

theorem vtH_ptsP (h : H.Ok) (hr : H.rows.length = 6) (hbc : H.bc.length = 2 ^ 23) :
    H.claims.map (·.point) = (List.range 165).map H.ptsP := by
  rw [vtH_points h hr hbc]
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.length_map, List.length_range] at h2
  simp only [List.getElem_map, List.getElem_range, ptsP]
  have e4 : (List.replicate 4 (H.point.take H.lm) ++ [H.point.take 19]).length = 5 := by simp
  have e157 : ((List.range 157).map fun k ↦ H.chiW.take (vtHt H.rows (vtEvTab k))).length = 157 := by
    simp
  by_cases hj4 : j < 4
  · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega),
      List.getElem_append_left (by simp; omega)]
    simp only [hj4, ↓reduceIte]
    interval_cases j <;> rfl
  by_cases hj5 : j = 4
  · subst hj5
    rw [List.getElem_append_left (by simp), List.getElem_append_left (by simp)]
    simp
  by_cases hj162 : j < 162
  · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
    simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil,
      List.getElem_map, List.getElem_range, hj4, hj5, hj162, ↓reduceIte]
  · rw [List.getElem_append_right (by simp; omega)]
    simp only [List.getElem_replicate, hj4, hj5, hj162, ↓reduceIte]

theorem take_self_len (l : List E) (k : ℕ) : l.take k = l.take (l.take k).length := by
  rw [List.length_take]; exact List.take_eq_take_min

theorem chiW_length (H : VtHonest) : H.chiW.length = H.n := by
  simp [VtHonest.chiW, zcChis]

theorem vtEvTab_lt : ∀ k < 157, vtEvTab k < 6 := fun k hk ↦ (vtEvTab_spec k hk).1

/-- `claim_cplen_g`'s words are the honest claims' points' lengths, in the exponent. -/
theorem cplenW_getD (hs : VtShape H) {j : ℕ} (hj : j < 162) :
    H.cplenW.getD j 0 = gen ^ (H.ptsP j).length := by
  have hr := hs.hr
  unfold VtHonest.cplenW ptsP
  by_cases hj4 : j < 4
  · simp only [hj4, ↓reduceIte, List.length_take, min_eq_left hs.hlmμ]
    interval_cases j <;> rfl
  by_cases hj5 : j = 4
  · subst hj5; simp [min_eq_left (show 19 ≤ H.point.length from hs.h19)]
  · simp only [hj4, hj5, hj, ↓reduceIte]
    rw [List.getD_append_right _ _ _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega),
      List.getElem_map, List.getElem_range]
    simp only [List.length_cons, List.length_nil, List.length_take, chiW_length]
    have hle : vtHt H.rows (vtEvTab (j - 5)) ≤ H.n := vt_n_ge hr (vtEvTab_lt _ (by omega))
    rw [min_eq_left hle, show j - (0 + 1 + 1 + 1 + 1 + 1) = j - 5 by omega]

/-- **`verify_tables`' context, honestly.** -/
theorem vtH_tctx (h : H.Ok) (hs : VtShape H) {rd : Reader} {zeta chi cplen : E}
    (hz : TbReadsAt rd zeta H.point) (hc : TbReadsAt rd chi H.chiW)
    (hcp : TbReadsAt rd cplen H.cplenW) :
    TCtx rd H.L H.bus H.claims [zeta, chi, H.rm, gen ^ H.point.length, gen ^ H.n, cplen] := by
  have hr := hs.hr
  have hbc := hs.hbc
  have hbus : H.bus = H.busH := (vt_spec h).2.1
  have hcol := vtH_columns h hr
  have hl : H.claims.length = 165 := by
    rw [← List.length_map (f := (·.column)), hcol]; decide +kernel
  obtain ⟨t, ht, htn⟩ := vt_n_ex hr
  refine ⟨H.chiW, by rw [hbus]; exact hz, by rw [hbus]; rfl, hc, by rw [chiW_length],
    by rw [chiW_length, hbus, ← htn]; exact hs.hτμ t ht, hl, hcol, fun j p hp ↦ ?_⟩
  rw [vtH_ptsP h hr hbc, List.getElem?_map] at hp
  have hj : j < 165 := by
    by_contra hn; rw [List.getElem?_eq_none (by simp; omega)] at hp; simp at hp
  rw [List.getElem?_range hj] at hp
  simp only [Option.map_some, Option.some.injEq] at hp
  subst hp
  rw [hbus]
  refine ⟨fun hj2 ↦ ?_, fun hj5 ↦ ?_, fun hj5 hj2 ↦ ?_, fun hj2 ↦ ?_⟩
  · have := hcp j (by simp [VtHonest.cplenW]; omega)
    rw [← List.getD_eq_getElem _ 0, cplenW_getD hs hj2] at this
    exact this
  · show H.ptsP j = H.point.take (H.ptsP j).length
    unfold ptsP
    by_cases hj4 : j < 4
    · simp only [hj4, ↓reduceIte]; exact take_self_len _ _
    · simp only [show j = 4 by omega, ↓reduceIte]; exact take_self_len _ _
  · have hj2' : j < 162 := hj2
    unfold ptsP
    simp only [show ¬ j < 4 by omega, show j ≠ 4 by omega, hj2', ↓reduceIte]
    exact take_self_len _ _
  · have hj2' : 162 ≤ j := hj2
    unfold ptsP
    simp only [show ¬ j < 4 by omega, show j ≠ 4 by omega, show ¬ j < 162 by omega, ↓reduceIte]

end VtHonest

/-- The columns' logs' codes over `[lm, 19, h₀, …, h₅, h₅ + 6]`. -/
def colCode : List ℕ :=
  [0, 0, 0, 0, 1, 8] ++ List.replicate 15 2 ++ List.replicate 15 3 ++ List.replicate 8 4 ++
    List.replicate 15 5 ++ List.replicate 14 6 ++ List.replicate 90 7

theorem colCode_length : colCode.length = 163 := by
  simp only [colCode, List.length_append, List.length_replicate, List.length_cons, List.length_nil]

theorem columnKappas_code (lm h0 h1 h2 h3 h4 h5 : ℕ) :
    columnKappas lm 19 [h0, h1, h2, h3, h4, h5] =
      colCode.map fun k ↦ [lm, 19, h0, h1, h2, h3, h4, h5, h5 + 6].getD k 0 := by
  rw [columnKappas_eq]
  simp [colCode]

theorem claim_code : ∀ j < 165, claimColumns.getD j 0 < 163 ∧
    colCode.getD (claimColumns.getD j 0) 9 =
      (if j < 4 then 0 else if j = 4 then 1 else if j < 162 then vtEvTab (j - 5) + 2 else 0) := by
  decide +kernel

theorem committedCols_zero : (committedCols 163).getD 0 0 = 0 := by decide +kernel

namespace VtHonest

variable {H : VtHonest}

/-- **Every honest claim's point has its column's number of variables.** -/
theorem vtH_hlen (h : H.Ok) (hs : VtShape H) (hlm1 : 1 ≤ H.lm) :
    ∀ c ∈ H.claims, c.point.length =
      (columnKappas H.L.logMemory H.L.logBytecode H.L.tableLogHeights).getD c.column 0 := by
  have hr := hs.hr
  have hbc := hs.hbc
  have hlb : H.L.logBytecode = 19 := by
    show Nat.log2 H.bc.length - busBits = 19
    rw [hbc, Nat.log2_two_pow]; rfl
  have hlm : H.L.logMemory = H.lm := rfl
  have hht : H.L.tableLogHeights = tableHeightsOf H.rows := rfl
  have hsl : (tableHeightsOf H.rows).length = 6 := vt_tableHeights_length hr
  have hcol := vtH_columns h hr
  have hpts := vtH_ptsP h hr hbc
  have hl : H.claims.length = 165 := by
    rw [← List.length_map (f := (·.column)), hcol]; decide +kernel
  -- the public input's point
  have hmem0 : (H.L.placement memory0).vars = H.lm := by
    have hk : (columnKappas H.L.logMemory H.L.logBytecode H.L.tableLogHeights).length = 163 :=
      columnKappas_length _ _ _
    have := VerifySub.placement_committed (layout := H.L) hk rfl (cc := 0) (by decide)
    rw [committedCols_zero] at this
    rw [show memory0 = 0 from rfl, this]
    simp only [hlb, hht, hlm]
    rw [committedKappas_columnKappas H.lm _ hsl]
    rfl
  intro c hc
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
  have ecol : H.claims[j].column = claimColumns.getD j 0 := by
    rw [← hcol, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map]
  have ept : H.claims[j].point = H.ptsP j := by
    have := congrArg (·[j]?) hpts
    simp only [List.getElem?_map, List.getElem?_eq_getElem hj,
      List.getElem?_range (show j < 165 by omega), Option.map_some, Option.some.injEq] at this
    exact this
  rw [ecol, ept, hlb, hht, hlm]
  obtain ⟨h0, h1, h2, h3, h4, h5, e6⟩ : ∃ h0 h1 h2 h3 h4 h5, tableHeightsOf H.rows =
      [h0, h1, h2, h3, h4, h5] := by
    match hm : tableHeightsOf H.rows, hsl with
    | [h0, h1, h2, h3, h4, h5], _ => exact ⟨h0, h1, h2, h3, h4, h5, rfl⟩
  obtain ⟨hlt, hcode⟩ := claim_code j (by omega)
  rw [e6, columnKappas_code, List.getD_eq_getElem _ _ (by rw [List.length_map, colCode_length]; exact hlt),
    List.getElem_map, ← List.getD_eq_getElem _ 9 (by rw [colCode_length]; exact hlt), hcode]
  have hn : ∀ t < 6, vtHt H.rows t ≤ H.n := fun t ht ↦ vt_n_ge hr ht
  have hv : ∀ t < 6, vtHt H.rows t = [h0, h1, h2, h3, h4, h5].getD t 0 := fun t _ ↦ by
    rw [← e6]; rfl
  unfold ptsP
  by_cases hj4 : j < 4
  · simp [hj4, min_eq_left hs.hlmμ]
  by_cases hj5 : j = 4
  · subst hj5; simp [min_eq_left (show 19 ≤ H.point.length from hs.h19)]
  by_cases hj162 : j < 162
  · have ht := vtEvTab_lt (j - 5) (by omega)
    simp only [hj4, hj5, hj162, ↓reduceIte, List.length_take, chiW_length,
      min_eq_left (hn _ ht)]
    rw [hv _ ht]
    interval_cases (vtEvTab (j - 5)) <;> rfl
  · simp only [hj4, hj5, hj162, ↓reduceIte, List.length_cons, List.length_replicate, hmem0]
    simp; omega

end VtHonest

end
end LeanVM.Guest.B1.Tables
