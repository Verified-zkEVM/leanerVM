/-
  LeanVM.Guest.B1.Comp.VsInv.Tables

  The tables' run over a hash model, backward: the claims it returns, their columns and their
  points, with the sumcheck point's length.
-/

module

public import LeanVM.Guest.B1.Comp.VsInv.Phases
public import LeanVM.Guest.B1.VerifySub.TablesLen

/-!
# The tables' claims over a hash model

`VerifyTablesInv.lean`'s `RunsTo.tablesSeg_inv` over a hash model `M`, by the same proofs at
`RunsM M` (`vs_tablesSeg_invM`): any run of `tablesSeg` returns the bus's five claims, the tables'
claims on their columns at prefixes of the reversed sumcheck challenges, and the public input's
three claims. `vs_tablesSeg_claimsOkM`: `TablesLen.lean`'s `vs_tablesSeg_claimsOk` over `M`, the
claims as the terminal reads them (`VsData.TOk`), by the same proof.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {M : HashModel}

theorem vs_tableTerms_invM (cp fp pt : List E) :
    ∀ (rows : List (Table × ℕ × List Form × E)) (cursor : ℕ) (final : E) (claims : List ColumnClaim)
      (s s' : St) (r : E × List ColumnClaim),
      RunsM M (tableTerms cp fp pt rows cursor final claims) s r s' →
      ∃ evss : List (List E), evss.length = rows.length ∧
        (∀ i (h1 : i < evss.length) (h2 : i < rows.length), evss[i].length = rows[i].1.width) ∧
        r.2 = claims ++ (List.zip rows evss).flatMap (rowClaims pt)
  | [], cursor, final, claims, s, s', r, h => by
    have h' : RunsM M (pure (final, claims) : Prog (E × List ColumnClaim)) s r s' := h
    obtain ⟨rfl, -⟩ := RunsM.pure_inv h'
    exact ⟨[], rfl, fun i h1 => absurd h1 (by simp), by simp⟩
  | (table, height, forms, weight) :: rest, cursor, final, claims, s, s', r, h => by
    unfold tableTerms at h
    obtain ⟨evs, s1, h1, h2⟩ := RunsM.bind_inv h
    have hl := (RunsM.readN_inv h1).1
    obtain ⟨evss, hl', hw, hr⟩ := vs_tableTerms_invM cp fp pt rest _ _ _ _ _ _ h2
    refine ⟨evs :: evss, by simp [hl'], fun i h1 h2 => ?_, ?_⟩
    · match i with
      | 0 => simpa using hl
      | i + 1 => simpa using hw i (by simpa using h1) (by simpa using h2)
    · rw [hr]
      simp [rowClaims, List.append_assoc]

theorem vs_tableSumcheck_invM {heights : List ℕ} {busForms : List (List Form)}
    {cps fps eqp : List E} {target : E} {s s' : St} {claims : List ColumnClaim}
    (h : RunsM M (tableSumcheck heights busForms cps fps eqp target) s claims s') :
    ∃ (chs : List E) (evss : List (List E)), chs.length = heights.foldl max 0 ∧
      evss.length = (List.zip tables (List.zip heights (List.zip busForms
        (tableWeights heights eqp chs.reverse)))).length ∧
      (∀ i (h1 : i < evss.length) (h2 : i < (List.zip tables (List.zip heights (List.zip busForms
        (tableWeights heights eqp chs.reverse)))).length),
        evss[i].length = (List.zip tables (List.zip heights (List.zip busForms
          (tableWeights heights eqp chs.reverse))))[i].1.width) ∧
      claims = (List.zip (List.zip tables (List.zip heights (List.zip busForms
        (tableWeights heights eqp chs.reverse)))) evss).flatMap (rowClaims chs.reverse) := by
  unfold tableSumcheck at h
  obtain ⟨⟨chs, cl⟩, s1, h1, h⟩ := RunsM.bind_inv h
  have hpt := RunsM.sumcheck_inv h1
  obtain ⟨⟨final, tc⟩, s3, h3, h⟩ := RunsM.bind_inv h
  obtain ⟨evss, hl, hw, hr⟩ := vs_tableTerms_invM _ _ _ _ _ _ _ _ _ _ h3
  obtain ⟨u, s5, h5, h⟩ := RunsM.bind_inv h
  obtain ⟨-, -⟩ := RunsM.require_inv h5
  obtain ⟨rfl, -⟩ := RunsM.ret_inv h
  refine ⟨chs, evss, by simpa using hpt, hl, hw, ?_⟩
  simpa using hr

theorem vs_tablePhase_invM {layout : Layout} {bus : BusResult} {s s' : St}
    {claims : List ColumnClaim} (h : RunsM M (tablePhase layout bus) s claims s') :
    ∃ (chs : List E) (evss : List (List E)) (ws : List E) ,
      chs.length = layout.tableLogHeights.foldl max 0 ∧
      ws = tableWeights layout.tableLogHeights bus.point chs.reverse ∧
      evss.length = (List.zip tables (List.zip layout.tableLogHeights (List.zip bus.forms ws))).length ∧
      (∀ i (h1 : i < evss.length) (h2 : i < (List.zip tables (List.zip layout.tableLogHeights
        (List.zip bus.forms ws))).length),
        evss[i].length = (List.zip tables (List.zip layout.tableLogHeights (List.zip bus.forms ws)))[i].1.width) ∧
      claims = bus.claims ++ (List.zip (List.zip tables (List.zip layout.tableLogHeights
        (List.zip bus.forms ws))) evss).flatMap (rowClaims chs.reverse) := by
  unfold tablePhase at h
  obtain ⟨xi, s1, h1, h⟩ := RunsM.bind_inv h
  obtain ⟨tc, s3, h3, h⟩ := RunsM.bind_inv h
  obtain ⟨chs, evss, hl, hel, hw, hc⟩ := vs_tableSumcheck_invM h3
  obtain ⟨rfl, -⟩ := RunsM.ret_inv h
  exact ⟨chs, evss, _, hl, rfl, hel, hw, by rw [hc]⟩

theorem vs_publicInputPhase_invM {layout : Layout} {pi : Digest} {s s' : St}
    {claims : List ColumnClaim} (h : RunsM M (publicInputPhase layout pi) s claims s') :
    ∃ rm, claims = piClaims layout pi rm := by
  unfold publicInputPhase at h
  obtain ⟨rm, s1, h1, h⟩ := RunsM.bind_inv h
  obtain ⟨rfl, -⟩ := RunsM.ret_inv h
  exact ⟨rm, rfl⟩

theorem vs_busRest_invM {ev : Evaluations} {layout : Layout} {alphas : List E} {beta : E}
    {point tv : List E} {s s' : St} {bus : BusResult}
    (h : RunsM M (busRest ev layout alphas beta point tv) s bus s') :
    ∃ (memory : List E) (mF bF bv : E), memory.length = 3 ∧
      bus = busVal layout alphas beta point tv memory mF bF bv := by
  unfold busRest at h
  obtain ⟨memory, s1, h1, h⟩ := RunsM.bind_inv h
  have hl := (RunsM.readN_inv h1).1
  obtain ⟨mF, s3, h3, h⟩ := RunsM.bind_inv h
  obtain ⟨bF, s5, h5, h⟩ := RunsM.bind_inv h
  obtain ⟨bv, s7, h7, h⟩ := RunsM.bind_inv h
  have h' : RunsM M (pure (busVal layout alphas beta point tv memory mF bF bv) : Prog BusResult) s7 bus s' := h
  obtain ⟨rfl, -⟩ := RunsM.ret_inv h'
  exact ⟨memory, mF, bF, bv, hl, rfl⟩

/-- **`tablesSeg`'s run over the model, inverted** (`RunsTo.tablesSeg_inv`). -/
theorem vs_tablesSeg_invM {ev : Evaluations} {layout : Layout} {pi : Digest} {alphas : List E}
    {beta : E} {point tv : List E} {s s' : St} {bus : BusResult} {claims : List ColumnClaim}
    (h : RunsM M (tablesSeg ev layout pi alphas beta point tv) s (bus, claims) s') :
    ∃ (memory : List E) (mF bF bv : E) (chs : List E) (evss : List (List E)) (ws : List E) (rm : E),
      memory.length = 3 ∧ bus = busVal layout alphas beta point tv memory mF bF bv ∧
      chs.length = layout.tableLogHeights.foldl max 0 ∧
      ws = tableWeights layout.tableLogHeights bus.point chs.reverse ∧
      evss.length = (List.zip tables (List.zip layout.tableLogHeights (List.zip bus.forms ws))).length ∧
      (∀ i (h1 : i < evss.length) (h2 : i < (List.zip tables (List.zip layout.tableLogHeights
        (List.zip bus.forms ws))).length),
        evss[i].length = (List.zip tables (List.zip layout.tableLogHeights (List.zip bus.forms ws)))[i].1.width) ∧
      claims = bus.claims ++ (List.zip (List.zip tables (List.zip layout.tableLogHeights
        (List.zip bus.forms ws))) evss).flatMap (rowClaims chs.reverse) ++ piClaims layout pi rm := by
  unfold tablesSeg at h
  obtain ⟨bus1, s1, h1, h⟩ := RunsM.bind_inv h
  obtain ⟨memory, mF, bF, bv, hl, rfl⟩ := vs_busRest_invM h1
  obtain ⟨tc, s3, h3, h⟩ := RunsM.bind_inv h
  obtain ⟨chs, evss, ws, hc, hws, hel, hw, htc⟩ := vs_tablePhase_invM h3
  obtain ⟨pc, s5, h5, h⟩ := RunsM.bind_inv h
  obtain ⟨rm, hpc⟩ := vs_publicInputPhase_invM h5
  obtain ⟨he, -⟩ := RunsM.ret_inv h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨memory, mF, bF, bv, chs, evss, ws, rm, hl, rfl, hc, hws, hel, hw, by rw [htc, hpc]⟩

theorem vs_tablesSeg_claimsOkM {bytecode : List K} (hb : bytecode.length = 2 ^ 22) {logMem : ℕ}
    (hm16 : 16 ≤ logMem) {rows : List ℕ} (hr : rows.length = 6) {ev : Evaluations} {pi : Digest}
    {alphas : List E} {beta : E} {point values : List E}
    {bus : BusResult} {claims : List ColumnClaim}
    (hpt : point.length = pushDepth (layoutOf bytecode logMem rows)) {s s' : St}
    (h : RunsM M (tablesSeg ev (layoutOf bytecode logMem rows) pi alphas beta point values) s
      (bus, claims) s') :
    ∃ (chis : List E) (rm : E),
      chis.length = (layoutOf bytecode logMem rows).tableLogHeights.foldl max 0 ∧
      chis.length ≤ point.length ∧ claims.map (·.column) = claimColumns ∧
      (∀ j (p : List E), (claims.map (·.point))[j]? = some p →
        (j < 5 → p = point.take p.length) ∧ (5 ≤ j → j < nPooled → p = chis.take p.length) ∧
          (nPooled ≤ j → p = rm :: List.replicate
            (((layoutOf bytecode logMem rows).placements.getD memory0 default).vars - 1) 0)) ∧
      ∀ c ∈ claims, c.point.length =
        ((layoutOf bytecode logMem rows).placements.getD c.column default).vars := by
  obtain ⟨memory, mF, bF, bv, chs, evss, ws, rm, hl, rfl, hc, hws, hel, hw, rfl⟩ := vs_tablesSeg_invM h
  obtain ⟨m0, m1, m2, rfl⟩ : ∃ a b c, memory = [a, b, c] := by
    match memory, hl with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
  obtain ⟨hlb, hth, -⟩ := layoutOf_blocks bytecode hb logMem rows hr
  set L := layoutOf bytecode logMem rows with hLd
  set bus := busVal L alphas beta point values [m0, m1, m2] mF bF bv with hbus
  have hfs : FormsShaped bus.forms := busVal_forms_shaped L alphas beta point values [m0, m1, m2] mF bF bv
  have hbl : bus.claims.length = 5 := rfl
  obtain ⟨h0, h1, h2, h3, h4, h5, hhs⟩ : ∃ h0 h1 h2 h3 h4 h5, rows.map log2Ceil = [h0, h1, h2, h3, h4, h5] := by
    match rows.map log2Ceil, (by simp [hr] : (rows.map log2Ceil).length = 6) with
    | [a, b, c, d, e, f], _ => exact ⟨a, b, c, d, e, f, rfl⟩
  have hmem : ∀ x ∈ pushKappas logMem (rows.map log2Ceil), x ≤ point.length := fun x hx => by
    rw [hpt, pushDepth_eq hb logMem rows hr]; exact le_log2Ceil_of_mem hx
  rw [hhs] at hmem
  have hm_le : logMem ≤ point.length := hmem _ (by simp [pushKappas])
  have h18 : 18 ≤ point.length := hmem _ (by simp [pushKappas])
  have hh : ∀ x ∈ L.tableLogHeights, x ≤ point.length := fun x hx => by
    rw [hth, hhs] at hx
    apply hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [pushKappas]
  have hn : chs.length ≤ point.length := by
    rw [hc]; exact foldl_max_le hh 0 (Nat.zero_le _)
  have hhn : ∀ x ∈ L.tableLogHeights, x ≤ chs.length := fun x hx => by
    rw [hc]; exact vt_le_foldl_max _ 0 x (Or.inl hx)
  have hthl : L.tableLogHeights.length = 6 := by rw [hth, hhs]; rfl
  set X := List.zip L.tableLogHeights (List.zip bus.forms ws) with hXd
  have hX : X.length = 6 := by
    simp [hXd, hthl, hfs.1, hws, tableWeights_length]
  have he6 : evss.length = 6 := by rw [hel]; simp [hX, tables_length']
  have hw' : ∀ t < 6, (evss.getD t []).length = (tables.getD t default).width := fun t ht => by
    have := hw t (by omega) (by simp [hX, tables_length']; omega)
    rw [List.getD_eq_getElem _ _ (by omega), this, List.getElem_zip,
      List.getD_eq_getElem _ _ (by simp [tables_length']; omega)]
  have hmap : X.map (·.1) = L.tableLogHeights := by
    rw [hXd]; exact List.map_fst_zip (by simp [hthl, hfs.1, hws, tableWeights_length])
  have hXg : ∀ t < 6, (X.getD t default).1 = L.tableLogHeights.getD t 0 := fun t ht => by
    have : (X.map (·.1)).getD t 0 = (X.getD t default).1 := by
      rw [List.getD_eq_getElem _ _ (by simp [hX]; omega), List.getElem_map,
        List.getD_eq_getElem _ _ (by omega)]
    rw [← this, hmap]
  have hpl : L.placements = (placementsOf (columnKappas logMem 18 L.tableLogHeights)).1 := by
    rw [← hlb]; rfl
  have hkl : (columnKappas logMem 18 L.tableLogHeights).length = 110 := by
    rw [columnKappas_length]; decide +kernel
  have hv0 : (L.placements.getD memory0 default).vars = logMem := by
    rw [hpl, placementsOf_vars _ (by rw [hkl]; decide)]; rfl
  have htl := tc_length chs.reverse X hX evss he6 hw'
  refine ⟨chs.reverse, rm, by rw [List.length_reverse]; exact hc, by rw [List.length_reverse]; exact hn,
    ?_, ?_, ?_⟩
  · rw [List.map_append, List.map_append, tc_columns chs.reverse X hX evss he6 hw']
    rfl
  · intro j p hp
    rw [List.map_append, List.map_append] at hp
    have hnp : nPooled = 109 := rfl
    rw [hnp]
    rcases lt_or_ge j 5 with hj | hj
    · rw [List.getElem?_append_left (by simp [htl, hbl]; omega), List.getElem?_append_left (by simp [hbl]; omega)] at hp
      refine ⟨fun _ => ?_, fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
      have hb5 : bus.claims.map (·.point) = [point.take L.logMemory, point.take L.logMemory,
          point.take L.logMemory, point.take L.logMemory, point.take L.logBytecode] := rfl
      rw [hb5] at hp
      interval_cases j <;> simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.some.injEq] at hp <;> subst hp <;> exact take_eq_take_length _ _
    rcases lt_or_ge j 109 with hj' | hj'
    · rw [List.getElem?_append_left (by simp [htl, hbl]; omega), List.getElem?_append_right (by simp [hbl]; omega)] at hp
      refine ⟨fun h => absurd h (by omega), fun _ _ => ?_, fun h => absurd h (by omega)⟩
      have hm := List.mem_of_getElem? hp
      obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hm
      obtain ⟨t, -, k, -, -, hpt'⟩ := tc_mem chs.reverse X hX evss he6 hw' hc'
      rw [hpt']; exact take_eq_take_length _ _
    · rw [List.getElem?_append_right (by simp [htl, hbl]; omega)] at hp
      refine ⟨fun h => absurd h (by omega), fun h h' => absurd h' (by omega), fun _ => ?_⟩
      have hm := List.mem_of_getElem? hp
      simp only [piClaims, List.zipWith_cons_cons, List.zipWith_nil_left, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl <;> rfl
  · intro c hcm
    rw [List.mem_append, List.mem_append] at hcm
    rcases hcm with (hcm | hcm) | hcm
    · simp only [hbus, busVal, List.zipWith_cons_cons, List.zipWith_nil_left, List.cons_append,
        List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hcm
      rcases hcm with rfl | rfl | rfl | rfl | rfl <;>
        (rw [hpl, placementsOf_vars _ (by rw [hkl]; simp [memory0, memory1, memory2,
           memoryFinalCounters, bytecodeFinalCounters])]
         simp [columnKappas, memory0, memory1, memory2, memoryFinalCounters, bytecodeFinalCounters,
          hlb, show L.logMemory = logMem from rfl, hm_le, h18])
    · obtain ⟨t, ht, k, hk, hcol, hpt'⟩ := tc_mem chs.reverse X hX evss he6 hw' hcm
      have hbw : ∀ t < 6, globalColumnBases.getD t 0 + (tables.getD t default).width ≤ 110 := by
        decide +kernel
      have := hbw t ht
      rw [hcol, hpt', hpl, placementsOf_vars _ (by rw [hkl]; omega),
        columnKappas_table _ _ _ ht hk, hXg t ht, List.length_take, List.length_reverse]
      have : L.tableLogHeights.getD t 0 ≤ chs.length :=
        hhn _ (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
      omega
    · simp only [piClaims, List.map_cons, List.map_nil, List.zipWith_cons_cons, List.zipWith_nil_left,
        List.mem_cons, List.not_mem_nil, or_false] at hcm
      rcases hcm with rfl | rfl | rfl <;>
        (simp only [List.length_cons, List.length_replicate]
         rw [hv0]
         first
           | omega
           | (rw [hpl, placementsOf_vars _ (by rw [hkl]; simp [memory1, memory2])]
              simp [columnKappas, memory1, memory2]
              omega))

end
end LeanVM.Guest.B1.VerifySub
