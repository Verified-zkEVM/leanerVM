/-
  LeanVM.Guest.B1.Comp.Tables.VtTraceC

  `tablesSeg`'s answered run over a hash model, read back with its stream and states at the
  model's total hash, every hash answered.
-/

module

public import LeanVM.Guest.B1.Comp.Tables.GkrInvC
public import LeanVM.Guest.B1.Tables.VerifyTablesCTrace
public import LeanVM.Guest.B1.Tables.VerifyTablesRunM

/-!
# The answered run of `tablesSeg`, with its stream

`VerifyTablesCTrace.lean` over a hash model `M` (`RunsToM M`): `RunsToM.tablesSeg_trace` reads
the bus's three memory words and two final counters (their absorbs answered, `ObsAns`), the table
sumcheck's rounds (`roundPoly 4`, each run answered), then each table's evaluations (answered),
the squeezes of `ξ` and of the public input's challenge answered; the states are those of the
total hash (`obsAllT`, `sqCvT`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {M : HashModel}

/-- A program reading nothing, run twice: the second run reads nothing too (`RunsTo.det_nil`). -/
theorem RunsToM.det_nil {α : Type} {p : Prog α} {cv c0 c : Digest} {xs : List E} {a0 a : α}
    (h0 : RunsToM M p cv [] a0 c0) (h : RunsToM M p cv xs a c) : xs = [] ∧ a = a0 ∧ c = c0 := by
  have e1 := h0 xs [] []
  have e2 := h [] [] []
  rw [List.append_nil] at e2
  rw [List.nil_append] at e1
  rw [e1] at e2
  simp only [Option.some.injEq, Prod.mk.injEq, St.mk.injEq] at e2
  obtain ⟨ha, hc, hx, -, -⟩ := e2
  exact ⟨hx, ha.symm, hc.symm⟩

theorem RunsToM.roundPoly4_len {claim : E} {cv cv' : Digest} {ws : List E} {r : E × E}
    (h : RunsToM M (roundPoly 4 claim none) cv ws r cv') : ws.length = 3 := by
  unfold roundPoly at h
  obtain ⟨x1, x2, msg, cv1, hx, h1, h⟩ := RunsToM.bind_inv' h
  unfold sumcheckRoundPoly at h1
  obtain ⟨y1, y2, c, cv2, hy, h2, h1⟩ := RunsToM.bind_inv' h1
  obtain ⟨hy1, -⟩ := RunsToM.readEP_inv h2
  obtain ⟨y3, y4, tail, cv3, hz, h3, h1⟩ := RunsToM.bind_inv' h1
  obtain ⟨hl, -, -⟩ := RunsToM.readNP_inv h3
  obtain ⟨hy4, -, -⟩ := RunsToM.pure_inv h1
  obtain ⟨x3, x4, ch, cv4, hw, h4, h⟩ := RunsToM.bind_inv' h
  obtain ⟨hx3, -, -⟩ := RunsToM.sampleEP_inv h4
  obtain ⟨hx4, -, -⟩ := RunsToM.pure_inv h
  rw [hx, hy, hz, hy1, hy4, hw, hx3, hx4]
  simp [hl]

/-- **`tableTerms`' answered run, inverted, with its stream** (`RunsTo.tableTerms_trace`). -/
theorem RunsToM.tableTerms_trace (cp fp pt : List E) :
    ∀ (rows : List (Table × ℕ × List Form × E)) (cursor : ℕ) (final : E)
      (claims : List ColumnClaim) (cv cv' : Digest) (xs : List E) (r : E × List ColumnClaim),
      RunsToM M (tableTerms cp fp pt rows cursor final claims) cv xs r cv' →
      ∃ evss : List (List E), evss.length = rows.length ∧
        (∀ i (h1 : i < evss.length) (h2 : i < rows.length), evss[i].length = rows[i].1.width) ∧
        xs = evss.flatten ∧ r = ttVal cp fp pt rows evss cursor final claims ∧
        ObsAns M cv evss.flatten ∧ cv' = obsAllT M cv evss.flatten
  | [], cursor, final, claims, cv, cv', xs, r, h => by
    have h' : RunsToM M (pure (final, claims) : Prog (E × List ColumnClaim)) cv xs r cv' := h
    obtain ⟨rfl, rfl, rfl⟩ := RunsToM.pure_inv h'
    exact ⟨[], rfl, fun i h1 => absurd h1 (by simp), rfl, rfl,
      fun i hi => absurd hi (Nat.not_lt_zero _), rfl⟩
  | (table, height, forms, weight) :: rest, cursor, final, claims, cv, cv', xs, r, h => by
    unfold tableTerms at h
    obtain ⟨x1, x2, evs, cv1, rfl, h1, h2⟩ := RunsToM.bind_inv' h
    obtain ⟨hl, he, hc⟩ := RunsToM.readNP_inv h1
    subst he
    obtain ⟨rfl, ha1⟩ := obsAllM_T hc
    obtain ⟨evss, hl', hw, rfl, rfl, ha2, rfl⟩ :=
      RunsToM.tableTerms_trace cp fp pt rest _ _ _ _ _ _ _ h2
    refine ⟨evs :: evss, by simp [hl'], fun i h1 h2 => ?_, by simp, rfl, ?_, ?_⟩
    · match i with
      | 0 => simpa using hl
      | i + 1 => simpa using hw i (by simpa using h1) (by simpa using h2)
    · rw [List.flatten_cons]; exact obsAns_append ha1 ha2
    · rw [List.flatten_cons, obsAllT_append]

/-- `busRest`'s answered stream and state (`RunsTo.busRest_trace`). -/
theorem RunsToM.busRest_trace {ev : Evaluations} {layout : Layout} {alphas : List E} {beta : E}
    {point tv : List E} {cv cv' : Digest} {xs : List E} {bus : BusResult} {bv : E}
    (hbv : BytecodeAtM M ev layout.bytecode (point.take layout.logBytecode ++ alphas) bv)
    (h : RunsToM M (busRest ev layout alphas beta point tv) cv xs bus cv') :
    ∃ (memory : List E) (mF bF : E), memory.length = 3 ∧ xs = memory ++ [mF, bF] ∧
      bus = busVal layout alphas beta point tv memory mF bF bv ∧
      ObsAns M cv (memory ++ [mF, bF]) ∧ cv' = obsAllT M cv (memory ++ [mF, bF]) := by
  unfold busRest at h
  obtain ⟨x1, x2, memory, cv1, e1, h1, k1⟩ := RunsToM.bind_inv' h
  obtain ⟨hl, em, ec1⟩ := RunsToM.readNP_inv h1
  obtain ⟨x3, x4, mF, cv3, e3, h3, k3⟩ := RunsToM.bind_inv' k1
  obtain ⟨ex3, ec3⟩ := RunsToM.readEP_inv h3
  obtain ⟨x5, x6, bF, cv5, e5, h5, k5⟩ := RunsToM.bind_inv' k3
  obtain ⟨ex5, ec5⟩ := RunsToM.readEP_inv h5
  obtain ⟨x7, x8, bv', cv7, e7, h7, k7⟩ := RunsToM.bind_inv' k5
  obtain ⟨ex7, eb, ec7⟩ := RunsToM.det_nil (runsToM_bytecodeAt hbv _) h7
  have k8 : RunsToM M (pure (busVal layout alphas beta point tv memory mF bF bv') : Prog BusResult)
    cv7 x8 bus cv' := k7
  obtain ⟨ex8, eb', ec8⟩ := RunsToM.pure_inv k8
  subst em
  obtain ⟨rfl, a1⟩ := obsAllM_T ec1
  have q3 := obsCvT_eq ec3
  have q5 := obsCvT_eq ec5
  subst q3 q5 ec7 ec8
  have hA : ObsAns M cv (memory ++ [mF, bF]) := obsAns_append a1 (fun i hi => by
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i
    · exact ec3
    · exact ec5)
  refine ⟨memory, mF, bF, hl, ?_, by rw [eb', eb], hA, ?_⟩
  · rw [e1, e3, e5, e7, ex3, ex5, ex7, ex8]; simp
  · rw [obsAllT_append]; rfl

/-- **`tablesSeg`'s answered run, read back** (`RunsTo.tablesSeg_trace`): the bus's five words,
their absorbs answered, the squeeze of `ξ` answered, the table sumcheck's rounds (each run
answered) from the state after it, the tables' evaluations, their absorbs answered, the terms'
sum the last claim, the squeeze of the public input's challenge answered, and the claims and
state at the end, at the total hash. -/
theorem RunsToM.tablesSeg_trace {ev : Evaluations} {layout : Layout} {pi : Digest}
    {alphas : List E} {beta : E} {point tv : List E} {cv cv' : Digest} {xs : List E}
    {bus : BusResult} {claims : List ColumnClaim} {bv : E}
    (hbv : BytecodeAtM M ev layout.bytecode (point.take layout.logBytecode ++ alphas) bv)
    (h : RunsToM M (tablesSeg ev layout pi alphas beta point tv) cv xs (bus, claims) cv') :
    ∃ (memory : List E) (mF bF : E) (cl : ℕ → E) (cvr : ℕ → Digest) (wsr : ℕ → List E)
      (ch : ℕ → E) (evss : List (List E)), memory.length = 3 ∧
      bus = busVal layout alphas beta point tv memory mF bF bv ∧
      xs = memory ++ [mF, bF] ++ ((List.range (vtN layout)).flatMap wsr ++ evss.flatten) ∧
      ObsAns M cv (memory ++ [mF, bF]) ∧
      sqCvM M (obsAllT M cv (memory ++ [mF, bF])) =
        some (sqCvT M (obsAllT M cv (memory ++ [mF, bF]))) ∧
      cl 0 = dot ((powers (challengeOf (sqCvT M (obsAllT M cv (memory ++ [mF, bF]))))
        (vtNC + 3)).drop vtNC) bus.totals ∧
      cvr 0 = sqCvT M (obsAllT M cv (memory ++ [mF, bF])) ∧
      (∀ r < vtN layout, RunsToM M (roundPoly 4 (cl r) none) (cvr r) (wsr r) (cl (r + 1), ch r)
        (cvr (r + 1))) ∧
      evss.length = (vtRows layout bus ((List.range (vtN layout)).map ch).reverse).length ∧
      (∀ i (h1 : i < evss.length)
        (h2 : i < (vtRows layout bus ((List.range (vtN layout)).map ch).reverse).length),
        evss[i].length = (vtRows layout bus ((List.range (vtN layout)).map ch).reverse)[i].1.width) ∧
      (ttVal ((powers (challengeOf (sqCvT M (obsAllT M cv (memory ++ [mF, bF])))) (vtNC + 3)).take
          vtNC)
        ((powers (challengeOf (sqCvT M (obsAllT M cv (memory ++ [mF, bF])))) (vtNC + 3)).drop vtNC)
        ((List.range (vtN layout)).map ch).reverse
        (vtRows layout bus ((List.range (vtN layout)).map ch).reverse)
        evss 0 0 []).1 = cl (vtN layout) ∧
      ObsAns M (cvr (vtN layout)) evss.flatten ∧
      sqCvM M (obsAllT M (cvr (vtN layout)) evss.flatten) =
        some (sqCvT M (obsAllT M (cvr (vtN layout)) evss.flatten)) ∧
      claims = bus.claims ++
        (ttVal ((powers (challengeOf (sqCvT M (obsAllT M cv (memory ++ [mF, bF])))) (vtNC + 3)).take
            vtNC)
          ((powers (challengeOf (sqCvT M (obsAllT M cv (memory ++ [mF, bF])))) (vtNC + 3)).drop
            vtNC)
          ((List.range (vtN layout)).map ch).reverse
          (vtRows layout bus ((List.range (vtN layout)).map ch).reverse) evss 0 0 []).2 ++
        piClaims layout pi (challengeOf (sqCvT M (obsAllT M (cvr (vtN layout)) evss.flatten))) ∧
      cv' = sqCvT M (obsAllT M (cvr (vtN layout)) evss.flatten) := by
  unfold tablesSeg at h
  obtain ⟨x1, x2, bus1, cv1, e1, h1, k1⟩ := RunsToM.bind_inv' h
  obtain ⟨memory, mF, bF, hl, ex1, eb1, hA1, ec1⟩ := RunsToM.busRest_trace hbv h1
  obtain ⟨x3, x4, tc, cv3, e3, h3, k3⟩ := RunsToM.bind_inv' k1
  obtain ⟨x5, x6, pc, cv5, e5, h5, k5⟩ := RunsToM.bind_inv' k3
  obtain ⟨ex6, epc, ec6⟩ := RunsToM.pure_inv k5
  simp only [Prod.mk.injEq] at epc
  obtain ⟨rfl, rfl⟩ := epc
  -- the public input
  unfold publicInputPhase at h5
  obtain ⟨y1, y2, rm, cy1, f1, g1, k6⟩ := RunsToM.bind_inv' h5
  obtain ⟨fy1, hq2, frm⟩ := RunsToM.sampleEP_inv g1
  obtain ⟨fy2, fpc, fcy2⟩ := RunsToM.pure_inv k6
  -- the table phase
  unfold tablePhase at h3
  obtain ⟨z1, z2, xi, cz1, f2, g2, k7⟩ := RunsToM.bind_inv' h3
  obtain ⟨fz1, hq1, fxi⟩ := RunsToM.sampleEP_inv g2
  obtain ⟨z3, z4, tcl, cz3, f3, g3, k8⟩ := RunsToM.bind_inv' k7
  obtain ⟨fz4, ftc, fcz4⟩ := RunsToM.pure_inv k8
  unfold tableSumcheck at g3
  obtain ⟨w1, w2, ⟨chs, cl⟩, cw1, f4, g4, k9⟩ := RunsToM.bind_inv' g3
  obtain ⟨cl', cvr, wsr, ch, hc0, hcv0, hr, hws, hpt, hfin, hcvS⟩ :=
    RunsToM.sumcheck_inv _ _ _ _ _ _ _ g4
  obtain ⟨w3, w4, ⟨fin, tcs⟩, cw3, f5, g5, k10⟩ := RunsToM.bind_inv' k9
  obtain ⟨evss, hel, hew, fx, fr, hA2, fc⟩ := RunsToM.tableTerms_trace _ _ _ _ _ _ _ _ _ _ _ g5
  obtain ⟨w5, w6, u, cw5, f6, g6, k11⟩ := RunsToM.bind_inv' k10
  obtain ⟨hreq, fw5, fcw5⟩ := RunsToM.requireP_inv g6
  obtain ⟨fw6, ftcs, fcw6⟩ := RunsToM.pure_inv k11
  simp only [List.length_replicate] at hr hws hpt hfin hcvS
  subst e1 ex1 e3 f2 fz1 f3 f4 hws f5 fx f6 fw5 fw6 fz4 e5 f1 fy1 fy2 ex6
  subst ec1 hcvS fcw5 fcw6 fcz4 fc fcy2 frm fpc ftcs ftc hpt hfin
  obtain rfl := (sqCvT_eq hq1).symm
  obtain rfl := (sqCvT_eq hq2).symm
  subst fxi
  have hfin' : fin = cl' (vtN layout) := hreq
  have hf1 := congrArg Prod.fst fr
  have hf2 := congrArg Prod.snd fr
  simp only at hf1 hf2
  unfold vtN at hfin' ⊢
  unfold vtRows
  refine ⟨memory, mF, bF, cl', cvr, wsr, ch, evss, hl, eb1, by simp, hA1, hq1, hc0, hcv0,
    fun r hr' => ?_, hel, hew, by rw [← hf1, hfin'], hA2, hq2, ?_, ec6⟩
  · have := hr r (by simpa using hr')
    simpa using this
  · rw [← hf2]; rfl

end
end LeanVM.Guest.B1.VerifySub
