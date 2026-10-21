import Sphincs.BridgeSampleBoundF

/-! **A linear potential with a refund of the unused budget.** If the potential at budget `y` is at
least the final value plus `a · y`, every step keeps it in expectation while making the payments of
`interp_potential2`, the potential at the start bounds the expected final value, the payments and
`a` per unit of budget left at the end. Equivalently the final value and the payments are paid by
the start potential minus `a` times the budget, plus `a` per unit of budget spent: a potential whose
every unit of budget is worth at least `a` pays `a` per query. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.HiddenDebt

open HiddenCost HiddenBridge HiddenOutside HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

variable {D R A ι : Type} [Fintype ι] [SampleableType R]
variable (tg : Targeting D R ι) (initial : Cache D R) (model : HiddenRows.Model D R A ι)

/-- **Linear potential with two payments and a refund of the unused budget.** -/
theorem interp_potential_refund {α : Type} (IsFleaf : D → Prop) (Inv : DebtState D R ι → Prop)
    (Φ : ℕ → DebtState D R ι → ℝ≥0∞) (payoff : (ι → Digest) → DebtState D R ι → ℝ≥0∞)
    (pay pay2 refund : ℝ≥0∞)
    (hfinal : ∀ budget state, Inv state → endValue payoff state + refund * budget ≤ Φ budget state)
    (hstep : ∀ (input : (SourceCostSpec D R ι).Domain) budget state, Inv state → sourceCost input ≤ budget →
      ∑' result, Pr{let x ← costStep model input state}[x = result] * Φ (budget - sourceCost input) result.2 +
        pay * digestCount tg (recorded input) + pay2 * fleafCount IsFleaf (recorded input) ≤ Φ budget state)
    (hinv : ∀ input state, Inv state → ∀ result ∈ support (costStep model input state), Inv result.2)
    (computation : OracleComp (SourceCostSpec D R ι) α) :
    ∀ budget state, Inv state →
      ∑' out, Pr{let x ← interp tg initial model computation budget state}[x = out] *
        (endValue payoff out.2 + pay * digestCount tg out.1.2.2.1 + pay2 * fleafCount IsFleaf out.1.2.2.1 +
          refund * ((budget - traceCost out.1.2.2.1 : ℕ) : ℝ≥0∞)) ≤
        Φ budget state := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro budget state hstate
      rw [interp_pure, OracleComp.tsum_prEvent_pure_mul]
      simpa [digestCount, fleafCount, traceCost] using hfinal budget state hstate
  | query_bind input next ih =>
      intro budget state hstate
      rw [interp_query_bind]
      split_ifs with hcost
      · rw [OracleComp.tsum_prEvent_bind_mul]
        set c : ℝ≥0∞ := pay * digestCount tg (recorded input) + pay2 * fleafCount IsFleaf (recorded input)
          with hc
        calc ∑' result, Pr{let x ← costStep model input state}[x = result] *
              ∑' out, Pr{let x ← ((fun out => ((out.1.1, revealed input ++ out.1.2.1,
                  recorded input ++ out.1.2.2.1, touch tg initial state input ++ out.1.2.2.2), out.2)) <$>
                interp tg initial model (next result.1) (budget - sourceCost input) result.2)}[x = out] *
                (endValue payoff out.2 + pay * digestCount tg out.1.2.2.1 + pay2 * fleafCount IsFleaf out.1.2.2.1 +
                  refund * ((budget - traceCost out.1.2.2.1 : ℕ) : ℝ≥0∞))
            ≤ ∑' result, Pr{let x ← costStep model input state}[x = result] *
                (Φ (budget - sourceCost input) result.2 + c) := by
              refine ENNReal.tsum_le_tsum fun result => ?_
              by_cases hr : result ∈ support (costStep model input state)
              · refine mul_le_mul_right ?_ _
                rw [OracleComp.tsum_prEvent_map_mul]
                simp only [digestCount_append, fleafCount_append, traceCost_append, recorded_cost, Nat.cast_add]
                calc ∑' out, Pr{let x ← (interp tg initial model (next result.1) (budget - sourceCost input)
                        result.2)}[x = out] *
                      (endValue payoff out.2 + pay * ((digestCount tg (recorded input) : ℝ≥0∞) +
                        digestCount tg out.1.2.2.1) + pay2 * ((fleafCount IsFleaf (recorded input) : ℝ≥0∞) +
                        fleafCount IsFleaf out.1.2.2.1) +
                        refund * ((budget - (sourceCost input + traceCost out.1.2.2.1) : ℕ) : ℝ≥0∞))
                    = ∑' out, Pr{let x ← (interp tg initial model (next result.1) (budget - sourceCost input)
                          result.2)}[x = out] *
                        (endValue payoff out.2 + pay * digestCount tg out.1.2.2.1 +
                          pay2 * fleafCount IsFleaf out.1.2.2.1 +
                          refund * ((budget - sourceCost input - traceCost out.1.2.2.1 : ℕ) : ℝ≥0∞)) +
                      (∑' out, Pr{let x ← (interp tg initial model (next result.1)
                        (budget - sourceCost input) result.2)}[x = out]) * c := by
                      rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
                      refine tsum_congr fun out => ?_
                      rw [hc, Nat.sub_add_eq]
                      ring
                  _ ≤ Φ (budget - sourceCost input) result.2 + 1 * c :=
                      add_le_add (ih result.1 _ _ (hinv input state hstate result hr))
                        (mul_le_mul' (OracleComp.tsum_prEvent_le_one _) le_rfl)
                  _ = _ := by rw [one_mul]
              · rw [(prEvent_eq_zero_of_not_mem_support _) hr, zero_mul, zero_mul]
          _ = ∑' result, Pr{let x ← costStep model input state}[x = result] * Φ (budget - sourceCost input) result.2 +
                (∑' result, Pr{let x ← costStep model input state}[x = result]) * c := by
              rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
              refine tsum_congr fun result => ?_
              ring
          _ ≤ ∑' result, Pr{let x ← costStep model input state}[x = result] * Φ (budget - sourceCost input) result.2 +
                1 * c := add_le_add le_rfl (mul_le_mul' (OracleComp.tsum_prEvent_le_one _) le_rfl)
          _ ≤ _ := by
              rw [one_mul, hc, ← add_assoc]
              exact hstep input budget state hstate hcost
      · rw [OracleComp.tsum_prEvent_pure_mul]
        simpa [digestCount, fleafCount, traceCost] using hfinal budget state hstate

end Sphincs.Security.HiddenDebt

namespace Sphincs.Security.PotentialA

open Concrete HiddenGraph HiddenDebt HiddenBridge HiddenCost HiddenReveal

set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable [Params]

/-- **Every unit of budget of the linear potential is worth at least `ρ / 2^128`.** -/
theorem Ctx.endValue_add_le (K : Ctx) (hρ : K.ρ ≤ 2) (y : ℕ) (s : DebtState HashInput HashOutput Coordinate) :
    endValue K.payoff s + ENNReal.ofReal (K.ρ / 2 ^ 128) * y ≤ K.pot y s := by
  have h0 : K.pot 0 s + (y * ν) * K.rate s = K.pot y s := by
    simp only [Ctx.pot, Nat.cast_zero, zero_mul, add_zero]
  rw [← h0]
  refine add_le_add (K.endValue_le s 0) ?_
  have hrate : ENNReal.ofReal K.ρ ≤ K.rate s := by
    refine le_trans ?_ le_self_add
    refine le_trans ?_ le_self_add
    unfold Ctx.vrate
    split_ifs
    · rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
      exact ENNReal.ofReal_le_ofReal hρ
    · exact le_rfl
  have hν : ENNReal.ofReal (K.ρ / 2 ^ 128) ≤ ν * ENNReal.ofReal K.ρ := by
    rw [ν_eq_ofReal, ← ENNReal.ofReal_mul (by positivity), div_eq_inv_mul]
  calc ENNReal.ofReal (K.ρ / 2 ^ 128) * y ≤ ν * ENNReal.ofReal K.ρ * y := by gcongr
    _ ≤ ν * K.rate s * y := by gcongr
    _ = (y * ν) * K.rate s := by ring

section Sample

variable (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
  (remaining : RemainingOutputs) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
  (known : Knowledge Coordinate) (ρ : ℝ)

/-- **The linear potential of the small route, paid per hash call**: the expected final payoff and
payments are at most `ρ / 2^128` per unit of budget the run spends, whatever its budget. -/
theorem smallRoute_potential_pay
    (hknown : known ∈ support (exposeR (aboveList (truncateHash parameterOutput) prepared.1)
      (knownOf (truncateHash parameterOutput) fixed)))
    (tg : Targeting HashInput HashOutput Coordinate) (hdigest : tg.digest = ForestSigner.IsMsgInput)
    (total : ℕ) (hN : Numeric ρ ((total : ℝ) / 2 ^ 128))
    {α : Type} (comp : OracleComp (SourceCostSpec HashInput HashOutput Coordinate) α) :
    ∑' out, Pr{let x ← (interp tg prepared.2 (sampleModel parameterOutput highs) comp total
        (DebtState.start prepared.2 known))}[x = out] *
      (endValue (payoffA parameterOutput fixed highs remaining prepared known ρ) out.2 +
        ENNReal.ofReal (ρ / 2 ^ 128) * digestCount tg out.1.2.2.1 +
        ENNReal.ofReal ((ρ - 1 - (total : ℝ) / 2 ^ 128) / 2 ^ 128) *
          fleafCount (IsFchainIn (truncateHash parameterOutput)) out.1.2.2.1) ≤
      ENNReal.ofReal (ρ / 2 ^ 128) * ∑' out, Pr{let x ← (interp tg prepared.2 (sampleModel parameterOutput highs)
        comp total (DebtState.start prepared.2 known))}[x = out] * (traceCost out.1.2.2.1 : ℝ≥0∞) := by
  set K := ctxA parameterOutput fixed highs remaining prepared known ρ with hK
  set run := interp tg prepared.2 (sampleModel parameterOutput highs) comp total (DebtState.start prepared.2 known)
    with hrun
  set a : ℝ≥0∞ := ENNReal.ofReal (ρ / 2 ^ 128) with ha
  have hMp : (sampleModel parameterOutput highs).parse = HiddenGraph.parse K.p (candidateActive K.p) :=
    sampleModel_parse parameterOutput highs
  have hMi := sampleModel_incoming parameterOutput highs
  have hMo := sampleModel_outgoing parameterOutput highs
  have hρ2 : K.ρ ≤ 2 := hN.high
  have h := interp_potential_refund tg prepared.2 (sampleModel parameterOutput highs) (IsFchainIn K.p) K.Inv
    (K.potCap total) K.payoff (ENNReal.ofReal (K.ρ / 2 ^ 128))
    (ENNReal.ofReal ((K.ρ - 1 - (total : ℝ) / 2 ^ 128) / 2 ^ 128)) (ENNReal.ofReal (K.ρ / 2 ^ 128))
    (fun budget state _ => by
      unfold Ctx.potCap
      split_ifs
      · exact K.endValue_add_le hρ2 budget state
      · exact le_top)
    (fun input budget state hinv hcost => K.stepF (sampleModel parameterOutput highs) hMp hMi hMo tg hdigest hN
      (ctxA_sec parameterOutput fixed highs remaining prepared known ρ)
      (ctxA_msg parameterOutput fixed highs remaining prepared known ρ) input budget state hinv hcost)
    (fun input state hinv => K.inv_step (sampleModel parameterOutput highs) hMp hMi input state hinv)
    comp total (DebtState.start prepared.2 known)
    (inv_start parameterOutput fixed highs remaining prepared known ρ hknown)
  have hp : K.pot total (DebtState.start prepared.2 known) = ENNReal.ofReal (ρ * total / 2 ^ 128) :=
    pot_start K known (show (0 : ℝ) ≤ ρ by linarith [hN.low]) total
  have hstart : K.potCap total total (DebtState.start prepared.2 known) = a * total := by
    unfold Ctx.potCap
    rw [ite_eq_left le_rfl, hp, ha, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by linarith [hN.low])]
    congr 1
    ring
  rw [hstart] at h
  have hle : ∀ out ∈ support run, traceCost out.1.2.2.1 ≤ total := fun out hout =>
    interp_traceCost_le tg prepared.2 (sampleModel parameterOutput highs) comp total _ out hout
  have hsplit : ∑' out, Pr{let x ← run}[x = out] * ((total - traceCost out.1.2.2.1 : ℕ) : ℝ≥0∞) +
      ∑' out, Pr{let x ← run}[x = out] * (traceCost out.1.2.2.1 : ℝ≥0∞) = total := by
    rw [← ENNReal.tsum_add]
    calc ∑' out, (Pr{let x ← run}[x = out] * ((total - traceCost out.1.2.2.1 : ℕ) : ℝ≥0∞) +
          Pr{let x ← run}[x = out] * (traceCost out.1.2.2.1 : ℝ≥0∞))
        = ∑' out, Pr{let x ← run}[x = out] * (total : ℝ≥0∞) := by
          refine tsum_congr fun out => ?_
          rw [← mul_add]
          by_cases hout : out ∈ support run
          · rw [← Nat.cast_add, Nat.sub_add_cancel (hle out hout)]
          · rw [(prEvent_eq_zero_of_not_mem_support _) hout, zero_mul, zero_mul]
      _ = total := by rw [ENNReal.tsum_mul_right, HiddenDebt.interp_mass, one_mul]
  have hfin : a * ∑' out, Pr{let x ← run}[x = out] * ((total - traceCost out.1.2.2.1 : ℕ) : ℝ≥0∞) ≠ ⊤ := by
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top (ENNReal.natCast_ne_top total) ?_)
    rw [← hsplit]
    exact le_self_add
  have h' : ∑' out, Pr{let x ← run}[x = out] *
      (endValue (payoffA parameterOutput fixed highs remaining prepared known ρ) out.2 +
        a * digestCount tg out.1.2.2.1 +
        ENNReal.ofReal ((ρ - 1 - (total : ℝ) / 2 ^ 128) / 2 ^ 128) *
          fleafCount (IsFchainIn (truncateHash parameterOutput)) out.1.2.2.1 +
        a * ((total - traceCost out.1.2.2.1 : ℕ) : ℝ≥0∞)) ≤ a * total := h
  refine (ENNReal.add_le_add_iff_right hfin).1 ?_
  calc _ = ∑' out, Pr{let x ← run}[x = out] *
        (endValue (payoffA parameterOutput fixed highs remaining prepared known ρ) out.2 +
          a * digestCount tg out.1.2.2.1 +
          ENNReal.ofReal ((ρ - 1 - (total : ℝ) / 2 ^ 128) / 2 ^ 128) *
            fleafCount (IsFchainIn (truncateHash parameterOutput)) out.1.2.2.1 +
          a * ((total - traceCost out.1.2.2.1 : ℕ) : ℝ≥0∞)) := by
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
        refine tsum_congr fun out => ?_
        ring
    _ ≤ a * total := h'
    _ = _ := by
        rw [← hsplit, mul_add]
        ring

end Sample

end Sphincs.Security.PotentialA

namespace Sphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForestPrice ForestSigner HiddenReveal
  SphincsFors.Security.Domination
open HiddenBridge PotentialA

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

open Completeness SeedModel _root_.Sphincs.Security.Graph Assembly Reduce Internalize in
attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

open Completeness SeedModel _root_.Sphincs.Security.Graph Assembly Reduce Internalize

set_option maxRecDepth 100000 in
/-- **One sample of the small-budget route, the linear potential paid per hash call**: the
baseline `ρ / 2^128` is paid by every unit of budget the run spends instead of every unit of the
budget `q`; the cover, coin, near and cap terms are those of `sample_boundF`. -/
theorem sample_boundF_pay (hb : 0 < subtreeHeight) (adversary : Adversary) (hnr : adversary.NoRepeat) (q : ℕ)
    (hq : q < 2 ^ 256)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (known : Knowledge Coordinate)
    (hk : known ∈ support (exposeR (aboveList (truncateHash parameterOutput) prepared.1)
      (knownOf (truncateHash parameterOutput) fixed)))
    (ρ : ℝ) (hN : Numeric ρ (((q - keygenCost : ℕ) : ℝ) / 2 ^ 128))
    (κ : ℝ) (hκ : 2 - ρ + ((q - keygenCost : ℕ) : ℝ) / 2 ^ 128 +
      (signatureLimit : ℝ) * (123 * ((2 : ℝ) ^ subtreeHeight * 2 ^ 15)⁻¹) ≤ κ) (hκ1 : κ ≤ 1)
    (b N : ℕ) (hbb : subtreeHeight = b) (hNN : signatureLimit = N)
    (t : H0.PoisT) (o : H0.OptF) (on : H0.OptN) (hpt : H0.checkPT t = true) (qtop : ℕ)
    (hrt : H0.checkRate b N qtop t = true) (hqtop : q - keygenCost ≤ qtop)
    (ho : H0.checkOptF b t o = true) (hon : H0.checkOptN t on = true) (hcthr : (o.cthr : ℝ) ≤ ρ / 2 ^ 128) :
    Pr{let x ← (HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
        (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
          (sampleData parameterOutput fixed highs remaining)))) known prepared.2)}[(HiddenReveal.StopOr RichWin) x] ≤
      ENNReal.ofReal (ρ / 2 ^ 128) *
          ∑' out, Pr{let x ← (interp (targetingA parameterOutput fixed highs remaining prepared.1) prepared.2
            (sampleModel parameterOutput highs) (costGameX (truncateHash parameterOutput)
              (sampleData parameterOutput fixed highs remaining) (internalize adversary)) q
            (DebtState.start prepared.2 known))}[x = out] * (traceCost out.1.2.2.1 : ℝ≥0∞) +
        (((q - keygenCost : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (o.B : ℝ) + failMass (failSet prepared.1)) +
          signatureLimit * failMass (failSet prepared.1)) +
        ν * (((Nat.choose (q - keygenCost) 2 : ℕ) : ℝ≥0∞) * rateS) +
        (ENNReal.ofReal κ * ((((q - keygenCost : ℕ) : ℝ≥0∞) * ν) *
            ((q - keygenCost : ℕ) * ENNReal.ofReal (((2 ^ b * on.En : ℚ) / 2 : ℚ) : ℝ))) +
          (((q - keygenCost : ℕ) : ℝ≥0∞) * ν) *
            ((q - keygenCost : ℕ) * failMass (failSet prepared.1) + signatureLimit * failMass (failSet prepared.1))) +
        2 * lam (H0.LmaxOf (q - keygenCost)) 0 (q - keygenCost) := by
  set param := truncateHash parameterOutput with hparam
  set data := sampleData parameterOutput fixed highs remaining with hdata
  set model := sampleModel parameterOutput highs with hmodel
  set tgA := targetingA parameterOutput fixed highs remaining prepared.1 with htgA
  set start : State := DebtState.start prepared.2 known with hstart
  set run := interp tgA prepared.2 model (costGameX param data (internalize adversary)) q start with hrun
  set b0 : ℝ≥0∞ := ENNReal.ofReal (ρ / 2 ^ 128) with hb0
  set pay := payoffA parameterOutput fixed highs remaining prepared known ρ with hpay'
  set q' := q - keygenCost with hq'
  set c0 : ℝ≥0∞ := ENNReal.ofReal ((ρ - 1 - ((q' : ℕ) : ℝ) / 2 ^ 128) / 2 ^ 128) with hc0
  set IsF := IsFchainIn param with hIsF
  have hrunK : ∀ hK : keygenCost ≤ q, run = (fun out => ((out.1.1, out.1.2.1, Sum.inr keygenCost :: out.1.2.2.1,
      out.1.2.2.2), out.2)) <$> interp tgA prepared.2 model
        (advProg param data ((internalize adversary).main ⟨data.root, param⟩) []) q' start := fun hK => by
    rw [hrun]
    unfold costGameX
    rw [interp_tick_bind tgA prepared.2 model _ _ q start hK, costRestX_eq]
  have hrunA : ¬keygenCost ≤ q → run = pure ((none, [], [], []), start) := fun hK => by
    rw [hrun]
    unfold costGameX
    exact interp_tick_bind_abort tgA prepared.2 model _ _ q start hK
  have hA3 : ∑' out, Pr{let x ← run}[x = out] * (endValue pay out.2 + b0 * (digestCount tgA out.1.2.2.1 : ℝ≥0∞) +
      c0 * (fleafCount IsF out.1.2.2.1 : ℝ≥0∞)) ≤
      b0 * ∑' out, Pr{let x ← run}[x = out] * (traceCost out.1.2.2.1 : ℝ≥0∞) := by
    by_cases hK : keygenCost ≤ q
    · rw [hrunK hK, OracleComp.tsum_prEvent_map_mul, OracleComp.tsum_prEvent_map_mul]
      refine le_trans (le_of_eq ?_) ((smallRoute_potential_pay parameterOutput fixed highs remaining
        prepared known ρ hk tgA rfl q' hN (advProg param data ((internalize adversary).main ⟨data.root, param⟩) [])).trans
        (mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun out => mul_le_mul' le_rfl ?_)))
      · refine tsum_congr fun out => ?_
        simp only [digestCount_cons_inrF, fleafCount_cons_inr]
        rfl
      · simp only [traceCost, List.map_cons, List.sum_cons, Nat.cast_add]
        exact le_add_self
    · have hrunEq : run = interp tgA prepared.2 model (costGameX param data (internalize adversary)) 0 start := by
        rw [hrunA hK]
        unfold costGameX
        rw [interp_tick_bind_abort tgA prepared.2 model keygenCost _ 0 start (by omega)]
      rw [hrunEq]
      have hq0 : (q' : ℕ) = 0 := by omega
      rw [hc0, hq0]
      exact smallRoute_potential_pay parameterOutput fixed highs remaining prepared known ρ hk tgA rfl 0
        (numeric_monoF hN (by rw [hq0]) (by norm_num)) (costGameX param data (internalize adversary))
  exact sample_boundF_of hb adversary hnr q hq parameterOutput fixed highs remaining prepared hprepared known hk ρ κ
    hκ hκ1 b N hbb hNN t o on hpt qtop hrt hqtop ho hon hcthr _ hA3

end Sphincs.Security.ForsPotential
