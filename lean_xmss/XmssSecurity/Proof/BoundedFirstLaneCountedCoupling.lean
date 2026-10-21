import XmssSecurity.Proof.BoundedFirstLaneCoupling
import XmssSecurity.Proof.FirstLaneExpectedBound

/-!
# The bounded lane-1 coupling, counted

`relTriple_simulateQ_bind_bounded_firstLane` couples a left run with the eager first-lane run until
a combined hit, keeping the hazards below a pathwise budget. Here the coupling also carries a count
of the left state that bounds the hazards so far, on both branches: after a hit the left count keeps
growing, so the right trace's hazards up to its first hit stay below the final left count
(`relTriple_simulateQ_bind_bounded_firstLane_counted`).
-/

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity

set_option maxHeartbeats 2000000

/-- A left count that grows at every query and at the finish grows along a whole run. -/
theorem leftCount_le_of_mem_support_run
    {spec : OracleSpec ι}
    (leftImpl : QueryImpl spec (StateT σ₁ ProbComp))
    (leftFinish : α → σ₁ → ProbComp (β × σ₁))
    (leftCount : σ₁ → Nat)
    (stepMono : ∀ (input : spec.Domain) (state : σ₁)
      (result : spec.Range input × σ₁),
      result ∈ support ((leftImpl input).run state) → leftCount state ≤ leftCount result.2)
    (finishMono : ∀ (value : α) (state : σ₁) (result : β × σ₁),
      result ∈ support (leftFinish value state) → leftCount state ≤ leftCount result.2)
    (computation : OracleComp spec α) (state : σ₁) (result : β × σ₁)
    (hresult : result ∈ support ((simulateQ leftImpl computation).run state >>= fun handled =>
      leftFinish handled.1 handled.2)) :
    leftCount state ≤ leftCount result.2 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, pure_bind] at hresult
      exact finishMono value state result hresult
  | query_bind input next ih =>
      simp only [StateT.run_bind, simulateQ_bind, simulateQ_spec_query, bind_assoc,
        mem_support_bind_iff] at hresult
      obtain ⟨head, hhead, htail⟩ := hresult
      exact (stepMono input state head hhead).trans
        (ih head.1 head.2 (by simpa [mem_support_bind_iff] using htail))

theorem relTriple_simulateQ_bind_bounded_firstLane_counted
    {spec : OracleSpec ι}
    [Fintype Index] [DecidableEq Index]
    (table : Index → Digest)
    (leftImpl : QueryImpl spec (StateT σ₁ ProbComp))
    (rightImpl : QueryImpl spec
      (StateT σ₂ (OracleComp (FirstLaneOracleSimulation.World Index))))
    (leftFinish : α → σ₁ → ProbComp (β × σ₁))
    (rightFinish : α → σ₂ →
      OracleComp (FirstLaneOracleSimulation.World Index) (β × σ₂))
    (cost : spec.Domain → Nat)
    (stateRel : σ₁ → σ₂ →
      FirstLaneOracleSimulation.ActionTrace Index → Prop)
    (accounted : σ₁ → Nat → Prop)
    (leftCount : σ₁ → Nat) (extra : Nat)
    (Budget : OracleComp spec α → Nat → σ₁ → Prop)
    (stepBudget : ∀ (input : spec.Domain)
      (next : spec.Range input → OracleComp spec α) (fuel : Nat)
      (leftState : σ₁) (result : spec.Range input × σ₁),
      Budget (liftM (spec.query input) >>= next) fuel leftState →
      result ∈ support ((leftImpl input).run leftState) →
      cost input ≤ fuel ∧ Budget (next result.1) (fuel - cost input) result.2)
    (stepMono : ∀ (input : spec.Domain) (state : σ₁)
      (result : spec.Range input × σ₁),
      result ∈ support ((leftImpl input).run state) → leftCount state ≤ leftCount result.2)
    (finishMono : ∀ (value : α) (state : σ₁) (result : β × σ₁),
      result ∈ support (leftFinish value state) → leftCount state ≤ leftCount result.2)
    (stepCoupling : ∀ (used : Nat) (input : spec.Domain)
      (leftState : σ₁) (rightState : σ₂)
      (trace : FirstLaneOracleSimulation.ActionTrace Index),
      stateRel leftState rightState trace →
      FirstLaneOracleSimulation.hazardCount trace ≤ used →
      accounted leftState used →
      FirstLaneOracleSimulation.hazardCount trace ≤ leftCount leftState →
      RelTriple ((leftImpl input).run leftState)
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          ((rightImpl input).run rightState)).run)
        (fun leftResult rightResult =>
          ((leftResult.1 = rightResult.1.1 ∧
            stateRel leftResult.2 rightResult.1.2
              (trace ++ rightResult.2) ∧
            FirstLaneOracleSimulation.hazardCount
                (trace ++ rightResult.2) ≤ used + cost input ∧
            accounted leftResult.2 (used + cost input)) ∨
          (FirstLaneOracleSimulation.CombinedHit table
              (trace ++ rightResult.2) ∧
            FirstLaneOracleSimulation.hazardCount
                (trace ++ rightResult.2) ≤ used + cost input)) ∧
          FirstLaneOracleSimulation.hazardCount (trace ++ rightResult.2) ≤
            leftCount leftResult.2))
    (countLimit hitLimit : Nat)
    (terminalCoupling : ∀ (value : α) (used fuel : Nat)
      (leftState : σ₁) (rightState : σ₂)
      (trace : FirstLaneOracleSimulation.ActionTrace Index),
      Budget (pure value) fuel leftState →
      stateRel leftState rightState trace →
      FirstLaneOracleSimulation.hazardCount trace ≤ used →
      accounted leftState used →
      used + fuel ≤ countLimit →
      FirstLaneOracleSimulation.hazardCount trace ≤ leftCount leftState →
      RelTriple (leftFinish value leftState)
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (rightFinish value rightState)).run)
        (fun leftResult rightResult =>
          ((leftResult.1 = rightResult.1.1 ∧
            stateRel leftResult.2 rightResult.1.2
              (trace ++ rightResult.2) ∧
            FirstLaneOracleSimulation.hazardCount
                (trace ++ rightResult.2) ≤ countLimit) ∨
          FirstLaneOracleSimulation.CombinedHit table
            (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
              (trace ++ rightResult.2))) ∧
          FirstLaneOracleSimulation.stoppedHazards table
              (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
                (trace ++ rightResult.2)) ≤ leftCount leftResult.2 + extra))
    (used fuel : Nat)
    (computation : OracleComp spec α)
    (leftState : σ₁) (rightState : σ₂)
    (hbudget : Budget computation fuel leftState)
    (trace : FirstLaneOracleSimulation.ActionTrace Index)
    (hstate : stateRel leftState rightState trace)
    (hcount : FirstLaneOracleSimulation.hazardCount trace ≤ used)
    (haccounted : accounted leftState used)
    (hleftCount : FirstLaneOracleSimulation.hazardCount trace ≤ leftCount leftState)
    (htotal : used + fuel ≤ countLimit)
    (hlimits : countLimit ≤ hitLimit) :
    RelTriple
      ((simulateQ leftImpl computation).run leftState >>= fun result =>
        leftFinish result.1 result.2)
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table) (do
        let result ← (simulateQ rightImpl computation).run rightState
        rightFinish result.1 result.2)).run)
      (fun leftResult rightResult =>
        ((leftResult.1 = rightResult.1.1 ∧
          stateRel leftResult.2 rightResult.1.2
            (trace ++ rightResult.2) ∧
          FirstLaneOracleSimulation.hazardCount
              (trace ++ rightResult.2) ≤ countLimit) ∨
        FirstLaneOracleSimulation.CombinedHit table
          (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
            (trace ++ rightResult.2))) ∧
        FirstLaneOracleSimulation.stoppedHazards table
            (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
              (trace ++ rightResult.2)) ≤ leftCount leftResult.2 + extra) := by
  induction computation using OracleComp.inductionOn generalizing leftState
      rightState trace used fuel with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, pure_bind]
      exact terminalCoupling value used fuel leftState rightState trace hbudget
        hstate hcount haccounted htotal hleftCount
  | query_bind input next ih =>
      simp only [StateT.run_bind, simulateQ_bind, WriterT.run_bind',
        simulateQ_spec_query, bind_assoc]
      apply relTriple_bind (relTriple_with_support
        (stepCoupling used input leftState rightState trace hstate hcount
          haccounted hleftCount))
      intro headLeft headRight hhead
      have hnextBudget := stepBudget input next fuel leftState headLeft hbudget
        hhead.2.1
      obtain ⟨⟨hgoodOrHit, hheadCount⟩, hheadLeftSupport, _hheadRightSupport⟩ := hhead
      rcases hgoodOrHit with hgood | hhit
      · obtain ⟨hvalue, hnextState, hnextCount, hnextAccounted⟩ := hgood
        have hnextBudget' : Budget (next headRight.1.1)
            (fuel - cost input) headLeft.2 := by
          rw [← hvalue]
          exact hnextBudget.2
        let appendTrace := fun result :
            ((β × σ₂) × FirstLaneOracleSimulation.ActionTrace Index) =>
          Prod.map id (fun tail => headRight.2 ++ tail) result
        have hrec := ih headRight.1.1 (used + cost input)
          (fuel - cost input) headLeft.2 headRight.1.2 hnextBudget'
            (trace ++ headRight.2) hnextState hnextCount hnextAccounted hheadCount
              (by omega)
        rw [simulateQ_bind, WriterT.run_bind'] at hrec
        change RelTriple _ _ _ at hrec
        have hlifted : RelTriple
            (id <$> ((simulateQ leftImpl (next headRight.1.1)).run headLeft.2 >>=
              fun result => leftFinish result.1 result.2))
            (appendTrace <$>
              (do
                let handled ←
                  (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
                    ((simulateQ rightImpl
                      (next headRight.1.1)).run headRight.1.2)).run
                Prod.map id (fun tail => handled.2 ++ tail) <$>
                  (simulateQ
                    (FirstLaneOracleSimulation.eagerTraceImpl table)
                    (rightFinish handled.1.1 handled.1.2)).run))
            (fun leftResult rightResult =>
              ((leftResult.1 = rightResult.1.1 ∧
                stateRel leftResult.2 rightResult.1.2
                  (trace ++ rightResult.2) ∧
                FirstLaneOracleSimulation.hazardCount
                    (trace ++ rightResult.2) ≤ countLimit) ∨
              FirstLaneOracleSimulation.CombinedHit table
                (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
                  (trace ++ rightResult.2))) ∧
              FirstLaneOracleSimulation.stoppedHazards table
                  (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
                    (trace ++ rightResult.2)) ≤ leftCount leftResult.2 + extra) := by
          apply relTriple_map
          apply relTriple_post_mono hrec
          intro leftResult rightResult hresult
          simpa [appendTrace, Prod.map, List.append_assoc] using hresult
        rw [hvalue]
        change RelTriple _ (appendTrace <$> _) _
        simpa only [id_map] using hlifted
      · obtain ⟨hhitTrace, hnextCount⟩ := hhit
        have hnextLimit : FirstLaneOracleSimulation.hazardCount
            (trace ++ headRight.2) ≤ hitLimit := hnextCount.trans (by omega)
        have hprefix : FirstLaneOracleSimulation.enforceHazardTrace hitLimit
            (trace ++ headRight.2) = trace ++ headRight.2 :=
          FirstLaneOracleSimulation.enforceHazardTrace_eq_self_of_count_le
            (trace ++ headRight.2) hitLimit hnextLimit
        let leftRest := (simulateQ leftImpl (next headLeft.1)).run headLeft.2 >>=
          fun result => leftFinish result.1 result.2
        let rightRest := (do
          let handled ←
            (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
              ((simulateQ rightImpl
                (next headRight.1.1)).run headRight.1.2)).run
          Prod.map id (fun tail => handled.2 ++ tail) <$>
            (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
              (rightFinish handled.1.1 handled.1.2)).run)
        have hbase := relTriple_with_support (relTriple_true leftRest
          (Prod.map id (fun suffix => headRight.2 ++ suffix) <$> rightRest))
        have hmapped : RelTriple leftRest
            (Prod.map id (fun suffix => headRight.2 ++ suffix) <$> rightRest)
            (fun leftResult rightResult =>
              ((leftResult.1 = rightResult.1.1 ∧
                stateRel leftResult.2 rightResult.1.2
                  (trace ++ rightResult.2) ∧
                FirstLaneOracleSimulation.hazardCount
                    (trace ++ rightResult.2) ≤ countLimit) ∨
              FirstLaneOracleSimulation.CombinedHit table
                (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
                  (trace ++ rightResult.2))) ∧
              FirstLaneOracleSimulation.stoppedHazards table
                  (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
                    (trace ++ rightResult.2)) ≤ leftCount leftResult.2 + extra) := by
          apply relTriple_post_mono hbase
          intro leftResult mappedResult hresult
          obtain ⟨_, hleftSupport, hrightSupport⟩ := hresult
          rw [support_map] at hrightSupport
          obtain ⟨rightResult, _, rfl⟩ := hrightSupport
          have hgrow := leftCount_le_of_mem_support_run leftImpl leftFinish leftCount
            stepMono finishMono (next headLeft.1) headLeft.2 leftResult hleftSupport
          have hsplit : FirstLaneOracleSimulation.enforceHazardTrace hitLimit
              (trace ++ (headRight.2 ++ rightResult.2)) =
              (trace ++ headRight.2) ++
                FirstLaneOracleSimulation.enforceHazardTrace
                  (hitLimit - FirstLaneOracleSimulation.hazardCount (trace ++ headRight.2))
                  rightResult.2 := by
            rw [← List.append_assoc, FirstLaneOracleSimulation.enforceHazardTrace_append,
              hprefix]
          refine ⟨Or.inr ?_, ?_⟩
          · simp only [Prod.map_snd]
            rw [hsplit]
            exact FirstLaneOracleSimulation.CombinedHit.append_of_prefix table _ _ hhitTrace
          · simp only [Prod.map_snd]
            rw [hsplit]
            exact (FirstLaneOracleSimulation.stoppedHazards_append_of_hit table _ _
              hhitTrace).trans ((hheadCount.trans hgrow).trans (Nat.le_add_right _ _))
        exact hmapped

end XmssSecurity
