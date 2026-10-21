import Sphincs.MultiTrace
import Sphincs.BridgeDet

/-! **Expected hash calls from the experiment to the seed-free game.** The bridges from the
deterministic experiment to the seed-free experiment bound the probability of a win within the
budget. With the win replaced by any outcome they bound the probability that the experiment stays
within a budget `b` by the probability that the seed-free game capped at `b` finishes, up to the
seed terms `3 b / 2^256` (`completes_le_seedFree`). The capped seed-free game spends more than `b`
only if its run capped at `b` does not finish (`traceCost_cap_gt_le`), so summing over the budgets
below `q` bounds the expected hash calls of the seed-free game by those of the experiment
(`mean_seedFree_le_experiment`). -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.Stop

open HiddenCost GraphView

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- **A run capped at `q` spends more than `b ≤ q` only if the run capped at `b` stops.** -/
theorem traceCost_cap_gt_le {α : Type} (f : HashInput → HashOutput) (table : HiddenGraph.Table)
    (computation : OracleComp CostSpec α) :
    ∀ q b : ℕ, b ≤ q →
      Pr{let x ← costRun f table (cap computation q)}[b < traceCost x.2] ≤
        Pr{let x ← costRun f table (cap computation b)}[x.1 = none] := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro q b _
      rw [cap_pure', costRun_pure, prEvent_pure]
      simp [traceCost]
  | query_bind input next ih =>
      intro q b hbq
      rw [cap_query_bind' input next q, cap_query_bind' input next b]
      by_cases hb : sourceCost input ≤ b
      · rw [ite_eq_left (hb.trans hbq), ite_eq_left hb, costRun_query_bind, costRun_query_bind]
        simp only [OracleComp.prEvent_bind_eq_tsum, prEvent_map]
        refine ENNReal.tsum_le_tsum fun answer => mul_le_mul' le_rfl ?_
        refine le_trans (prEvent_mono_of_support _ _ _ fun result _ hresult => ?_)
          (ih answer (q - sourceCost input) (b - sourceCost input) (by omega))
        have h : b < traceCost (recorded input ++ result.2) := hresult
        rw [traceCost_append, recorded_cost] at h
        show b - sourceCost input < traceCost result.2
        omega
      · rw [ite_eq_right hb, costRun_pure, prEvent_pure]
        simp only [ite_true]
        exact prEvent_le_one _

end Sphincs.Security.Stop

namespace Sphincs.Security.DetValue

open HiddenCost GraphView Stop

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable (g : HashInput → HashOutput) (c : HiddenGraph.Table)

variable [Params]

open Internalize ForsPotential

/-! ### Finishing within the budget, memoized and averaged -/

theorem finishBool_done (parameter : PublicParameter) (data : PublicData) (L L' : QueryLog SigningSpec)
    (forgery : Forgery) (b : ℕ) :
    val g c (fun _ => True) (finishBool parameter data L forgery) b ≤
      val g c (fun _ => True) (finishBool parameter data L' forgery) b := by
  unfold finishBool
  refine val_bind_mono g c _ _ _ _ (fun v _ b' => ?_) b
  rw [val_pure, val_pure]

open Memo in
/-- Memoizing never makes a run finish within the budget less often. -/
theorem memo_done (parameter : PublicParameter) (data : PublicData) (rnd : Det.RTable) :
    ∀ (M : OracleComp AdvSpec Forgery) (record : Record) (L L' : QueryLog SigningSpec),
      MemoInv g c parameter data rnd record L L' → ∀ b,
        val g c (fun _ => True) (advDet parameter data rnd M L) b ≤
          val g c (fun _ => True) (advDet parameter data rnd (Prod.fst <$> (simulateQ memoImpl M).run record) L') b := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure forgery =>
      intro record L L' hinv b
      simp only [simulateQ_pure, StateT.run_pure, map_pure, advDet_pure]
      exact finishBool_done g c parameter data L L' forgery b
  | query_bind t next ih =>
      intro record L L' hinv b
      rw [memo_run_query_bind]
      rcases t with t | m
      · rw [memoImpl_world, bind_map_left, map_bind, advDet_world, advDet_world]
        exact val_bind_mono g c _ _ _ _ (fun v _ b' => ih v record L L' hinv b') b
      · cases hm : record m with
        | some σ =>
            rw [memoImpl_sign_some m record σ hm, pure_bind, advDet_sign]
            obtain ⟨hdet, hmemσ⟩ := hinv.1 m σ hm
            refine val_bind_le_of g c _ _ _ _ b fun x hx b' hb' => ?_
            rw [hdet, support_pure, Set.mem_singleton_iff] at hx
            subst hx
            refine le_trans (val_mono g c _ _ _ _ hb') (ih x record _ L' ⟨hinv.1, fun e => ?_, ?_⟩ b)
            · rw [List.mem_append, List.mem_singleton, hinv.2.1 e]
              constructor
              · rintro (h | rfl)
                · exact h
                · exact hmemσ
              · exact Or.inl
            · rw [List.length_append]
              exact le_trans hinv.2.2 (Nat.le_add_right _ _)
        | none =>
            rw [memoImpl_sign_none m record hm, bind_map_left, map_bind, advDet_sign, advDet_sign]
            obtain ⟨x0, hdet⟩ := signCostDet_det g c parameter data rnd m
            refine val_bind_mono g c _ _ _ _ (fun x hx b' => ?_) b
            rw [hdet, support_pure, Set.mem_singleton_iff] at hx
            subst hx
            refine ih x _ _ _ ⟨fun m' σ hm' => ?_, fun e => ?_, ?_⟩ b'
            · change Function.update record m (some x) m' = some σ at hm'
              by_cases heq : m' = m
              · subst heq
                rw [Function.update_self] at hm'
                cases hm'
                exact ⟨hdet, List.mem_append_right _ (List.mem_singleton_self _)⟩
              · rw [Function.update_of_ne heq] at hm'
                obtain ⟨h1, h2⟩ := hinv.1 m' σ hm'
                exact ⟨h1, List.mem_append_left _ h2⟩
            · rw [List.mem_append, List.mem_append, hinv.2.1 e]
            · rw [List.length_append, List.length_append]
              exact Nat.add_le_add_right hinv.2.2 _

theorem memo_game_done (parameter : PublicParameter) (data : PublicData) (rnd : Det.RTable)
    (adversary : Adversary) (b : ℕ) :
    val g c (fun _ => True) (Det.costGameDet parameter data rnd adversary) b ≤
      val g c (fun _ => True) (Det.costGameDet parameter data rnd (Memo.memoAdv adversary)) b := by
  unfold Det.costGameDet
  refine val_bind_mono g c _ _ _ _ (fun _ _ b' => ?_) b
  rw [costRestDet_eq, costRestDet_eq]
  change _ ≤ val g c (fun _ => True) (advDet parameter data rnd
    ((simulateQ Memo.memoImpl (adversary.main ⟨data.root, parameter⟩)).run' Memo.emptyRecord) []) b'
  rw [StateT.run'_eq]
  exact memo_done g c parameter data rnd _ Memo.emptyRecord [] []
    ⟨fun m σ h => by simp [Memo.emptyRecord] at h, fun e => Iff.rfl, le_rfl⟩ b'

theorem avg_game_done (parameter : PublicParameter) (data : PublicData) (adversary : Adversary)
    (hnr : adversary.NoRepeat) (b : ℕ) :
    ∑' rnd, Pr{let x ← ($ᵗ Det.RTable : ProbComp Det.RTable)}[x = rnd] *
        val g c (fun _ => True) (Det.costGameDet parameter data rnd adversary) b ≤
      val g c (fun _ => True) (costGame parameter data adversary) b := by
  unfold Det.costGameDet costGame
  refine val_bind_le_avg g c _ _ _ _ _ (fun _ _ b' => ?_) b
  simp only [costRestDet_eq, costRest_eq]
  exact avg_advDet g c _ parameter data _ [] [] (hnr _) b'

/-- **Finishing within the budget, memoized and averaged.** -/
theorem done_avg_le (parameter : PublicParameter) (data : PublicData) (adversary : Adversary)
    (hnr : (Memo.memoAdv adversary).NoRepeat) (b : ℕ) :
    Pr{let x ← (do
        let rnd ← ($ᵗ Det.RTable : ProbComp Det.RTable)
        costRun g c (cap (Det.costGameDet parameter data rnd adversary) b))}[∃ v, x.1 = some v ∧ True] ≤
      Pr{let x ← costRun g c (cap (costGame parameter data (Memo.memoAdv adversary)) b)}[∃ v, x.1 = some v ∧ True] := by
  rw [OracleComp.prEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' rnd, Pr{let x ← ($ᵗ Det.RTable : ProbComp Det.RTable)}[x = rnd] *
          val g c (fun _ => True) (Det.costGameDet parameter data rnd (Memo.memoAdv adversary)) b :=
      ENNReal.tsum_le_tsum fun rnd => mul_le_mul' le_rfl (memo_game_done g c parameter data rnd adversary b)
    _ ≤ _ := avg_game_done g c parameter data _ hnr b

end Sphincs.Security.DetValue

namespace Sphincs.Security.Det

open Completeness SeedCoupling Internalize Eager Short SeedModel _root_.Sphincs.Security.Graph Assembly Stop
  HiddenCost GraphView Reduce DetValue

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
attribute [local instance] Classical.propDecidable

variable [Params]

open SeedModel _root_.Sphincs.Security.Graph Assembly Eager in
noncomputable local instance detLabelsSampleableM : SampleableType CanonicalGraphLabels :=
  graphLabelsSampleable

/-! ### The bridges for any outcome -/

section Budgeted

attribute [local irreducible] experimentDet count2 leftRun rightRun sampleMasterSeed

/-- Internalizing long inputs never lowers the probability of an outcome within the budget. -/
theorem budgetedE_le_internalize (adversary : Adversary) (q : Nat) (E : Bool → Prop) :
    Pr{let result ← experimentDet adversary}[E result.1 ∧ result.2 ≤ q] ≤
      Pr{let result ← experimentDet (internalize adversary)}[E result.1 ∧ result.2 ≤ q] := by
  rw [(evalDist_experimentDet_internalize adversary).prEvent_eq,
    experimentDet_eq_rightRun, leftRun_eq_split, rightRun_eq_split, prEvent_map, prEvent_map,
    prEvent_map, prEvent_map]
  refine prEvent_mono_of_support _ _ _ fun result _ hresult => ⟨hresult.1, ?_⟩
  exact le_trans (Nat.le_add_right _ _) hresult.2

end Budgeted

/-- **The scheme seed, for any outcome.** -/
theorem budgetedE_le_master (adversary : Adversary) (q : ℕ) (E : Bool → Prop) :
    Pr{let result ← experimentDet (internalize adversary)}[E result.1 ∧ result.2 ≤ q] ≤
      Pr{let result ← experimentMasterDet (internalize adversary)}[E result.1 ∧ result.2 ≤ q] +
        q / (2 : ℝ≥0∞) ^ 256 := by
  set game := gameAfterMasterDet (internalize adversary)
  set run : (HashInput → HashOutput) → MasterSeed → ProbComp (Bool × ℕ) :=
    fun F master => simulateQ (fixedRom F) (countHashQueries (game master)) with hrun
  have hnew : experimentDet (internalize adversary) =ᵈ
      (($ᵗ Eager.Table : ProbComp Eager.Table) >>= fun table => sampleMasterSeed >>= fun master =>
        sampleMasterSeed >>= fun seed =>
          (fun result => (result.1, 1 + result.2)) <$>
            run (Function.update (extend ∅ table) (schemeSeedInput seed) master) master) := by
    rw [experimentDet, gameCoreDet_eq_sampling]
    refine (evalDist_counted_eager _ (OnlyW.gameAfterSeedDet_internalize adversary)).trans ?_
    conv_lhs => enter [2, seed, 2, table]; rw [fixed_gameAfterSeedDet]
    calc
      _ =ᵈ (sampleMasterSeed >>= fun seed => ($ᵗ Eager.Table : ProbComp Eager.Table) >>= fun table =>
            sampleMasterSeed >>= fun master =>
              (fun result => (result.1, 1 + result.2)) <$>
                run (Function.update (extend ∅ table) (schemeSeedInput seed) master) master) := by
        refine EvalDistEq.bind_right _ fun seed => ?_
        have h := evalDist_table_point ⟨schemeSeedInput seed, schemeSeedInput_short seed⟩
          (fun master table => (fun result => (result.1, 1 + result.2)) <$> run (extend ∅ table) master)
        simp only [extend_empty_update] at h
        refine EvalDistEq.trans ?_ h
        simp only [extend, dite_eq_left (schemeSeedInput_short seed), hrun]
        rfl
      _ =ᵈ _ := by
        refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
        refine EvalDistEq.bind_right _ fun table => ?_
        exact OracleComp.EvalDistEq.bind_bind_swap _ _ _
  have hold : experimentMasterDet (internalize adversary) =ᵈ
      (($ᵗ Eager.Table : ProbComp Eager.Table) >>= fun table => sampleMasterSeed >>= fun master =>
        run (extend ∅ table) master) := by
    rw [experimentMasterDet, gameCoreMasterDet]
    exact (evalDist_counted_eager _ (OnlyW.gameAfterMasterDet_internalize adversary)).trans
      (OracleComp.EvalDistEq.bind_bind_swap _ _ _)
  rw [hnew.prEvent_eq, hold.prEvent_eq]
  refine probEvent_bind_le_add_const _ _ _ _ _ _ fun table => ?_
  refine probEvent_bind_le_add_const _ _ _ _ _ _ fun master => ?_
  refine le_trans (probEvent_bind_mono _ _ _ _ fun seed => ?_) (probEvent_update_seed_le (game master)
    (extend ∅ table) master E q)
  rw [prEvent_map]
  exact prEvent_mono_of_support _ _ _ fun result _ hresult =>
    ⟨hresult.1, by have := hresult.2; simp only at this; omega⟩

/-- One sample, for any outcome. -/
theorem per_sampleDetE (adversary : Adversary) (q : Nat) (material : Material) (seed : MasterSeed)
    (answers : CanonicalGraphLabels) (table : Eager.Table) (rnd : RTable) (E : Bool → Prop) :
    Pr{let result ← (simulateQ (fixedRom (extend (preparedCache material seed answers)
          (plant (SeedModel.parameter material) seed table rnd)))
          (countHashQueries (gameAfterMasterDet adversary seed)))}[E result.1 ∧ result.2 ≤ q] ≤
      Pr{let x ← detRun adversary q material answers table rnd}[∃ v, x.1 = some v ∧ E v] +
        Pr{let result ← detRun adversary q material answers table rnd}[Hits (Marked seed) result.2] := by
  set table' := plant (SeedModel.parameter material) seed table rnd
  have hrun := (sample_costGameDet adversary material seed answers table rnd).trans
    (evalDist_fixedCostSource _ _ _)
  rw [(hrun).prEvent_eq, prEvent_map]
  refine le_trans (le_of_eq ?_) (le_trans (probEvent_costRun_le_cap (sampleFn material seed answers table')
    (sampleCoordinates material seed answers table')
    (costGameDet (SeedModel.parameter material) (publicData (labelsOf material answers)) rnd adversary)
    q E) ?_)
  · rfl
  · rw [sampleCoordinates_eq]
    exact probEvent_costRun_le (sampleFn material seed answers table') (graphFn material answers table)
      (graphCoordinates material answers) (Marked seed)
      (sampleFn_plant_agree material seed answers table rnd) _ (fun x => ∃ v, x.1 = some v ∧ E v)

attribute [local irreducible] experimentDet experimentMasterDet sampleMasterSeed

/-- **Seed elimination for finishing within the budget.** -/
theorem doneMaster_le_seedFree (adversary : Adversary) (q : Nat) :
    Pr{let result ← experimentMasterDet (internalize adversary)}[True ∧ result.2 ≤ q] ≤
      Pr{let x ← seedFreeExperiment (internalize (Memo.memoAdv adversary)) q}[∃ v, x.1 = some v ∧ True] +
        2 * (q / (2 : ℝ≥0∞) ^ 256) := by
  calc
    _ = Pr{let result ← (do
          let material ← sampleMaterial
          let seed ← sampleMasterSeed
          let answers ← $ᵗ CanonicalGraphLabels
          let table ← $ᵗ Eager.Table
          simulateQ (fixedRom (extend (preparedCache material seed answers) table))
            (countHashQueries (gameAfterMasterDet (internalize adversary) seed)))}[True ∧ result.2 ≤ q] :=
      (evalDist_experimentMasterDet_fixed adversary).prEvent_eq (fun result => True ∧ result.2 ≤ q)
    _ = Pr{let result ← (do
          let material ← sampleMaterial
          let seed ← sampleMasterSeed
          let answers ← $ᵗ CanonicalGraphLabels
          let table ← $ᵗ Eager.Table
          let rnd ← $ᵗ RTable
          simulateQ (fixedRom (extend (preparedCache material seed answers)
              (plant (SeedModel.parameter material) seed table rnd)))
            (countHashQueries (gameAfterMasterDet (internalize adversary) seed)))}[True ∧ result.2 ≤ q] := by
      refine EvalDistEq.prEvent_eq ?_ _
      refine EvalDistEq.bind_right _ fun material => EvalDistEq.bind_right _ fun seed =>
        EvalDistEq.bind_right _ fun answers => ?_
      exact evalDist_table_split (SeedModel.parameter material) seed _
    _ ≤ Pr{let x ← (do
          let material ← sampleMaterial
          let _seed ← sampleMasterSeed
          let answers ← $ᵗ CanonicalGraphLabels
          let table ← $ᵗ Eager.Table
          let rnd ← $ᵗ RTable
          detRun (internalize adversary) q material answers table rnd)}[∃ v, x.1 = some v ∧ True] +
        Pr{let pair ← (do
          let material ← sampleMaterial
          let seed ← sampleMasterSeed
          let answers ← $ᵗ CanonicalGraphLabels
          let table ← $ᵗ Eager.Table
          let rnd ← $ᵗ RTable
          (fun result => (seed, result)) <$> detRun (internalize adversary) q material answers table rnd)}[Hits (Marked pair.1) pair.2.2] := by
      refine probEvent_bind_le_add _ _ _ _ _ _ _ fun material => ?_
      refine probEvent_bind_le_add _ _ _ _ _ _ _ fun seed => ?_
      refine probEvent_bind_le_add _ _ _ _ _ _ _ fun answers => ?_
      refine probEvent_bind_le_add _ _ _ _ _ _ _ fun table => ?_
      refine probEvent_bind_le_add _ _ _ _ _ _ _ fun rnd => ?_
      rw [prEvent_map]
      exact per_sampleDetE (internalize adversary) q material seed answers table rnd (fun _ => True)
    _ ≤ Pr{let x ← seedFreeExperiment (internalize (Memo.memoAdv adversary)) q}[∃ v, x.1 = some v ∧ True] +
        2 * (q / (2 : ℝ≥0∞) ^ 256) := by
      refine add_le_add ?_ ?_
      · unfold seedFreeExperiment
        refine probEvent_bind_mono _ _ _ _ fun material => ?_
        refine probEvent_bind_le_of _ _ _ _ fun _ => ?_
        refine probEvent_bind_mono _ _ _ _ fun answers => ?_
        refine probEvent_bind_mono _ _ _ _ fun table => ?_
        unfold detRun seedFreeRun
        rw [Memo.internalize_memoAdv]
        exact done_avg_le (graphFn material answers table) (graphCoordinates material answers)
          (SeedModel.parameter material) (publicData (labelsOf material answers)) (internalize adversary)
          (noRepeat_internalize_memoAdv adversary) q
      · refine probEvent_bind_le_of _ _ _ _ fun material => ?_
        rw [(OracleComp.EvalDistEq.bind_bind_swap sampleMasterSeed
          ($ᵗ CanonicalGraphLabels) _).prEvent_eq]
        refine probEvent_bind_le_of _ _ _ _ fun answers => ?_
        rw [(OracleComp.EvalDistEq.bind_bind_swap sampleMasterSeed
          ($ᵗ Eager.Table) _).prEvent_eq]
        refine probEvent_bind_le_of _ _ _ _ fun table => ?_
        rw [(OracleComp.EvalDistEq.bind_bind_swap sampleMasterSeed
          ($ᵗ RTable) _).prEvent_eq]
        refine probEvent_bind_le_of _ _ _ _ fun rnd => ?_
        exact marked_hit_le (detRun (internalize adversary) q material answers table rnd)
          (fun result => result.2) q (fun result hresult => costRun_cap_cost_le _ _ _ q result hresult)

/-- **Staying within the budget is finishing the capped seed-free game**, up to `3 b / 2^256` for
naming the hidden seeds. -/
theorem completes_le_seedFree (adversary : Adversary) (b : Nat) :
    Pr{let result ← experimentDet adversary}[result.2 ≤ b] ≤
      Pr{let x ← seedFreeExperiment (internalize (Memo.memoAdv adversary)) b}[∃ v, x.1 = some v ∧ True] +
        3 * (b / (2 : ℝ≥0∞) ^ 256) := by
  calc
    _ = Pr{let result ← experimentDet adversary}[True ∧ result.2 ≤ b] :=
        prEvent_congr_of_support _ _ _ fun _ _ => ⟨fun h => ⟨trivial, h⟩, And.right⟩
    _ ≤ Pr{let result ← experimentDet (internalize adversary)}[True ∧ result.2 ≤ b] :=
        budgetedE_le_internalize adversary b (fun _ => True)
    _ ≤ Pr{let result ← experimentMasterDet (internalize adversary)}[True ∧ result.2 ≤ b] +
          b / (2 : ℝ≥0∞) ^ 256 := budgetedE_le_master adversary b (fun _ => True)
    _ ≤ Pr{let x ← seedFreeExperiment (internalize (Memo.memoAdv adversary)) b}[∃ v, x.1 = some v ∧ True] +
          2 * (b / (2 : ℝ≥0∞) ^ 256) + b / (2 : ℝ≥0∞) ^ 256 :=
        add_le_add (doneMaster_le_seedFree adversary b) le_rfl
    _ = _ := by ring

/-! ### Summing over the budgets -/

omit [Params] in
theorem mean_one {α : Type} (mx : ProbComp α) : mean mx (fun _ => 1) = 1 := by
  unfold mean
  simp only [mul_one]
  exact OracleComp.tsum_prEvent_eq_one mx

omit [Params] in
theorem prob_add_not {α : Type} (mx : ProbComp α) (E : α → Prop) :
    Pr{let x ← mx}[E x] + Pr{let x ← mx}[¬E x] = 1 := by
  rw [← mean_indicator, ← mean_indicator, ← mean_add]
  refine (congrArg (mean mx) (funext fun a => ?_)).trans (mean_one mx)
  by_cases h : E a <;> simp [h]

omit [Params] in
theorem natCast_min_eq_sum (n : ℕ) : ∀ q : ℕ,
    ((min n q : ℕ) : ℝ≥0∞) = ∑ b ∈ Finset.range q, if b < n then 1 else 0
  | 0 => by simp
  | q + 1 => by
      rw [Finset.sum_range_succ, ← natCast_min_eq_sum n q]
      by_cases h : q < n
      · rw [ite_eq_left h, show min n (q + 1) = min n q + 1 by omega, Nat.cast_add, Nat.cast_one]
      · rw [ite_eq_right h, add_zero, show min n (q + 1) = min n q by omega]

omit [Params] in
theorem mean_finset_sum {α : Type} (mx : ProbComp α) (s : Finset ℕ) (G : ℕ → α → ℝ≥0∞) :
    mean mx (fun a => ∑ b ∈ s, G b a) = ∑ b ∈ s, mean mx (G b) := by
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      unfold mean
      simp
  | insert b s hb ih =>
      simp only [Finset.sum_insert hb]
      rw [mean_add, ih]

omit [Params] in
/-- The mean of a count capped at `q` is the sum over `b < q` of the chance that it exceeds `b`. -/
theorem mean_min_eq_sum {α : Type} (mx : ProbComp α) (F : α → ℕ) (q : ℕ) :
    mean mx (fun a => ((min (F a) q : ℕ) : ℝ≥0∞)) = ∑ b ∈ Finset.range q, Pr{let a ← mx}[b < F a] := by
  simp only [natCast_min_eq_sum]
  rw [mean_finset_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact mean_indicator mx (fun a => b < F a)

/-- **A seed-free run capped at `q` spends more than `b ≤ q` at most as often as the experiment
leaves the budget `b`**, up to `3 b / 2^256`. -/
theorem seedFree_gt_le (adversary : Adversary) (q b : ℕ) (hbq : b ≤ q) :
    Pr{let x ← seedFreeExperiment (internalize (Memo.memoAdv adversary)) q}[b < traceCost x.2] ≤
      Pr{let r ← experimentDet adversary}[b < r.2] + 3 * (b / (2 : ℝ≥0∞) ^ 256) := by
  have hstop : Pr{let x ← seedFreeExperiment (internalize (Memo.memoAdv adversary)) q}[b < traceCost x.2] ≤
      Pr{let x ← seedFreeExperiment (internalize (Memo.memoAdv adversary)) b}[¬∃ v, x.1 = some v ∧ True] := by
    unfold seedFreeExperiment
    refine HiddenBridge.probEvent_bind_mono_support _ _ _ _ _ fun material _ => ?_
    refine HiddenBridge.probEvent_bind_mono_support _ _ _ _ _ fun answers _ => ?_
    refine HiddenBridge.probEvent_bind_mono_support _ _ _ _ _ fun table _ => ?_
    unfold seedFreeRun
    refine le_trans (traceCost_cap_gt_le _ _ _ q b hbq) (prEvent_mono_of_support _ _ _ fun x _ hx => ?_)
    rintro ⟨v, hv, -⟩
    rw [hx] at hv
    cases hv
  have hdone := completes_le_seedFree adversary b
  have h1 := prob_add_not (seedFreeExperiment (internalize (Memo.memoAdv adversary)) b)
    (fun x => ∃ v, x.1 = some v ∧ True)
  have h2 := prob_add_not (experimentDet adversary) (fun r => r.2 ≤ b)
  refine hstop.trans ?_
  set S := Pr{let x ← seedFreeExperiment (internalize (Memo.memoAdv adversary)) b}[∃ v, x.1 = some v ∧ True]
  set N := Pr{let x ← seedFreeExperiment (internalize (Memo.memoAdv adversary)) b}[¬∃ v, x.1 = some v ∧ True]
  set W := Pr{let r ← experimentDet adversary}[r.2 ≤ b]
  have hW : Pr{let r ← experimentDet adversary}[¬r.2 ≤ b] = Pr{let r ← experimentDet adversary}[b < r.2] :=
    prEvent_congr_of_support _ _ _ fun r _ => not_le
  rw [hW] at h2
  set G := Pr{let r ← experimentDet adversary}[b < r.2]
  have hWfin : W ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (prEvent_le_one _)
  refine (ENNReal.add_le_add_iff_left hWfin).1 ?_
  calc W + N ≤ (S + 3 * (b / (2 : ℝ≥0∞) ^ 256)) + N := add_le_add hdone le_rfl
    _ = (S + N) + 3 * (b / (2 : ℝ≥0∞) ^ 256) := by ring
    _ = (W + G) + 3 * (b / (2 : ℝ≥0∞) ^ 256) := by rw [h1, h2]
    _ = W + (G + 3 * (b / (2 : ℝ≥0∞) ^ 256)) := by ring

/-- **The expected hash calls of the capped seed-free game are at most those of the experiment**,
capped at the same budget, up to the seed terms. -/
theorem mean_seedFree_le_experiment (adversary : Adversary) (q : ℕ) :
    mean (seedFreeExperiment (internalize (Memo.memoAdv adversary)) q) (fun x => (traceCost x.2 : ℝ≥0∞)) ≤
      mean (experimentDet adversary) (fun r => ((min r.2 q : ℕ) : ℝ≥0∞)) +
        3 * ((q : ℝ≥0∞) * q / (2 : ℝ≥0∞) ^ 256) := by
  have hcap : mean (seedFreeExperiment (internalize (Memo.memoAdv adversary)) q) (fun x => (traceCost x.2 : ℝ≥0∞)) =
      mean (seedFreeExperiment (internalize (Memo.memoAdv adversary)) q)
        (fun x => ((min (traceCost x.2) q : ℕ) : ℝ≥0∞)) := by
    refine le_antisymm (mean_mono_support _ fun x hx => ?_) (mean_mono _ fun x => by exact_mod_cast min_le_left _ _)
    have hle : traceCost x.2 ≤ q := by
      unfold seedFreeExperiment at hx
      simp only [mem_support_bind_iff] at hx
      obtain ⟨material, -, answers, -, table, -, hx⟩ := hx
      exact costRun_cap_cost_le _ _ _ q x hx
    rw [min_eq_left hle]
  rw [hcap, mean_min_eq_sum, mean_min_eq_sum]
  calc ∑ b ∈ Finset.range q, Pr{let x ← seedFreeExperiment (internalize (Memo.memoAdv adversary)) q}[b < traceCost x.2]
      ≤ ∑ b ∈ Finset.range q, (Pr{let r ← experimentDet adversary}[b < r.2] + 3 * ((q : ℝ≥0∞) / 2 ^ 256)) := by
        refine Finset.sum_le_sum fun b hb => ?_
        have hbq : b ≤ q := (Finset.mem_range.1 hb).le
        refine (seedFree_gt_le adversary q b hbq).trans (add_le_add le_rfl (mul_le_mul' le_rfl ?_))
        exact ENNReal.div_le_div_right (by exact_mod_cast hbq) _
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        congr 1
        rw [mul_left_comm, mul_div_assoc]

end Sphincs.Security.Det

namespace Sphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView HiddenReveal HiddenBridge Eager Short
open Domination ForestPrice ForestSigner SphincsFors.Security.Domination PotentialA

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
attribute [local instance] Classical.propDecidable

variable [Params]

open Completeness SeedModel _root_.Sphincs.Security.Graph Assembly Reduce Internalize in
attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

open Completeness SeedModel _root_.Sphincs.Security.Graph Assembly Reduce Internalize

/-- The key's hash calls of the seed-free game are at most all its hash calls. -/
theorem mean_keyCharged_le (adversary : Adversary) (q : ℕ) :
    mean ($ᵗ HashOutput) (fun parameterOutput => mean (seedFreeFrom adversary q parameterOutput)
        fun x => min (q : ℝ≥0∞) (keyCharged parameterOutput x.2)) ≤
      mean (seedFreeExperiment adversary q) (fun x => (traceCost x.2 : ℝ≥0∞)) := by
  rw [mean_seedFree]
  refine mean_mono _ fun parameterOutput => mean_mono _ fun x => (min_le_right _ _).trans ?_
  exact_mod_cast chargedCost_le _ _

set_option maxRecDepth 100000 in
/-- **Small budgets, deterministic signer, paid by the expected hash calls**: the probability of a
win within `q` hash calls is at most `ρ / 2^128 / (1 − q ρ / 2^128)` times the expected hash calls of
the experiment capped at `q`, plus the sample-independent terms of `det_smallF_budgeted` without its
linear term. -/
theorem det_smallF_expected (hb : 0 < subtreeHeight) (adversary : Adversary) (q : ℕ)
    (hq : q < 2 ^ 256)
    (ρ : ℝ) (hN : Numeric ρ (((q - keygenCost : ℕ) : ℝ) / 2 ^ 128))
    (κ : ℚ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hκ : 2 - ρ + ((q - keygenCost : ℕ) : ℝ) / 2 ^ 128 +
      (signatureLimit : ℝ) * (123 * ((2 : ℝ) ^ subtreeHeight * 2 ^ 15)⁻¹) ≤ (κ : ℝ))
    (b N : ℕ) (hbb : subtreeHeight = b) (hNN : signatureLimit = N)
    (t : H0.PoisT) (o : H0.OptF) (on : H0.OptN) (hpt : H0.checkPT t = true) (qtop : ℕ)
    (hrt : H0.checkRate b N qtop t = true) (hqtop : q - keygenCost ≤ qtop)
    (ho : H0.checkOptF b t o = true) (hon : H0.checkOptN t on = true) (hcthr : (o.cthr : ℝ) ≤ ρ / 2 ^ 128)
    (hc : (q : ℝ≥0∞) * ENNReal.ofReal (ρ / 2 ^ 128) < 1) :
    Det.budgetedAdvantageDet adversary q ≤
      ENNReal.ofReal (ρ / 2 ^ 128) * (1 - (q : ℝ≥0∞) * ENNReal.ofReal (ρ / 2 ^ 128))⁻¹ *
          (mean (Det.experimentDet adversary) (fun r => ((min r.2 q : ℕ) : ℝ≥0∞)) +
            3 * ((q : ℝ≥0∞) * q / (2 : ℝ≥0∞) ^ 256)) +
        (smallRestF q o.B (κ * ((2 ^ b * on.En : ℚ) / 2)) +
          2 * lam (H0.LmaxOf (q - keygenCost)) 0 (q - keygenCost)) + smallFailF q * (2 : ℝ≥0∞)⁻¹ ^ 201 +
        3 * ((q : ℝ≥0∞) / 2 ^ 256) := by
  refine le_trans (Det.budgetedAdvantageDet_le_seedFree adversary q) (add_le_add ?_ le_rfl)
  refine le_trans (small_seedFree_trace hb (Memo.memoAdv adversary) (Memo.memoAdv_noRepeat adversary) q hq ρ hN
    κ hκ0 hκ1 hκ b N hbb hNN t o on hpt qtop hrt hqtop ho hon hcthr hc) ?_
  refine add_le_add (add_le_add (mul_le_mul' le_rfl ?_) le_rfl) (mul_le_mul' le_rfl expectedFail_le)
  exact (mean_keyCharged_le _ q).trans (Det.mean_seedFree_le_experiment adversary q)

end Sphincs.Security.ForsPotential
