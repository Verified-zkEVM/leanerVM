import XmssSecurity.Proof.Bridge.Model
import XmssSecurity.Proof.Bridge.SchemeSeed
import XmssSecurity.Proof.Seeded.CountTransport
import XmssSecurity.Proof.CappedExpectedLanes

/-!
# The attributed count through the bridge

The model's expected count of hash calls after key generation that start with the key's parameter
(`expectedParameterQueries`) is at most the real one (`realAttributedMean`) plus the two seed
guesses' share: the bridge's hops are equalities in distribution, erasures and seed guesses, and the
count goes through each (`Seeded.CountTransport`).
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Bridge

open Seeded DeterministicSigning

set_option backward.isDefEq.respectTransparency false

-- Real key generation builds a tree of literal height; keep elaboration from unrolling it.
attribute [local irreducible] realKeygen

/-- The mean of a run's count, from a cache. -/
noncomputable def countMeanFrom {α : Type} (computation : OracleComp OracleWorld (α × Nat))
    (cache : QueryCache HashSpec) : ℝ≥0∞ :=
  ∑' r, Pr{let x ← ((simulateQ romImpl computation).run' cache)}[x = r] * (r.2 : ℝ≥0∞)

theorem isParameterQuery_hash (parameter : PublicParameter) :
    ∀ input, IsParameterQuery parameter input → (input matches .inr _) := by
  intro input h
  cases input with
  | inl _ => exact h.elim
  | inr _ => rfl

/-- The real game after the scheme's seed: real key generation, then the rest, counting the calls
that start with the key's parameter. -/
noncomputable def countedAfterSeed (adversary : LeanXmss.Security.Adversary) (seed : MasterSeed) :
    OracleComp OracleWorld (Bool × Nat) :=
  (liftM (realKeygen seed) : OracleComp OracleWorld _) >>= fun keys =>
    QueryCounting.counted (IsParameterQuery keys.1.parameter) (realRest adversary keys.1 keys.2)

/-- The real game, counting the calls after key generation that start with the key's parameter:
the key's seed, the seed hash, real key generation, then the counted rest. -/
noncomputable def realCounted (adversary : LeanXmss.Security.Adversary) :
    OracleComp OracleWorld (Bool × Nat) :=
  (liftM sampleMasterSeed : OracleComp OracleWorld _) >>= fun keySeed =>
    liftM (OracleWorld.query (.inr (LeanXmss.seedHashInput keySeed))) >>=
      countedAfterSeed adversary

/-- The real expected number of calls after key generation that start with the key's parameter. -/
noncomputable def realAttributedMean (adversary : LeanXmss.Security.Adversary) : ℝ≥0∞ :=
  countMeanFrom (realCounted adversary) ∅

/-! ## The scheme's seed -/

theorem countMeanFrom_lift_sample_bind {α β : Type} (sample : ProbComp β)
    (next : β → OracleComp OracleWorld (α × Nat)) (cache : QueryCache HashSpec) :
    countMeanFrom ((liftM sample : OracleComp OracleWorld β) >>= next) cache =
      ∑' b, Pr{let x ← sample}[x = b] * countMeanFrom (next b) cache := by
  unfold countMeanFrom
  rw [run'_lift_sample_bind, OracleComp.tsum_prEvent_bind_mul]

theorem countMeanFrom_le_of_seedHash (adversary : LeanXmss.Security.Adversary) (q : Nat)
    (hbound : SeededBudget adversary q) :
    countMeanFrom ((liftM sampleMasterSeed : OracleComp OracleWorld _) >>=
        countedAfterSeed adversary) ∅ ≤
      realAttributedMean adversary + ((q - 1) * (q - 1) : Nat) / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  have hreal : ((simulateQ romImpl (realCounted adversary)).run' ∅) =ᵈ
      (sampleMasterSeed >>= fun seed => sampleMasterSeed >>= fun keySeed =>
        (simulateQ romImpl (countedAfterSeed adversary seed)).run' (keySeedCache keySeed seed)) := by
    rw [realCounted, run'_lift_sample_bind]
    simp only [run'_query_bind, run_seedHash, bind_map_left]
    refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
    exact evalDist_sampleMasterSeed.symm.bind_left _
  have hrealMean : realAttributedMean adversary =
      ∑' seed, Pr{let x ← sampleMasterSeed}[x = seed] *
        ∑' keySeed, Pr{let x ← sampleMasterSeed}[x = keySeed] *
          countMeanFrom (countedAfterSeed adversary seed) (keySeedCache keySeed seed) := by
    unfold realAttributedMean countMeanFrom
    rw [tsum_prEvent_mul_congr hreal, OracleComp.tsum_prEvent_bind_mul]
    simp only [OracleComp.tsum_prEvent_bind_mul]
  rw [countMeanFrom_lift_sample_bind, hrealMean]
  calc
    _ ≤ ∑' seed, Pr{let x ← sampleMasterSeed}[x = seed] *
          (∑' keySeed, Pr{let x ← sampleMasterSeed}[x = keySeed] *
            countMeanFrom (countedAfterSeed adversary seed) (keySeedCache keySeed seed) +
          ((q - 1) * (q - 1) : Nat) / ((2 ^ 256 : Nat) : ℝ≥0∞)) := by
      refine ENNReal.tsum_le_tsum fun seed => mul_le_mul' le_rfl ?_
      have hrest : HashQueryBound ((liftM (realKeygen seed) : OracleComp OracleWorld _) >>=
          fun keys => realRest adversary keys.1 keys.2) ∅ (q - 1) := hbound seed
      have hseed : HashQueryBound (countedAfterSeed adversary seed) ∅ (q - 1) :=
        (hashQueryBound_bind_counted_iff (liftM (realKeygen seed))
          (fun keys => IsParameterQuery keys.1.parameter)
          (fun keys => realRest adversary keys.1 keys.2) ∅ (q - 1)).mpr hrest
      exact tsum_snd_random_cache_change_le guessBound_keySeedHit (countedAfterSeed adversary seed)
        (keySeedCache · seed) ∅ (fun keySeed => agreeOutside_keySeedCache keySeed seed) (q - 1)
        hseed (q - 1) (snd_le_of_mem_support_bind_counted (liftM (realKeygen seed))
          (fun keys => IsParameterQuery keys.1.parameter)
          (fun keys => isParameterQuery_hash keys.1.parameter)
          (fun keys => realRest adversary keys.1 keys.2) ∅ (q - 1) hrest)
    _ = _ := tsum_prEvent_mul_add_const _ _ _

/-! ## Presampling and erasure -/

/-- The table game's expected attributed count from the scheme's seed `S`. -/
noncomputable def tableMean (adversary : LeanXmss.Security.Adversary) (seed : MasterSeed) :
    ℝ≥0∞ :=
  ∑' d, Pr{let x ← drawDerivations}[x = d] *
    ∑' r, Pr{let x ← ((simulateQ randomOracle (honestRun d).withQueryLog).run
        (progCache seed d))}[x = r] *
      expectedSimulatedQueryCount romImpl (IsParameterQuery d.parameter)
        (Seeded.gameRest (tableScheme d.rnd) (toModelAdversary adversary)
          (modelPublicKey d r.1) (modelSecretKey d r.1)) r.2

theorem tableMean_le (adversary : LeanXmss.Security.Adversary) (seed : MasterSeed) :
    tableMean adversary seed ≤ countMeanFrom (countedAfterSeed adversary seed) ∅ := by
  have hpresample := evalDist_presample_computation (countedAfterSeed adversary seed)
    (liftM (preparation seed) : OracleComp OracleWorld _) ∅
  rw [lift_hash_romImpl] at hpresample
  have hsplit : countMeanFrom (countedAfterSeed adversary seed) ∅ =
      ∑' d, Pr{let x ← drawDerivations}[x = d] *
        ∑' r, Pr{let x ← ((simulateQ randomOracle (honestRun d).withQueryLog).run
            (progCache seed d))}[x = r] *
          countMeanFrom (countedAfterSeed adversary seed) r.2 := by
    unfold countMeanFrom
    rw [tsum_prEvent_mul_congr hpresample, OracleComp.tsum_prEvent_bind_mul,
      tsum_prEvent_mul_congr (run_preparation seed) (fun result =>
        ∑' r, Pr{let x ← ((simulateQ romImpl (countedAfterSeed adversary seed)).run'
          result.2)}[x = r] * (r.2 : ℝ≥0∞))]
    simp only [OracleComp.tsum_prEvent_bind_mul, OracleComp.tsum_prEvent_pure_mul]
  rw [hsplit]
  refine ENNReal.tsum_le_tsum fun d => mul_le_mul' le_rfl ?_
  refine ENNReal.tsum_le_tsum fun r => ?_
  by_cases hr : r ∈ support ((simulateQ randomOracle (honestRun d).withQueryLog).run
    (progCache seed d))
  · refine mul_le_mul' le_rfl ?_
    have h := prepared_of_mem seed d r.1 r.2 hr
    have hkeygen := (h.realKeygen).run_eq_pure
    have hrun : countMeanFrom (countedAfterSeed adversary seed) r.2 =
        expectedSimulatedQueryCount romImpl (IsParameterQuery d.parameter)
          (realRest adversary ⟨r.1.1.1, d.parameter⟩ ⟨seed, d.parameter, r.1.1.1⟩) r.2 := by
      unfold countMeanFrom countedAfterSeed
      rw [run'_lift_hash_bind, hkeygen, pure_bind]
      exact tsum_counted_eq_expectedSimulatedQueryCount _ _ _
    rw [hrun]
    exact (h.erases_rest adversary).expectedSimulatedQueryCount_le _ r.2 le_rfl
  · rw [(prEvent_eq_zero_of_not_mem_support _) hr, zero_mul, zero_mul]

/-! ## Seed elimination -/

/-- The clean table game's expected attributed count. -/
noncomputable def cleanMean (adversary : LeanXmss.Security.Adversary) : ℝ≥0∞ :=
  ∑' d, Pr{let x ← drawDerivations}[x = d] *
    ∑' p, Pr{let x ← ((simulateQ randomOracle (honestRun d).withQueryLog).run ∅)}[x = p] *
      expectedSimulatedQueryCount romImpl (IsParameterQuery d.parameter)
        (Seeded.gameRest (tableScheme d.rnd) (toModelAdversary adversary)
          (modelPublicKey d p.1) (modelSecretKey d p.1)) p.2

theorem tsum_mul_tsum_comm {α β : Type} (a : α → ℝ≥0∞) (f : α → β → ℝ≥0∞) :
    ∑' x, a x * ∑' y, f x y = ∑' y, ∑' x, a x * f x y := by
  simp_rw [← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_comm

theorem cleanMean_le (adversary : LeanXmss.Security.Adversary) (q : Nat) (hq : q < 2 ^ 256)
    (hbound : SeededBudget adversary q) :
    cleanMean adversary ≤
      ∑' seed, Pr{let x ← sampleMasterSeed}[x = seed] * tableMean adversary seed +
        ((q - keygenQueries) * (q - keygenQueries) : Nat) / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  let δ := ((q - keygenQueries) * (q - keygenQueries) : Nat) / ((2 ^ 256 : Nat) : ℝ≥0∞)
  let X := fun (d : Derivations) (p : ((Digest × (TopIndex → Option (Randomness × Encoding))) ×
      QueryLog HashSpec) × QueryCache HashSpec) (cache : QueryCache HashSpec) =>
    expectedSimulatedQueryCount romImpl (IsParameterQuery d.parameter)
      (Seeded.gameRest (tableScheme d.rnd) (toModelAdversary adversary)
        (modelPublicKey d p.1) (modelSecretKey d p.1)) cache
  have htable : ∀ seed, tableMean adversary seed =
      ∑' d, Pr{let x ← drawDerivations}[x = d] *
        ∑' p, Pr{let x ← ((simulateQ randomOracle (honestRun d).withQueryLog).run ∅)}[x = p] *
          X d p (overlay (progCache seed d) p.2) := by
    intro seed
    unfold tableMean
    refine tsum_congr fun d => congrArg _ ?_
    rw [run_progCache, OracleComp.tsum_prEvent_map_mul]
  calc
    cleanMean adversary ≤ ∑' d, Pr{let x ← drawDerivations}[x = d] *
        ∑' p, Pr{let x ← ((simulateQ randomOracle (honestRun d).withQueryLog).run ∅)}[x = p] *
          (∑' seed, Pr{let x ← sampleMasterSeed}[x = seed] * X d p (overlay (progCache seed d) p.2) +
            δ) := by
      refine ENNReal.tsum_le_tsum fun d => mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun p => ?_)
      by_cases hp : p ∈ support ((simulateQ randomOracle (honestRun d).withQueryLog).run ∅)
      · exact mul_le_mul' le_rfl (tsum_counted_random_cache_change_le guessBound_seedHit
          (IsParameterQuery d.parameter) (isParameterQuery_hash d.parameter) _
          (fun seed => overlay (progCache seed d) p.2) p.2
          (fun seed => agreeOutside_overlay_progCache seed d p.2) (q - keygenQueries)
          (cleanBudget adversary q hq hbound d hp).2)
      · rw [(prEvent_eq_zero_of_not_mem_support _) hp, zero_mul, zero_mul]
    _ ≤ (∑' d, Pr{let x ← drawDerivations}[x = d] *
        ∑' p, Pr{let x ← ((simulateQ randomOracle (honestRun d).withQueryLog).run ∅)}[x = p] *
          ∑' seed, Pr{let x ← sampleMasterSeed}[x = seed] * X d p (overlay (progCache seed d) p.2)) +
        δ := by
      simp only [tsum_prEvent_mul_add_const]
      exact le_rfl
    _ = _ := by
      congr 1
      simp only [htable]
      conv_rhs => rw [tsum_mul_tsum_comm]
      refine tsum_congr fun d => ?_
      simp_rw [mul_left_comm _ (Pr{let x ← drawDerivations}[x = d])]
      rw [ENNReal.tsum_mul_left]
      congr 1
      conv_rhs => rw [tsum_mul_tsum_comm]
      refine tsum_congr fun p => ?_
      simp_rw [mul_left_comm _ (Pr{let x ← ((simulateQ randomOracle
        (honestRun d).withQueryLog).run ∅)}[x = p])]
      rw [ENNReal.tsum_mul_left]

/-! ## Memoization and the model's signer -/

theorem expectedSimulatedQueryCount_presample {α β : Type}
    (predicate : OracleWorld.Domain → Prop) [DecidablePred predicate]
    (computation : OracleComp OracleWorld α) (preparation : OracleComp OracleWorld β)
    (cache : QueryCache HashSpec) :
    expectedSimulatedQueryCount romImpl predicate computation cache =
      ∑' result, Pr{let x ← ((simulateQ romImpl preparation).run cache)}[x = result] *
        expectedSimulatedQueryCount romImpl predicate computation result.2 := by
  rw [← tsum_counted_eq_expectedSimulatedQueryCount,
    tsum_prEvent_mul_congr (evalDist_presample_computation _ preparation cache),
    OracleComp.tsum_prEvent_bind_mul]
  simp only [tsum_counted_eq_expectedSimulatedQueryCount]

theorem expectedSimulatedQueryCount_runSigning_memoize_le {α : Type}
    {Request Answer : Type} [Fintype Request] [DecidableEq Request]
    (sign : Request → OracleComp HashSpec Answer)
    (predicate : OracleWorld.Domain → Prop) [DecidablePred predicate]
    (computation : OracleComp (OracleWorld + (Request →ₒ Answer)) α) (cache : QueryCache HashSpec) :
    expectedSimulatedQueryCount romImpl predicate (runSigning sign (memoize computation ∅)) cache ≤
      expectedSimulatedQueryCount romImpl predicate (runSigning sign computation) cache := by
  let preparation : OracleComp OracleWorld (Request → Answer) := liftM (prepareSigning sign)
  rw [expectedSimulatedQueryCount_presample predicate _ preparation cache,
    expectedSimulatedQueryCount_presample predicate _ preparation cache]
  refine ENNReal.tsum_le_tsum fun prepared => ?_
  by_cases hprepared : prepared ∈ support ((simulateQ romImpl preparation).run cache)
  · refine mul_le_mul' le_rfl ?_
    have hrun : simulateQ romImpl preparation = simulateQ randomOracle (prepareSigning sign) :=
      QueryImpl.simulateQ_add_liftM_right _ _ _
    rw [hrun] at hprepared
    have hknown := resolves_prepareSigning sign cache prepared hprepared
    exact (erases_memoize prepared.2 sign prepared.1 hknown computation ∅
      (fun request answer h => by simp at h)).expectedSimulatedQueryCount_le predicate
        prepared.2 le_rfl
  · rw [(prEvent_eq_zero_of_not_mem_support _) hprepared, zero_mul, zero_mul]

theorem expectedSimulatedQueryCount_table_memo_le (adversary : Adversary)
    (randomizers : RandomizerOutputs) (publicKey : PublicKey) (secretKey : XmssSecurity.SecretKey)
    (predicate : OracleWorld.Domain → Prop) [DecidablePred predicate]
    (cache : QueryCache HashSpec) :
    expectedSimulatedQueryCount romImpl predicate
        (Seeded.gameRest (tableScheme randomizers) (memoAdversary adversary) publicKey secretKey)
        cache ≤
      expectedSimulatedQueryCount romImpl predicate
        (Seeded.gameRest (tableScheme randomizers) adversary publicKey secretKey) cache := by
  let sign := fun (request : SignRequest) =>
    (tableSign randomizers secretKey request.leafIndex request.message :
      OracleComp HashSpec (Option Signature))
  rw [← runSigning_sourceGame, ← runSigning_sourceGame, ← snd_transcriptReduction]
  have hsnd : runSigning sign (Prod.snd <$> transcriptReduction publicKey adversary) =
      Prod.snd <$> runSigning sign (transcriptReduction publicKey adversary) := by
    simp only [runSigning, simulateQ_map]
  have hfst : runSigning sign (memoize (sourceGame publicKey adversary) ∅) =
      Prod.fst <$> runSigning sign (transcriptReduction publicKey adversary) := by
    rw [← fst_transcriptReduction]
    simp only [runSigning, simulateQ_map]
  change expectedSimulatedQueryCount romImpl predicate
      (runSigning sign (Prod.snd <$> transcriptReduction publicKey adversary)) cache ≤
    expectedSimulatedQueryCount romImpl predicate (runSigning sign (sourceGame publicKey adversary))
      cache
  rw [hsnd, expectedSimulatedQueryCount_map, ← expectedSimulatedQueryCount_map romImpl predicate
    Prod.fst, ← hfst]
  exact expectedSimulatedQueryCount_runSigning_memoize_le sign predicate _ cache

/-- Count one per hash call satisfying `predicate`, beside the cache. -/
noncomputable def costHashOf (predicate : HashInput → Prop) [DecidablePred predicate] :
    QueryImpl HashSpec (StateT CostState ProbComp) := fun input state => do
  let result ← (randomOracle input).run state.1
  return (result.1, result.2, state.2 + if predicate input then 1 else 0)

theorem run_costWorldOf (parameter : PublicParameter) {α : Type}
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (cost : Nat) :
    (simulateQ (worldHandler (costHashOf (IsParameterHashInput parameter))) computation).run
        (cache, cost) =
      (fun result => (result.1.1, result.2, cost + result.1.2)) <$>
        (simulateQ romImpl (QueryCounting.counted (IsParameterQuery parameter) computation)).run
          cache := by
  induction computation using OracleComp.inductionOn generalizing cache cost with
  | pure value =>
      simp only [simulateQ_pure, QueryCounting.counted_pure, StateT.run_pure, map_pure,
        Nat.add_zero]
  | query_bind input next ih =>
      have hstep : ((worldHandler (costHashOf (IsParameterHashInput parameter))) input).run
          (cache, cost) = (fun result => (result.1, result.2,
            cost + if IsParameterQuery parameter input then 1 else 0)) <$>
              (romImpl input).run cache := by
        cases input with
        | inl input => rfl
        | inr input =>
            change (do
              let result ← (randomOracle input).run cache
              pure (result.1, result.2,
                cost + if IsParameterHashInput parameter input then 1 else 0)) = _
            rw [bind_pure_comp]
            rfl
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        QueryCounting.counted_query_bind, simulateQ_pure, StateT.run_pure, map_bind, hstep,
        bind_map_left]
      apply bind_congr
      intro result
      rw [ih]
      simp only [map_pure, bind_pure_comp, Nat.add_assoc]

theorem expectedSimulatedQueryCount_eq_costWorldOf (parameter : PublicParameter) {α : Type}
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    expectedSimulatedQueryCount romImpl (IsParameterQuery parameter) computation cache =
      ∑' result, Pr{let x ← ((simulateQ (worldHandler (costHashOf (IsParameterHashInput parameter)))
          computation).run (cache, 0))}[x = result] * (result.2.2 : ℝ≥0∞) := by
  rw [run_costWorldOf, OracleComp.tsum_prEvent_map_mul,
    ← tsum_counted_run_eq_expectedSimulatedQueryCount]
  simp

theorem expectedSimulatedQueryCount_table_memo_eq (adversary : Adversary) (publicKey : PublicKey)
    (secretKey : XmssSecurity.SecretKey) (parameter : PublicParameter)
    (cache : QueryCache HashSpec) :
    ∑' randomizers, Pr{let x ← sampleRandomizerOutputs}[x = randomizers] *
        expectedSimulatedQueryCount romImpl (IsParameterQuery parameter)
          (Seeded.gameRest (tableScheme randomizers) (memoAdversary adversary) publicKey
            secretKey) cache =
      expectedSimulatedQueryCount romImpl (IsParameterQuery parameter)
        (Seeded.gameRest Concrete.scheme (memoAdversary adversary) publicKey secretKey) cache := by
  simp only [expectedSimulatedQueryCount_eq_costWorldOf]
  rw [← tsum_prEvent_mul_congr (evalDist_table_memo_run
    (costHashOf (IsParameterHashInput parameter)) adversary publicKey secretKey (cache, 0)),
    OracleComp.tsum_prEvent_bind_mul]

/-! ## The model's game -/

theorem evalDist_drawDerivations_withRnd {β : Type} (f : Derivations → ProbComp β) :
    (drawDerivations >>= fun d => sampleRandomizerOutputs >>= fun rnd => f (d.withRnd rnd)) =ᵈ
      (drawDerivations >>= f) := by
  unfold drawDerivations
  simp only [bind_assoc, pure_bind]
  apply EvalDistEq.bind_right
  intro param
  apply EvalDistEq.bind_right
  intro bottom
  apply EvalDistEq.bind_right
  intro top
  simp only [Derivations.withRnd]
  refine (OracleComp.EvalDistEq.bind_const sampleRandomizerOutputs
    (sampleTopRnd >>= fun topRnd => sampleRandomizerOutputs >>= fun rnd =>
      f ⟨param, bottom, top, rnd, topRnd⟩)).trans ?_
  exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

/-- The model's expected attributed count, from the table's view of key generation. -/
noncomputable def refMean (adversary : LeanXmss.Security.Adversary) : ℝ≥0∞ :=
  ∑' d, Pr{let x ← drawDerivations}[x = d] *
    ∑' p, Pr{let x ← ((simulateQ randomOracle (honestRun d).withQueryLog).run ∅)}[x = p] *
      expectedSimulatedQueryCount romImpl (IsParameterQuery d.parameter)
        (Seeded.gameRest Concrete.scheme (modelAdversary adversary)
          (modelPublicKey d p.1) (modelSecretKey d p.1)) p.2

theorem refMean_le_cleanMean (adversary : LeanXmss.Security.Adversary) :
    refMean adversary ≤ cleanMean adversary := by
  let H := fun (rnd : RandomizerOutputs) (d : Derivations) =>
    ∑' p, Pr{let x ← ((simulateQ randomOracle (honestRun d).withQueryLog).run ∅)}[x = p] *
      expectedSimulatedQueryCount romImpl (IsParameterQuery d.parameter)
        (Seeded.gameRest (tableScheme rnd) (modelAdversary adversary)
          (modelPublicKey d p.1) (modelSecretKey d p.1)) p.2
  have hmemo : ∑' d, Pr{let x ← drawDerivations}[x = d] * H d.rnd d ≤ cleanMean adversary := by
    unfold cleanMean
    refine ENNReal.tsum_le_tsum fun d => mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun p =>
      mul_le_mul' le_rfl ?_)
    exact expectedSimulatedQueryCount_table_memo_le (toModelAdversary adversary) d.rnd _ _ _ _
  refine le_trans (le_of_eq ?_) hmemo
  have hresample := tsum_prEvent_mul_congr (evalDist_drawDerivations_withRnd pure)
    (fun d => H d.rnd d)
  rw [bind_pure] at hresample
  rw [← hresample, OracleComp.tsum_prEvent_bind_mul]
  unfold refMean
  refine tsum_congr fun d => congrArg _ ?_
  rw [OracleComp.tsum_prEvent_bind_mul]
  simp only [OracleComp.tsum_prEvent_pure_mul]
  change _ = ∑' rnd, Pr{let x ← sampleRandomizerOutputs}[x = rnd] * H rnd d
  unfold H
  rw [tsum_mul_tsum_comm]
  refine tsum_congr fun p => ?_
  simp_rw [mul_left_comm _ (Pr{let x ← ((simulateQ randomOracle
    (honestRun d).withQueryLog).run ∅)}[x = p])]
  rw [ENNReal.tsum_mul_left]
  congr 1
  exact (expectedSimulatedQueryCount_table_memo_eq (toModelAdversary adversary) _ _ _ _).symm

theorem refMean_eq_expectedParameterQueries (adversary : LeanXmss.Security.Adversary) :
    refMean adversary = expectedParameterQueries Concrete.scheme (modelAdversary adversary) := by
  let H := fun (publicKey : PublicKey) (secretKey : XmssSecurity.SecretKey)
      (cache : QueryCache HashSpec) =>
    (simulateQ romImpl (QueryCounting.counted (IsParameterQuery publicKey.parameter)
      (Seeded.gameRest Concrete.scheme (modelAdversary adversary) publicKey secretKey))).run' cache
  have h := tsum_prEvent_mul_congr (evalDist_keygen H) (fun r => (r.2 : ℝ≥0∞))
  simp only [OracleComp.tsum_prEvent_bind_mul, H, tsum_counted_eq_expectedSimulatedQueryCount] at h
  exact h

/-! ## The bridge, for the attributed count -/

/-- **The attributed count through the bridge.** The model's expected attributed count for the
translated, memoized adversary is at most the real one plus the two seed guesses' share. -/
theorem expectedParameterQueries_le_realAttributedMean (adversary : LeanXmss.Security.Adversary)
    (q : Nat) (hq : q < 2 ^ 256) (hbound : SeededBudget adversary q) :
    expectedParameterQueries Concrete.scheme (modelAdversary adversary) ≤
      realAttributedMean adversary +
        (((q - 1) * (q - 1) : Nat) / ((2 ^ 256 : Nat) : ℝ≥0∞) +
          ((q - keygenQueries) * (q - keygenQueries) : Nat) / ((2 ^ 256 : Nat) : ℝ≥0∞)) := by
  rw [← refMean_eq_expectedParameterQueries]
  calc
    refMean adversary ≤ cleanMean adversary := refMean_le_cleanMean adversary
    _ ≤ ∑' seed, Pr{let x ← sampleMasterSeed}[x = seed] * tableMean adversary seed +
          ((q - keygenQueries) * (q - keygenQueries) : Nat) / ((2 ^ 256 : Nat) : ℝ≥0∞) :=
      cleanMean_le adversary q hq hbound
    _ ≤ countMeanFrom ((liftM sampleMasterSeed : OracleComp OracleWorld _) >>=
          countedAfterSeed adversary) ∅ +
          ((q - keygenQueries) * (q - keygenQueries) : Nat) / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
      rw [countMeanFrom_lift_sample_bind]
      gcongr with seed
      exact tableMean_le adversary seed
    _ ≤ _ := by
      rw [← add_assoc]
      gcongr
      exact countMeanFrom_le_of_seedHash adversary q hbound

end XmssSecurity.Bridge
