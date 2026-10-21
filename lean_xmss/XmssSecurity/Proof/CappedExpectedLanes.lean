import XmssSecurity.Proof.CappedExpectedFirstLane
import XmssSecurity.Proof.Interface

/-!
# The model's bound on the attributed expected count

Both lanes count only hash calls that start with the key's parameter `P`: lane 1's hazards
(`CappedExpectedFirstLane`) and lane 2's encoding and structural calls (`IsEncodingHashQuery`,
`keygenStructuralTargetInput`). So the model's forgery probability is two units per expected
`P`-prefixed hash call after key generation (`expectedParameterQueries`), plus a constant and a
second-order term (`concreteScheme_afterKeygenSecurity_expected`).
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

/-- The expected number of hash calls after key generation that start with the key's parameter:
the adversary's, the signer's and the final verification's. -/
noncomputable def expectedParameterQueries {Key : Type} (scheme : Scheme Key)
    (adversary : Adversary) : ℝ≥0∞ :=
  ∑' keyResult, Pr{let x ← (simulateQ romImpl scheme.keygen).run ∅}[x = keyResult] *
    expectedSimulatedQueryCount romImpl (IsParameterQuery keyResult.1.1.parameter)
      (Seeded.gameRest scheme adversary keyResult.1.1 keyResult.1.2) keyResult.2

theorem expectedSimulatedQueryCount_le_bind {ι : Type} {spec : OracleSpec ι} {α β state : Type}
    (implementation : QueryImpl spec (StateT state ProbComp))
    (predicate : spec.Domain → Prop) [DecidablePred predicate]
    (head : OracleComp spec α) (continuation : α → OracleComp spec β) (initialState : state) :
    expectedSimulatedQueryCount implementation predicate head initialState ≤
      expectedSimulatedQueryCount implementation predicate (head >>= continuation)
        initialState := by
  rw [expectedSimulatedQueryCount_bind]
  exact le_self_add

theorem expectedSimulatedQueryCount_query
    {ι : Type} {spec : OracleSpec ι} {state : Type}
    (implementation : QueryImpl spec (StateT state ProbComp))
    (predicate : spec.Domain → Prop) [DecidablePred predicate]
    (input : spec.Domain) (initialState : state) :
    expectedSimulatedQueryCount implementation predicate
        (liftM (spec.query input) : OracleComp spec (spec.Range input)) initialState =
      if predicate input then 1 else 0 := by
  have h := expectedSimulatedQueryCount_query_bind implementation predicate input
    (fun output => (pure output : OracleComp spec (spec.Range input))) initialState
  rw [bind_pure] at h
  rw [h]
  simp

theorem precomputedKeygen_support_parameter_eq
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅)) :
    keyResult.1.2.parameter = keyResult.1.1.parameter := by
  change keyResult ∈ support ((simulateQ romImpl Concrete.precomputedKeygen).run ∅) at hmem
  unfold Concrete.precomputedKeygen at hmem
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff, simulateQ_pure,
    StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
  obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := hmem
  rfl

namespace CappedChain

/-- An adversary hash call attributable to the key with parameter `P`. -/
def AdversaryParameterQuery (parameter : PublicParameter) :
    (OracleWorld + SigningSpec).Domain → Prop
  | .inl input => IsParameterQuery parameter input
  | .inr _ => False

instance (parameter : PublicParameter) : DecidablePred (AdversaryParameterQuery parameter) :=
  fun input => match input with
    | .inl input => inferInstanceAs (Decidable (IsParameterQuery parameter input))
    | .inr _ => isFalse id

theorem adversaryParameterQuery_indicator (parameter : PublicParameter)
    (input : (OracleWorld + SigningSpec).Domain) :
    (if AdversaryParameterQuery parameter input then (1 : ℝ≥0∞) else 0) =
      (parameterHashCost parameter input : ℝ≥0∞) := by
  rcases input with (worldInput | request)
  · rcases worldInput with n | hashInput
    · simp [AdversaryParameterQuery, IsParameterQuery, parameterHashCost, oracleParameterCost]
    · by_cases h : IsParameterHashInput parameter hashInput <;>
        simp [AdversaryParameterQuery, IsParameterQuery, parameterHashCost, oracleParameterCost, h]
  · simp [AdversaryParameterQuery, parameterHashCost]

/-- The adversary's attributable calls, interpreted by the direct traced oracle, are at most the
attributable calls of the mapped adversary in the random oracle. -/
theorem expectedSimulatedQueryCount_sourceDirectTraced_le
    (publicKey : PublicKey) (secretKey : SecretKey) (parameter : PublicParameter)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) (trace : AttackerActionTrace) :
    expectedSimulatedQueryCount (sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
        (AdversaryParameterQuery parameter) computation (cache, trace) ≤
      expectedSimulatedQueryCount romImpl (IsParameterQuery parameter)
        (simulateQ (sourceUnloggedMappedAdversaryImpl publicKey secretKey) computation)
          cache := by
  induction computation using OracleComp.inductionOn generalizing cache trace with
  | pure value => simp
  | query_bind input next ih =>
      rw [expectedSimulatedQueryCount_query_bind, simulateQ_query_bind,
        expectedSimulatedQueryCount_bind]
      have hstep : ∀ cache trace, (sourceDirectTracedMappedAdversaryImpl publicKey secretKey
          input).run (cache, trace) =
          (fun result => (result.1, (result.2, trace ++ attackerActionFragment input result.1))) <$>
            (simulateQ romImpl (sourceUnloggedMappedAdversaryImpl publicKey secretKey input)).run
              cache := by
        intro cache trace
        unfold sourceDirectTracedMappedAdversaryImpl actionTracedStateImpl
        rw [sourceDirectMappedAdversaryImpl_eq_compose]
        simp [QueryImpl.apply_compose, map_eq_bind_pure_comp]
      rw [hstep, OracleComp.tsum_prEvent_map_mul]
      refine add_le_add ?_ (ENNReal.tsum_le_tsum fun result =>
        mul_le_mul' le_rfl (ih result.1 result.2 _))
      rcases input with (worldInput | request)
      · have hquery : expectedSimulatedQueryCount romImpl (IsParameterQuery parameter)
            (liftM (sourceUnloggedMappedAdversaryImpl publicKey secretKey
              (OracleSpec.query (spec := OracleWorld + SigningSpec) (.inl worldInput)).input))
              cache =
            if IsParameterQuery parameter worldInput then 1 else 0 :=
          expectedSimulatedQueryCount_query romImpl _ worldInput cache
        rw [hquery]
        by_cases h : IsParameterQuery parameter worldInput <;>
          simp [AdversaryParameterQuery, h]
      · simp [AdversaryParameterQuery]

/-- The adversary's attributable hash inputs, recorded by the traced game, are at most the
attributable calls of the game after key generation. -/
theorem attributedMean_afterKeygen_le
    (adversary : Adversary) (publicKey : PublicKey) (secretKey : SecretKey)
    (cache : QueryCache HashSpec) :
    ∑' x, Pr{let y ← (cappedDetailedGameAfterKeygenWithBothTraces adversary publicKey
        secretKey cache)}[y = x] * (attributedHashInputs publicKey.parameter x.2.2 : ℝ≥0∞) ≤
      expectedSimulatedQueryCount romImpl (IsParameterQuery publicKey.parameter)
        (cappedSourceUnloggedDetailedGameAfterKeygen adversary publicKey secretKey) cache := by
  let attributed := fun state : (((QueryCache HashSpec × SigningCacheTrace) ×
      EncodingActionTrace) × AttackerActionTrace) =>
    (attributedHashInputs publicKey.parameter state.2 : ℝ≥0∞)
  have hadversary :
      ∑' x, Pr{let y ← (cappedDetailedGameAfterKeygenWithBothTraces adversary publicKey
        secretKey cache)}[y = x] * (attributedHashInputs publicKey.parameter x.2.2 : ℝ≥0∞) =
      ∑' x, Pr{let y ← (simulateQ (cappedBothTracedMappedAdversaryImpl publicKey secretKey)
        (adversary.main publicKey)).run ((((cache, []), []), []))}[y = x] * attributed x.2 := by
    unfold cappedDetailedGameAfterKeygenWithBothTraces
    rw [OracleComp.tsum_prEvent_bind_mul]
    refine tsum_congr fun result => ?_
    congr 1
    rw [OracleComp.tsum_prEvent_bind_mul]
    simp only [OracleComp.tsum_prEvent_pure_mul]
    exact tsum_prEvent_mul_const _ _
  have hdirect :
      ∑' x, Pr{let y ← (simulateQ (cappedBothTracedMappedAdversaryImpl publicKey secretKey)
        (adversary.main publicKey)).run ((((cache, []), []), []))}[y = x] * attributed x.2 =
      ∑' x, Pr{let y ← (simulateQ (sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
        (adversary.main publicKey)).run (cache, [])}[y = x] *
          (attributedHashInputs publicKey.parameter x.2.2 : ℝ≥0∞) := by
    rw [← cappedBothTracedMappedAdversaryImpl_actionProjection publicKey secretKey
      (adversary.main publicKey) ((cache, []), []) [], OracleComp.tsum_prEvent_map_mul]
    rfl
  rw [hadversary, hdirect]
  calc
    _ ≤ (attributedHashInputs publicKey.parameter [] : ℝ≥0∞) +
        expectedSimulatedQueryCount (sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
          (AdversaryParameterQuery publicKey.parameter) (adversary.main publicKey) (cache, []) := by
      refine expectedResource_le_initial_add_expectedSimulatedQueryCount
        (sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
        (AdversaryParameterQuery publicKey.parameter)
        (fun state => (attributedHashInputs publicKey.parameter state.2 : ℝ≥0∞)) ?_
        (adversary.main publicKey) (cache, [])
      intro input state result hresult
      unfold sourceDirectTracedMappedAdversaryImpl actionTracedStateImpl at hresult
      simp only [StateT.run_mk, mem_support_bind_iff, mem_support_pure_iff] at hresult
      obtain ⟨step, _, rfl⟩ := hresult
      rw [adversaryParameterQuery_indicator, attributedHashInputs_append,
        attributedHashInputs_fragment]
      push_cast
      exact le_rfl
    _ = expectedSimulatedQueryCount (sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
          (AdversaryParameterQuery publicKey.parameter) (adversary.main publicKey) (cache, []) := by
      simp [attributedHashInputs, AttackerActionTrace.hashInputs]
    _ ≤ expectedSimulatedQueryCount romImpl (IsParameterQuery publicKey.parameter)
          (simulateQ (sourceUnloggedMappedAdversaryImpl publicKey secretKey)
            (adversary.main publicKey)) cache :=
      expectedSimulatedQueryCount_sourceDirectTraced_le publicKey secretKey _ _ cache []
    _ ≤ _ := by
      unfold cappedSourceUnloggedDetailedGameAfterKeygen
      exact expectedSimulatedQueryCount_le_bind romImpl _ _ _ cache

end CappedChain

open CappedChain

/-! ## The model's expected count -/

theorem expectedSimulatedQueryCount_gameRest_eq_cappedSource
    (adversary : Adversary) (publicKey : PublicKey) (secretKey : SecretKey)
    (predicate : OracleWorld.Domain → Prop) [DecidablePred predicate]
    (cache : QueryCache HashSpec) :
    expectedSimulatedQueryCount romImpl predicate
        (Seeded.gameRest Concrete.scheme adversary publicKey secretKey) cache =
      expectedSimulatedQueryCount romImpl predicate
        (cappedSourceUnloggedDetailedGameAfterKeygen adversary publicKey secretKey) cache := by
  have hrest : GameOutcome.won <$>
      detailedGameAfterKeygen Concrete.scheme adversary publicKey secretKey =
        Seeded.gameRest Concrete.scheme adversary publicKey secretKey := by
    classical
    simp [Seeded.gameRest, detailedGameAfterKeygen, GameOutcome.won]
  rw [← hrest, expectedSimulatedQueryCount_map,
    ← cappedDetailedGameAfterKeygen_unloggedProjection, expectedSimulatedQueryCount_map]

theorem sourceAttributedMean_le (adversary : Adversary) :
    sourceAttributedMean adversary ≤
      expectedParameterQueries Concrete.scheme adversary +
        ((verifyHashBound + forgeryProbeCount : Nat) : ℝ≥0∞) := by
  unfold sourceAttributedMean
  have hsplit : ∀ x : SourceGlobalExactTracedProgramResult,
      ((attributedHashInputs x.1.publicKey.parameter x.2.2.2 + verifyHashBound +
        forgeryProbeCount : Nat) : ℝ≥0∞) =
      (attributedHashInputs x.1.publicKey.parameter x.2.2.2 : ℝ≥0∞) +
        ((verifyHashBound + forgeryProbeCount : Nat) : ℝ≥0∞) := by
    intro x
    push_cast
    ring
  simp_rw [hsplit]
  rw [tsum_prEvent_mul_add_const]
  gcongr
  let observe := fun y : CappedBothTraceGameResult =>
    (attributedHashInputs y.1.1.1.parameter y.2.2.2 : ℝ≥0∞)
  calc
    _ = ∑' y, Pr{let z ← (sourceGlobalExactProgramResult <$>
          sourceGlobalExactTracedProgram adversary)}[z = y] * observe y := by
      rw [OracleComp.tsum_prEvent_map_mul]
      rfl
    _ = ∑' y, Pr{let z ← cappedDetailedGameWithKeygenCacheAndBothTraces adversary}[z = y] *
          observe y :=
      tsum_prEvent_mul_congr (evalDist_sourceGlobalExact_eq_cappedBothTraces adversary) _
    _ ≤ _ := by
      unfold cappedDetailedGameWithKeygenCacheAndBothTraces expectedParameterQueries
      rw [OracleComp.tsum_prEvent_bind_mul]
      refine ENNReal.tsum_le_tsum fun keyResult => mul_le_mul' le_rfl ?_
      rw [OracleComp.tsum_prEvent_bind_mul]
      simp only [OracleComp.tsum_prEvent_pure_mul, observe]
      rw [expectedSimulatedQueryCount_gameRest_eq_cappedSource]
      exact CappedChain.attributedMean_afterKeygen_le adversary keyResult.1.1 keyResult.1.2
        keyResult.2

/-! ## Lane 2 counts attributable calls -/

theorem CappedSuffix.keygenChainTargetInput_eq_self_of_not (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput)
    (hinput : ¬IsParameterHashInput secretKey.parameter input) :
    CappedSuffix.keygenChainTargetInput secretKey cache input = input := by
  unfold CappedSuffix.keygenChainTargetInput
  split_ifs with h
  · obtain ⟨_, _, rfl⟩ := h
    exact (hinput (isParameterHashInput_tweakableHashInput _ _ _)).elim
  · rfl

theorem CappedLeaf.keygenLeafTargetInput_eq_self_of_not (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput)
    (hinput : ¬IsParameterHashInput secretKey.parameter input) :
    CappedLeaf.keygenLeafTargetInput secretKey cache input = input := by
  unfold CappedLeaf.keygenLeafTargetInput
  split_ifs with h
  · obtain ⟨_, _, rfl⟩ := h
    exact (hinput (isParameterHashInput_tweakableHashInput _ _ _)).elim
  · rfl

theorem CappedMerkle.keygenMerkleTargetInput_eq_self_of_not (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput)
    (hinput : ¬IsParameterHashInput secretKey.parameter input) :
    CappedMerkle.keygenMerkleTargetInput secretKey cache input = input := by
  unfold CappedMerkle.keygenMerkleTargetInput
  split_ifs with h
  · obtain ⟨_, _, _, rfl⟩ := h
    exact (hinput (isParameterHashInput_tweakableHashInput _ _ _)).elim
  · rfl

theorem CappedTop.keygenTopTargetInput_eq_self_of_not (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput)
    (hinput : ¬IsParameterHashInput secretKey.parameter input) :
    CappedTop.keygenTopTargetInput secretKey cache input = input := by
  unfold CappedTop.keygenTopTargetInput
  split_ifs with h1 h2 h3 h4
  · obtain ⟨_, _, rfl⟩ := h1
    exact (hinput (isParameterHashInput_tweakableHashInput _ _ _)).elim
  · obtain ⟨_, _, rfl⟩ := h2
    exact (hinput (isParameterHashInput_tweakableHashInput _ _ _)).elim
  · obtain ⟨_, _, _, rfl⟩ := h3
    exact (hinput (isParameterHashInput_tweakableHashInput _ _ _)).elim
  · obtain ⟨_, _, rfl⟩ := h4
    exact (hinput (isParameterHashInput_tweakableHashInput _ _ _)).elim
  · rfl

theorem isParameterHashInput_of_keygenStructuralTargetInput_ne (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput)
    (hne : keygenStructuralTargetInput secretKey cache input ≠ input) :
    IsParameterHashInput secretKey.parameter input := by
  by_contra hinput
  apply hne
  unfold keygenStructuralTargetInput
  rw [CappedSuffix.keygenChainTargetInput_eq_self_of_not _ _ _ hinput,
    CappedLeaf.keygenLeafTargetInput_eq_self_of_not _ _ _ hinput,
    CappedMerkle.keygenMerkleTargetInput_eq_self_of_not _ _ _ hinput,
    CappedTop.keygenTopTargetInput_eq_self_of_not _ _ _ hinput]

/-- **Lane 2, attributed.** -/
theorem secondLane_le_expectedParameterQueries
    (q : Nat) (adversary : Adversary)
    (hbound : HasAfterKeygenHashQueryBound Concrete.scheme adversary q) (hq : q < 2 ^ 127) :
    Pr{let x ← cappedDetailedGameWithEncodingTrace adversary}[WinningSecondLaneBadEventOccurs x] ≤
      expectedParameterQueries Concrete.scheme adversary /
        ((2 ^ digestBits : Nat) : ENNReal) := by
  have hstructural :
      Pr{let execution ← cappedDetailedGameWithEncodingTrace adversary}[WinningStructuralCollisionOccurs execution.2.1.1 execution.1] ≤
      expectedPostKeygenStructuralQueries adversary /
        ((2 ^ digestBits : Nat) : ENNReal) := by
    calc
      _ = Pr{let execution ← detailedGameWithCache Concrete.scheme adversary}[WinningStructuralCollisionOccurs execution.2 execution.1] := by
        rw [← cappedDetailedGameWithEncodingTrace_cache_projection, prEvent_map]
      _ ≤ _ :=
        winningStructuralCollision_probability_le_expectedPostKeygenStructuralQueries
          adversary
  unfold WinningSecondLaneBadEventOccurs
  refine (prEvent_or_le _ _ _).trans ?_
  refine (add_le_add
    (capped_cachedSelection_probability_le_expectedDigest q adversary hbound hq)
    hstructural).trans ?_
  rw [← ENNReal.add_div]
  gcongr
  unfold CappedEncodingMonitor.expectedPostKeygenEncodingQueries
    expectedPostKeygenStructuralQueries expectedParameterQueries
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun keyResult => ?_
  rw [← mul_add]
  by_cases hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅)
  · refine mul_le_mul' le_rfl ?_
    have hparameter := precomputedKeygen_support_parameter_eq keyResult hkey
    rw [expectedSimulatedQueryCount_gameRest_eq_cappedSource,
      ← expectedSimulatedQueryCount_or_of_disjoint romImpl _ _
        (encodingHashQuery_structuralQuery_disjoint keyResult.1.2 keyResult.2)]
    apply expectedSimulatedQueryCount_mono
    intro input hinput
    rcases input with n | hashInput
    · rcases hinput with h | h <;> simp [CappedEncodingMonitor.IsEncodingHashQuery,
        Rom.IsRelevantHashQuery] at h
    · change IsParameterHashInput keyResult.1.1.parameter hashInput
      rw [← hparameter]
      rcases hinput with h | h
      · change (encodingInputLeafIndex? keyResult.1.2.parameter hashInput).isSome at h
        cases hleaf : encodingInputLeafIndex? keyResult.1.2.parameter hashInput with
        | none => simp [hleaf] at h
        | some leafIndex =>
            exact CappedChain.isParameterHashInput_of_encodingInputLeafIndex hleaf
      · exact isParameterHashInput_of_keygenStructuralTargetInput_ne _ _ _ h
  · rw [(prEvent_eq_zero_of_not_mem_support _) hkey, zero_mul, zero_mul]

/-! ## The model's bound -/

/-- What lane 1 adds to the attributed count: the verification's calls and the forgery's probes. -/
def firstLaneExpectedSlack : Nat := verifyHashBound + forgeryProbeCount

theorem fuel_mul_inv_le (q : Nat) (hq : q < 2 ^ 127) :
    ((q + forgeryProbeCount : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ ≤ 3 / 4 := by
  have hprobes : forgeryProbeCount = 290 := by
    simp [forgeryProbeCount, numChains, chainLength, winternitzBits]
  have hle : q + forgeryProbeCount ≤ 3 * 2 ^ 126 := by omega
  rw [← div_eq_mul_inv, ENNReal.div_le_iff (by simp [digestBits]) (by simp [digestBits])]
  calc
    ((q + forgeryProbeCount : Nat) : ℝ≥0∞) ≤ ((3 * 2 ^ 126 : Nat) : ℝ≥0∞) := by exact_mod_cast hle
    _ = 3 / 4 * ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
      rw [show (2 ^ digestBits : Nat) = 4 * 2 ^ 126 by norm_num [digestBits], Nat.cast_mul,
        Nat.cast_mul, ← mul_assoc]
      congr 1
      rw [show ((4 : Nat) : ℝ≥0∞) = 4 by norm_num, ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
      norm_num

/-- **The model, attributed.** For a pathwise budget `q < 2^127` after key generation, the model's
forgery probability is two units per expected hash call after key generation that starts with the
key's parameter (`N`), plus lane 1's constant, plus a second-order term relative to `q`. -/
theorem concreteScheme_afterKeygenSecurity_expected
    (q : Nat) (hq : q < 2 ^ 127) (adversary : Adversary)
    (hbound : HasAfterKeygenHashQueryBound Concrete.scheme adversary q) :
    forgeAdvantage Concrete.scheme adversary ≤
      (2 * expectedParameterQueries Concrete.scheme adversary + firstLaneExpectedSlack) /
          ((2 ^ 128 : Nat) : ℝ≥0∞) +
        4 * (((q + forgeryProbeCount : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) *
          ((expectedParameterQueries Concrete.scheme adversary + firstLaneExpectedSlack) /
            ((2 ^ 128 : Nat) : ℝ≥0∞)) := by
  let N := expectedParameterQueries Concrete.scheme adversary
  let u := ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹
  have hu : u = ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ := by simp [u, digestBits]
  have hmean : sourceAttributedMean adversary ≤ N + firstLaneExpectedSlack :=
    sourceAttributedMean_le adversary
  have hfirst : Pr{let x ← cappedDetailedGameWithEncodingTrace adversary}[WinningExactFirstLaneBadEventOccurs x] ≤
      u * (N + firstLaneExpectedSlack) +
        4 * (((q + forgeryProbeCount : Nat) : ℝ≥0∞) * u) * (u * (N + firstLaneExpectedSlack)) := by
    rw [cappedExactFirstLane_probability_eq_sourceGlobalExact]
    refine (sourceWinningExactFirstLane_probability_le_expected q adversary hbound
      (fuel_mul_inv_le q hq)).trans ?_
    gcongr
  have hsecond := secondLane_le_expectedParameterQueries q adversary hbound hq
  refine (capped_forgeAdvantage_le_exactFirstLane_add_secondLane adversary).trans
    ((add_le_add hfirst hsecond).trans_eq ?_)
  simp only [div_eq_mul_inv, ← hu]
  ring

end XmssSecurity
