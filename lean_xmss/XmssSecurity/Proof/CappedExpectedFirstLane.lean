import XmssSecurity.Proof.CappedExactFirstLaneBound
import XmssSecurity.Proof.BoundedFirstLaneCountedCoupling
import XmssSecurity.Proof.VerifyQueryBound
import XmssSecurity.Proof.ExpectedTail

/-!
# Lane 1 on the attributed expected count

Every hazard of the first lane comes from a hash input that starts with the key's parameter `P`:
an encoding input, a chain step or a leaf. So the lane's coupling counts the adversary's
`P`-prefixed hash inputs (`parameterHashCost`), and on both of its branches the right trace's
hazards up to its first hit stay below that count plus the verification's hash calls.
-/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity

/-- A hash input attributable to the key with parameter `P`: it starts with `P`. -/
def IsParameterHashInput (parameter : PublicParameter) (input : HashInput) : Prop :=
  bytesLE 16 parameter <+: input

instance (parameter : PublicParameter) : DecidablePred (IsParameterHashInput parameter) :=
  fun input => inferInstanceAs (Decidable (bytesLE 16 parameter <+: input))

/-- A hash query attributable to the key with parameter `P`. -/
def IsParameterQuery (parameter : PublicParameter) : OracleWorld.Domain → Prop
  | .inl _ => False
  | .inr input => IsParameterHashInput parameter input

instance (parameter : PublicParameter) : DecidablePred (IsParameterQuery parameter) :=
  fun input => match input with
    | .inl _ => isFalse id
    | .inr input => inferInstanceAs (Decidable (IsParameterHashInput parameter input))

theorem isParameterHashInput_tweakableHashInput (parameter : PublicParameter)
    (domain : HashDomain) (message : HashInput) :
    IsParameterHashInput parameter (tweakableHashInput parameter domain message) := by
  unfold IsParameterHashInput tweakableHashInput
  simp only [List.append_assoc]
  exact List.prefix_append _ _

namespace CappedChain

set_option maxRecDepth 1000000

/-- One per hash call attributable to the key with parameter `P`. -/
def oracleParameterCost (parameter : PublicParameter) : OracleWorld.Domain → Nat
  | .inl _ => 0
  | .inr input => if IsParameterHashInput parameter input then 1 else 0

/-- One per adversary hash call attributable to the key with parameter `P`. -/
def parameterHashCost (parameter : PublicParameter) :
    (OracleWorld + SigningSpec).Domain → Nat
  | .inl input => oracleParameterCost parameter input
  | .inr _ => 0

theorem parameterHashCost_le_direct (parameter : PublicParameter)
    (input : (OracleWorld + SigningSpec).Domain) :
    parameterHashCost parameter input ≤ directHashActionCost input := by
  rcases input with (uniformOrHash | request)
  · rcases uniformOrHash with n | hashInput
    · simp [parameterHashCost, oracleParameterCost, directHashActionCost]
    · simp only [parameterHashCost, oracleParameterCost, directHashActionCost]
      split <;> omega
  · simp [parameterHashCost, directHashActionCost]

/-- The adversary's hash inputs attributable to the key with parameter `P`. -/
def attributedHashInputs (parameter : PublicParameter) (trace : AttackerActionTrace) : Nat :=
  (trace.hashInputs.filter fun input => decide (IsParameterHashInput parameter input)).length

theorem attributedHashInputs_append (parameter : PublicParameter)
    (left right : AttackerActionTrace) :
    attributedHashInputs parameter (left ++ right) =
      attributedHashInputs parameter left + attributedHashInputs parameter right := by
  simp [attributedHashInputs, List.filter_append]

theorem attributedHashInputs_fragment (parameter : PublicParameter)
    (input : (OracleWorld + SigningSpec).Domain)
    (output : (OracleWorld + SigningSpec).Range input) :
    attributedHashInputs parameter (attackerActionFragment input output) =
      parameterHashCost parameter input := by
  rcases input with (uniformOrHash | request)
  · rcases uniformOrHash with n | hashInput
    · rfl
    · simp only [attributedHashInputs, attackerActionFragment_hash, parameterHashCost,
        oracleParameterCost]
      by_cases h : IsParameterHashInput parameter hashInput <;>
        simp [AttackerActionTrace.hashInputs, AttackerAction.hashInput?, h]
  · rfl

/-! ## Every hazard is attributable -/

theorem isParameterHashInput_of_encodingInputLeafIndex
    {parameter : PublicParameter} {input : HashInput} {leafIndex : LeafIndex}
    (h : encodingInputLeafIndex? parameter input = some leafIndex) :
    IsParameterHashInput parameter input := by
  obtain ⟨payload, rfl⟩ :=
    exists_encodingInput_of_encodingInputLeafIndex?_eq_some parameter input leafIndex h
  exact isParameterHashInput_tweakableHashInput _ _ _

theorem isParameterHashInput_of_globalChainInputProbe
    {parameter : PublicParameter} {input : HashInput}
    {probe : GlobalChainValueIndex × Digest}
    (h : globalChainInputProbe? parameter input = some probe) :
    IsParameterHashInput parameter input := by
  unfold globalChainInputProbe? at h
  split at h
  · rename_i hexists
    obtain ⟨data, rfl⟩ := hexists
    exact isParameterHashInput_tweakableHashInput _ _ _
  · cases h

theorem isParameterHashInput_of_globalLeafInputData
    {parameter : PublicParameter} {input : HashInput} {data : GlobalLeafInputData}
    (h : globalLeafInputData? parameter input = some data) :
    IsParameterHashInput parameter input := by
  rw [globalLeafInputData?_eq_some_iff] at h
  subst h
  exact isParameterHashInput_tweakableHashInput _ _ _

theorem globalCausalAttackerHashQueryFromHigh_probeBound_zero
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (hinput : ¬IsParameterHashInput secretKey.parameter input) :
    (globalCausalAttackerHashQueryFromHigh high secretKey input).run state
      |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  rw [globalCausalAttackerHashQueryFromHigh_run]
  have hchain : globalChainInputProbe? secretKey.parameter input = none := by
    cases h : globalChainInputProbe? secretKey.parameter input with
    | none => rfl
    | some probe => exact (hinput (isParameterHashInput_of_globalChainInputProbe h)).elim
  have hleaf : globalLeafInputData? secretKey.parameter input = none := by
    cases h : globalLeafInputData? secretKey.parameter input with
    | none => rfl
    | some data => exact (hinput (isParameterHashInput_of_globalLeafInputData h)).elim
  have hplan : ∀ index target, globalFilteredCausalAttackerHashPlan secretKey input state ≠
      .probeThenFresh index target := by
    intro index target
    unfold globalFilteredCausalAttackerHashPlan
    split
    · simp
    · rw [hchain]
      unfold globalFilteredCausalUncachedAttackerHashPlan globalFilteredCausalLeafHashPlan
      simp [hleaf]
  generalize hplanEq : globalFilteredCausalAttackerHashPlan secretKey input state = plan
  cases plan with
  | cached output => simp
  | redirect output => simp
  | fresh =>
      exact globalCausalHashQuery_run_isProbeQueryBoundP input
        (globalCausalRecordedState secretKey input state)
  | reveal index =>
      exact globalCausalRevealHashQueryFromHigh_isProbeQueryBoundP high
        secretKey input state index
  | probeThenFresh index target => exact (hplan index target hplanEq).elim

theorem globalFirstLaneAttackerHashQueryFromHigh_attributedHazardBound
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) :
    (globalFirstLaneAttackerHashQueryFromHighRun high secretKey input state)
      |>.IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery
        (if IsParameterHashInput secretKey.parameter input then 1 else 0) := by
  by_cases hinput : IsParameterHashInput secretKey.parameter input
  · simp only [hinput, ↓reduceIte]
    exact globalFirstLaneAttackerHashQueryFromHigh_hazardBound high secretKey input state
  · simp only [hinput, ↓reduceIte]
    have hleafIndex : encodingInputLeafIndex? secretKey.parameter input = none := by
      cases h : encodingInputLeafIndex? secretKey.parameter input with
      | none => rfl
      | some leafIndex =>
          exact (hinput (isParameterHashInput_of_encodingInputLeafIndex h)).elim
    rw [globalFirstLaneAttackerHashQueryFromHighRun_eq_none high secretKey
      input state hleafIndex]
    exact globalFirstLaneLiftRevealProbe_hazardBound _ 0
      (globalCausalAttackerHashQueryFromHigh_probeBound_zero high secretKey input state hinput)

theorem globalFirstLaneOracleExecution_attributedHazardBound
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : OracleWorld.Domain) (state : GlobalCausalHashState) :
    (globalFirstLaneOracleExecution keyView edgeHigh input state)
      |>.IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery
        (oracleParameterCost keyView.secretKey.parameter input) := by
  cases input with
  | inl n =>
      exact globalFirstLaneUniformImpl_hazardBound n state
  | inr input =>
      exact globalFirstLaneAttackerHashQueryFromHigh_attributedHazardBound
        (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey input state

theorem globalFirstLaneExactTracedOracleImpl_attributedHazardBound
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : OracleWorld.Domain)
    (state : GlobalHighDirectTracedState) :
    ((globalFirstLaneExactTracedOracleImpl keyView edgeHigh input).run state)
      |>.IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery
        (oracleParameterCost keyView.secretKey.parameter input) := by
  unfold globalFirstLaneExactTracedOracleImpl
  apply globalExactTracedLift_hazardBound
  exact globalFirstLaneOracleExecution_attributedHazardBound keyView edgeHigh input
    state.causalState

theorem globalFirstLaneExactTracedMappedAdversaryImpl_attributedHazardBound
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalHighDirectTracedState) :
    ((globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh input).run
      state).IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery
        (parameterHashCost keyView.secretKey.parameter input) := by
  rcases input with (worldInput | request)
  · unfold globalFirstLaneExactTracedMappedAdversaryImpl
    exact globalFirstLaneExactTracedOracleImpl_attributedHazardBound keyView edgeHigh
      worldInput state
  · unfold globalFirstLaneExactTracedMappedAdversaryImpl
    exact globalFirstLaneExactTracedSigningImpl_hazardBound keyView request state

/-! ## The counted coupling of the detailed executions -/

theorem cappedBothTracedMappedAdversaryImpl_support_trace
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (state : SourceExactTracedState)
    (result : (OracleWorld + SigningSpec).Range input × SourceExactTracedState)
    (hresult : result ∈ support
      ((cappedBothTracedMappedAdversaryImpl publicKey secretKey input).run state)) :
    result.2.2 = state.2 ++ attackerActionFragment input result.1 := by
  unfold cappedBothTracedMappedAdversaryImpl at hresult
  rw [QueryImpl.extendState_apply, mem_support_bind_iff] at hresult
  obtain ⟨step, _, hstep⟩ := hresult
  rw [mem_support_pure_iff] at hstep
  subst hstep
  rfl

theorem globalFirstLaneExactTracedVerifier_hazardCount_le
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (publicKey : PublicKey) (forgery : Forgery) (state : GlobalHighDirectTracedState)
    (result : (Bool × GlobalHighDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ (globalFirstLaneExactTracedVerifierImpl keyView edgeHigh)
          (Concrete.scheme.verify publicKey forgery.leafIndex forgery.message
            forgery.signature)).run state)).run)) :
    FirstLaneOracleSimulation.hazardCount result.2 ≤ verifyHashBound :=
  FirstLaneOracleSimulation.simulate_eagerTrace_support_hazardCount_le table _ verifyHashBound
    (OracleComp.IsQueryBoundP.simulateQ_run_StateT_of_step
      (scheme_verify_isHashQueryBound _ _ _ _)
      (fun input stepState => by
        rcases input with n | x
        · exact globalFirstLaneExactTracedVerifierImpl_hazardBound keyView edgeHigh
            (.inl n) stepState
        · exact globalFirstLaneExactTracedVerifierImpl_hazardBound keyView edgeHigh
            (.inr x) stepState)
      state)
    result hresult

theorem relTriple_sourceExact_firstLane_detailedExecution_boundedHit_counted
    (countLimit hitLimit : Nat)
    (adversary : Adversary)
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (hsourceBound :
      HashQueryBound (sourceUnloggedDetailedGameAfterKeygen adversary
        (Concrete.materializeCachedKeyResult left.keyResult).1.1
        (Concrete.materializeCachedKeyResult left.keyResult).1.2)
          (Concrete.materializeCachedKeyResult left.keyResult).2 countLimit)
    (hlimits : countLimit ≤ hitLimit) :
    RelTriple
      (sourceGlobalExactTracedDetailedExecution adversary left)
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
        ((globalFirstLaneExactTracedDetailedExecution adversary right.1.1
          right.2).run (GlobalHighDirectTracedState.initial
            (globalFilteredCausalKeygenState right.1.1)))).run)
      (fun leftResult firstLaneResult =>
        ((leftResult.1 = firstLaneResult.1.1 ∧
          SourceFirstLaneExactGoodStateRelation left right.1 leftResult.2
            firstLaneResult.1.2 firstLaneResult.2 ∧
          FirstLaneOracleSimulation.hazardCount firstLaneResult.2 ≤
            countLimit) ∨
        FirstLaneOracleSimulation.CombinedHit right.1.2
          (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
            firstLaneResult.2)) ∧
        FirstLaneOracleSimulation.stoppedHazards right.1.2
            (FirstLaneOracleSimulation.enforceHazardTrace hitLimit firstLaneResult.2) ≤
          attributedHashInputs left.publicKey.parameter leftResult.2.2 + verifyHashBound) := by
  have hparameter : right.1.1.secretKey.parameter = left.publicKey.parameter :=
    (programmedGlobal_secretKey_parameter_eq left right hrel hleftSupport hrightSupport).trans
      (keygen_parameter_eq left.keyResult
        (trajectoryProgrammedGlobalChainKeygen_support_keyResult left hleftSupport)).symm
  let secretKey :=
    Concrete.materializePrecomputation left.cache left.secretKey
  let sourceInitial : SourceExactTracedState := ((((left.cache, []), []), []))
  let highInitial : GlobalMonitoredTracedState :=
    (⟨globalFilteredCausalKeygenState right.1.1, []⟩, [])
  let firstLaneInitial : GlobalHighDirectTracedState :=
    GlobalHighDirectTracedState.initial
      (globalFilteredCausalKeygenState right.1.1)
  have hinitial : SourceFirstLaneExactGoodStateRelation left right.1
      sourceInitial firstLaneInitial [] := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [sourceInitial, highInitial, firstLaneInitial,
        globalStateOfFirstLane, sourceExactSigningProjection,
        FirstLaneOracleSimulation.ActionTrace.chainActions] using
        globalSigningMonitoredTracedStateRelation_initial left right hrel
          hleftSupport hrightSupport
    · simp [sourceInitial,
        FirstLaneOracleSimulation.ActionTrace.encodingActions]
    · simp [CappedEncodingMonitor.validObservedSignLeafIndices,
        FirstLaneOracleSimulation.ActionTrace.encodingActions,
        CappedEncodingMonitor.validActions,
        EncodingMonitor.observedSignLeafIndices]
  let finish : Forgery → OracleComp OracleWorld (Forgery × Bool) :=
    fun forgery => Prod.mk forgery <$> Concrete.scheme.verify
      left.publicKey forgery.leafIndex forgery.message forgery.signature
  let Budget := fun
    (rest : OracleComp (OracleWorld + SigningSpec) Forgery)
    (remaining : Nat) (state : SourceExactTracedState) =>
      HashQueryBound (simulateQ
        (sourceUnloggedMappedAdversaryImpl left.publicKey secretKey) rest >>=
          finish) state.1.1.1 remaining
  let leftFinish := fun (forgery : Forgery)
    (initial : SourceExactTracedState) => do
      let verified ← (simulateQ sourceSigningTracedVerifierImpl
        (Concrete.scheme.verify left.publicKey forgery.leafIndex forgery.message
          forgery.signature)).run (sourceExactSigningProjection initial)
      pure ((forgery, verified.1),
        ((verified.2.1,
          appendVerificationEncodingObservation secretKey forgery
            initial.1.1.1 verified.2.1.1 initial.1.2), verified.2.2))
  let rightFinish := fun (forgery : Forgery)
    (initial : GlobalHighDirectTracedState) => do
      let verified ← (simulateQ
        (globalFirstLaneExactTracedVerifierImpl right.1.1 right.2)
        (Concrete.scheme.verify left.publicKey forgery.leafIndex forgery.message
          forgery.signature)).run initial
      pure ((forgery, verified.1),
        firstLaneAppendVerificationState right.1.1.secretKey forgery initial
          verified.2)
  have hfullBound : Budget (adversary.main left.publicKey) countLimit sourceInitial := by
    unfold Budget finish
    unfold sourceUnloggedDetailedGameAfterKeygen at hsourceBound
    simp only [bind_pure_comp] at hsourceBound
    exact hsourceBound
  let leftCount := fun state : SourceExactTracedState =>
    attributedHashInputs left.publicKey.parameter state.2
  have hcoupling := relTriple_simulateQ_bind_bounded_firstLane_counted right.1.2
    (cappedBothTracedMappedAdversaryImpl left.publicKey secretKey)
    (globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2)
    leftFinish rightFinish directHashActionCost
    (SourceFirstLaneExactGoodStateRelation left right.1)
    (fun state spent => state.2.hashInputs.length = spent) leftCount verifyHashBound Budget
    (by
      intro input next remaining state result hrest hresult
      unfold Budget at hrest ⊢
      rw [simulateQ_query_bind, bind_assoc] at hrest
      have hr : (result.1, result.2.1.1.1) ∈ support
          ((simulateQ romImpl (sourceUnloggedMappedAdversaryImpl left.publicKey secretKey input)).run state.1.1.1) := by
        rw [← cappedBothTracedMappedAdversaryImpl_cache_projection, support_map]
        exact ⟨result, hresult, rfl⟩
      exact sourceUnloggedMappedAdversaryImpl_consistent_query_bound left.publicKey secretKey input
        (fun response => simulateQ (sourceUnloggedMappedAdversaryImpl left.publicKey secretKey)
          (next ((OracleSpec.query input).cont response)) >>= finish) state.1.1.1 remaining hrest _ hr)
    (by
      intro input state result hresult
      have htrace := cappedBothTracedMappedAdversaryImpl_support_trace _ _ input state result
        hresult
      simp only [leftCount, htrace, attributedHashInputs_append]
      exact Nat.le_add_right _ _)
    (by
      intro forgery initial result hresult
      simp only [leftFinish, mem_support_bind_iff, mem_support_pure_iff] at hresult
      obtain ⟨verified, hverified, rfl⟩ := hresult
      rw [sourceSigningTracedVerifierImpl_run_eq, support_map] at hverified
      obtain ⟨base, _, rfl⟩ := hverified
      exact le_rfl)
    (by
      intro spent input state firstState history hstates hprefix hacct hcountLeft
      apply relTriple_post_mono (relTriple_with_support
        (relTriple_sourceExact_firstLane_action spent left right hrel
          hleftSupport hrightSupport input state firstState history hstates
            hprefix))
      intro leftResult firstResult hresult
      obtain ⟨hresult, hleftResultSupport, hfirstResultSupport⟩ := hresult
      have hfragment := FirstLaneOracleSimulation.simulate_eagerTrace_support_hazardCount_le
        right.1.2 _ _
        (globalFirstLaneExactTracedMappedAdversaryImpl_attributedHazardBound right.1.1 right.2
          input firstState) firstResult hfirstResultSupport
      rw [hparameter] at hfragment
      have htrace := cappedBothTracedMappedAdversaryImpl_support_trace _ _ input state
        leftResult hleftResultSupport
      refine ⟨?_, ?_⟩
      · rcases hresult with hgood | hhit
        · exact Or.inl ⟨hgood.1, hgood.2.1, hgood.2.2.1, by
            rw [hgood.2.2.2, hacct]⟩
        · exact Or.inr hhit
      · simp only [leftCount, htrace, attributedHashInputs_append, attributedHashInputs_fragment,
          FirstLaneOracleSimulation.hazardCount_append]
        exact Nat.add_le_add hcountLeft hfragment)
    countLimit hitLimit
    (by
      intro forgery spent remaining state firstState history hremaining
        hstates hcount hacct htotal hcountLeft
      unfold Budget finish at hremaining
      simp only [simulateQ_pure, pure_bind] at hremaining
      have hverifyBound :
          HashQueryBound (Concrete.scheme.verify left.publicKey forgery.leafIndex forgery.message
            forgery.signature) state.1.1.1 remaining :=
        (hashQueryBound_map_iff _ _ _ _).mp hremaining
      have hverifier :=
        relTriple_sourceExact_firstLane_verifier_boundedHit countLimit hitLimit
          spent remaining left right hrel hleftSupport hrightSupport
            (Concrete.scheme.verify left.publicKey forgery.leafIndex
              forgery.message forgery.signature) state hverifyBound firstState
                history hstates hcount htotal hlimits
      let sourceFinish := fun verified : Bool × SourceExactTracedState =>
        ((forgery, verified.1),
          sourceAppendVerificationState secretKey forgery state verified.2)
      let firstFinish := fun verified :
          ((Bool × GlobalHighDirectTracedState) ×
            FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (((forgery, verified.1.1),
          firstLaneAppendVerificationState right.1.1.secretKey forgery
            firstState verified.1.2), verified.2)
      have hlifted : RelTriple
          (sourceFinish <$>
            (simulateQ sourceExactTracedVerifierImpl
              (Concrete.scheme.verify left.publicKey forgery.leafIndex
                forgery.message forgery.signature)).run state)
          (firstFinish <$>
            (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
              ((simulateQ
                (globalFirstLaneExactTracedVerifierImpl right.1.1 right.2)
                (Concrete.scheme.verify left.publicKey forgery.leafIndex
                  forgery.message forgery.signature)).run firstState)).run)
          (fun leftResult firstResult =>
            (leftResult.1 = firstResult.1.1 ∧
              SourceFirstLaneExactGoodStateRelation left right.1 leftResult.2
                firstResult.1.2 (history ++ firstResult.2) ∧
              FirstLaneOracleSimulation.hazardCount
                (history ++ firstResult.2) ≤ countLimit) ∨
            FirstLaneOracleSimulation.CombinedHit right.1.2
              (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
                (history ++ firstResult.2))) := by
        apply relTriple_map
        apply relTriple_post_mono (relTriple_with_support hverifier)
        intro leftVerified firstVerified hvertified
        obtain ⟨hverifiedRelation, hleftVerifiedSupport,
          hfirstVerifiedSupport⟩ := hvertified
        rcases hverifiedRelation with hgood | hhit
        · exact Or.inl ⟨congrArg (Prod.mk forgery) hgood.1,
            SourceFirstLaneExactGoodStateRelation.appendVerification left right
              hrel hleftSupport hrightSupport forgery state leftVerified.2
                firstState firstVerified.1.2 history
                  (history ++ firstVerified.2) hstates hgood.2.1 (by
                    rw [FirstLaneOracleSimulation.ActionTrace.encodingActions_append]
                    have hpublicKey : left.publicKey =
                        right.1.1.publicKey := hrel.1.toStable.1.2.1
                    rw [hpublicKey] at hfirstVerifiedSupport
                    have hlocal :=
                      globalFirstLaneExactTracedVerifier_append_trace_sublist
                        right.1.2 right.1.1 right.2 forgery firstState
                          leftVerified.2.1.2
                          (by
                            have hkeyResult :=
                              trajectoryProgrammedGlobalChainKeygen_support_keyResult
                                right.1.1 hrightSupport
                            exact keygen_parameter_eq right.1.1.keyResult
                              hkeyResult)
                          firstVerified hfirstVerifiedSupport
                    have hleftEncoding : leftVerified.2.1.2 = state.1.2 := by
                      rw [sourceExactTracedVerifierImpl_run_eq, support_map]
                        at hleftVerifiedSupport
                      obtain ⟨baseResult, _hbase, heq⟩ := hleftVerifiedSupport
                      subst leftVerified
                      rfl
                    have hencodingInitial := hstates.2.1
                    have hencodingFinal : List.Sublist leftVerified.2.1.2
                        history.encodingActions := by
                      rw [hleftEncoding]
                      exact hencodingInitial
                    exact hlocal.trans
                      (hencodingFinal.append (List.Sublist.refl _))),
            hgood.2.2⟩
        · exact Or.inr hhit
      have hsource : leftFinish forgery state = sourceFinish <$>
          (simulateQ sourceExactTracedVerifierImpl
            (Concrete.scheme.verify left.publicKey forgery.leafIndex
              forgery.message forgery.signature)).run state := by
        unfold leftFinish
        rw [sourceExactTracedVerifierImpl_run_eq]
        simp [sourceFinish, sourceAppendVerificationState, Functor.map_map]
      have hright :
          (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
            (rightFinish forgery firstState)).run =
          firstFinish <$>
            (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
              ((simulateQ
                (globalFirstLaneExactTracedVerifierImpl right.1.1 right.2)
                (Concrete.scheme.verify left.publicKey forgery.leafIndex
                  forgery.message forgery.signature)).run firstState)).run := by
        unfold rightFinish
        rw [simulateQ_bind, WriterT.run_bind']
        simp [firstFinish, firstLaneAppendVerificationState]
      rw [hsource, hright]
      apply relTriple_post_mono (relTriple_with_support hlifted)
      intro leftResult firstResult hresult
      obtain ⟨hresult, hleftResultSupport, hfirstResultSupport⟩ := hresult
      refine ⟨hresult, ?_⟩
      rw [support_map] at hleftResultSupport hfirstResultSupport
      obtain ⟨leftVerified, hleftVerified, rfl⟩ := hleftResultSupport
      obtain ⟨firstVerified, hfirstVerified, rfl⟩ := hfirstResultSupport
      have hverifierHazards := globalFirstLaneExactTracedVerifier_hazardCount_le right.1.2
        right.1.1 right.2 left.publicKey forgery firstState firstVerified hfirstVerified
      rw [sourceExactTracedVerifierImpl_run_eq, support_map] at hleftVerified
      obtain ⟨leftBase, hleftBase, rfl⟩ := hleftVerified
      rw [sourceSigningTracedVerifierImpl_run_eq, support_map] at hleftBase
      obtain ⟨leftCacheResult, _, rfl⟩ := hleftBase
      calc
        _ ≤ FirstLaneOracleSimulation.hazardCount
            (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
              (history ++ firstVerified.2)) :=
          FirstLaneOracleSimulation.stoppedHazards_le _ _
        _ ≤ FirstLaneOracleSimulation.hazardCount (history ++ firstVerified.2) :=
          FirstLaneOracleSimulation.hazardCount_enforceHazardTrace_le_self _ _
        _ ≤ leftCount state + verifyHashBound := by
          rw [FirstLaneOracleSimulation.hazardCount_append]
          exact Nat.add_le_add hcountLeft hverifierHazards
        _ = _ := by
          simp [leftCount, sourceFinish, sourceAppendVerificationState,
            sourceExactSigningProjection])
    0 countLimit (adversary.main left.publicKey) sourceInitial
      firstLaneInitial hfullBound [] hinitial
      (by simp [FirstLaneOracleSimulation.hazardCount]) (by rfl)
      (by simp [FirstLaneOracleSimulation.hazardCount]) (by omega) hlimits
  have hpublicKey : left.publicKey = right.1.1.publicKey :=
    hrel.1.toStable.1.2.1
  unfold sourceGlobalExactTracedDetailedExecution
    globalFirstLaneExactTracedDetailedExecution
  simp only [StateT.run_mk]
  rw [← hpublicKey]
  exact hcoupling



/-! ## The counted coupling of the programs, and lane 1 in expected form -/

theorem relTriple_sourceGlobalExact_firstLane_program_counted
    (q hitLimit : Nat)
    (adversary : Adversary)
    (hbound : HasAfterKeygenHashQueryBound Concrete.scheme adversary q)
    (hlimits : q ≤ hitLimit) :
    RelTriple (sourceGlobalExactTracedProgram adversary)
      (globalFirstLaneExactCoupledProgram adversary)
      (fun left right => SourceFirstLaneExactBoundedProgramRelation q hitLimit left right ∧
        FirstLaneOracleSimulation.stoppedHazards right.1.1.2
            (FirstLaneOracleSimulation.enforceHazardTrace hitLimit right.2.2) ≤
          attributedHashInputs left.1.publicKey.parameter left.2.2.2 + verifyHashBound) := by
  unfold sourceGlobalExactTracedProgram globalFirstLaneExactCoupledProgram
  apply relTriple_bind
    (relTriple_with_support
      relTriple_trajectoryProgrammedGlobalChainKeygen_withBaseHigh_stable)
  intro left right hkeygen
  obtain ⟨hrel, hleftSupport, hrightSupport⟩ := hkeygen
  have hrightViewSupport :=
    coupledGlobalChainKeygenWithBaseHighFull_support_keyView right
      hrightSupport
  have hleftKeyResult :=
    trajectoryProgrammedGlobalChainKeygen_support_keyResult left hleftSupport
  have hmaterializedKeyResult :
      Concrete.materializeCachedKeyResult left.keyResult ∈ support
        ((simulateQ romImpl Concrete.scheme.keygen).run ∅) := by
    exact Concrete.oldKeygen_support_materializedPrecomputedKeygen
      left.keyResult hleftKeyResult
  have hsourceBound :=
    sourceUnloggedDetailedGameAfterKeygen_hashQueryBound_sub_keygen
      q adversary hbound (Concrete.materializeCachedKeyResult left.keyResult)
        hmaterializedKeyResult
  apply relTriple_bind
    (relTriple_sourceExact_firstLane_detailedExecution_boundedHit_counted
      q hitLimit adversary left right hrel
        hleftSupport hrightViewSupport hsourceBound hlimits)
  intro leftExecution rightExecution hexecution
  apply relTriple_pure_pure
  exact ⟨⟨hrel, hexecution.1⟩, hexecution.2⟩

/-- The source run's adversary hash calls attributable to its key, plus the verification's and the
forgery's probes. -/
noncomputable def sourceAttributedMean (adversary : Adversary) : ℝ≥0∞ :=
  ∑' x, Pr{let y ← sourceGlobalExactTracedProgram adversary}[y = x] *
    ((attributedHashInputs x.1.publicKey.parameter x.2.2.2 + verifyHashBound +
      forgeryProbeCount : Nat) : ℝ≥0∞)

theorem hazardCount_liftForgeryProbeTrace (result : GlobalExactTracedResult) :
    FirstLaneOracleSimulation.hazardCount
        (liftGlobalChainTrace (globalHighDirectExactForgeryPrimaryProbeTrace result)) =
      forgeryProbeCount := by
  rw [liftGlobalChainTrace_hazardCount, observedProbeCount_exactForgeryPrimaryProbeTrace]

set_option maxHeartbeats 4000000 in
/-- **Lane 1, expected.** The exact first lane's bad event costs `2^-128` per expected attributed
hash call of the adversary, the verification's calls and the forgery's probes, up to a second-order
term `4 (q + probes) / 2^128` relative to the main one, `q` the pathwise budget. -/
theorem sourceWinningExactFirstLane_probability_le_expected
    (q : Nat) (adversary : Adversary)
    (hbound : HasAfterKeygenHashQueryBound Concrete.scheme adversary q)
    (hq : ((q + forgeryProbeCount : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ ≤ 3 / 4) :
    Pr{let x ← sourceGlobalExactTracedProgram adversary}[SourceWinningExactFirstLaneEvent x] ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ * sourceAttributedMean adversary +
        4 * (((q + forgeryProbeCount : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) *
          (((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ * sourceAttributedMean adversary) := by
  let fuel := q + forgeryProbeCount
  let u := ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹
  let hit := Pr{let x ← globalFirstLaneExactPublicEagerExperiment adversary}[(GlobalFirstLaneExactPublicEnforcedHit fuel) x]
  have hsource : Pr{let x ← sourceGlobalExactTracedProgram adversary}[SourceWinningExactFirstLaneEvent x] ≤
      hit :=
    (sourceWinningExactFirstLane_probability_le_coupled_enforcedHit q fuel adversary hbound
      le_rfl).trans_eq (coupled_enforcedHit_probability_eq_public_eager fuel adversary)
  have hstopped :
      ∑' x, Pr{let y ← globalFirstLaneExactPublicEagerExperiment adversary}[y = x] *
          (FirstLaneOracleSimulation.stoppedHazards x.1
            (FirstLaneOracleSimulation.enforceHazardTrace fuel x.2.2) : ℝ≥0∞) ≤
        sourceAttributedMean adversary := by
    rw [← tsum_prEvent_mul_congr
      (evalDist_globalFirstLaneExactCoupledPublicProjection_eq_eager adversary),
      OracleComp.tsum_prEvent_map_mul]
    refine tsum_le_of_relTriple
      (relTriple_sourceGlobalExact_firstLane_program_counted q fuel adversary hbound
        (by omega)) _ _ fun left right hrelation => ?_
    have happend : FirstLaneOracleSimulation.stoppedHazards
          (globalFirstLaneExactCoupledPublicProjection right).1
          (FirstLaneOracleSimulation.enforceHazardTrace fuel
            (globalFirstLaneExactCoupledPublicProjection right).2.2) ≤
        FirstLaneOracleSimulation.stoppedHazards right.1.1.2
            (FirstLaneOracleSimulation.enforceHazardTrace fuel right.2.2) +
          forgeryProbeCount := by
      simp only [globalFirstLaneExactCoupledPublicProjection, appendGlobalFirstLaneExactPublicTrace,
        globalFirstLaneExactCoupledProjection]
      rw [FirstLaneOracleSimulation.enforceHazardTrace_append]
      refine (FirstLaneOracleSimulation.stoppedHazards_append_le _ _ _).trans ?_
      gcongr
      refine (FirstLaneOracleSimulation.hazardCount_enforceHazardTrace_le_self _ _).trans_eq ?_
      exact hazardCount_liftForgeryProbeTrace _
    have := hrelation.2
    omega
  have hloop : hit ≤ u * sourceAttributedMean adversary + (fuel * u) * hit := by
    have hbase := FirstLaneOracleSimulation.enforcedHit_le_stoppedHazards
      (globalFirstLaneExactTracedPublicProgram adversary) fuel
    change hit ≤ u * (_ + fuel * hit) at hbase
    calc
      hit ≤ u * (_ + fuel * hit) := hbase
      _ ≤ u * (sourceAttributedMean adversary + fuel * hit) := by
        gcongr
        exact hstopped
      _ = _ := by ring
  exact (hsource.trans (le_add_four_mul_of_le_add_mul (prEvent_le_one _) hq hloop)).trans_eq
    (by ring)

end CappedChain

end XmssSecurity
