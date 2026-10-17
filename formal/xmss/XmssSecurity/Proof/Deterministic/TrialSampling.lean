import XmssSecurity.Proof.Deterministic.TrialLoop
import XmssSecurity.Proof.StatementLemmas

open OracleComp OracleSpec

namespace XmssSecurity.Seeded

open DeterministicSigning

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 100000

attribute [local irreducible] Concrete.precomputedSignAttempt

variable {State : Type}

def trialKernel (_ : Trial) (output : HashOutput) : StateT State ProbComp HashOutput := pure output

theorem trialTableRun_eq (handler : QueryImpl OracleWorld (StateT State ProbComp)) (tape : TrialTape)
    (secretKey : XmssSecurity.SecretKey) (leafIndex : LeafIndex) (message : Message) (attempts trial : Nat) :
    tableRun handler trialKernel tape (trialLoop secretKey leafIndex message attempts trial) =
      simulateQ handler (liftM (tableSignFrom (fun position => tape position.2) secretKey leafIndex message attempts trial :
        OracleComp HashSpec TrialResult) : OracleComp OracleWorld TrialResult) := by
  induction attempts generalizing trial with
  | zero => rfl
  | succ attempts ih =>
      simp only [trialLoop, tableSignFrom, tableRun, simulateQ_bind, simulateQ_spec_query,
        liftM_bind]
      change (pure (tape (BitVec.ofNat 32 trial)) >>= fun output =>
        simulateQ (handler + fun input => trialKernel input (tape input))
          (baseLift (liftM (Concrete.precomputedSignAttempt secretKey leafIndex message (output.extractLsb' 0 randomnessBits) : OracleComp HashSpec _) :
            OracleComp OracleWorld _) : OracleComp TrialWorld _) >>= _) = _
      rw [pure_bind, simulateQ_baseLift]
      apply congrArg (fun k => simulateQ handler
        (liftM (Concrete.precomputedSignAttempt secretKey leafIndex message ((tape (BitVec.ofNat 32 trial)).extractLsb' 0 randomnessBits)) :
          OracleComp OracleWorld _) >>= k)
      funext attempt
      cases attempt with
      | none => exact ih _
      | some result => rfl

def randomizerHalves : HashOutput ≃ (BitVec 64 × Randomness) where
  toFun output := (output.extractLsb' randomnessBits 64, output.extractLsb' 0 randomnessBits)
  invFun pair := pair.1 ++ pair.2
  left_inv output := BitVec.extractLsb'_append_extractLsb' (w := 64) (len := 192) (x := output)
  right_inv pair := by
    apply Prod.ext
    · exact BitVec.extractLsb'_append_eq_left
    · exact BitVec.extractLsb'_append_eq_right

noncomputable local instance : SampleableType Randomness := SampleableType.ofFintype Randomness

theorem evalDist_uniform_discard {A B : Type} [SampleableType A] (next : ProbComp B) :
    (do let _ ← $ᵗ A; next) =ᵈ next :=
  OracleComp.EvalDistEq.bind_const _ _

theorem evalDist_randomizer :
    ((fun output : HashOutput => output.extractLsb' 0 randomnessBits) <$> ($ᵗ HashOutput)) =ᵈ Concrete.signingRandomness := by
  have h := SampleableType.map_uniformSample_evalDistEq_of_bijective
    (α := HashOutput) (β := BitVec 64 × Randomness) randomizerHalves.bijective
  have hpair := evalDist_independent_uniform_pair (α := BitVec 64) (β := Randomness)
  calc
    _ =ᵈ (Prod.snd <$> (randomizerHalves <$> ($ᵗ HashOutput))) := by
      simp only [Functor.map_map]; rfl
    _ =ᵈ (Prod.snd <$> ($ᵗ (BitVec 64 × Randomness))) := h.map _
    _ =ᵈ (Prod.snd <$> (do
        let high ← $ᵗ (BitVec 64)
        let low ← $ᵗ Randomness
        pure (high, low))) := hpair.symm.map _
    _ =ᵈ _ := by
      simp only [map_bind, bind_pure_comp, Functor.map_map, id_map', Concrete.signingRandomness_eq]
      exact evalDist_uniform_discard (A := BitVec 64) ($ᵗ Randomness)


theorem run_freshTrialLoop_succ (hash : QueryImpl HashSpec (StateT State ProbComp))
    (secretKey : XmssSecurity.SecretKey) (leafIndex : LeafIndex) (message : Message) (attempts trial : Nat) (state : State) :
    (freshRun (worldHandler hash) trialKernel (trialLoop secretKey leafIndex message (attempts + 1) trial)).run state = (do
      let output ← ($ᵗ HashOutput : ProbComp HashOutput)
      let result ← (simulateQ (worldHandler hash) (liftM
        (Concrete.precomputedSignAttempt secretKey leafIndex message (output.extractLsb' 0 randomnessBits) : OracleComp HashSpec _) : OracleComp OracleWorld _)).run state
      (freshRun (worldHandler hash) trialKernel (match result.1 with
        | none => trialLoop secretKey leafIndex message attempts (trial + 1)
        | some signature => pure (some signature))).run result.2) := by
  rw [trialLoop, freshRun_request_bind]
  simp only [trialKernel, pure_bind]
  simp_rw [freshRun_baseLift_bind]
  simp only [StateT.run_bind, StateT.run_liftM, bind_assoc, pure_bind]
  apply bind_congr
  intro output
  apply bind_congr
  intro result
  cases result.1 <;> rfl

theorem run_randomTrialLoop_succ (hash : QueryImpl HashSpec (StateT State ProbComp))
    (secretKey : XmssSecurity.SecretKey) (leafIndex : LeafIndex) (message : Message) (attempts : Nat) (state : State) :
    (simulateQ (worldHandler hash) (Concrete.precomputedSignBoundedAttempts (attempts + 1) secretKey leafIndex message)).run state = (do
      let randomness ← Concrete.signingRandomness
      let result ← (simulateQ (worldHandler hash) (liftM
        (Concrete.precomputedSignAttempt secretKey leafIndex message randomness : OracleComp HashSpec _) : OracleComp OracleWorld _)).run state
      (simulateQ (worldHandler hash) (match result.1 with
        | none => Concrete.precomputedSignBoundedAttempts attempts secretKey leafIndex message
        | some signature => pure (some signature))).run result.2) := by
  rw [Concrete.precomputedSignBoundedAttempts, worldHandler_sampling_bind]
  apply bind_congr
  intro randomness
  simp only [simulateQ_bind, StateT.run_bind]
  apply bind_congr
  intro result
  cases result.1 <;> rfl

theorem evalDist_freshTrialLoop (hash : QueryImpl HashSpec (StateT State ProbComp))
    (secretKey : XmssSecurity.SecretKey) (leafIndex : LeafIndex) (message : Message) (attempts trial : Nat) (state : State) :
    ((freshRun (worldHandler hash) trialKernel (trialLoop secretKey leafIndex message attempts trial)).run state) =ᵈ ((simulateQ (worldHandler hash) (Concrete.precomputedSignBoundedAttempts attempts secretKey leafIndex message)).run state) := by
  induction attempts generalizing trial state with
  | zero => rfl
  | succ attempts ih =>
      rw [run_freshTrialLoop_succ, run_randomTrialLoop_succ]
      refine EvalDistEq.trans ?_ (evalDist_randomizer.bind_left _)
      rw [bind_map_left]

      apply EvalDistEq.bind_right
      intro output
      apply EvalDistEq.bind_right
      intro result
      cases result.1 with
      | none => exact ih (trial + 1) result.2
      | some indices => rfl

noncomputable local instance : SampleableType TrialTape := trialTapeSampleableType

theorem evalDist_tableSignFrom (hash : QueryImpl HashSpec (StateT State ProbComp))
    (secretKey : XmssSecurity.SecretKey) (leafIndex : LeafIndex) (message : Message) (attempts trial : Nat)
    (hbound : trial + attempts ≤ 2 ^ 32) (state : State) :
    (do
      let tape ← sampleTrialTape
      (simulateQ (worldHandler hash) (liftM (tableSignFrom (fun position => tape position.2)
        secretKey leafIndex message attempts trial : OracleComp HashSpec TrialResult) : OracleComp OracleWorld TrialResult)).run state) =ᵈ ((simulateQ (worldHandler hash) (Concrete.precomputedSignBoundedAttempts attempts secretKey leafIndex message)).run state) := by
  simp_rw [← trialTableRun_eq]
  exact ((freshRequests_trialLoop secretKey leafIndex message attempts trial hbound).evalDist_tableRun
    (worldHandler hash) trialKernel state).trans
      (evalDist_freshTrialLoop hash secretKey leafIndex message attempts trial state)

end XmssSecurity.Seeded
