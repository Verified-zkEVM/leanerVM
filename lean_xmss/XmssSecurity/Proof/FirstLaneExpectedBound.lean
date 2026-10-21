import XmssSecurity.Proof.FirstLaneEagerBound
import XmssSecurity.Proof.FirstLaneHazardEnforcement

/-!
# Lane 1 in expected form

`FirstLaneEagerBound` bounds a hit of the combined monitor by `fuel / 2^128`, `fuel` a pathwise
bound on the hazard queries. Here the same potential argument runs with the fuel replaced by the
hazards the monitor actually processes: the structural run also returns how many hazard actions it
processed before it stopped (`runStructuralC`), and a hit costs at most `2^-128` per expected
processed hazard (`structuralExperimentC_le`). On the eager experiment this is
`Pr[CombinedHit] ≤ E[observedHazards] / 2^128`, `observedHazards` the hazards of the trace up to the
monitor's first hit (`combinedHit_le_observedHazards`).
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

/-! ## Expected counts of runs returning a hit and a count -/

/-- The expected count of a run returning a hit flag and a count. -/
noncomputable def countMean (mx : ProbComp (Bool × Nat)) : ℝ≥0∞ :=
  ∑' x, Pr{let y ← mx}[y = x] * (x.2 : ℝ≥0∞)

/-- One more hazard. -/
def addHazard (x : Bool × Nat) : Bool × Nat := (x.1, x.2 + 1)

theorem countMean_bind {α : Type} (mx : ProbComp α) (f : α → ProbComp (Bool × Nat)) :
    countMean (mx >>= f) = ∑' a, Pr{let y ← mx}[y = a] * countMean (f a) :=
  OracleComp.tsum_prEvent_bind_mul mx f _

@[simp]
theorem countMean_pure (b : Bool) (n : Nat) : countMean (pure (b, n)) = n :=
  OracleComp.tsum_prEvent_pure_mul (spec := unifSpec) (b, n) fun x => (x.2 : ℝ≥0∞)

theorem countMean_map_addHazard (mx : ProbComp (Bool × Nat)) :
    countMean (addHazard <$> mx) = countMean mx + 1 := by
  unfold countMean
  rw [OracleComp.tsum_prEvent_map_mul]
  simp only [addHazard, Nat.cast_add, Nat.cast_one, mul_add, mul_one]
  rw [ENNReal.tsum_add, OracleComp.tsum_prEvent_eq_one]

theorem countMean_congr {mx my : ProbComp (Bool × Nat)} (h : mx =ᵈ my) :
    countMean mx = countMean my := by
  unfold countMean
  exact tsum_congr fun x => by rw [h.prEvent_eq (· = x)]

theorem prHit_map_addHazard (mx : ProbComp (Bool × Nat)) :
    Pr{let x ← addHazard <$> mx}[x.1 = true] = Pr{let x ← mx}[x.1 = true] := by
  rw [prEvent_map]
  rfl

theorem tsum_prEvent_mul_add_const {α : Type} (mx : ProbComp α) (f : α → ℝ≥0∞) (c : ℝ≥0∞) :
    ∑' a, Pr{let y ← mx}[y = a] * (f a + c) = (∑' a, Pr{let y ← mx}[y = a] * f a) + c := by
  simp only [mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, OracleComp.tsum_prEvent_eq_one, one_mul]

theorem tsum_prEvent_mul_const {α : Type} (mx : ProbComp α) (c : ℝ≥0∞) :
    ∑' a, Pr{let y ← mx}[y = a] * c = c := by
  rw [ENNReal.tsum_mul_right, OracleComp.tsum_prEvent_eq_one, one_mul]

/-- The potential step: a bound of every continuation's hit by `c` per expected count plus an
offset bounds the bind's hit by `c` per expected count plus the mean offset. -/
theorem prHit_bind_le {α : Type} (mx : ProbComp α) (f : α → ProbComp (Bool × Nat))
    (ψ : α → ℝ≥0∞) (c : ℝ≥0∞)
    (h : ∀ a, Pr{let x ← f a}[x.1 = true] ≤ c * countMean (f a) + ψ a) :
    Pr{let x ← mx >>= f}[x.1 = true] ≤
      c * countMean (mx >>= f) + ∑' a, Pr{let y ← mx}[y = a] * ψ a := by
  rw [OracleComp.prEvent_bind_eq_tsum, countMean_bind]
  calc
    _ ≤ ∑' a, Pr{let y ← mx}[y = a] * (c * countMean (f a) + ψ a) :=
      ENNReal.tsum_le_tsum fun a => mul_le_mul' le_rfl (h a)
    _ = _ := by
      simp only [mul_add]
      rw [ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
      congr 1
      exact tsum_congr fun a => by ring

/-- `prHit_bind_le` with a constant offset. -/
theorem prHit_bind_le_const {α : Type} (mx : ProbComp α) (f : α → ProbComp (Bool × Nat))
    (offset c : ℝ≥0∞)
    (h : ∀ a, Pr{let x ← f a}[x.1 = true] ≤ c * countMean (f a) + offset) :
    Pr{let x ← mx >>= f}[x.1 = true] ≤ c * countMean (mx >>= f) + offset :=
  (prHit_bind_le mx f (fun _ => offset) c h).trans_eq (by rw [tsum_prEvent_mul_const])

@[simp]
theorem prHit_pure (b : Bool) (n : Nat) :
    Pr{let x ← (pure (b, n) : ProbComp (Bool × Nat))}[x.1 = true] = if b = true then 1 else 0 := by
  rw [prEvent_pure]

theorem countMean_congr_of_eq {mx my : ProbComp (Bool × Nat)} (h : mx = my) :
    countMean mx = countMean my := h ▸ rfl

/-! ## The encoding monitor, counted -/

namespace CappedEncodingMonitor

set_option maxRecDepth 100000

local notation "u" => (Fintype.card Digest : ℝ≥0∞)⁻¹

theorem tsum_uniformDigest_eq_sum (f : Digest → ℝ≥0∞) :
    ∑' digest, Pr{let x ← $ᵗ Digest}[x = digest] * f digest =
      ∑ digest : Digest, Pr{let x ← $ᵗ Digest}[x = digest] * f digest :=
  tsum_fintype _

/-- `applyUniformQueryMonitor` with counted continuations: a hit stops with count `0`. -/
noncomputable def applyUniformQueryMonitorC
    (leafIndex : LeafIndex)
    (resume : Digest → EncodingMonitor.State → ProbComp (Bool × Nat))
    (state : EncodingMonitor.State) : ProbComp (Bool × Nat) := do
  let digest ← $ᵗ Digest
  match state.signed leafIndex with
  | some target =>
      if digest = target then pure (true, 0) else resume digest state
  | none =>
      if TargetSum.ValidDigest digest then
        resume digest (state.addPending leafIndex digest)
      else resume digest state

theorem applyUniformQueryMonitorC_le
    (leafIndex : LeafIndex)
    (resume : Digest → EncodingMonitor.State → ProbComp (Bool × Nat))
    (state : EncodingMonitor.State) (offset : ℝ≥0∞)
    (hresume : ∀ digest nextState,
      Pr{let x ← resume digest nextState}[x.1 = true] ≤
        u * countMean (resume digest nextState) + (offset + State.pendingRisk nextState)) :
    Pr{let x ← applyUniformQueryMonitorC leafIndex resume state}[x.1 = true] ≤
      u * (countMean (applyUniformQueryMonitorC leafIndex resume state) + 1) +
        (offset + State.pendingRisk state) := by
  unfold applyUniformQueryMonitorC
  cases hsigned : state.signed leafIndex with
  | some target =>
      refine (prHit_bind_le _ _
        (fun digest => (if digest = target then 1 else 0) + (offset + State.pendingRisk state))
        u fun digest => ?_).trans_eq ?_
      · by_cases heq : digest = target
        · simp [heq]
        · simpa [heq] using hresume digest state
      · rw [tsum_prEvent_mul_add_const, tsum_uniformDigest_eq_sum]
        have hpoint : ∑ digest : Digest, Pr{let x ← $ᵗ Digest}[x = digest] *
            (if digest = target then 1 else 0) = u := by
          simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
            SampleableType.prEvent_uniformSample_eq_singleton]
        rw [hpoint, mul_add, mul_one]
        ac_rfl
  | none =>
      refine (prHit_bind_le _ _
        (fun digest => (if TargetSum.ValidDigest digest then
            (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ else 0) + (offset + State.pendingRisk state))
        u fun digest => ?_).trans_eq ?_
      · by_cases hvalid : TargetSum.ValidDigest digest
        · simp only [hvalid, ↓reduceIte]
          refine (hresume digest _).trans ?_
          have hrisk := State.pendingRisk_addPending_le state leafIndex digest
          calc
            _ ≤ u * countMean (resume digest (state.addPending leafIndex digest)) +
                (offset + (State.pendingRisk state + (TargetSum.validDigests.card : ℝ≥0∞)⁻¹)) := by
              gcongr
            _ = _ := by ac_rfl
        · simpa [hvalid] using hresume digest state
      · rw [tsum_prEvent_mul_add_const, tsum_uniformDigest_eq_sum,
          uniformDigest_valid_bonus_sum_eq, mul_add, mul_one]
        ac_rfl

/-- `applyUniformSignAttemptMonitor` with counted continuations. -/
noncomputable def applyUniformSignAttemptMonitorC
    (leafIndex : LeafIndex)
    (resume : Digest → EncodingMonitor.State → ProbComp (Bool × Nat))
    (state : EncodingMonitor.State) : ProbComp (Bool × Nat) := do
  let digest ← $ᵗ Digest
  if TargetSum.ValidDigest digest then
    match state.signed leafIndex with
    | some _ => pure (false, 0)
    | none =>
        if digest ∈ state.pending leafIndex then pure (true, 0)
        else resume digest (state.install leafIndex digest)
  else resume digest state

theorem applyUniformSignAttemptMonitorC_le
    (leafIndex : LeafIndex)
    (resume : Digest → EncodingMonitor.State → ProbComp (Bool × Nat))
    (state : EncodingMonitor.State) (offset : ℝ≥0∞)
    (hresume : ∀ digest nextState,
      Pr{let x ← resume digest nextState}[x.1 = true] ≤
        u * countMean (resume digest nextState) + (offset + State.pendingRisk nextState)) :
    Pr{let x ← applyUniformSignAttemptMonitorC leafIndex resume state}[x.1 = true] ≤
      u * countMean (applyUniformSignAttemptMonitorC leafIndex resume state) +
        (offset + State.pendingRisk state) := by
  unfold applyUniformSignAttemptMonitorC
  cases hsigned : state.signed leafIndex with
  | some target =>
      refine (prHit_bind_le_const _ _ (offset + State.pendingRisk state) u fun digest => ?_)
      by_cases hvalid : TargetSum.ValidDigest digest
      · simp [hvalid]
      · simpa [hvalid] using hresume digest state
  | none =>
      let remaining := State.pendingRisk (state.install leafIndex 0)
      let removed := ((state.pending leafIndex).card : ℝ≥0∞) *
        (TargetSum.validDigests.card : ℝ≥0∞)⁻¹
      have hrisk : remaining + removed = State.pendingRisk state :=
        State.pendingRisk_install_add state leafIndex 0
      refine (prHit_bind_le _ _
        (fun digest => (if TargetSum.ValidDigest digest then
            (if digest ∈ state.pending leafIndex then 1 else 0) else removed) +
          (offset + remaining))
        u fun digest => ?_).trans ?_
      · by_cases hvalid : TargetSum.ValidDigest digest
        · simp only [hvalid, ↓reduceIte]
          by_cases hmem : digest ∈ state.pending leafIndex
          · simp [hmem]
          · simp only [hmem, ↓reduceIte, zero_add]
            have hriskEq : State.pendingRisk (state.install leafIndex digest) = remaining := by
              unfold remaining State.pendingRisk
              rw [EncodingMonitor.State.pendingCount_install_eq state leafIndex digest 0]
            simpa [hriskEq] using hresume digest (state.install leafIndex digest)
        · simp only [hvalid, ↓reduceIte]
          refine (hresume digest state).trans_eq ?_
          rw [← hrisk]
          ac_rfl
      · rw [tsum_prEvent_mul_add_const, tsum_uniformDigest_eq_sum]
        calc
          _ ≤ u * countMean _ + (removed + (offset + remaining)) := by
            gcongr
            exact uniformDigest_sign_bonus_sum_le (state.pending leafIndex)
          _ = _ := by rw [← hrisk]; ac_rfl

/-- `applyProgrammedQueryMonitor`, counted. -/
noncomputable def applyProgrammedQueryMonitorC
    (leafIndex : LeafIndex)
    (resume : HashOutput → EncodingMonitor.State → ProbComp (Bool × Nat))
    (state : EncodingMonitor.State) : ProbComp (Bool × Nat) :=
  applyUniformQueryMonitorC leafIndex
    (fun digest nextState =>
      Rom.sampleHashOutputWithDigest digest >>= fun output =>
        resume output nextState)
    state

theorem applyProgrammedQueryMonitorC_le
    (leafIndex : LeafIndex)
    (resume : HashOutput → EncodingMonitor.State → ProbComp (Bool × Nat))
    (state : EncodingMonitor.State) (offset : ℝ≥0∞)
    (hresume : ∀ output nextState,
      Pr{let x ← resume output nextState}[x.1 = true] ≤
        u * countMean (resume output nextState) + (offset + State.pendingRisk nextState)) :
    Pr{let x ← applyProgrammedQueryMonitorC leafIndex resume state}[x.1 = true] ≤
      u * (countMean (applyProgrammedQueryMonitorC leafIndex resume state) + 1) +
        (offset + State.pendingRisk state) :=
  applyUniformQueryMonitorC_le leafIndex _ state offset fun _ nextState =>
    prHit_bind_le_const _ _ _ _ fun output => hresume output nextState

/-- `applyProgrammedSignAttemptMonitor`, counted. -/
noncomputable def applyProgrammedSignAttemptMonitorC
    (leafIndex : LeafIndex)
    (resume : HashOutput → EncodingMonitor.State → ProbComp (Bool × Nat))
    (state : EncodingMonitor.State) : ProbComp (Bool × Nat) :=
  applyUniformSignAttemptMonitorC leafIndex
    (fun digest nextState =>
      Rom.sampleHashOutputWithDigest digest >>= fun output =>
        resume output nextState)
    state

theorem applyProgrammedSignAttemptMonitorC_le
    (leafIndex : LeafIndex)
    (resume : HashOutput → EncodingMonitor.State → ProbComp (Bool × Nat))
    (state : EncodingMonitor.State) (offset : ℝ≥0∞)
    (hresume : ∀ output nextState,
      Pr{let x ← resume output nextState}[x.1 = true] ≤
        u * countMean (resume output nextState) + (offset + State.pendingRisk nextState)) :
    Pr{let x ← applyProgrammedSignAttemptMonitorC leafIndex resume state}[x.1 = true] ≤
      u * countMean (applyProgrammedSignAttemptMonitorC leafIndex resume state) +
        (offset + State.pendingRisk state) :=
  applyUniformSignAttemptMonitorC_le leafIndex _ state offset fun _ nextState =>
    prHit_bind_le_const _ _ _ _ fun output => hresume output nextState

/-- The observed form of a counted query: a hit stops with count `0`. -/
noncomputable def applyObservedQueryC
    (leafIndex : LeafIndex)
    (resume : HashOutput → EncodingMonitor.State → ProbComp (Bool × Nat))
    (state : EncodingMonitor.State) : ProbComp (Bool × Nat) :=
  uniformHashOutput >>= fun output =>
    match State.applyObserved state (.query leafIndex output) with
    | none => pure (false, 0)
    | some (nextState, hit) => if hit then pure (true, 0) else resume output nextState

/-- The observed form of a counted signing attempt. -/
noncomputable def applyObservedSignAttemptC
    (leafIndex : LeafIndex)
    (resume : HashOutput → EncodingMonitor.State → ProbComp (Bool × Nat))
    (state : EncodingMonitor.State) : ProbComp (Bool × Nat) :=
  uniformHashOutput >>= fun output =>
    match State.applyObserved state (.sign leafIndex output) with
    | none => pure (false, 0)
    | some (nextState, hit) => if hit then pure (true, 0) else resume output nextState

theorem applyProgrammedQueryMonitorC_evalDist_eq
    (leafIndex : LeafIndex)
    (resume : HashOutput → EncodingMonitor.State → ProbComp (Bool × Nat))
    (state : EncodingMonitor.State) :
    (applyProgrammedQueryMonitorC leafIndex resume state) =ᵈ
      (applyObservedQueryC leafIndex resume state) := by
  let continuation := fun result : Digest × HashOutput =>
    match state.signed leafIndex with
    | some target =>
        if result.1 = target then pure (true, 0) else resume result.2 state
    | none =>
        if TargetSum.ValidDigest result.1 then
          resume result.2 (state.addPending leafIndex result.1)
        else resume result.2 state
  calc
    _ =ᵈ ($ᵗ Digest >>= fun digest =>
          Rom.sampleHashOutputWithDigest digest >>= fun output =>
            continuation (digest, output)) := by
      unfold applyProgrammedQueryMonitorC applyUniformQueryMonitorC continuation
      apply EvalDistEq.bind_right
      intro digest
      cases hsigned : state.signed leafIndex with
      | none =>
          by_cases hvalid : TargetSum.ValidDigest digest <;>
            simp only [hvalid, ↓reduceIte, EvalDistEq.refl]
      | some target =>
          by_cases heq : digest = target
          · simp only [heq, ↓reduceIte]
            symm
            exact OracleComp.EvalDistEq.bind_const _ _
          · simp only [heq, ↓reduceIte, EvalDistEq.refl]
    _ =ᵈ (Rom.sampledHashOutputWithDigest >>= continuation) := .of_eq rfl
    _ =ᵈ ($ᵗ HashOutput >>= fun output =>
          continuation (truncateHash output, output)) :=
      Rom.evalDist_sampledHashOutputWithDigest_bind_eq_uniform_bind continuation
    _ = _ := by
      unfold applyObservedQueryC continuation
      apply bind_congr
      intro output
      cases hsigned : state.signed leafIndex with
      | some target =>
          by_cases heq : truncateHash output = target <;>
            simp [State.applyObserved, hsigned, heq]
      | none =>
          by_cases hvalid : TargetSum.ValidDigest (truncateHash output) <;>
            simp [State.applyObserved, hsigned, hvalid]

theorem applyProgrammedSignAttemptMonitorC_evalDist_eq
    (leafIndex : LeafIndex)
    (resume : HashOutput → EncodingMonitor.State → ProbComp (Bool × Nat))
    (state : EncodingMonitor.State) :
    (applyProgrammedSignAttemptMonitorC leafIndex resume state) =ᵈ
      (applyObservedSignAttemptC leafIndex resume state) := by
  let continuation := fun result : Digest × HashOutput =>
    if TargetSum.ValidDigest result.1 then
      match state.signed leafIndex with
      | some _ => pure (false, 0)
      | none =>
          if result.1 ∈ state.pending leafIndex then pure (true, 0)
          else resume result.2 (state.install leafIndex result.1)
    else resume result.2 state
  calc
    _ =ᵈ ($ᵗ Digest >>= fun digest =>
          Rom.sampleHashOutputWithDigest digest >>= fun output =>
            continuation (digest, output)) := by
      unfold applyProgrammedSignAttemptMonitorC applyUniformSignAttemptMonitorC continuation
      apply EvalDistEq.bind_right
      intro digest
      by_cases hvalid : TargetSum.ValidDigest digest
      · simp only [hvalid, ↓reduceIte]
        cases hsigned : state.signed leafIndex with
        | some target =>
            symm
            exact OracleComp.EvalDistEq.bind_const _ _
        | none =>
            by_cases hmem : digest ∈ state.pending leafIndex
            · simp only [hmem, ↓reduceIte]
              symm
              exact OracleComp.EvalDistEq.bind_const _ _
            · simp only [hmem, ↓reduceIte, EvalDistEq.refl]
      · simp only [hvalid, ↓reduceIte, EvalDistEq.refl]
    _ =ᵈ (Rom.sampledHashOutputWithDigest >>= continuation) := .of_eq rfl
    _ =ᵈ ($ᵗ HashOutput >>= fun output =>
          continuation (truncateHash output, output)) :=
      Rom.evalDist_sampledHashOutputWithDigest_bind_eq_uniform_bind continuation
    _ = _ := by
      unfold applyObservedSignAttemptC continuation
      apply bind_congr
      intro output
      by_cases hvalid : TargetSum.ValidDigest (truncateHash output)
      · cases hsigned : state.signed leafIndex with
        | some target => simp [State.applyObserved, hvalid, hsigned]
        | none =>
            by_cases hmem : truncateHash output ∈ state.pending leafIndex <;>
              simp [State.applyObserved, hvalid, hsigned, hmem]
      · simp [State.applyObserved, hvalid]

end CappedEncodingMonitor

/-! ## The counted structural run -/

namespace FirstLaneOracleSimulation

variable {Index : Type} [Fintype Index] [DecidableEq Index]

local notation "u" => ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹

/-- A query is a hazard, a signing attempt is not. -/
def encodingActionHazards : EncodingMonitor.ObservedAction → Nat
  | .query _ _ => 1
  | .sign _ _ => 0

/-- The hazard actions of a trace the combined monitor processes, the one it stops at included. -/
noncomputable def observedHazards (table : Index → Digest) :
    Option EncodingMonitor.State → AdaptiveRevealMonitor.State Index →
      ActionTrace Index → Nat
  | _encodingState, _chainState, [] => 0
  | encodingState, chainState, .encoding action :: rest =>
      (match encodingState with
        | none => observedHazards table none chainState rest
        | some state =>
            match CappedEncodingMonitor.State.applyObserved state action with
            | none => observedHazards table none chainState rest
            | some (nextState, hit) =>
                if hit then 0 else observedHazards table (some nextState) chainState rest) +
        encodingActionHazards action
  | encodingState, chainState, .chain (.probe index target) :: rest =>
      (match chainState.revealed index with
        | some _ => observedHazards table encodingState chainState rest
        | none => observedHazards table encodingState
            (chainState.addPending index target) rest) + 1
  | encodingState, chainState, .chain (.reveal index _value) :: rest =>
      match chainState.revealed index with
      | some _ => observedHazards table encodingState chainState rest
      | none =>
          if table index ∈ chainState.pending index then 0
          else observedHazards table encodingState
            (chainState.install index (table index)) rest

/-- `applyEncodingRequest`, counted: a hit stops with count `0`. -/
noncomputable def applyEncodingRequestC
    (request : EncodingRequest)
    (resume : HashOutput → Option EncodingMonitor.State → ProbComp (Bool × Nat)) :
    Option EncodingMonitor.State → ProbComp (Bool × Nat)
  | none => uniformHashOutput >>= fun output => resume output none
  | some state => uniformHashOutput >>= fun output =>
      match CappedEncodingMonitor.State.applyObserved state
        (request.observed output) with
      | none => resume output none
      | some (nextState, hit) =>
          if hit then pure (true, 0) else resume output (some nextState)

theorem evalDist_sample_applyEncodingRequestC
    (sample : ProbComp β)
    (request : EncodingRequest)
    (resume : β → HashOutput → Option EncodingMonitor.State → ProbComp (Bool × Nat))
    (state : Option EncodingMonitor.State) :
    (sample >>= fun seed =>
      applyEncodingRequestC request (resume seed) state) =ᵈ
      (applyEncodingRequestC request
        (fun output nextState => sample >>= fun seed =>
          resume seed output nextState) state) := by
  cases state with
  | none =>
      unfold applyEncodingRequestC
      exact OracleComp.EvalDistEq.bind_bind_swap _ _ _
  | some state =>
      unfold applyEncodingRequestC
      refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
      apply EvalDistEq.bind_right
      intro output
      cases happly : CappedEncodingMonitor.State.applyObserved state
        (request.observed output) with
      | none => rfl
      | some result =>
          rcases result with ⟨nextState, hit⟩
          cases hit with
          | false => rfl
          | true =>
              exact OracleComp.EvalDistEq.bind_const sample (pure (true, 0))

theorem card_digest_inv :
    (Fintype.card Digest : ℝ≥0∞)⁻¹ = ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [HiddenValue.card_digest]

theorem applyEncodingRequestC_le
    (request : EncodingRequest)
    (resume : HashOutput → Option EncodingMonitor.State → ProbComp (Bool × Nat))
    (state : Option EncodingMonitor.State) (offset : ℝ≥0∞)
    (hresume : ∀ output nextState,
      Pr{let x ← resume output nextState}[x.1 = true] ≤
        u * countMean (resume output nextState) + (offset + encodingPendingRisk nextState)) :
    Pr{let x ← applyEncodingRequestC request resume state}[x.1 = true] ≤
      u * (countMean (applyEncodingRequestC request resume state) + request.cost) +
        (offset + encodingPendingRisk state) := by
  have hsome : ∀ output nextState,
      Pr{let x ← resume output (some nextState)}[x.1 = true] ≤
        (Fintype.card Digest : ℝ≥0∞)⁻¹ * countMean (resume output (some nextState)) +
          (offset + CappedEncodingMonitor.State.pendingRisk nextState) := fun output nextState => by
    rw [card_digest_inv]
    simpa [encodingPendingRisk] using hresume output (some nextState)
  cases request with
  | query leafIndex =>
      cases state with
      | none =>
          unfold applyEncodingRequestC
          refine (prHit_bind_le_const _ _ offset u fun output => by
            simpa [encodingPendingRisk] using hresume output none).trans ?_
          simp only [EncodingRequest.cost, encodingPendingRisk, add_zero, Nat.cast_one]
          gcongr
          exact le_self_add
      | some state =>
          have hdirect :
              applyEncodingRequestC (.query leafIndex) resume (some state) =
                CappedEncodingMonitor.applyObservedQueryC leafIndex
                  (fun output nextState => resume output (some nextState)) state := by
            unfold applyEncodingRequestC CappedEncodingMonitor.applyObservedQueryC
            apply bind_congr
            intro output
            cases hsigned : state.signed leafIndex with
            | none =>
                by_cases hvalid : TargetSum.ValidDigest (truncateHash output) <;>
                  simp [EncodingRequest.observed, CappedEncodingMonitor.State.applyObserved,
                    hsigned, hvalid]
            | some target =>
                simp [EncodingRequest.observed, CappedEncodingMonitor.State.applyObserved,
                  hsigned]
          have hdist :
              (applyEncodingRequestC (.query leafIndex) resume (some state)) =ᵈ
                (CappedEncodingMonitor.applyProgrammedQueryMonitorC leafIndex
                  (fun output nextState => resume output (some nextState)) state) := by
            rw [hdirect]
            exact (CappedEncodingMonitor.applyProgrammedQueryMonitorC_evalDist_eq _ _ _).symm
          rw [hdist.prEvent_eq (fun x => x.1 = true), countMean_congr hdist]
          simpa [EncodingRequest.cost, encodingPendingRisk, card_digest_inv] using
            CappedEncodingMonitor.applyProgrammedQueryMonitorC_le leafIndex
              (fun output nextState => resume output (some nextState)) state offset hsome
  | sign leafIndex =>
      cases state with
      | none =>
          unfold applyEncodingRequestC
          simpa [EncodingRequest.cost, encodingPendingRisk] using
            prHit_bind_le_const _ _ offset u fun output => by
              simpa [encodingPendingRisk] using hresume output none
      | some state =>
          cases hsigned : state.signed leafIndex with
          | none =>
              have hdirect :
                  applyEncodingRequestC (.sign leafIndex) resume (some state) =
                    CappedEncodingMonitor.applyObservedSignAttemptC leafIndex
                      (fun output nextState => resume output (some nextState)) state := by
                unfold applyEncodingRequestC CappedEncodingMonitor.applyObservedSignAttemptC
                apply bind_congr
                intro output
                by_cases hvalid : TargetSum.ValidDigest (truncateHash output) <;>
                  simp [EncodingRequest.observed, CappedEncodingMonitor.State.applyObserved,
                    hsigned, hvalid]
              have hdist :
                  (applyEncodingRequestC (.sign leafIndex) resume (some state)) =ᵈ
                    (CappedEncodingMonitor.applyProgrammedSignAttemptMonitorC leafIndex
                      (fun output nextState => resume output (some nextState)) state) := by
                rw [hdirect]
                exact (CappedEncodingMonitor.applyProgrammedSignAttemptMonitorC_evalDist_eq
                  _ _ _).symm
              rw [hdist.prEvent_eq (fun x => x.1 = true), countMean_congr hdist]
              simpa [EncodingRequest.cost, encodingPendingRisk, card_digest_inv] using
                CappedEncodingMonitor.applyProgrammedSignAttemptMonitorC_le leafIndex
                  (fun output nextState => resume output (some nextState)) state offset hsome
          | some target =>
              unfold applyEncodingRequestC
              refine (prHit_bind_le_const _ _ (offset + encodingPendingRisk (some state)) u
                fun output => ?_).trans ?_
              · by_cases hvalid : TargetSum.ValidDigest (truncateHash output)
                · rw [show CappedEncodingMonitor.State.applyObserved state
                      ((EncodingRequest.sign leafIndex).observed output) = none by
                    simp [EncodingRequest.observed, CappedEncodingMonitor.State.applyObserved,
                      hsigned, hvalid]]
                  refine (hresume output none).trans ?_
                  simp only [encodingPendingRisk, add_zero]
                  gcongr
                  exact le_self_add
                · rw [show CappedEncodingMonitor.State.applyObserved state
                      ((EncodingRequest.sign leafIndex).observed output) = some (state, false) by
                    simp [EncodingRequest.observed, CappedEncodingMonitor.State.applyObserved,
                      hvalid]]
                  exact hresume output (some state)
              · simp [EncodingRequest.cost]

/-- One counted query of the eager experiment: hazards add one, a hit stops with count `0`. -/
noncomputable def runEagerQueryC
    (table : Index → Digest)
    (encodingState : Option EncodingMonitor.State)
    (chainState : AdaptiveRevealMonitor.State Index)
    (input : Query Index)
    (resume : (World Index).Range input → Option EncodingMonitor.State →
      AdaptiveRevealMonitor.State Index → ProbComp (Bool × Nat)) :
    ProbComp (Bool × Nat) :=
  match input with
  | .uniform n => do
      let output ← (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
      resume output encodingState chainState
  | .encodingQuery leafIndex =>
      addHazard <$> applyEncodingRequestC (.query leafIndex)
        (fun output nextState => resume output nextState chainState) encodingState
  | .encodingSignAttempt leafIndex =>
      applyEncodingRequestC (.sign leafIndex)
        (fun output nextState => resume output nextState chainState) encodingState
  | .probe index target =>
      addHazard <$> match chainState.revealed index with
        | some _ => resume () encodingState chainState
        | none => resume () encodingState (chainState.addPending index target)
  | .reveal index =>
      match chainState.revealed index with
      | some _ => resume (table index) encodingState chainState
      | none =>
          let value := table index
          if value ∈ chainState.pending index then pure (true, 0)
          else resume value encodingState (chainState.install index value)

/-- The structural run, counted: the hit flag and the hazards processed before stopping. -/
noncomputable def runStructuralC
    (table : Index → Digest)
    (encodingState : Option EncodingMonitor.State)
    (chainState : AdaptiveRevealMonitor.State Index)
    (computation : OracleComp (World Index) α) : ProbComp (Bool × Nat) :=
  OracleComp.construct
    (C := fun _ => Option EncodingMonitor.State →
      AdaptiveRevealMonitor.State Index → ProbComp (Bool × Nat))
    (fun _ _encodingState chainState =>
      pure (RevealProbeOracleSimulation.tableHits chainState table, 0))
    (fun input _next recursivelyRun encodingState chainState =>
      runEagerQueryC table encodingState chainState input recursivelyRun)
    computation encodingState chainState

theorem runStructuralC_query_bind
    (table : Index → Digest)
    (encodingState : Option EncodingMonitor.State)
    (chainState : AdaptiveRevealMonitor.State Index)
    (input : (World Index).Domain)
    (next : (World Index).Range input → OracleComp (World Index) α) :
    runStructuralC table encodingState chainState
        ((liftM (OracleSpec.query input) :
          OracleComp (World Index) ((World Index).Range input)) >>= next) =
      runEagerQueryC table encodingState chainState input fun output
        nextEncoding nextChain =>
          runStructuralC table nextEncoding nextChain (next output) := by
  rw [runStructuralC, OracleComp.construct_query_bind]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem evalDist_observed_eagerTrace_eq_runStructuralC
    (table : Index → Digest)
    (encodingState : Option EncodingMonitor.State)
    (chainState : AdaptiveRevealMonitor.State Index)
    (computation : OracleComp (World Index) α) :
    ((fun result => (runObserved table encodingState chainState result.2,
        observedHazards table encodingState chainState result.2)) <$>
      (simulateQ (eagerTraceImpl table) computation).run) =ᵈ
    (runStructuralC table encodingState chainState computation) := by
  induction computation using OracleComp.inductionOn generalizing
      encodingState chainState with
  | pure result =>
      simp [eagerTraceImpl, runObserved, observedHazards, runStructuralC]
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [eagerTrace_query_bind_run, runStructuralC_query_bind]
          simp only [eagerImpl, traceFragment, map_bind, runEagerQueryC]
          apply EvalDistEq.bind_right
          intro output
          simpa [runObserved, observedHazards] using ih output encodingState chainState
      | encodingQuery leafIndex =>
          cases encodingState with
          | none =>
              rw [eagerTrace_query_bind_run, runStructuralC_query_bind]
              simp only [eagerImpl, traceFragment, runEagerQueryC, applyEncodingRequestC]
              rw [map_bind, map_bind]
              apply EvalDistEq.bind_right
              intro output
              have h := (ih output none chainState).map addHazard
              simp only [Functor.map_map] at h
              refine (EvalDistEq.of_eq ?_).trans h
              simp [map_eq_bind_pure_comp, runObserved, observedHazards, encodingActionHazards,
                addHazard]
          | some state =>
              rw [eagerTrace_query_bind_run, runStructuralC_query_bind]
              simp only [eagerImpl, traceFragment, runEagerQueryC, applyEncodingRequestC,
                EncodingRequest.observed]
              rw [map_bind, map_bind]
              apply EvalDistEq.bind_right
              intro output
              cases happly : CappedEncodingMonitor.State.applyObserved state
                (.query leafIndex output) with
              | none =>
                  have h := (ih output none chainState).map addHazard
                  simp only [Functor.map_map] at h
                  refine (EvalDistEq.of_eq ?_).trans h
                  simp [map_eq_bind_pure_comp, runObserved, observedHazards,
                    encodingActionHazards, addHazard, happly]
              | some result =>
                  rcases result with ⟨nextState, hit⟩
                  cases hit with
                  | false =>
                      have h := (ih output (some nextState) chainState).map addHazard
                      simp only [Functor.map_map] at h
                      refine (EvalDistEq.of_eq ?_).trans h
                      simp [map_eq_bind_pure_comp, runObserved, observedHazards,
                        encodingActionHazards, addHazard, happly]
                  | true =>
                      simp [runObserved, observedHazards, encodingActionHazards, addHazard,
                        happly]
                      exact OracleComp.EvalDistEq.map_const _ _
      | encodingSignAttempt leafIndex =>
          cases encodingState with
          | none =>
              rw [eagerTrace_query_bind_run, runStructuralC_query_bind]
              simp only [eagerImpl, traceFragment, runEagerQueryC, applyEncodingRequestC]
              rw [map_bind]
              apply EvalDistEq.bind_right
              intro output
              refine (EvalDistEq.of_eq ?_).trans (ih output none chainState)
              simp [map_eq_bind_pure_comp, runObserved, observedHazards, encodingActionHazards]
          | some state =>
              rw [eagerTrace_query_bind_run, runStructuralC_query_bind]
              simp only [eagerImpl, traceFragment, runEagerQueryC, applyEncodingRequestC,
                EncodingRequest.observed]
              rw [map_bind]
              apply EvalDistEq.bind_right
              intro output
              cases happly : CappedEncodingMonitor.State.applyObserved state
                (.sign leafIndex output) with
              | none =>
                  refine (EvalDistEq.of_eq ?_).trans (ih output none chainState)
                  simp [map_eq_bind_pure_comp, runObserved, observedHazards,
                    encodingActionHazards, happly]
              | some result =>
                  rcases result with ⟨nextState, hit⟩
                  cases hit with
                  | false =>
                      refine (EvalDistEq.of_eq ?_).trans (ih output (some nextState) chainState)
                      simp [map_eq_bind_pure_comp, runObserved, observedHazards,
                        encodingActionHazards, happly]
                  | true =>
                      simp [runObserved, observedHazards, encodingActionHazards, happly]
                      exact OracleComp.EvalDistEq.map_const _ _
      | probe index target =>
          rw [eagerTrace_query_bind_run, runStructuralC_query_bind]
          simp only [eagerImpl, traceFragment, runEagerQueryC, pure_bind]
          cases hrevealed : chainState.revealed index with
          | none =>
              have h := (ih () encodingState (chainState.addPending index target)).map addHazard
              simp only [Functor.map_map] at h
              refine (EvalDistEq.of_eq ?_).trans h
              simp [map_eq_bind_pure_comp, runObserved, observedHazards, addHazard, hrevealed]
          | some value =>
              have h := (ih () encodingState chainState).map addHazard
              simp only [Functor.map_map] at h
              refine (EvalDistEq.of_eq ?_).trans h
              simp [map_eq_bind_pure_comp, runObserved, observedHazards, addHazard, hrevealed]
      | reveal index =>
          rw [eagerTrace_query_bind_run, runStructuralC_query_bind]
          simp only [eagerImpl, traceFragment, runEagerQueryC, pure_bind]
          cases hrevealed : chainState.revealed index with
          | some value =>
              refine (EvalDistEq.of_eq ?_).trans (ih (table index) encodingState chainState)
              simp [map_eq_bind_pure_comp, runObserved, observedHazards, hrevealed]
          | none =>
              by_cases hhit : table index ∈ chainState.pending index
              · simp [runObserved, observedHazards, hrevealed, hhit]
                exact OracleComp.EvalDistEq.map_const _ _
              · simp only [hhit, ↓reduceIte]
                refine (EvalDistEq.of_eq ?_).trans
                  (ih (table index) encodingState (chainState.install index (table index)))
                simp [map_eq_bind_pure_comp, runObserved, observedHazards, hrevealed, hhit]

/-- The counted structural run over a table drawn after the revealed values. -/
noncomputable def structuralExperimentC
    (encodingState : Option EncodingMonitor.State)
    (chainState : AdaptiveRevealMonitor.State Index)
    (computation : OracleComp (World Index) α) : ProbComp (Bool × Nat) := do
  let base ← RevealProbeOracleSimulation.eagerTableSample
  runStructuralC (RevealProbeOracleSimulation.extendTable chainState base)
    encodingState chainState computation

theorem structuralExperimentC_query_bind
    (encodingState : Option EncodingMonitor.State)
    (chainState : AdaptiveRevealMonitor.State Index)
    (input : (World Index).Domain)
    (next : (World Index).Range input → OracleComp (World Index) α) :
    structuralExperimentC encodingState chainState
        ((liftM (OracleSpec.query input) :
          OracleComp (World Index) ((World Index).Range input)) >>= next) =
      RevealProbeOracleSimulation.eagerTableSample >>= fun base =>
        runEagerQueryC
          (RevealProbeOracleSimulation.extendTable chainState base)
          encodingState chainState input fun output nextEncoding nextChain =>
              runStructuralC
                (RevealProbeOracleSimulation.extendTable chainState base)
                nextEncoding nextChain (next output) := by
  unfold structuralExperimentC
  apply bind_congr
  intro base
  exact runStructuralC_query_bind _ _ _ _ _

/-- A hidden value revealed, counted. -/
noncomputable def applyRevealRequestC
    (state : AdaptiveRevealMonitor.State Index) (index : Index)
    (resume : Digest → AdaptiveRevealMonitor.State Index → ProbComp (Bool × Nat)) :
    ProbComp (Bool × Nat) := do
  let value ← $ᵗ Digest
  if value ∈ state.pending index then pure (true, 0)
  else resume value (state.install index value)

theorem tsum_prEvent_mul_indicator {β : Type} (mx : ProbComp β) (p : β → Prop)
    [DecidablePred p] :
    ∑' x, Pr{let y ← mx}[y = x] * (if p x then 1 else 0) = Pr{let y ← mx}[p y] := by
  rw [OracleComp.prEvent_eq_tsum_ite]
  exact tsum_congr fun x => by split_ifs <;> simp

theorem applyRevealRequestC_le
    (state : AdaptiveRevealMonitor.State Index) (index : Index)
    (resume : Digest → AdaptiveRevealMonitor.State Index → ProbComp (Bool × Nat))
    (offset : ℝ≥0∞)
    (hresume : ∀ value,
      Pr{let x ← resume value (state.install index value)}[x.1 = true] ≤
        u * (countMean (resume value (state.install index value)) +
          (state.install index value).pendingCount) + offset) :
    Pr{let x ← applyRevealRequestC state index resume}[x.1 = true] ≤
      u * (countMean (applyRevealRequestC state index resume) + state.pendingCount) +
        offset := by
  classical
  let installedCount := (state.install index 0).pendingCount
  unfold applyRevealRequestC
  refine (prHit_bind_le _ _
    (fun value => (if value ∈ state.pending index then 1 else 0) +
      (u * installedCount + offset)) u fun value => ?_).trans ?_
  · by_cases hhit : value ∈ state.pending index
    · simp [hhit]
    · simp only [hhit, ↓reduceIte, zero_add]
      have hcount : (state.install index value).pendingCount = installedCount := rfl
      refine (hresume value).trans_eq ?_
      rw [hcount, mul_add, add_assoc]
  · rw [tsum_prEvent_mul_add_const, tsum_prEvent_mul_indicator]
    have hconserve := state.pendingCount_install_add index 0
    calc
      _ ≤ u * countMean _ + ((state.pending index).card * u + (u * installedCount + offset)) := by
        gcongr
        exact RevealProbeOracleSimulation.uniformDigest_mem_finset_le (state.pending index)
      _ = u * (countMean _ + ((installedCount + (state.pending index).card : Nat) : ℝ≥0∞)) +
          offset := by
        push_cast
        ring
      _ = _ := by rw [hconserve]

theorem evalDist_eagerTableSample_applyRevealRequestC
    (chainState : AdaptiveRevealMonitor.State Index)
    (index : Index) (hrevealed : chainState.revealed index = none)
    (resume : (Index → Digest) → Digest →
      AdaptiveRevealMonitor.State Index → ProbComp (Bool × Nat)) :
    (RevealProbeOracleSimulation.eagerTableSample >>= fun base =>
      let table := RevealProbeOracleSimulation.extendTable chainState base
      let value := table index
      if value ∈ chainState.pending index then pure (true, 0)
      else resume table value (chainState.install index value)) =ᵈ
      (applyRevealRequestC chainState index fun value nextState =>
        RevealProbeOracleSimulation.eagerTableSample >>= fun base =>
          resume (RevealProbeOracleSimulation.extendTable nextState base)
            value nextState) := by
  let continuation := fun (base : Index → Digest) =>
    let table := RevealProbeOracleSimulation.extendTable chainState base
    let value := table index
    if value ∈ chainState.pending index then pure (true, 0)
    else resume table value (chainState.install index value)
  calc
    _ =ᵈ (do
          let value ← $ᵗ Digest
          let base ← RevealProbeOracleSimulation.eagerTableSample
          if value ∈ chainState.pending index then pure (true, 0)
          else
            resume
              (RevealProbeOracleSimulation.extendTable
                (chainState.install index value) base)
              value (chainState.install index value)) := by
        unfold RevealProbeOracleSimulation.eagerTableSample
        refine (RevealProbeOracleSimulation.evalDist_uniformTable_eq_bind_update
          index continuation).trans ?_
        apply EvalDistEq.bind_right
        intro value
        apply EvalDistEq.bind_right
        intro base
        simp only [continuation]
        rw [RevealProbeOracleSimulation.extendTable_update_eq_install
          chainState index value base hrevealed]
        have hinstalled :
            RevealProbeOracleSimulation.extendTable
              (chainState.install index value) base index = value := by
          simp [RevealProbeOracleSimulation.extendTable,
            AdaptiveRevealMonitor.State.install]
        rw [hinstalled]
    _ =ᵈ (_ : ProbComp (Bool × Nat)) := by
      unfold applyRevealRequestC
      apply EvalDistEq.bind_right
      intro value
      by_cases hhit : value ∈ chainState.pending index
      · simp only [hhit, ↓reduceIte]
        exact OracleComp.EvalDistEq.bind_const
          RevealProbeOracleSimulation.eagerTableSample (pure (true, 0))
      · simp [hhit]

theorem eagerFinalizeC_le
    (encodingState : Option EncodingMonitor.State)
    (chainState : AdaptiveRevealMonitor.State Index)
    (hvalid : RevealProbeOracleSimulation.StateValid chainState) :
    Pr{let x ← (RevealProbeOracleSimulation.eagerTableSample >>= fun base =>
        (pure (RevealProbeOracleSimulation.tableHits chainState
          (RevealProbeOracleSimulation.extendTable chainState base), 0) :
            ProbComp (Bool × Nat)))}[x.1 = true] ≤
      u * (countMean (RevealProbeOracleSimulation.eagerTableSample >>= fun base =>
        (pure (RevealProbeOracleSimulation.tableHits chainState
          (RevealProbeOracleSimulation.extendTable chainState base), 0) :
            ProbComp (Bool × Nat))) + chainState.pendingCount) +
        encodingPendingRisk encodingState := by
  have hzero : countMean (RevealProbeOracleSimulation.eagerTableSample >>= fun base =>
      (pure (RevealProbeOracleSimulation.tableHits chainState
        (RevealProbeOracleSimulation.extendTable chainState base), 0) :
          ProbComp (Bool × Nat))) = 0 := by
    rw [countMean_bind]
    simp
  rw [hzero, zero_add]
  have hmap : Pr{let x ← (RevealProbeOracleSimulation.eagerTableSample >>= fun base =>
      (pure (RevealProbeOracleSimulation.tableHits chainState
        (RevealProbeOracleSimulation.extendTable chainState base), 0) :
          ProbComp (Bool × Nat)))}[x.1 = true] =
      Pr{let hit ← ((fun base : Index → Digest =>
        RevealProbeOracleSimulation.tableHits chainState
          (RevealProbeOracleSimulation.extendTable chainState base)) <$>
        RevealProbeOracleSimulation.eagerTableSample)}[hit = true] := by
    rw [bind_pure_comp, prEvent_map, prEvent_map]
  rw [hmap]
  refine (RevealProbeOracleSimulation.eagerFinalize_true_probability_le
    chainState hvalid).trans ?_
  rw [mul_comm]
  exact le_self_add

set_option maxRecDepth 100000 in
/-- The counted potential argument: a hit costs `2^-128` per expected processed hazard, plus the
pending targets and the encoding monitor's pending risk. -/
theorem structuralExperimentC_le
    (encodingState : Option EncodingMonitor.State)
    (chainState : AdaptiveRevealMonitor.State Index)
    (hvalid : RevealProbeOracleSimulation.StateValid chainState)
    (computation : OracleComp (World Index) α) :
    Pr{let x ← structuralExperimentC encodingState chainState computation}[x.1 = true] ≤
      u * (countMean (structuralExperimentC encodingState chainState computation) +
        chainState.pendingCount) + encodingPendingRisk encodingState := by
  induction computation using OracleComp.inductionOn generalizing
      encodingState chainState with
  | pure result =>
      exact eagerFinalizeC_le encodingState chainState hvalid
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          have hdist :
              (structuralExperimentC encodingState chainState
                ((liftM (OracleSpec.query (spec := World Index) (.uniform n)) :
                  OracleComp (World Index) _) >>= next)) =ᵈ
                ((liftM (unifSpec.query n) : ProbComp _) >>= fun output =>
                  structuralExperimentC encodingState chainState (next output)) := by
            rw [structuralExperimentC_query_bind]
            simp only [runEagerQueryC]
            exact OracleComp.EvalDistEq.bind_bind_swap _ _ _
          rw [hdist.prEvent_eq (fun x => x.1 = true), countMean_congr hdist]
          refine (prHit_bind_le_const _ _
            (u * chainState.pendingCount + encodingPendingRisk encodingState) u
            fun output => (ih output encodingState chainState hvalid).trans_eq (by ring)).trans_eq
            (by ring)
      | encodingQuery leafIndex =>
          let resume := fun output nextState =>
            structuralExperimentC nextState chainState (next output)
          have hdist :
              (structuralExperimentC encodingState chainState
                ((liftM (OracleSpec.query (spec := World Index)
                  (.encodingQuery leafIndex)) :
                  OracleComp (World Index) _) >>= next)) =ᵈ
                (addHazard <$> applyEncodingRequestC (.query leafIndex) resume encodingState) := by
            rw [structuralExperimentC_query_bind]
            simp only [runEagerQueryC]
            rw [← map_bind]
            exact (evalDist_sample_applyEncodingRequestC
              RevealProbeOracleSimulation.eagerTableSample (.query leafIndex)
              (fun base output nextState =>
                runStructuralC (RevealProbeOracleSimulation.extendTable chainState base)
                  nextState chainState (next output)) encodingState).map addHazard
          rw [hdist.prEvent_eq (fun x => x.1 = true), countMean_congr hdist,
            prHit_map_addHazard, countMean_map_addHazard]
          refine (applyEncodingRequestC_le (.query leafIndex) resume encodingState
            (u * chainState.pendingCount) fun output nextState =>
              (ih output nextState chainState hvalid).trans_eq (by ring)).trans_eq ?_
          simp only [EncodingRequest.cost, Nat.cast_one]
          ring
      | encodingSignAttempt leafIndex =>
          let resume := fun output nextState =>
            structuralExperimentC nextState chainState (next output)
          have hdist :
              (structuralExperimentC encodingState chainState
                ((liftM (OracleSpec.query (spec := World Index)
                  (.encodingSignAttempt leafIndex)) :
                  OracleComp (World Index) _) >>= next)) =ᵈ
                (applyEncodingRequestC (.sign leafIndex) resume encodingState) := by
            rw [structuralExperimentC_query_bind]
            simp only [runEagerQueryC]
            exact evalDist_sample_applyEncodingRequestC
              RevealProbeOracleSimulation.eagerTableSample (.sign leafIndex)
              (fun base output nextState =>
                runStructuralC (RevealProbeOracleSimulation.extendTable chainState base)
                  nextState chainState (next output)) encodingState
          rw [hdist.prEvent_eq (fun x => x.1 = true), countMean_congr hdist]
          refine (applyEncodingRequestC_le (.sign leafIndex) resume encodingState
            (u * chainState.pendingCount) fun output nextState =>
              (ih output nextState chainState hvalid).trans_eq (by ring)).trans_eq ?_
          simp only [EncodingRequest.cost, Nat.cast_zero, add_zero]
          ring
      | probe index target =>
          cases hrevealed : chainState.revealed index with
          | some value =>
              have heq : structuralExperimentC encodingState chainState
                  ((liftM (OracleSpec.query (spec := World Index) (.probe index target)) :
                    OracleComp (World Index) _) >>= next) =
                  addHazard <$> structuralExperimentC encodingState chainState (next ()) := by
                rw [structuralExperimentC_query_bind]
                simp only [runEagerQueryC, hrevealed]
                rw [structuralExperimentC, map_bind]
              rw [heq, prHit_map_addHazard, countMean_map_addHazard]
              refine (ih () encodingState chainState hvalid).trans ?_
              gcongr
              exact le_self_add
          | none =>
              have heq : structuralExperimentC encodingState chainState
                  ((liftM (OracleSpec.query (spec := World Index) (.probe index target)) :
                    OracleComp (World Index) _) >>= next) =
                  addHazard <$> structuralExperimentC encodingState
                    (chainState.addPending index target) (next ()) := by
                rw [structuralExperimentC_query_bind]
                simp only [runEagerQueryC, hrevealed]
                rw [structuralExperimentC, map_bind]
                rfl
              rw [heq, prHit_map_addHazard, countMean_map_addHazard]
              refine (ih () encodingState (chainState.addPending index target)
                (hvalid.addPending index target hrevealed)).trans ?_
              have hnat := chainState.pendingCount_addPending_le index target
              have hsum : countMean (structuralExperimentC encodingState
                    (chainState.addPending index target) (next ())) +
                  ((chainState.addPending index target).pendingCount : ℝ≥0∞) ≤
                  countMean (structuralExperimentC encodingState
                    (chainState.addPending index target) (next ())) + 1 +
                  (chainState.pendingCount : ℝ≥0∞) := by
                calc
                  _ ≤ countMean (structuralExperimentC encodingState
                        (chainState.addPending index target) (next ())) +
                      ((chainState.pendingCount + 1 : Nat) : ℝ≥0∞) := by
                    gcongr
                  _ = _ := by push_cast; ring
              exact add_le_add (mul_le_mul' le_rfl hsum) le_rfl
      | reveal index =>
          cases hrevealed : chainState.revealed index with
          | some value =>
              have heq : structuralExperimentC encodingState chainState
                  ((liftM (OracleSpec.query (spec := World Index) (.reveal index)) :
                    OracleComp (World Index) _) >>= next) =
                  structuralExperimentC encodingState chainState (next value) := by
                rw [structuralExperimentC_query_bind]
                simp only [runEagerQueryC, hrevealed]
                simp only [RevealProbeOracleSimulation.extendTable, hrevealed, Option.getD_some]
                rfl
              rw [heq]
              exact ih value encodingState chainState hvalid
          | none =>
              let resume := fun value nextState =>
                structuralExperimentC encodingState nextState (next value)
              have hdist :
                  (structuralExperimentC encodingState chainState
                    ((liftM (OracleSpec.query (spec := World Index)
                      (.reveal index)) :
                      OracleComp (World Index) _) >>= next)) =ᵈ
                    (applyRevealRequestC chainState index resume) := by
                rw [structuralExperimentC_query_bind]
                simp only [runEagerQueryC, hrevealed]
                exact evalDist_eagerTableSample_applyRevealRequestC chainState index
                  hrevealed fun table value nextState =>
                    runStructuralC table encodingState nextState (next value)
              rw [hdist.prEvent_eq (fun x => x.1 = true), countMean_congr hdist]
              exact applyRevealRequestC_le chainState index resume
                (encodingPendingRisk encodingState) fun value =>
                  ih value encodingState (chainState.install index value)
                    (hvalid.install index value)

/-- **Lane 1 in expected form**: a combined monitor hit of the eager experiment costs at most
`2^-128` per expected hazard the monitor processes before its first hit. -/
theorem combinedHit_le_observedHazards (computation : OracleComp (World Index) α) :
    Pr{let result ← eagerExperiment computation}[CombinedHit result.1 result.2.2] ≤
      u * ∑' result, Pr{let y ← eagerExperiment computation}[y = result] *
        (observedHazards result.1 (some EncodingMonitor.State.empty)
          AdaptiveRevealMonitor.State.empty result.2.2 : ℝ≥0∞) := by
  let observe := fun result : (Index → Digest) × (α × ActionTrace Index) =>
    (runObserved result.1 (some EncodingMonitor.State.empty)
      AdaptiveRevealMonitor.State.empty result.2.2,
     observedHazards result.1 (some EncodingMonitor.State.empty)
      AdaptiveRevealMonitor.State.empty result.2.2)
  have hdist : (observe <$> eagerExperiment computation) =ᵈ
      structuralExperimentC (some EncodingMonitor.State.empty)
        AdaptiveRevealMonitor.State.empty computation := by
    unfold eagerExperiment structuralExperimentC
    rw [map_bind]
    apply EvalDistEq.bind_right
    intro table
    have hextend : RevealProbeOracleSimulation.extendTable
        (AdaptiveRevealMonitor.State.empty : AdaptiveRevealMonitor.State Index) table = table := by
      funext index
      simp [RevealProbeOracleSimulation.extendTable, AdaptiveRevealMonitor.State.empty]
    rw [hextend]
    refine (EvalDistEq.of_eq ?_).trans
      (evalDist_observed_eagerTrace_eq_runStructuralC table (some EncodingMonitor.State.empty)
        AdaptiveRevealMonitor.State.empty computation)
    simp [observe, map_eq_bind_pure_comp]
  have hbound := structuralExperimentC_le (some EncodingMonitor.State.empty)
    AdaptiveRevealMonitor.State.empty RevealProbeOracleSimulation.stateValid_empty computation
  rw [← hdist.prEvent_eq (fun x => x.1 = true), ← countMean_congr hdist] at hbound
  simp only [AdaptiveRevealMonitor.State.pendingCount_empty, Nat.cast_zero, add_zero,
    encodingPendingRisk, CappedEncodingMonitor.State.pendingRisk_empty] at hbound
  calc
    _ = Pr{let x ← observe <$> eagerExperiment computation}[x.1 = true] := by
      rw [prEvent_map]
      exact prEvent_congr _ _ _ fun result =>
        (runObserved_empty_eq_combinedHit result.1 result.2.2).symm
    _ ≤ _ := hbound
    _ = _ := by
      unfold countMean
      rw [OracleComp.tsum_prEvent_map_mul]

/-! ## Hazards up to the first hit -/

omit [Fintype Index] in
theorem observedHazards_le_hazardCount (table : Index → Digest)
    (encodingState : Option EncodingMonitor.State)
    (chainState : AdaptiveRevealMonitor.State Index) (trace : ActionTrace Index) :
    observedHazards table encodingState chainState trace ≤ hazardCount trace := by
  induction trace generalizing encodingState chainState with
  | nil => simp [observedHazards]
  | cons action rest ih =>
      cases action with
      | encoding action =>
          have hcount : hazardCount (.encoding action :: rest) =
              hazardCount rest + encodingActionHazards action := by
            cases action <;> simp [hazardCount, encodingActionHazards]
          rw [hcount]
          simp only [observedHazards]
          gcongr
          cases encodingState with
          | none => exact ih _ _
          | some state =>
              simp only
              split
              · exact ih _ _
              · split
                · exact Nat.zero_le _
                · exact ih _ _
      | chain action =>
          cases action with
          | probe index target =>
              simp only [observedHazards, hazardCount]
              split
              · exact Nat.succ_le_succ (ih _ _)
              · exact Nat.succ_le_succ (ih _ _)
          | reveal index value =>
              simp only [observedHazards, hazardCount]
              split
              · exact ih _ _
              · split
                · exact Nat.zero_le _
                · exact ih _ _

open scoped Classical in
/-- The hazards of a trace up to the first prefix the combined monitor hits on, `prefix` the
part already read. -/
noncomputable def stoppedHazardsFrom (table : Index → Digest) (pre : ActionTrace Index) :
    ActionTrace Index → Nat
  | [] => hazardCount pre
  | action :: rest =>
      if CombinedHit table pre then hazardCount pre
      else stoppedHazardsFrom table (pre ++ [action]) rest

/-- The hazards of a trace up to its first prefix the combined monitor hits on. -/
noncomputable def stoppedHazards (table : Index → Digest) (trace : ActionTrace Index) : Nat :=
  stoppedHazardsFrom table [] trace

theorem stoppedHazardsFrom_le (table : Index → Digest) (pre trace : ActionTrace Index) :
    stoppedHazardsFrom table pre trace ≤ hazardCount (pre ++ trace) := by
  induction trace generalizing pre with
  | nil => simp [stoppedHazardsFrom]
  | cons action rest ih =>
      unfold stoppedHazardsFrom
      split
      · rw [hazardCount_append]
        exact Nat.le_add_right _ _
      · simpa [List.append_assoc] using ih (pre ++ [action])

theorem stoppedHazards_le (table : Index → Digest) (trace : ActionTrace Index) :
    stoppedHazards table trace ≤ hazardCount trace := by
  unfold stoppedHazards
  simpa using stoppedHazardsFrom_le table [] trace

theorem stoppedHazardsFrom_append_of_hit (table : Index → Digest)
    (pre left right : ActionTrace Index) (hhit : CombinedHit table (pre ++ left)) :
    stoppedHazardsFrom table pre (left ++ right) ≤ hazardCount (pre ++ left) := by
  induction left generalizing pre with
  | nil =>
      cases right with
      | nil => simp [stoppedHazardsFrom]
      | cons action rest =>
          simp only [List.append_nil] at hhit
          simp [stoppedHazardsFrom, hhit]
  | cons action rest ih =>
      simp only [List.cons_append]
      unfold stoppedHazardsFrom
      split
      · rw [hazardCount_append]
        exact Nat.le_add_right _ _
      · simpa [List.append_assoc] using ih (pre ++ [action]) (by simpa using hhit)

theorem stoppedHazards_append_of_hit (table : Index → Digest)
    (left right : ActionTrace Index) (hhit : CombinedHit table left) :
    stoppedHazards table (left ++ right) ≤ hazardCount left := by
  unfold stoppedHazards
  simpa using stoppedHazardsFrom_append_of_hit table [] left right (by simpa using hhit)

theorem stoppedHazardsFrom_append_le (table : Index → Digest)
    (pre left right : ActionTrace Index) :
    stoppedHazardsFrom table pre (left ++ right) ≤
      stoppedHazardsFrom table pre left + hazardCount right := by
  induction left generalizing pre with
  | nil =>
      simpa [stoppedHazardsFrom, hazardCount_append] using stoppedHazardsFrom_le table pre right
  | cons action rest ih =>
      simp only [List.cons_append]
      unfold stoppedHazardsFrom
      split
      · exact Nat.le_add_right _ _
      · exact ih (pre ++ [action])

theorem stoppedHazards_append_le (table : Index → Digest) (left right : ActionTrace Index) :
    stoppedHazards table (left ++ right) ≤ stoppedHazards table left + hazardCount right :=
  stoppedHazardsFrom_append_le table [] left right

theorem stoppedHazardsFrom_eq_of_not_hit (table : Index → Digest)
    (pre trace : ActionTrace Index) (hmiss : ¬CombinedHit table (pre ++ trace)) :
    stoppedHazardsFrom table pre trace = hazardCount (pre ++ trace) := by
  induction trace generalizing pre with
  | nil => simp [stoppedHazardsFrom]
  | cons action rest ih =>
      unfold stoppedHazardsFrom
      have hpre : ¬CombinedHit table pre := fun h =>
        hmiss (CombinedHit.append_of_prefix table pre (action :: rest) h)
      simp only [hpre, ↓reduceIte]
      simpa [List.append_assoc] using ih (pre ++ [action]) (by simpa using hmiss)

open scoped Classical in
theorem observedHazards_le_stopped (table : Index → Digest) (trace : ActionTrace Index) :
    observedHazards table (some EncodingMonitor.State.empty)
        AdaptiveRevealMonitor.State.empty trace ≤
      stoppedHazards table trace + if CombinedHit table trace then hazardCount trace else 0 := by
  by_cases hhit : CombinedHit table trace
  · simp only [hhit, ↓reduceIte]
    exact (observedHazards_le_hazardCount table _ _ trace).trans (Nat.le_add_left _ _)
  · simp only [hhit, ↓reduceIte, add_zero]
    rw [stoppedHazards,
      stoppedHazardsFrom_eq_of_not_hit table [] trace (by simpa using hhit)]
    simpa using observedHazards_le_hazardCount table _ _ trace

omit [Fintype Index] [DecidableEq Index] in
theorem hazardCount_enforceHazardTrace_le (fuel : Nat) (trace : ActionTrace Index) :
    hazardCount (enforceHazardTrace fuel trace) ≤ fuel := by
  induction trace generalizing fuel with
  | nil => simp [enforceHazardTrace, hazardCount]
  | cons action rest ih =>
      cases action with
      | encoding action =>
          cases action with
          | sign leafIndex output =>
              simpa [enforceHazardTrace, hazardCount] using ih fuel
          | query leafIndex output =>
              cases fuel with
              | zero => simpa [enforceHazardTrace] using ih 0
              | succ fuel => simpa [enforceHazardTrace, hazardCount] using ih fuel
      | chain action =>
          cases action with
          | reveal index value =>
              simpa [enforceHazardTrace, hazardCount] using ih fuel
          | probe index target =>
              cases fuel with
              | zero => simpa [enforceHazardTrace] using ih 0
              | succ fuel => simpa [enforceHazardTrace, hazardCount] using ih fuel

omit [Fintype Index] [DecidableEq Index] in
theorem hazardCount_enforceHazardTrace_le_self (fuel : Nat) (trace : ActionTrace Index) :
    hazardCount (enforceHazardTrace fuel trace) ≤ hazardCount trace := by
  induction trace generalizing fuel with
  | nil => simp [enforceHazardTrace, hazardCount]
  | cons action rest ih =>
      cases action with
      | encoding action =>
          cases action with
          | sign leafIndex output =>
              simpa [enforceHazardTrace, hazardCount] using ih fuel
          | query leafIndex output =>
              cases fuel with
              | zero => simpa [enforceHazardTrace, hazardCount] using (ih 0).trans (Nat.le_succ _)
              | succ fuel => simpa [enforceHazardTrace, hazardCount] using ih fuel
      | chain action =>
          cases action with
          | reveal index value =>
              simpa [enforceHazardTrace, hazardCount] using ih fuel
          | probe index target =>
              cases fuel with
              | zero => simpa [enforceHazardTrace, hazardCount] using (ih 0).trans (Nat.le_succ _)
              | succ fuel => simpa [enforceHazardTrace, hazardCount] using ih fuel

open scoped Classical in
/-- **Lane 1, enforced and stopped.** A combined hit on the fuel-enforced trace costs `2^-128` per
expected hazard up to the first hit, plus `fuel` hazards for each hit: the hazards after a hit
count fully but only on the hit's probability. -/
theorem enforcedHit_le_stoppedHazards (computation : OracleComp (World Index) α) (fuel : Nat) :
    Pr{let x ← eagerExperiment computation}[CombinedHit x.1 (enforceHazardTrace fuel x.2.2)] ≤
      u * (∑' x, Pr{let y ← eagerExperiment computation}[y = x] *
          (stoppedHazards x.1 (enforceHazardTrace fuel x.2.2) : ℝ≥0∞) +
        fuel * Pr{let x ← eagerExperiment computation}[CombinedHit x.1
          (enforceHazardTrace fuel x.2.2)]) := by
  have hmap := eagerExperiment_enforceHazardBound_eq_map computation fuel
  have hhit : Pr{let x ← eagerExperiment computation}[CombinedHit x.1
        (enforceHazardTrace fuel x.2.2)] =
      Pr{let result ← eagerExperiment (enforceHazardBound fuel computation)}[CombinedHit
        result.1 result.2.2] := by
    rw [hmap, prEvent_map]
    rfl
  rw [hhit]
  refine (combinedHit_le_observedHazards (enforceHazardBound fuel computation)).trans ?_
  rw [← hhit, hmap, OracleComp.tsum_prEvent_map_mul]
  gcongr
  calc
    _ ≤ ∑' x, Pr{let y ← eagerExperiment computation}[y = x] *
          ((stoppedHazards x.1 (enforceHazardTrace fuel x.2.2) : ℝ≥0∞) +
            fuel * (if CombinedHit x.1 (enforceHazardTrace fuel x.2.2) then 1 else 0)) := by
      refine ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl ?_
      have hbound := observedHazards_le_stopped x.1 (enforceHazardTrace fuel x.2.2)
      have hfuel := hazardCount_enforceHazardTrace_le fuel x.2.2
      by_cases hx : CombinedHit x.1 (enforceHazardTrace fuel x.2.2)
      · simp only [hx, ↓reduceIte, mul_one] at hbound ⊢
        exact_mod_cast hbound.trans (Nat.add_le_add_left hfuel _)
      · simp only [hx, ↓reduceIte, add_zero, mul_zero] at hbound ⊢
        exact_mod_cast hbound
    _ = _ := by
      simp only [mul_add]
      rw [ENNReal.tsum_add]
      congr 1
      rw [← tsum_prEvent_mul_indicator, ← ENNReal.tsum_mul_left]
      exact tsum_congr fun x => by ring

end FirstLaneOracleSimulation

end XmssSecurity
