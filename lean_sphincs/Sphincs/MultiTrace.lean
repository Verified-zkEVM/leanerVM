import Sphincs.MultiClass
import Sphincs.BridgeDetCloseF

/-! **Expected costs along the bridges.** The bridges of the small route bound probabilities of
events. A multi-user bound pays each reduction for the hash calls of its own key, so the expected
number of those calls must be carried from the experiment down to the interpreted run. Each lemma
here is the expectation form of one bridge, for a function of the run bounded by `C`: the
comparison runs agree with the stopped execution until it stops, after which they cost at most
`C`. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security

/-! ### Means of functions of probabilistic runs -/

/-- The mean of a function of a run. -/
noncomputable def mean {α : Type} (mx : ProbComp α) (F : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' a, Pr{let x ← mx}[x = a] * F a

theorem mean_pure {α : Type} (a : α) (F : α → ℝ≥0∞) : mean (pure a : ProbComp α) F = F a :=
  OracleComp.tsum_prEvent_pure_mul a F

theorem mean_bind {α β : Type} (mx : ProbComp α) (f : α → ProbComp β) (F : β → ℝ≥0∞) :
    mean (mx >>= f) F = mean mx fun a => mean (f a) F := by
  simp only [mean, OracleComp.tsum_prEvent_bind_mul]

theorem mean_map {α β : Type} (mx : ProbComp α) (g : α → β) (F : β → ℝ≥0∞) :
    mean (g <$> mx) F = mean mx (F ∘ g) := by
  simp only [mean, OracleComp.tsum_prEvent_map_mul, Function.comp_apply]

theorem mean_congr {α : Type} {mx my : ProbComp α} (h : mx =ᵈ my) (F : α → ℝ≥0∞) : mean mx F = mean my F := by
  unfold mean
  refine tsum_congr fun a => ?_
  rw [h.prEvent_eq]

theorem mean_mono_support {α : Type} (mx : ProbComp α) {F G : α → ℝ≥0∞} (h : ∀ a ∈ support mx, F a ≤ G a) :
    mean mx F ≤ mean mx G := by
  unfold mean
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ support mx
  · exact mul_le_mul' le_rfl (h a ha)
  · rw [(prEvent_eq_zero_of_not_mem_support _) ha, zero_mul, zero_mul]

theorem mean_mono {α : Type} (mx : ProbComp α) {F G : α → ℝ≥0∞} (h : ∀ a, F a ≤ G a) :
    mean mx F ≤ mean mx G := mean_mono_support mx fun a _ => h a

theorem mean_le_const {α : Type} (mx : ProbComp α) {F : α → ℝ≥0∞} {C : ℝ≥0∞} (h : ∀ a, F a ≤ C) :
    mean mx F ≤ C := by
  refine (mean_mono mx h).trans ?_
  unfold mean
  rw [ENNReal.tsum_mul_right]
  exact mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _)

theorem mean_add {α : Type} (mx : ProbComp α) (F G : α → ℝ≥0∞) :
    mean mx (fun a => F a + G a) = mean mx F + mean mx G := by
  simp only [mean, mul_add, ENNReal.tsum_add]

theorem mean_const_mul {α : Type} (mx : ProbComp α) (c : ℝ≥0∞) (F : α → ℝ≥0∞) :
    mean mx (fun a => c * F a) = c * mean mx F := by
  simp only [mean, ← ENNReal.tsum_mul_left]
  exact tsum_congr fun a => by ring

theorem mean_indicator {α : Type} (mx : ProbComp α) (E : α → Prop) [DecidablePred E] :
    mean mx (fun a => if E a then 1 else 0) = Pr{let x ← mx}[E x] := by
  rw [mean, OracleComp.prEvent_eq_tsum_ite]
  refine tsum_congr fun a => ?_
  split_ifs <;> simp

end Sphincs.Security

namespace Sphincs.Security.HiddenDebt

open HiddenOutside HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable {D R A ι : Type} [Fintype ι] [SampleableType R]

/-- A function of a stopped run: `C` once stopped. -/
def stopVal {β : Type} (C : ℝ≥0∞) (F : β → ℝ≥0∞) : Option β → ℝ≥0∞
  | none => C
  | some value => F value

omit [Fintype ι] in
/-- **Expected stopping coupling.** The guess-recording comparison and the stopped run agree until
the stopped run stops; a function bounded by `C` of the comparison has a mean at most that of the
stopped run, a stop counting `C`. -/
theorem fixedRun_exp_le_stopped {α : Type} (model : HiddenRows.Model D R A ι) (table : ι → Digest)
    (computation : OracleComp (HiddenRows.SourceSpec D R ι) α) (F : α × Cache D R → ℝ≥0∞) (C : ℝ≥0∞)
    (hF : ∀ x, F x ≤ C) (state : DebtState D R ι) (hagree : Agrees state.known table) :
    ∑' r, Pr{let x ← fixedRun model table computation state}[x = r] * F (r.1, r.2.cache) ≤
      ∑' x, Pr{let y ← stopped model table computation state.known state.cache}[y = x] * stopVal C F x := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [stopped, OracleComp.construct_pure, fixedRun_pure, OracleComp.tsum_prEvent_pure_mul, stopVal]
      exact le_rfl
  | query_bind input next ih =>
      rw [stopped_query_bind, fixedRun_query_bind, OracleComp.tsum_prEvent_bind_mul]
      rcases input with draw | (bytes | coordinate)
      · rw [fixedStep_draw]
        simp only [stoppedStep, OracleComp.tsum_prEvent_bind_mul, OracleComp.tsum_prEvent_map_mul]
        refine ENNReal.tsum_le_tsum fun value => mul_le_mul' le_rfl ?_
        exact ih value state hagree
      · have hreadStep : ∀ base : DebtState D R ι, base.known = state.known → base.cache = state.cache →
            ∑' first, Pr{let x ← readOutside bytes base}[x = first] *
              ∑' r, Pr{let x ← fixedRun model table (next first.1) first.2}[x = r] * F (r.1, r.2.cache) ≤
            ∑' x, Pr{let y ← (outsideRead bytes state.cache >>= fun result =>
              stopped model table (next result.1) state.known result.2)}[y = x] * stopVal C F x := by
          intro base hknown hcache
          simp only [readOutside, OracleComp.tsum_prEvent_map_mul, OracleComp.tsum_prEvent_bind_mul, hcache]
          refine ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl ?_
          have h := ih result.1 { base with cache := result.2 } (by simpa [hknown] using hagree)
          simpa [hknown] using h
        cases hp : model.parse bytes with
        | none =>
            rw [fixedStep_unparsed model table bytes state hp, stoppedStep_unparsed model table bytes _ _ _ hp]
            exact hreadStep state rfl rfl
        | some query =>
            cases hk : state.known (model.incoming query.1) with
            | none =>
                rw [fixedStep_guess model table bytes state query hp hk]
                by_cases hguess : query.2 = table (model.incoming query.1)
                · rw [stoppedStep_stop model table bytes _ _ _ query hp ⟨hk, hguess⟩,
                    OracleComp.tsum_prEvent_pure_mul]
                  simp only [stopVal]
                  calc _ ≤ ∑' first, Pr{let x ← (readOutside bytes
                          (state.record (model.incoming query.1, query.2)))}[x = first] * C := by
                        refine ENNReal.tsum_le_tsum fun first => mul_le_mul' le_rfl ?_
                        calc _ ≤ ∑' r, Pr{let x ← fixedRun model table (next first.1) first.2}[x = r] * C :=
                              ENNReal.tsum_le_tsum fun r => mul_le_mul' le_rfl (hF _)
                          _ ≤ C := by
                              rw [ENNReal.tsum_mul_right]
                              exact mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _)
                    _ ≤ C := by
                        rw [ENNReal.tsum_mul_right]
                        exact mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _)
                · rw [stoppedStep_miss model table bytes _ _ _ query hp hguess]
                  exact hreadStep _ rfl rfl
            | some canonical =>
                have hcanon : table (model.incoming query.1) = canonical := hagree _ _ hk
                by_cases heq : query.2 = canonical
                · rw [fixedStep_canonical model table bytes state query hp canonical hk heq,
                    OracleComp.tsum_prEvent_pure_mul,
                    stoppedStep_canonical model table bytes _ _ _ query hp (by simp [hk]) (heq.trans hcanon.symm)]
                  exact ih _ (state.expose (model.outgoing query.1) (table (model.outgoing query.1)))
                    (hagree.cacheQuery _)
                · rw [fixedStep_other model table bytes state query hp canonical hk heq,
                    stoppedStep_miss model table bytes _ _ _ query hp (fun h => heq (h.trans hcanon))]
                  exact hreadStep state rfl rfl
      · rw [fixedStep_reveal, OracleComp.tsum_prEvent_pure_mul]
        simp only [stoppedStep]
        exact ih _ (state.expose coordinate (table coordinate)) (hagree.cacheQuery coordinate)

end Sphincs.Security.HiddenDebt

namespace Sphincs.Security.HiddenBridge

open HiddenCost Stop GraphView HiddenGraph HiddenDebt

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable {A : Type}

theorem stopVal_map {β γ : Type} (C : ℝ≥0∞) (F : γ → ℝ≥0∞) (g : β → γ) (x : Option β) :
    stopVal C F (Option.map g x) = stopVal C (F ∘ g) x := by
  cases x <;> rfl

/-- **The stopped execution is a part of the fixed-function cost run**: until it stops the two
agree, so a function of the finished stopped runs has a mean at most that of the cost run. -/
theorem stopped_exp_le_costRun {α : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate)
    (table : HiddenGraph.Table) (outside : HashInput → HashOutput)
    (computation : OracleComp CostSpec α) (known : HiddenReveal.Knowledge Coordinate)
    (F : α × List (Entry HashInput) → ℝ≥0∞) :
    ∑' x, Pr{let y ← HiddenRows.stopped model table outside (erase (trace computation)) known}[y = x] *
        stopVal 0 F x ≤
      ∑' r, Pr{let y ← costRun (HiddenRows.answer model table outside) table computation}[y = r] * F r := by
  induction computation using OracleComp.inductionOn generalizing known F with
  | pure value =>
      rw [costRun_pure, OracleComp.tsum_prEvent_pure_mul]
      change ∑' x, Pr{let y ← (pure (some (value, [])) : ProbComp _)}[y = x] * stopVal 0 F x ≤ _
      rw [OracleComp.tsum_prEvent_pure_mul]
      rfl
  | query_bind input next ih =>
      rw [costRun_query_bind, erase_trace_query_bind]
      rcases input with (draw | (bytes | coordinate)) | amount
      · change ∑' x, Pr{let y ← (HiddenRows.stopped model table outside
          (liftM ((HiddenRows.SourceSpec HashInput HashOutput Coordinate).query (.inl draw)) >>= _) known)}[y = x] *
            stopVal 0 F x ≤ _
        rw [HiddenRows.stopped_private, OracleComp.tsum_prEvent_bind_mul, OracleComp.tsum_prEvent_bind_mul]
        refine ENNReal.tsum_le_tsum fun value => mul_le_mul' le_rfl ?_
        rw [stopped_map, OracleComp.tsum_prEvent_map_mul, OracleComp.tsum_prEvent_map_mul]
        simp only [stopVal_map]
        exact ih value known _
      · change ∑' x, Pr{let y ← (HiddenRows.stopped model table outside
          (liftM ((HiddenRows.SourceSpec HashInput HashOutput Coordinate).query (.inr (.inl bytes))) >>= _) known)}[y = x] *
            stopVal 0 F x ≤ _
        rw [HiddenRows.stopped_hash]
        rw [show fixedCostP (HiddenRows.answer model table outside) table (.inl (.inr (.inl bytes))) =
          (pure (HiddenRows.answer model table outside bytes) : ProbComp HashOutput) from rfl, pure_bind,
          OracleComp.tsum_prEvent_map_mul]
        cases hp : model.parse bytes with
        | none =>
            dsimp only
            rw [stopped_map, OracleComp.tsum_prEvent_map_mul]
            simp only [stopVal_map]
            exact ih _ known _
        | some query =>
            dsimp only
            split_ifs with hstop hcanonical
            · rw [OracleComp.tsum_prEvent_pure_mul]
              exact bot_le
            · rw [stopped_map, OracleComp.tsum_prEvent_map_mul]
              simp only [stopVal_map]
              exact ih _ _ _
            · rw [stopped_map, OracleComp.tsum_prEvent_map_mul]
              simp only [stopVal_map]
              exact ih _ known _
      · change ∑' x, Pr{let y ← (HiddenRows.stopped model table outside
          (liftM ((HiddenRows.SourceSpec HashInput HashOutput Coordinate).query (.inr (.inr coordinate))) >>= _) known)}[y = x] *
            stopVal 0 F x ≤ _
        rw [HiddenRows.stopped_reveal, show fixedCostP (HiddenRows.answer model table outside) table
          (.inl (.inr (.inr coordinate))) = (pure (table coordinate) : ProbComp Digest) from rfl, pure_bind,
          stopped_map, OracleComp.tsum_prEvent_map_mul, OracleComp.tsum_prEvent_map_mul]
        simp only [stopVal_map]
        exact ih _ _ _
      · rw [show eraseQuery (D := HashInput) (R := HashOutput) (ι := Coordinate) (.inr amount) = pure () from rfl,
          show fixedCostP (HiddenRows.answer model table outside) table (.inr amount) = (pure () : ProbComp Unit)
            from rfl, pure_bind, pure_bind, stopped_map, OracleComp.tsum_prEvent_map_mul,
          OracleComp.tsum_prEvent_map_mul]
        simp only [stopVal_map]
        exact ih () known _

end Sphincs.Security.HiddenBridge

namespace Sphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForestPrice ForestSigner HiddenReveal
  SphincsFors.Security.Domination
open HiddenBridge PotentialA

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

variable [Params]

open Completeness SeedModel _root_.Sphincs.Security.Graph Assembly Reduce Internalize in
attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

open Completeness SeedModel _root_.Sphincs.Security.Graph Assembly Reduce Internalize

section Sample

variable (adversary : Adversary) (q : ℕ) (parameterOutput : HashOutput) (fixed : HiddenGraph.Table)
  (highs : CoordinateHighs) (remaining : RemainingOutputs)
  (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec) (known : Knowledge Coordinate)
  (tg : Targeting HashInput HashOutput Coordinate)

/-- The program of one sample's stopped experiment. -/
noncomputable abbrev sampleProg :=
  erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
    (sampleData parameterOutput fixed highs remaining)))

/-- The interpreted run of one sample. -/
noncomputable abbrev sampleRun :=
  interp tg prepared.2 (sampleModel parameterOutput highs)
    (costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
      (internalize adversary)) q (DebtState.start prepared.2 known)

theorem mean_sampleRun_eq (G : ((Option HiddenBridge.Outcome × List Coordinate) × List (Entry HashInput)) × State →
    ℝ≥0∞) :
    mean (sampleRun adversary q parameterOutput fixed highs remaining prepared known tg)
        (fun out => G (((out.1.1, out.1.2.1), out.1.2.2.1), out.2)) =
      mean (lazyRun (sampleModel parameterOutput highs) (sampleProg adversary q parameterOutput fixed highs remaining)
        (DebtState.start prepared.2 known)) G := by
  rw [sampleProg, richProgram, lazyRun_wrapped tg prepared.2, mean_map]
  rfl

omit [Params] in
/-- **The interpreted run costs what the stopped experiment costs, a stop counting `C`.** -/
theorem mean_lazyRun_le_stopped {α : Type} (model : HiddenRows.Model HashInput HashOutput Address Coordinate)
    (prog : OracleComp (HiddenRows.SourceSpec HashInput HashOutput Coordinate) α) (start : State)
    (F : α → ℝ≥0∞) (C : ℝ≥0∞) (hF : ∀ v, F v ≤ C) :
    mean (lazyRun model prog start) (fun r => F r.1) ≤
      mean (HiddenOutside.stoppedExperiment model prog start.known start.cache) (stopVal C fun v => F v.1) := by
  have hmass : ∀ r : α × State, mean ((fun table => (table, r)) <$> completion r.2.known)
      (fun x => F x.2.1) = F r.1 := by
    intro r
    rw [mean_map]
    unfold mean
    simp only [Function.comp_apply, ENNReal.tsum_mul_right]
    rw [OracleComp.tsum_prEvent_eq_one, one_mul]
  calc mean (lazyRun model prog start) (fun r => F r.1)
      = mean (lazyRun model prog start >>= fun r => (fun table => (table, r)) <$> completion r.2.known)
          (fun x => F x.2.1) := by
        rw [mean_bind]
        exact (congrArg _ (funext hmass)).symm
    _ = mean (withTable (fun table => fixedRun model table prog start) start.known) (fun x => F x.2.1) :=
        (mean_congr (withTable_fixedRun model prog start) _).symm
    _ = mean (completion start.known) (fun table => mean (fixedRun model table prog start) (fun r => F r.1)) := by
        unfold withTable
        rw [mean_bind]
        refine congrArg _ (funext fun table => ?_)
        rw [mean_map]
        rfl
    _ ≤ mean (completion start.known) (fun table =>
          mean (HiddenOutside.stopped model table prog start.known start.cache) (stopVal C fun v => F v.1)) :=
        mean_mono_support _ fun table htab => by
          have hag : Agrees start.known table := by
            unfold completion at htab
            rw [support_map] at htab
            obtain ⟨t, _, rfl⟩ := htab
            exact fun c v hc => completion_known _ c v hc t
          have h := fixedRun_exp_le_stopped model table prog (fun v => F v.1) C (fun v => hF v.1) start hag
          unfold mean
          exact h
    _ = _ := by
        unfold HiddenOutside.stoppedExperiment
        rw [mean_bind]

omit [Params] in
/-- **A stop is a correct guess of the lazy run.** -/
theorem stopped_none_le_guess {α : Type} (model : HiddenRows.Model HashInput HashOutput Address Coordinate)
    (prog : OracleComp (HiddenRows.SourceSpec HashInput HashOutput Coordinate) α) (start : State) :
    Pr{let x ← HiddenOutside.stoppedExperiment model prog start.known start.cache}[x = none] ≤
      mean (lazyRun model prog start) fun r => Pr{let T ← completion r.2.known}[CorrectGuess T r.2] := by
  unfold HiddenOutside.stoppedExperiment
  rw [OracleComp.prEvent_bind_eq_tsum]
  calc _ ≤ ∑' table, Pr{let x ← completion start.known}[x = table] *
        Pr{let r ← fixedRun model table prog start}[CorrectGuess table r.2] := by
        refine ENNReal.tsum_le_tsum fun table => ?_
        by_cases htab : table ∈ support (completion start.known)
        · have hag : Agrees start.known table := by
            unfold completion at htab
            rw [support_map] at htab
            obtain ⟨t, _, rfl⟩ := htab
            exact fun c v hc => completion_known _ c v hc t
          refine mul_le_mul' le_rfl ?_
          refine le_trans (prEvent_mono_of_support _ _ (StopOr fun _ => False) fun x _ hx => ?_)
            ((stopped_le_fixedRun model table prog (fun _ => False) start hag).trans
              (prEvent_mono_of_support _ _ _ fun r _ h => h.resolve_right id))
          rw [hx]
          trivial
        · rw [(prEvent_eq_zero_of_not_mem_support _) htab, zero_mul, zero_mul]
    _ = Pr{let x ← withTable (fun table => fixedRun model table prog start) start.known}[CorrectGuess x.1 x.2.2] := by
        unfold withTable
        rw [OracleComp.prEvent_bind_eq_tsum]
        refine tsum_congr fun table => ?_
        rw [prEvent_map]
    _ = Pr{let x ← (lazyRun model prog start >>= fun result =>
          (fun table => (table, result)) <$> completion result.2.known)}[CorrectGuess x.1 x.2.2] :=
        (withTable_fixedRun model prog start).prEvent_eq _
    _ = _ := by
        rw [OracleComp.prEvent_bind_eq_tsum]
        unfold mean
        refine tsum_congr fun r => ?_
        rw [prEvent_map]

omit [Params] in
theorem mean_stopVal {β : Type} (mx : ProbComp (Option β)) (C : ℝ≥0∞) (F : β → ℝ≥0∞) :
    mean mx (stopVal C F) = mean mx (stopVal 0 F) + C * Pr{let x ← mx}[x = none] := by
  rw [← mean_indicator, ← mean_const_mul, ← mean_add]
  refine congrArg _ (funext fun x => ?_)
  cases x <;> simp [stopVal]

/-- A correct guess of a run's state is paid by the end value of the linear potential. -/
theorem guess_le_endValue (ρ : ℝ) (s : State) :
    Pr{let T ← completion s.known}[CorrectGuess T s] ≤
      endValue (payoffA parameterOutput fixed highs remaining prepared known ρ) s := by
  refine le_trans (prEvent_mono_of_support _ _ (fun T => CorrectGuess T s ∧ tableExtending s.known T = T)
    fun T hT h => ⟨h, ?_⟩) (probEvent_le_endValueF _ s _ fun T h => ?_)
  · unfold completion at hT
    rw [support_map] at hT
    obtain ⟨t, _, rfl⟩ := hT
    funext c
    simp only [tableExtending]
    cases s.known c <;> rfl
  · unfold payoffA Ctx.payoff
    exact ite_eq_left_of_eq_true _ _
      (eq_true (Or.inl (hit_of_correctGuess parameterOutput fixed highs remaining prepared known ρ s T h.2 h.1)))

/-- **The hash calls of one sample's interpreted run**: those of its stopped experiment, a stop
costing the whole budget, and a stop is a correct guess paid by the end value. -/
theorem sampleRun_charged_le (ρ : ℝ) (Free : HashInput → Prop) :
    mean (sampleRun adversary q parameterOutput fixed highs remaining prepared known tg)
        (fun out => min (q : ℝ≥0∞) (chargedCost Free out.1.2.2.1)) ≤
      mean (HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
          (sampleProg adversary q parameterOutput fixed highs remaining) known prepared.2)
          (stopVal 0 fun v => min (q : ℝ≥0∞) (chargedCost Free v.1.2)) +
        q * mean (sampleRun adversary q parameterOutput fixed highs remaining prepared known tg)
          (fun out => endValue (payoffA parameterOutput fixed highs remaining prepared known ρ) out.2) := by
  have h1 := mean_sampleRun_eq adversary q parameterOutput fixed highs remaining prepared known tg
    (fun r => min (q : ℝ≥0∞) (chargedCost Free r.1.2))
  have h2 := mean_lazyRun_le_stopped (sampleModel parameterOutput highs)
    (sampleProg adversary q parameterOutput fixed highs remaining) (DebtState.start prepared.2 known)
    (fun v => min (q : ℝ≥0∞) (chargedCost Free v.2)) q (fun v => min_le_left _ _)
  have h3 := stopped_none_le_guess (sampleModel parameterOutput highs)
    (sampleProg adversary q parameterOutput fixed highs remaining) (DebtState.start prepared.2 known)
  have h4 := mean_sampleRun_eq adversary q parameterOutput fixed highs remaining prepared known tg
    (fun r => Pr{let T ← completion r.2.known}[CorrectGuess T r.2])
  rw [mean_stopVal] at h2
  refine (le_of_eq h1).trans (h2.trans (add_le_add le_rfl (mul_le_mul' le_rfl ?_)))
  refine h3.trans ((le_of_eq h4.symm).trans (mean_mono _ fun out => ?_))
  exact guess_le_endValue parameterOutput fixed highs remaining prepared known ρ out.2

/-- The targeting of one sample with the digests of its own key. -/
noncomputable abbrev tgKey : Targeting HashInput HashOutput Coordinate :=
  { targetingA parameterOutput fixed highs remaining prepared.1 with
    digest := MsgOfKey (truncateHash parameterOutput) }

/-- The hash calls of one sample's run charged to its key. -/
noncomputable abbrev keyCharged (entries : List (Entry HashInput)) : ℝ≥0∞ :=
  (chargedCost (fun x => ¬OfKey (truncateHash parameterOutput) x) entries : ℝ≥0∞)

/-- **The end value of the linear potential is paid by the key's hash calls.** -/
theorem sampleRun_endValue_le (ρ : ℝ)
    (hk : known ∈ support (exposeR (aboveList (truncateHash parameterOutput) prepared.1)
      (knownOf (truncateHash parameterOutput) fixed)))
    (hN : Numeric ρ (((q - keygenCost : ℕ) : ℝ) / 2 ^ 128)) :
    mean (sampleRun adversary q parameterOutput fixed highs remaining prepared known
        (tgKey parameterOutput fixed highs remaining prepared))
        (fun out => endValue (payoffA parameterOutput fixed highs remaining prepared known ρ) out.2) ≤
      ENNReal.ofReal (ρ / 2 ^ 128) * mean (sampleRun adversary q parameterOutput fixed highs remaining prepared
        known (tgKey parameterOutput fixed highs remaining prepared))
        (fun out => keyCharged parameterOutput out.1.2.2.1) := by
  set param := truncateHash parameterOutput with hparam
  set data := sampleData parameterOutput fixed highs remaining with hdata
  set model := sampleModel parameterOutput highs with hmodel
  set tgA := tgKey parameterOutput fixed highs remaining prepared with htgA
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
      b0 * ∑' out, Pr{let x ← run}[x = out] *
        (chargedCost (fun x => ¬OfKey (truncateHash parameterOutput) x) out.1.2.2.1 : ℝ≥0∞) := by
    by_cases hK : keygenCost ≤ q
    · rw [hrunK hK, OracleComp.tsum_prEvent_map_mul, OracleComp.tsum_prEvent_map_mul]
      refine le_trans (le_of_eq ?_) ((smallRoute_potential_payClass parameterOutput fixed highs remaining
        prepared known ρ hk tgA rfl q' hN (advProg param data ((internalize adversary).main ⟨data.root, param⟩) [])).trans
        (mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun out => mul_le_mul' le_rfl ?_)))
      · refine tsum_congr fun out => ?_
        simp only [digestCount_cons_inrF, fleafCount_cons_inr]
        rfl
      · simp only [chargedCost, chargedEntry, List.map_cons, List.sum_cons, Nat.cast_add]
        exact le_add_self
    · have hrunEq : run = interp tgA prepared.2 model (costGameX param data (internalize adversary)) 0 start := by
        rw [hrunA hK]
        unfold costGameX
        rw [interp_tick_bind_abort tgA prepared.2 model keygenCost _ 0 start (by omega)]
      rw [hrunEq]
      have hq0 : (q' : ℕ) = 0 := by omega
      rw [hc0, hq0]
      exact smallRoute_potential_payClass parameterOutput fixed highs remaining prepared known ρ hk tgA rfl 0
        (numeric_monoF hN (by rw [hq0]) (by norm_num)) (costGameX param data (internalize adversary))
  refine le_trans ?_ hA3
  exact ENNReal.tsum_le_tsum fun out => mul_le_mul' le_rfl (le_self_add.trans le_self_add)

omit [Params] in
/-- Solving the self-bound of the charged calls: `X ≤ Z + q E` and `E ≤ a X` give `X (1 − q a) ≤ Z`. -/
theorem solve_selfBound {X Z E a c : ℝ≥0∞} (hX : X ≤ Z + c * E) (hE : E ≤ a * X) (hfin : X ≠ ⊤) :
    X * (1 - c * a) ≤ Z := by
  rcases le_or_gt 1 (c * a) with hca | hca
  · rw [tsub_eq_zero_of_le hca, mul_zero]
    exact bot_le
  rcases eq_or_ne (c * a) 0 with h0 | h0
  · rw [h0, tsub_zero, mul_one]
    calc X ≤ Z + c * E := hX
      _ ≤ Z + c * (a * X) := add_le_add le_rfl (mul_le_mul' le_rfl hE)
      _ = Z := by rw [← mul_assoc, h0, zero_mul, add_zero]
  rw [ENNReal.mul_sub (fun _ _ => hfin), mul_one, tsub_le_iff_right]
  calc X ≤ Z + c * E := hX
    _ ≤ Z + c * (a * X) := add_le_add le_rfl (mul_le_mul' le_rfl hE)
    _ = Z + X * (c * a) := by ring

set_option maxRecDepth 100000 in
/-- **One sample, the linear potential paid by the expected hash calls of the key**: the hash calls
of the interpreted run are those of the stopped execution plus a stop, a stop is paid by the end
value, which the calls pay at `ρ / 2^128` each, so the calls of the run are at most those of the
stopped execution divided by `1 − q ρ / 2^128`. -/
theorem sample_boundF_trace (hb : 0 < subtreeHeight) (adversary : Adversary) (hnr : adversary.NoRepeat) (q : ℕ)
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
    (ho : H0.checkOptF b t o = true) (hon : H0.checkOptN t on = true) (hcthr : (o.cthr : ℝ) ≤ ρ / 2 ^ 128)
    (hc : (q : ℝ≥0∞) * ENNReal.ofReal (ρ / 2 ^ 128) < 1) :
    Pr{let x ← (HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
        (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
          (sampleData parameterOutput fixed highs remaining)))) known prepared.2)}[(HiddenReveal.StopOr RichWin) x] ≤
      ENNReal.ofReal (ρ / 2 ^ 128) * ((1 - (q : ℝ≥0∞) * ENNReal.ofReal (ρ / 2 ^ 128))⁻¹ *
          mean (HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
            (sampleProg adversary q parameterOutput fixed highs remaining) known prepared.2)
            (stopVal 0 fun v => min (q : ℝ≥0∞) (keyCharged parameterOutput v.1.2))) +
        (((q - keygenCost : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (o.B : ℝ) + failMass (failSet prepared.1)) +
          signatureLimit * failMass (failSet prepared.1)) +
        ν * (((Nat.choose (q - keygenCost) 2 : ℕ) : ℝ≥0∞) * rateS) +
        (ENNReal.ofReal κ * ((((q - keygenCost : ℕ) : ℝ≥0∞) * ν) *
            ((q - keygenCost : ℕ) * ENNReal.ofReal (((2 ^ b * on.En : ℚ) / 2 : ℚ) : ℝ))) +
          (((q - keygenCost : ℕ) : ℝ≥0∞) * ν) *
            ((q - keygenCost : ℕ) * failMass (failSet prepared.1) + signatureLimit * failMass (failSet prepared.1))) +
        2 * lam (H0.LmaxOf (q - keygenCost)) 0 (q - keygenCost) := by
  have h := sample_boundF_class hb adversary hnr q hq parameterOutput fixed highs remaining prepared hprepared known
    hk ρ hN κ hκ hκ1 b N hbb hNN t o on hpt qtop hrt hqtop ho hon hcthr
  refine h.trans ?_
  gcongr ?_ + _ + _ + _ + _
  refine mul_le_mul' le_rfl ?_
  set tgA := tgKey parameterOutput fixed highs remaining prepared with htgA
  set run := sampleRun adversary q parameterOutput fixed highs remaining prepared known tgA with hrun
  set b0 : ℝ≥0∞ := ENNReal.ofReal (ρ / 2 ^ 128) with hb0
  set Z := mean (HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
    (sampleProg adversary q parameterOutput fixed highs remaining) known prepared.2)
    (stopVal 0 fun v => min (q : ℝ≥0∞) (keyCharged parameterOutput v.1.2)) with hZ
  have hX := sampleRun_charged_le adversary q parameterOutput fixed highs remaining prepared known tgA ρ
    (fun x => ¬OfKey (truncateHash parameterOutput) x)
  have hE := sampleRun_endValue_le adversary q parameterOutput fixed highs remaining prepared known ρ hk hN
  have hmin : mean run (fun out => min (q : ℝ≥0∞) (keyCharged parameterOutput out.1.2.2.1)) =
      mean run (fun out => keyCharged parameterOutput out.1.2.2.1) := by
    refine le_antisymm (mean_mono _ fun out => min_le_right _ _) (mean_mono_support _ fun out hout => ?_)
    have hcost := interp_traceCost_le tgA prepared.2 (sampleModel parameterOutput highs) _ q _ out hout
    have hle : chargedCost (fun x => ¬OfKey (truncateHash parameterOutput) x) out.1.2.2.1 ≤ q :=
      (chargedCost_le _ _).trans hcost
    exact le_min (by exact_mod_cast hle) le_rfl
  have hfin : mean run (fun out => keyCharged parameterOutput out.1.2.2.1) ≠ ⊤ := by
    rw [← hmin]
    exact ne_top_of_le_ne_top (ENNReal.natCast_ne_top q) (mean_le_const _ fun out => min_le_left _ _)
  have hX' : mean run (fun out => keyCharged parameterOutput out.1.2.2.1) ≤
      Z + (q : ℝ≥0∞) * mean run (fun out => endValue (payoffA parameterOutput fixed highs remaining prepared known ρ)
        out.2) := hmin.symm.le.trans hX
  have hsolve := solve_selfBound hX' hE hfin
  change mean run (fun out => keyCharged parameterOutput out.1.2.2.1) ≤ _
  rw [mul_comm, ← div_eq_mul_inv, ENNReal.le_div_iff_mul_le (Or.inl (tsub_pos_of_lt hc).ne')
    (Or.inl (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self))]
  exact hsolve

end Sample

end Sphincs.Security.ForsPotential

namespace Sphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView HiddenReveal HiddenBridge Eager Short
open Domination ForestPrice ForestSigner SphincsFors.Security.Domination PotentialA

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

variable [Params]

open Completeness SeedModel _root_.Sphincs.Security.Graph Assembly Reduce Internalize in
attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

open Completeness SeedModel _root_.Sphincs.Security.Graph Assembly Reduce Internalize

omit [Params] in
theorem mean_bind_mono {α β γ : Type} (mx : ProbComp α) (f : α → ProbComp β) (g : α → ProbComp γ)
    (F : β → ℝ≥0∞) (G : γ → ℝ≥0∞) (h : ∀ a, mean (f a) F ≤ mean (g a) G) :
    mean (mx >>= f) F ≤ mean (mx >>= g) G := by
  rw [mean_bind, mean_bind]
  exact mean_mono _ h

/-- The rich program and the capped graph-view program have the same stopped traces. -/
theorem mean_stopped_rich (adversary : Adversary) (q : ℕ) (parameterOutput : HashOutput) (fixed : HiddenGraph.Table)
    (highs : CoordinateHighs) (remaining : RemainingOutputs) (known : Knowledge Coordinate)
    (cache : QueryCache HashSpec) (F : List (Entry HashInput) → ℝ≥0∞) :
    mean (HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
        (sampleProg adversary q parameterOutput fixed highs remaining) known cache) (stopVal 0 fun v => F v.1.2) =
      mean (HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
        (erase (trace (sampleProgram (internalize adversary) q parameterOutput fixed highs remaining))) known cache)
        (stopVal 0 fun v => F v.1.2) := by
  unfold HiddenOutside.stoppedExperiment
  rw [mean_bind, mean_bind]
  refine congrArg _ (funext fun table => ?_)
  have hprog : sampleProgram (internalize adversary) q parameterOutput fixed highs remaining =
      (fun result => Option.map outcomeWins result.1) <$> richProgram (internalize adversary) q
        (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining) :=
    cap_costGame_eq _ _ _ _
  rw [hprog, trace_map, erase_map, outside_stopped_map, mean_map]
  refine congrArg _ (funext fun x => ?_)
  cases x <;> rfl

/-- **One sample of the stopped prepared world costs at most the seed-free sample**, for a function
of the trace, a stop counting `0`. -/
theorem stoppedP_le_seedFree_sample (adversary : Adversary) (q : ℕ) (parameterOutput : HashOutput)
    (fixed : HiddenGraph.Table) (highs : CoordinateHighs) (remaining : RemainingOutputs)
    (F : List (Entry HashInput) → ℝ≥0∞) :
    mean (preparation parameterOutput fixed highs remaining >>= fun prepared =>
        exposeR (aboveList (truncateHash parameterOutput) prepared.1)
          (knownOf (truncateHash parameterOutput) fixed) >>= fun known =>
        HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
          (sampleProg adversary q parameterOutput fixed highs remaining) known prepared.2)
      (stopVal 0 fun v => F v.1.2) ≤
    mean (($ᵗ Eager.Table : ProbComp Eager.Table) >>= fun outsideTable =>
        HiddenReveal.completion (knownOf (truncateHash parameterOutput) fixed) >>= fun table =>
          hiddenRun (internalize adversary) q parameterOutput fixed highs remaining outsideTable table)
      (fun x => F x.2) := by
  set comp := erase (trace (sampleProgram (internalize adversary) q parameterOutput fixed highs remaining)) with hcomp
  set model := sampleModel parameterOutput highs with hmodel
  set known0 := knownOf (truncateHash parameterOutput) fixed with hknown0
  have hshort : OnlyShort comp :=
    OnlyC.erase (OnlyC.trace (OnlyC.cap (OnlyC.costGame (truncateHash parameterOutput)
      (GraphView.publicData (labelsOf (splitMaterial parameterOutput highs remaining fixed)
        (splitAnswers highs remaining fixed))) _) q))
  have hL : mean (preparation parameterOutput fixed highs remaining >>= fun prepared =>
        exposeR (aboveList (truncateHash parameterOutput) prepared.1) known0 >>= fun known =>
        HiddenOutside.stoppedExperiment model (sampleProg adversary q parameterOutput fixed highs remaining)
          known prepared.2) (stopVal 0 fun v => F v.1.2) =
      mean (preparation parameterOutput fixed highs remaining >>= fun prepared =>
        exposeR (aboveList (truncateHash parameterOutput) prepared.1) known0 >>= fun known =>
        Option.map Prod.fst <$> HiddenOutside.stoppedExperiment model comp known prepared.2)
        (stopVal 0 fun r => F r.2) := by
    rw [mean_bind, mean_bind]
    refine congrArg _ (funext fun prepared => ?_)
    rw [mean_bind, mean_bind]
    refine congrArg _ (funext fun known => ?_)
    rw [mean_stopped_rich, mean_map]
    refine congrArg _ (funext fun x => ?_)
    cases x <;> rfl
  rw [hL]
  unfold preparation
  rw [← mean_congr (evalDist_expose_prep model _ (truncateHash parameterOutput)
      (sampleData parameterOutput fixed highs remaining).forestKey comp hshort known0
      (aboveList (truncateHash parameterOutput)))]
  refine mean_bind_mono _ _ _ _ _ fun outsideTable => ?_
  unfold HiddenRows.stoppedExperiment
  rw [← mean_congr (evalDist_completion_exposeT
    (fun table known => HiddenRows.stopped model table
      (extend (structCache (splitMaterial parameterOutput highs remaining fixed)
        (splitAnswers highs remaining fixed)) outsideTable) comp known) _ known0)]
  refine mean_bind_mono _ _ _ _ _ fun table => ?_
  rw [hiddenRun_eq]
  exact stopped_exp_le_costRun model table _ (sampleProgram (internalize adversary) q parameterOutput fixed highs
    remaining) _ (fun r => F r.2)

/-- The seed-free experiment from a parameter output: the public and structural samples, then the
coordinate table as a completion of the known coordinates (`evalDist_seedFree_completion`). -/
noncomputable def seedFreeFrom (adversary : Adversary) (q : ℕ) (parameterOutput : HashOutput) :
    ProbComp (Option Bool × List (Entry HashInput)) := do
  let fixed ← $ᵗ HiddenGraph.Table
  let highs ← $ᵗ CoordinateHighs
  let remaining ← $ᵗ RemainingOutputs
  let outsideTable ← $ᵗ Eager.Table
  let table ← HiddenReveal.completion (knownOf (truncateHash parameterOutput) fixed)
  hiddenRun adversary q parameterOutput fixed highs remaining outsideTable table

/-- The stopped prepared world from a parameter output. -/
noncomputable def stoppedFrom (adversary : Adversary) (q : ℕ) (parameterOutput : HashOutput) :
    ProbComp (Option ((((Option Outcome × List Coordinate) × List (Entry HashInput))) × QueryCache HashSpec)) := do
  let fixed ← $ᵗ HiddenGraph.Table
  let highs ← $ᵗ CoordinateHighs
  let remaining ← $ᵗ RemainingOutputs
  let prepared ← preparation parameterOutput fixed highs remaining
  let known ← exposeR (aboveList (truncateHash parameterOutput) prepared.1)
    (knownOf (truncateHash parameterOutput) fixed)
  HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
    (sampleProg adversary q parameterOutput fixed highs remaining) known prepared.2

theorem mean_seedFree (adversary : Adversary) (q : ℕ) (F : Option Bool × List (Entry HashInput) → ℝ≥0∞) :
    mean (seedFreeExperiment adversary q) F =
      mean ($ᵗ HashOutput) fun parameterOutput => mean (seedFreeFrom adversary q parameterOutput) F := by
  rw [mean_congr (evalDist_seedFree_completion adversary q), mean_bind]
  rfl

/-- **The stopped prepared world costs at most the seed-free experiment**, for a function of the
parameter output and the trace, a stop counting `0`: the exposure, the preparation and the
completion are exact resamplings, and the stopped execution is a part of the cost run. -/
theorem stoppedFrom_le_seedFree (adversary : Adversary) (q : ℕ) (parameterOutput : HashOutput)
    (F : List (Entry HashInput) → ℝ≥0∞) :
    mean (stoppedFrom adversary q parameterOutput) (stopVal 0 fun v => F v.1.2) ≤
      mean (seedFreeFrom (internalize adversary) q parameterOutput) (fun x => F x.2) := by
  refine mean_bind_mono _ _ _ _ _ fun fixed => ?_
  refine mean_bind_mono _ _ _ _ _ fun highs => ?_
  refine mean_bind_mono _ _ _ _ _ fun remaining => ?_
  exact stoppedP_le_seedFree_sample adversary q parameterOutput fixed highs remaining F

omit [Params] in
/-- One level of averaging of an affine bound. -/
theorem mean_affine_le {α : Type} (mx : ProbComp α) (g M φ : α → ℝ≥0∞) (k A C : ℝ≥0∞)
    (h : ∀ x ∈ support mx, g x ≤ k * M x + A + C * φ x) :
    mean mx g ≤ k * mean mx M + A + C * mean mx φ := by
  refine (mean_mono_support mx h).trans ?_
  rw [mean_add, mean_add, mean_const_mul, mean_const_mul]
  exact add_le_add (add_le_add le_rfl (mean_le_const _ fun _ => le_rfl)) le_rfl

/-- The sample-independent part of the small-budget bound without its linear term. -/
noncomputable def smallRestF (q : ℕ) (B c : ℚ) : ℝ≥0∞ :=
  ((q - keygenCost : ℕ) : ℝ≥0∞) * ENNReal.ofReal (B : ℝ) +
    ν * (((Nat.choose (q - keygenCost) 2 : ℕ) : ℝ≥0∞) * rateS) +
    (((q - keygenCost : ℕ) : ℝ≥0∞) * ν) * ((q - keygenCost : ℕ) * ENNReal.ofReal (c : ℝ))

set_option maxRecDepth 100000 in
/-- **Small budgets, seed-free win, paid by the expected hash calls of the key**: the linear term
`ρ q / 2^128` of `small_seedFree_boundF` becomes `ρ / 2^128` times the expected hash calls of the
seed-free experiment on the inputs of its key, divided by `1 − q ρ / 2^128`. -/
theorem small_seedFree_trace (hb : 0 < subtreeHeight) (adversary : Adversary) (hnr : adversary.NoRepeat) (q : ℕ)
    (hq : q < 2 ^ 256)
    (ρ : ℝ) (hN : Numeric ρ (((q - keygenCost : ℕ) : ℝ) / 2 ^ 128))
    (κ : ℚ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hκ : 2 - ρ + ((q - keygenCost : ℕ) : ℝ) / 2 ^ 128 +
      (signatureLimit : ℝ) * (123 * ((2 : ℝ) ^ subtreeHeight * 2 ^ 15)⁻¹) ≤ (κ : ℝ))
    (b N : ℕ) (hbb : subtreeHeight = b) (hNN : signatureLimit = N)
    (t : H0.PoisT) (o : H0.OptF) (on : H0.OptN) (hpt : H0.checkPT t = true) (qtop : ℕ)
    (hrt : H0.checkRate b N qtop t = true) (hqtop : q - keygenCost ≤ qtop)
    (ho : H0.checkOptF b t o = true) (hon : H0.checkOptN t on = true) (hcthr : (o.cthr : ℝ) ≤ ρ / 2 ^ 128)
    (hc : (q : ℝ≥0∞) * ENNReal.ofReal (ρ / 2 ^ 128) < 1) :
    Pr{let x ← seedFreeExperiment (internalize adversary) q}[Win x] ≤
      ENNReal.ofReal (ρ / 2 ^ 128) * (1 - (q : ℝ≥0∞) * ENNReal.ofReal (ρ / 2 ^ 128))⁻¹ *
          mean ($ᵗ HashOutput) (fun parameterOutput => mean (seedFreeFrom (internalize adversary) q parameterOutput)
            fun x => min (q : ℝ≥0∞) (keyCharged parameterOutput x.2)) +
        (smallRestF q o.B (κ * ((2 ^ b * on.En : ℚ) / 2)) +
          2 * lam (H0.LmaxOf (q - keygenCost)) 0 (q - keygenCost)) + smallFailF q * expectedFail := by
  refine le_trans (seedFree_le_exposeP adversary q) ?_
  set k : ℝ≥0∞ := ENNReal.ofReal (ρ / 2 ^ 128) * (1 - (q : ℝ≥0∞) * ENNReal.ofReal (ρ / 2 ^ 128))⁻¹ with hk
  set A := smallRestF q o.B (κ * ((2 ^ b * on.En : ℚ) / 2)) +
    2 * lam (H0.LmaxOf (q - keygenCost)) 0 (q - keygenCost) with hA
  set C := smallFailF q with hC
  have hκ1R : (κ : ℝ) ≤ 1 := by exact_mod_cast hκ1
  have hsample : ∀ parameterOutput fixed highs remaining prepared,
      prepared ∈ support (preparation parameterOutput fixed highs remaining) →
      ∀ known ∈ support (exposeR (aboveList (truncateHash parameterOutput) prepared.1)
        (knownOf (truncateHash parameterOutput) fixed)),
      mean (HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
          (sampleProg adversary q parameterOutput fixed highs remaining) known prepared.2)
          (fun x => if (HiddenReveal.StopOr RichWin) x then 1 else 0) ≤
        k * mean (HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
          (sampleProg adversary q parameterOutput fixed highs remaining) known prepared.2)
          (stopVal 0 fun v => min (q : ℝ≥0∞) (keyCharged parameterOutput v.1.2)) +
          A + C * failMass (failSet prepared.1) := by
    intro parameterOutput fixed highs remaining prepared hprepared known hknown
    rw [mean_indicator]
    refine le_trans (sample_boundF_trace hb adversary hnr q hq parameterOutput fixed highs remaining prepared
      hprepared known hknown ρ hN (κ : ℝ) hκ hκ1R b N hbb hNN t o on hpt qtop hrt hqtop ho hon hcthr hc)
      (le_of_eq ?_)
    rw [hk, hA, hC]
    unfold smallRestF smallFailF
    rw [Rat.cast_mul, ENNReal.ofReal_mul (Rat.cast_nonneg.2 hκ0)]
    ring
  set φ : HashOutput → ℝ≥0∞ := fun parameterOutput =>
    mean ($ᵗ HiddenGraph.Table) fun fixed => mean ($ᵗ CoordinateHighs) fun highs =>
      mean ($ᵗ RemainingOutputs) fun remaining => mean (preparation parameterOutput fixed highs remaining)
        fun prepared => failMass (failSet prepared.1) with hφ
  have hpo : ∀ parameterOutput,
      mean (stoppedFrom adversary q parameterOutput) (fun x => if (HiddenReveal.StopOr RichWin) x then 1 else 0) ≤
        k * mean (stoppedFrom adversary q parameterOutput)
          (stopVal 0 fun v => min (q : ℝ≥0∞) (keyCharged parameterOutput v.1.2)) + A + C * φ parameterOutput := by
    intro parameterOutput
    unfold stoppedFrom
    simp only [hφ, mean_bind]
    refine mean_affine_le _ _ _ _ k A C fun fixed _ => ?_
    refine mean_affine_le _ _ _ _ k A C fun highs _ => ?_
    refine mean_affine_le _ _ _ _ k A C fun remaining _ => ?_
    refine mean_affine_le _ _ _ _ k A C fun prepared hprepared => ?_
    refine (mean_affine_le _ _ _ (fun _ => failMass (failSet prepared.1)) k A C fun known hknown =>
      hsample parameterOutput fixed highs remaining prepared hprepared known hknown).trans ?_
    exact add_le_add le_rfl (mul_le_mul' le_rfl (mean_le_const _ fun _ => le_rfl))
  rw [← mean_indicator]
  change mean (($ᵗ HashOutput : ProbComp HashOutput) >>= fun parameterOutput => stoppedFrom adversary q parameterOutput)
    _ ≤ _
  rw [mean_bind]
  refine (mean_affine_le _ _ _ _ k A C fun parameterOutput _ => hpo parameterOutput).trans ?_
  refine add_le_add (add_le_add (mul_le_mul' le_rfl (mean_mono _ fun parameterOutput =>
    stoppedFrom_le_seedFree adversary q parameterOutput
      (fun e => min (q : ℝ≥0∞) (keyCharged parameterOutput e)))) le_rfl) (le_of_eq ?_)
  rw [hφ]
  unfold expectedFail mean
  rfl

end Sphincs.Security.ForsPotential
